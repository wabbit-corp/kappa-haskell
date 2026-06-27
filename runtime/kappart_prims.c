/* kappart_prims.c — the kpf_* primitive entry points, the IO builtins, the
 * algebraic-effect runtime, and the IO trampoline.
 *
 * Split out of kappart.c (see kappart_internal.h).  Owns the kpf_io_* IO
 * builtins, the §18.1 effect runtime (eff_bind_k / kpf___effBind /
 * kpf___handleEff / ...), the bytes/option/hash helpers, kvalue_rep_eq, every
 * kpf_* direct entry, and the IO executor (kdefer_frame + krun_io /
 * krun_io_checked).  The pure kp_* helpers it forwards to live in
 * kappart_bignum.c / kappart_show.c; the unicode helpers come from
 * kappart_unicode.c — all reached through kappart_internal.h / kappart.h. */
#include "kappart.h"
#include "kappart_internal.h"

#include <gmp.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
/* §34.5.3 IO builtin direct entry points (codegen calls these via K_NATIVE,
 * never by name).  The pure builtins are the kp_ and kpf_ helpers below; these
 * kpf_io_ entries are the effectful ones the do-kernel sequences. */
KValue *kpf_io_printString(KValue **a) {
  if (a[0]->tag != K_STR) krt_fail("printString: argument is not a String");
  fwrite(a[0]->as.str.p, 1, a[0]->as.str.len, stdout);
  return kunit();
}
KValue *kpf_io_printlnString(KValue **a) {
  if (a[0]->tag != K_STR) krt_fail("printlnString: argument is not a String");
  fwrite(a[0]->as.str.p, 1, a[0]->as.str.len, stdout);
  fputc('\n', stdout);
  return kunit();
}
KValue *kpf_io_ioPure(KValue **a) { return a[0]; }
KValue *kpf_io_ioBind(KValue **a) {
  KValue *r = krun_io(a[0]);
  if (kis_fail(r)) return r;
  return krun_io(kapp(a[1], r));
}
KValue *kpf_io_ioThen(KValue **a) {
  KValue *r = krun_io(a[0]);
  if (kis_fail(r)) return r;
  return krun_io(a[1]);
}
KValue *kpf_io_throwIO(KValue **a) { return kfail(a[0]); }
KValue *kpf_io_catchIO(KValue **a) {
  KValue *r = krun_io(a[0]);
  if (kis_fail(r)) return krun_io(kapp(a[1], r->as.fail.err));
  return r;
}
KValue *kpf_io_finallyIO(KValue **a) {
  KValue *r = krun_io(a[0]);
  KValue *fr = krun_io(a[1]);
  if (kis_fail(r)) return r;
  if (kis_fail(fr)) return fr;
  return r;
}
KValue *kpf_io_newRef(KValue **a) { return kref_new(a[0]); }
KValue *kpf_io_readRef(KValue **a) { return kref_get(a[0]); }
KValue *kpf_io_writeRef(KValue **a) { return kref_set(a[0], a[1]); }

/* §18.1.13 STM, single-agent semantics — matching the reference interpreter
 * (Kappa.Interp.stmAtomically, which runs an STM action through the very same
 * IO runner): a TVar is a mutable cell and `atomically` runs the transaction
 * directly.  A transaction that never `retry`s commits in one pass, which is
 * everything expressible without a concurrent writer.  Real multi-fiber STM —
 * journaled reads, optimistic commit, retry-parking — lives in the kappart2
 * scheduler (stm.c) and is reached once the do-kernel is CPS-lowered so a
 * transaction can suspend a fiber. */
KValue *kpf_io_newTVar(KValue **a) { return kref_new(a[0]); }
KValue *kpf_io_readTVar(KValue **a) { return kref_get(a[0]); }
KValue *kpf_io_writeTVar(KValue **a) { return kref_set(a[0], a[1]); }
KValue *kpf_io_atomically(KValue **a) { return krun_io(a[0]); }
KValue *kpf_io_retry(KValue **a) {
  (void)a;
  /* Single-agent: there is no concurrent writer to advance a read TVar, so a
   * blocked transaction can never make progress.  Fail loudly rather than
   * livelock; blocking retry needs the concurrent scheduler. */
  krt_fail("STM retry: the single-agent native runtime has no concurrent writer "
           "to wake a blocked transaction (needs the kappart2 scheduler)");
}
KValue *kpf_io_check(KValue **a) {
  /* check b = if b then pure () else retry (§18.1.13). */
  return kas_bool(a[0]) ? kunit() : kpf_io_retry(a);
}
/* ── §18.1 algebraic-effect runtime ───────────────────────────────────
 * Mirrors Kappa.Eval.evalEffPrim over the untyped OpCall tree
 * (`__EffPure v` / `__EffOp label op payload cont`).  Labels are string
 * tokens (the label global's name); the handler `ops` is a record keyed by
 * operation name.  Continuations are GC closures built with kclo/kpush. */
KValue *kpf___effBind(KValue **a);
KValue *kpf___handleEff(KValue **a);
KValue *kpf___absurd(KValue **a);

static KValue *eff_bind_k(KEnv *env, KValue *x) {
  /* env: kvar0 = f, kvar1 = cont.  \x -> __effBind (cont x) f */
  KValue *f = kvar(env, 0), *cont = kvar(env, 1);
  KValue *args[2]; args[0] = kapp(cont, x); args[1] = f;
  return kpf___effBind(args);
}

/* §12.4.3 first-class borrowed views. A borrow carries no runtime
 * witness (it IS its value), so captureBorrow reifies the view as the
 * value itself and withBorrowView eliminates it by reinstating the
 * borrowed binder (applying the continuation to the viewed value). */
KValue *kpf_captureBorrow(KValue **a) { return a[0]; }
KValue *kpf_withBorrowView(KValue **a) { return kapp(a[1], a[0]); }

/* runPure : Eff <[]> a -> a  (§18.1.14) */
KValue *kpf_runPure(KValue **a) {
  if (kctor_tagid(a[0]) == KCT_EFFPURE) return kctor_arg(a[0], 0);
  krt_fail("runPure: computation is not fully handled (an operation escaped its handlers)");
  return 0;
}

KValue *kpf___absurd(KValue **a) {
  (void)a;
  krt_fail("__absurd: attempted to eliminate a Void value");
  return 0;
}

/* __effBind m f : monadic bind over the Eff tree (§18.1.14) */
KValue *kpf___effBind(KValue **a) {
  KValue *m = a[0], *f = a[1];
  int t = kctor_tagid(m);
  if (t == KCT_EFFPURE) return kapp(f, kctor_arg(m, 0));
  if (t == KCT_EFFOP) {
    KEnv *env = kpush(f, kpush(kctor_arg(m, 3), 0)); /* kvar0=f, kvar1=cont */
    KValue *args[4];
    args[0] = kctor_arg(m, 0); args[1] = kctor_arg(m, 1); args[2] = kctor_arg(m, 2);
    args[3] = kclo(eff_bind_k, env);
    return kctor(KCT_EFFOP, "__EffOp", 4, args);
  }
  krt_fail("__effBind: not an Eff value");
  return 0;
}

/* env for the deep/propagate resumption: kvar0=cont,1=ops,2=ret,3=label,4=deep */
static KValue *eff_reinstall_k(KEnv *env, KValue *x) {
  KValue *cont = kvar(env, 0), *ops = kvar(env, 1), *ret = kvar(env, 2),
         *label = kvar(env, 3), *deepV = kvar(env, 4);
  KValue *args[5];
  args[0] = deepV; args[1] = label; args[2] = ret; args[3] = ops;
  args[4] = kapp(cont, x);
  return kpf___handleEff(args);
}
static int eff_label_eq(KValue *x, KValue *y) {
  return x->tag == K_STR && y->tag == K_STR && x->as.str.len == y->as.str.len &&
         memcmp(x->as.str.p, y->as.str.p, x->as.str.len) == 0;
}

/* __handleEff deep label ret ops comp  (§18.1.21/.22) */
KValue *kpf___handleEff(KValue **a) {
  KValue *deepV = a[0], *label = a[1], *ret = a[2], *ops = a[3], *comp = a[4];
  int t = kctor_tagid(comp);
  if (t == KCT_EFFPURE) return kapp(ret, kctor_arg(comp, 0));
  if (t == KCT_EFFOP) {
    KValue *l = kctor_arg(comp, 0), *op = kctor_arg(comp, 1),
           *pay = kctor_arg(comp, 2), *cont = kctor_arg(comp, 3);
    KEnv *renv = kpush(cont, kpush(ops, kpush(ret, kpush(label, kpush(deepV, 0)))));
    if (eff_label_eq(l, label)) {
      KValue *clause = kproj(ops, op->as.str.p); /* op is a null-terminated KString */
      KValue *k = (kctor_tagid(deepV) == KCT_TRUE) ? kclo(eff_reinstall_k, renv) : cont;
      return kapp(kapp(clause, pay), k);
    } else {
      KValue *args[4];
      args[0] = l; args[1] = op; args[2] = pay; args[3] = kclo(eff_reinstall_k, renv);
      return kctor(KCT_EFFOP, "__EffOp", 4, args);
    }
  }
  krt_fail("__handleEff: not an Eff value");
  return 0;
}
/* first index of needle in hay, or -1 (portable; no memmem dependency). */
static long bytes_index_of(const unsigned char *hay, size_t hl, const unsigned char *ned, size_t nl) {
  if (nl == 0) return 0;
  if (nl > hl) return -1;
  for (size_t i = 0; i + nl <= hl; i++)
    if (memcmp(hay + i, ned, nl) == 0) return (long)i;
  return -1;
}

static int bytes_cmp(KValue *a, KValue *b) { /* lexicographic by byte */
  size_t la = a->as.bytes.len, lb = b->as.bytes.len, m = la < lb ? la : lb;
  int c = memcmp(a->as.bytes.p, b->as.bytes.p, m);
  if (c != 0) return c < 0 ? -1 : 1;
  return la < lb ? -1 : (la > lb ? 1 : 0);
}

/* §29.1 representation equality (for atomicCompareExchange): structural
 * equality over the canonical first-order runtime values, matching the
 * interpreter's `convertible` on the atomic representation.  Integers
 * compare by value across the inline/bignum boundary. */
int kvalue_rep_eq(KValue *a, KValue *b) {
  if (a == b) return 1;   /* immediates canonicalise: word identity == value equality */
  /* §5.3: any Int/Int pair normalizes across immediate / inline / bignum. */
  if (kis_int_any(a) && kis_int_any(b)) return kint_cmp(a, b) == 0;
  /* Stage 1d/1e: a b011 packed ctor (one OR two fields) compares STRUCTURALLY
   * against a ctor in any rep (another packed word, or a boxed K_CTOR) — same tag
   * id, same arity AND recursively-equal fields — through the immediate-aware
   * accessors.  Two packed words of the same value are already caught by a==b
   * (canonical), so a packed-vs-packed pair that reaches here differs; the
   * structural compare still gives the right answer and the boxed-vs-packed
   * direction satisfies Pair 1 2 == Pair 1 2 defensively even though
   * canonicalization means a boxed packing-eligible ctor should not normally
   * arise. */
  if (kis_imm_packed(a) || kis_imm_packed(b)) {
    int ta = kctor_tagid(a), tb = kctor_tagid(b);
    if (ta < 0 || ta != tb) return 0;          /* one side not a ctor, or different ctor */
    int na = kctor_argc(a);
    if (na != kctor_argc(b)) return 0;          /* differing arity → unequal */
    for (int i = 0; i < na; i++)
      if (!kvalue_rep_eq(kctor_arg(a, i), kctor_arg(b, i))) return 0;
    return 1;
  }
  /* Past the Int/packed cases, an immediate paired with a non-Int (or two
   * immediates of different value, already ruled out by a==b) is unequal — guard
   * the deref. */
  if (kis_imm(a) || kis_imm(b)) return 0;
  if (a->tag != b->tag) return 0;
  switch (a->tag) {
    case K_DBL: return a->as.d == b->as.d;
    case K_CHR: return a->as.chr == b->as.chr;
    case K_UNIT: return 1;
    case K_BYTE: return a->as.byte == b->as.byte;
    case K_STR:
      return a->as.str.len == b->as.str.len && memcmp(a->as.str.p, b->as.str.p, a->as.str.len) == 0;
    case K_BYTES:
      return a->as.bytes.len == b->as.bytes.len && memcmp(a->as.bytes.p, b->as.bytes.p, a->as.bytes.len) == 0;
    case K_CTOR: {
      if (strcmp(a->as.ctor.name, b->as.ctor.name) != 0 || a->as.ctor.argc != b->as.ctor.argc) return 0;
      for (int i = 0; i < a->as.ctor.argc; i++)
        if (!kvalue_rep_eq(a->as.ctor.args[i], b->as.ctor.args[i])) return 0;
      return 1;
    }
    case K_REC: {
      if (a->as.rec.n != b->as.rec.n) return 0;
      for (int i = 0; i < a->as.rec.n; i++)
        if (strcmp(a->as.rec.names[i], b->as.rec.names[i]) != 0 ||
            !kvalue_rep_eq(a->as.rec.vals[i], b->as.rec.vals[i])) return 0;
      return 1;
    }
    case K_VARIANT:
      return strcmp(a->as.var.tag, b->as.var.tag) == 0 && kvalue_rep_eq(a->as.var.payload, b->as.var.payload);
    default:
      return 0; /* closures/thunks/etc. are not canonical atomic values */
  }
}

/* The §29.3 FNV-1a lane: state mixed with 8 little-endian bytes of v. */
static uint64_t fnv_mix_u64(uint64_t s, uint64_t v) {
  for (int i = 0; i < 8; i++) s = (s ^ ((v >> (8 * i)) & 0xff)) * 1099511628211ULL;
  return s;
}
static uint64_t fnv_mix_bytes(uint64_t s, const unsigned char *p, size_t n) {
  for (size_t i = 0; i < n; i++) s = (s ^ p[i]) * 1099511628211ULL;
  return s;
}

/* Low 64 bits of an integer value in Haskell floor-mod sense (matches
 * `fromIntegral :: Integer -> Word64`).  K_INT casts directly (two's
 * complement); K_BIGINT reduces modulo 2^64. */
static uint64_t kint_low64(KValue *v) {
  if (kis_imm_int(v)) return (uint64_t)kimm_int_val(v);   /* Stage 1 immediate */
  if (v->tag == K_INT) return (uint64_t)v->as.i;
  if (v->tag == K_BIGINT) {
    mpz_t r; mpz_init(r);
    mpz_fdiv_r_2exp(r, (const __mpz_struct *)v->as.big.mpz, 64); /* 0 <= r < 2^64 */
    uint64_t lo = 0; size_t count = 0;
    mpz_export(&lo, &count, -1, sizeof(uint64_t), 0, 0, r);      /* little-endian limb */
    mpz_clear(r);
    return lo;
  }
  krt_fail("hash mix on a non-integer value");
}
/* ── per-primitive direct entry points (codegen calls these directly;
 * the string dispatcher below is the bootstrap/interpreter path only). */
KValue *kpf_addInt(KValue **a) {
  return kp_addInt(a[0], a[1]);
}
KValue *kpf_subInt(KValue **a) {
  return kp_subInt(a[0], a[1]);
}
KValue *kpf_mulInt(KValue **a) {
  return kp_mulInt(a[0], a[1]);
}
KValue *kpf_divInt(KValue **a) {
  return kp_divInt(a[0], a[1]);
}
KValue *kpf_modInt(KValue **a) {
  return kp_modInt(a[0], a[1]);
}
KValue *kpf_negInt(KValue **a) {
  return kp_negInt(a[0]);
}
KValue *kpf_eqInt(KValue **a) {
  return kp_eqInt(a[0], a[1]);
}
KValue *kpf_ltInt(KValue **a) {
  return kp_ltInt(a[0], a[1]);
}
KValue *kpf_leInt(KValue **a) {
  return kp_leInt(a[0], a[1]);
}
KValue *kpf_addDouble(KValue **a) {
  return kp_addDouble(a[0], a[1]);
}
KValue *kpf_subDouble(KValue **a) {
  return kp_subDouble(a[0], a[1]);
}
KValue *kpf_mulDouble(KValue **a) {
  return kp_mulDouble(a[0], a[1]);
}
KValue *kpf_divDouble(KValue **a) {
  return kp_divDouble(a[0], a[1]);
}
KValue *kpf_negDouble(KValue **a) {
  return kp_negDouble(a[0]);
}
KValue *kpf_ltDouble(KValue **a) {
  return kp_ltDouble(a[0], a[1]);
}
KValue *kpf_floatEq(KValue **a) {
  return kp_floatEq(a[0], a[1]);
}
KValue *kpf_eqDouble(KValue **a) {
  return kp_eqDouble(a[0], a[1]);
}
KValue *kpf_stringAppend(KValue **a) {
  return kp_stringAppend(a[0], a[1]);
}
KValue *kpf_eqStr(KValue **a) {
  return kp_eqStr(a[0], a[1]);
}
KValue *kpf_ltStr(KValue **a) {
  return kp_ltStr(a[0], a[1]);
}
KValue *kpf_eqScalar(KValue **a) {
  return kp_eqScalar(a[0], a[1]);
}
KValue *kpf_ltScalar(KValue **a) {
  return kp_ltScalar(a[0], a[1]);
}
KValue *kpf_natToInt(KValue **a) {
  return a[0];
}
KValue *kpf_intToNat(KValue **a) {
  int neg;
  if (kis_int_word(a[0])) neg = kint_word(a[0]) < 0;       /* immediate or inline */
  else neg = mpz_sgn((const __mpz_struct *)a[0]->as.big.mpz) < 0;
  if (neg) krt_fail("intToNat: negative Int has no Nat image");
  return a[0];
}
KValue *kpf_intToDouble(KValue **a) {
  return kp_intToDouble(a[0]);
}
KValue *kpf_primitiveIntToString(KValue **a) {
  return show_int_val(a[0]);
}
KValue *kpf_showInt(KValue **a) {
  return kp_showInt(a[0]);
}
KValue *kpf_showDouble(KValue **a) {
  return kp_showDouble(a[0]);
}
KValue *kpf_showScalar(KValue **a) {
  return kp_showScalar(a[0]);
}
KValue *kpf_showStringLit(KValue **a) {
  return kp_showStringLit(a[0]);
}
KValue *kpf___ratOfInt(KValue **a) {
  mpz_t n, d; mpz_init(d); mpz_set_ui(d, 1); mpz_init(n); kload_mpz(a[0], n);
    return krat(n, d);
}
KValue *kpf___ratNum(KValue **a) {
  mpz_t n, d; mpz_init(n); mpz_init(d); as_rat(a[0], n, d); return kfrom_mpz(n);
}
KValue *kpf___ratDen(KValue **a) {
  mpz_t n, d; mpz_init(n); mpz_init(d); as_rat(a[0], n, d); return kfrom_mpz(d);
}
KValue *kpf_addRat(KValue **a) {
  return rat_addsub(a[0], a[1], 0);
}
KValue *kpf_subRat(KValue **a) {
  return rat_addsub(a[0], a[1], 1);
}
KValue *kpf_mulRat(KValue **a) {
  mpz_t a1, b1, c1, d1, n, den; mpz_inits(a1, b1, c1, d1, n, den, NULL);
    as_rat(a[0], a1, b1); as_rat(a[1], c1, d1);
    mpz_mul(n, a1, c1); mpz_mul(den, b1, d1); return krat(n, den);
}
KValue *kpf_divRat(KValue **a) {
  mpz_t a1, b1, c1, d1, n, den; mpz_inits(a1, b1, c1, d1, n, den, NULL);
    as_rat(a[0], a1, b1); as_rat(a[1], c1, d1);
    if (mpz_sgn(c1) == 0) krt_fail("divRat: division by zero");
    mpz_mul(n, a1, d1); mpz_mul(den, b1, c1); return krat(n, den);
}
KValue *kpf_negRat(KValue **a) {
  mpz_t n, d; mpz_init(n); mpz_init(d); as_rat(a[0], n, d); mpz_neg(n, n); return krat(n, d);
}
KValue *kpf_eqRat(KValue **a) {
  mpz_t a1, b1, c1, d1, l, r; mpz_inits(a1, b1, c1, d1, l, r, NULL);
    as_rat(a[0], a1, b1); as_rat(a[1], c1, d1);
    mpz_mul(l, a1, d1); mpz_mul(r, c1, b1); /* dens positive, so cross-mul preserves order */
    int c = mpz_cmp(l, r);
    return kbool(1 ? c == 0 : c < 0);
}
KValue *kpf_ltRat(KValue **a) {
  mpz_t a1, b1, c1, d1, l, r; mpz_inits(a1, b1, c1, d1, l, r, NULL);
    as_rat(a[0], a1, b1); as_rat(a[1], c1, d1);
    mpz_mul(l, a1, d1); mpz_mul(r, c1, b1); /* dens positive, so cross-mul preserves order */
    int c = mpz_cmp(l, r);
    return kbool(0 ? c == 0 : c < 0);
}
KValue *kpf_showRat(KValue **a) {
  mpz_t n, d; mpz_init(n); mpz_init(d); as_rat(a[0], n, d);
    /* A small Rational (e.g. 1/2) is a b011 packed word now, so read its parts
     * through the rep-agnostic kctor_arg rather than a raw deref. */
    KValue *ns = show_int_val(kctor_arg(a[0], 0));
    if (mpz_cmp_ui(d, 1) == 0) return ns;
    return str_append(str_append(ns, kstr0("/")), show_int_val(kctor_arg(a[0], 1)));
}
KValue *kpf_ratOfDouble(KValue **a) {
  double x = kas_dbl(a[0]);
    if (isnan(x) || isinf(x)) { mpz_t n, d; mpz_init(n); mpz_init_set_ui(d, 1); return krat(n, d); }
    int e2; double frac = frexp(x, &e2);            /* x = frac * 2^e2, 0.5<=|frac|<1 */
    long long mant = (long long)ldexp(frac, 53);    /* exact integer significand */
    int sh = e2 - 53;
    mpz_t n, d; mpz_init(n); kmpz_set_i64(n, (int64_t)mant); mpz_init_set_ui(d, 1);
    if (sh >= 0) mpz_mul_2exp(n, n, (unsigned)sh); else mpz_mul_2exp(d, d, (unsigned)(-sh));
    return krat(n, d);
}
KValue *kpf_eqByte(KValue **a) {
  return kp_eqByte(a[0], a[1]);
}
KValue *kpf_ltByte(KValue **a) {
  return kp_ltByte(a[0], a[1]);
}
KValue *kpf_showByte(KValue **a) {
  char t[8]; snprintf(t, sizeof t, "b'\\x%02x'", a[0]->as.byte); return kstr0(t);
}
KValue *kpf_eqBytes(KValue **a) {
  return kbool(bytes_cmp(a[0], a[1]) == 0);
}
KValue *kpf_ltBytes(KValue **a) {
  return kbool(bytes_cmp(a[0], a[1]) < 0);
}
KValue *kpf_showBytes(KValue **a) {
  sbuf b; sb_init(&b); sb_puts(&b, "0x");
    for (size_t i = 0; i < a[0]->as.bytes.len; i++) { char t[3]; snprintf(t, 3, "%02x", a[0]->as.bytes.p[i]); sb_puts(&b, t); }
    return sb_to_str(&b);
}
KValue *kpf_eqGrapheme(KValue **a) {
  return kbool(klit_eq(a[0], a[1]));
}
KValue *kpf_showGrapheme(KValue **a) {
  return str_append(str_append(kstr0("g'"), a[0]), kstr0("'"));
}
KValue *kpf___bytesEmpty(KValue **a) {
  return kbytes((const unsigned char *)"", 0);
}
KValue *kpf___bytesSingleton(KValue **a) {
  unsigned char w = a[0]->as.byte; return kbytes(&w, 1);
}
KValue *kpf___bytesLength(KValue **a) {
  return kint((int64_t)a[0]->as.bytes.len);
}
KValue *kpf___bytesIsEmpty(KValue **a) {
  return kbool(a[0]->as.bytes.len == 0);
}
KValue *kpf___bytesGet(KValue **a) {
  int64_t i = kas_int(a[1]);
    if (i >= 0 && i < (int64_t)a[0]->as.bytes.len) return ksome(kbyte(a[0]->as.bytes.p[i]));
    return knone();
}
KValue *kpf___bytesIndexUnsafe(KValue **a) {
  int64_t i = kas_int(a[1]);
    if (i < 0 || i >= (int64_t)a[0]->as.bytes.len) krt_fail("__bytesIndexUnsafe: out of range");
    return kbyte(a[0]->as.bytes.p[i]);
}
KValue *kpf___bytesAppend(KValue **a) {
  size_t la = a[0]->as.bytes.len, lb = a[1]->as.bytes.len;
    unsigned char *buf = (unsigned char *)kgc_alloc_atomic(la + lb ? la + lb : 1);
    memcpy(buf, a[0]->as.bytes.p, la); memcpy(buf + la, a[1]->as.bytes.p, lb);
    return kbytes(buf, la + lb);
}
KValue *kpf___bytesSlice(KValue **a) {
  int64_t st = kas_int(a[1]), ln = kas_int(a[2]); size_t len = a[0]->as.bytes.len;
    if (st < 0) st = 0;
    if (st > (int64_t)len) st = (int64_t)len;
    if (ln < 0) ln = 0;
    if (st + ln > (int64_t)len) ln = (int64_t)len - st;
    return kbytes(a[0]->as.bytes.p + st, (size_t)ln);
}
KValue *kpf___bytesTake(KValue **a) {
  int64_t n = kas_int(a[0]); size_t len = a[1]->as.bytes.len; if (n < 0) n = 0; if (n > (int64_t)len) n = (int64_t)len;
    return kbytes(a[1]->as.bytes.p, (size_t)n);
}
KValue *kpf___bytesDrop(KValue **a) {
  int64_t n = kas_int(a[0]); size_t len = a[1]->as.bytes.len; if (n < 0) n = 0; if (n > (int64_t)len) n = (int64_t)len;
    return kbytes(a[1]->as.bytes.p + n, len - (size_t)n);
}
KValue *kpf___bytesStartsWith(KValue **a) {
  size_t pl = a[0]->as.bytes.len, hl = a[1]->as.bytes.len;
    return kbool(pl <= hl && memcmp(a[1]->as.bytes.p, a[0]->as.bytes.p, pl) == 0);
}
KValue *kpf___bytesEndsWith(KValue **a) {
  size_t sl = a[0]->as.bytes.len, hl = a[1]->as.bytes.len;
    return kbool(sl <= hl && memcmp(a[1]->as.bytes.p + (hl - sl), a[0]->as.bytes.p, sl) == 0);
}
KValue *kpf___bytesContains(KValue **a) {
  return kbool(bytes_index_of(a[1]->as.bytes.p, a[1]->as.bytes.len, a[0]->as.bytes.p, a[0]->as.bytes.len) >= 0);
}
KValue *kpf___bytesFind(KValue **a) {
  unsigned char w = a[0]->as.byte;
    for (size_t i = 0; i < a[1]->as.bytes.len; i++) if (a[1]->as.bytes.p[i] == w) return ksome(kint((int64_t)i));
    return knone();
}
KValue *kpf___bytesBreakIndex(KValue **a) {
  long ix = bytes_index_of(a[1]->as.bytes.p, a[1]->as.bytes.len, a[0]->as.bytes.p, a[0]->as.bytes.len);
    return ix < 0 ? knone() : ksome(kint((int64_t)ix));
}
KValue *kpf___bytesToList(KValue **a) {
  KValue *acc = knil();
    for (size_t i = a[0]->as.bytes.len; i > 0; i--) acc = kcons(kbyte(a[0]->as.bytes.p[i - 1]), acc);
    return acc;
}
KValue *kpf___bytesFromList(KValue **a) {
  /* count then fill */
    size_t n = 0; for (KValue *v = a[0]; kis_cons(v); v = kctor_arg(v, 1)) n++;
    unsigned char *buf = (unsigned char *)kgc_alloc_atomic(n ? n : 1); size_t i = 0;
    for (KValue *v = a[0]; kis_cons(v); v = kctor_arg(v, 1)) buf[i++] = kctor_arg(v, 0)->as.byte;
    return kbytes(buf, n);
}
KValue *kpf___bytesCompact(KValue **a) {
  return a[0];
}
KValue *kpf___newBytesBuilder(KValue **a) {
  return kbytes((const unsigned char *)"", 0);
}
KValue *kpf___bytesBuilderByte(KValue **a) {
  /* (byte, builder) -> builder */
    size_t n = a[1]->as.bytes.len;
    unsigned char *buf = (unsigned char *)kgc_alloc_atomic(n + 1);
    memcpy(buf, a[1]->as.bytes.p, n); buf[n] = a[0]->as.byte;
    return kbytes(buf, n + 1);
}
KValue *kpf___bytesBuilderBytes(KValue **a) {
  /* (bytes, builder) -> builder */
    size_t na = a[1]->as.bytes.len, nb = a[0]->as.bytes.len;
    unsigned char *buf = (unsigned char *)kgc_alloc_atomic(na + nb ? na + nb : 1);
    memcpy(buf, a[1]->as.bytes.p, na); memcpy(buf + na, a[0]->as.bytes.p, nb);
    return kbytes(buf, na + nb);
}
KValue *kpf___finishBytesBuilder(KValue **a) {
  return a[0];
}
KValue *kpf___utf8Bytes(KValue **a) {
  return kbytes((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len);
}
KValue *kpf___utf8Valid(KValue **a) {
  return kbool(utf8_valid_all(a[0]->as.bytes.p, a[0]->as.bytes.len));
}
KValue *kpf___decodeUtf8Lossy(KValue **a) {
  /* Lenient decode (one U+FFFD per ill-formed maximal subpart).  The
     * std.unicode wrapper only calls this after __utf8Valid succeeds, so
     * the reachable case is the exact identity decode of valid UTF-8. */
    const unsigned char *p = a[0]->as.bytes.p, *end = p + a[0]->as.bytes.len;
    sbuf b; sb_init(&b);
    while (p < end) {
      uint32_t cp; int n = utf8_strict(p, end, &cp);
      if (n > 0) { for (int i = 0; i < n; i++) sb_putc(&b, (char)p[i]); p += n; }
      else { sb_puts(&b, "\xEF\xBF\xBD"); if (n == 0) p = end; else p += 1; }
    }
    return sb_to_str(&b);
}
KValue *kpf___byteLength(KValue **a) {
  return kint((int64_t)a[0]->as.str.len);
}
KValue *kpf___uniScalarValue(KValue **a) {
  return kint((int64_t)a[0]->as.chr);
}
KValue *kpf___scalarInRange(KValue **a) {
  int64_t n = kas_int(a[0]);
    return kbool(n >= 0 && n <= 0x10FFFF && !(n >= 0xD800 && n <= 0xDFFF));
}
KValue *kpf___scalarOfValue(KValue **a) {
  int64_t n = kas_int(a[0]);
    if (n >= 0 && n <= 0x10FFFF && !(n >= 0xD800 && n <= 0xDFFF)) return kchr((uint32_t)n);
    krt_fail("__scalarOfValue: value is not a Unicode scalar");
}
KValue *kpf___scalarToString(KValue **a) {
  sbuf b; sb_init(&b); utf8_encode(a[0]->as.chr, &b); return sb_to_str(&b);
}
KValue *kpf___scalarCount(KValue **a) {
  return kint((int64_t)utf8_scalar_count((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len));
}
KValue *kpf___stringScalars(KValue **a) {
  const unsigned char *p = (const unsigned char *)a[0]->as.str.p, *end = p + a[0]->as.str.len;
    KValue *acc = knil();
    /* collect codepoints then fold right-to-left into a cons list */
    size_t cnt = utf8_scalar_count(p, a[0]->as.str.len);
    KValue **tmp = (KValue **)kgc_alloc(sizeof(KValue *) * (cnt ? cnt : 1));
    size_t i = 0; const unsigned char *q = p;
    while (q < end) { uint32_t cp; int k = utf8_next(q, end, &cp); q += (k > 0 ? k : 1); tmp[i++] = kchr(cp); }
    for (size_t j = cnt; j > 0; j--) acc = kcons(tmp[j - 1], acc);
    return acc;
}
KValue *kpf___byteToNat(KValue **a) {
  return kint((int64_t)a[0]->as.byte);
}
KValue *kpf___natToByte(KValue **a) {
  return kbyte((unsigned char)(kint_low64(a[0]) & 0xff));
}
KValue *kpf___graphemeToString(KValue **a) {
  return a[0];
}
KValue *kpf___queryFromList(KValue **a) {
  return a[0];
}
KValue *kpf_unsafeConsume(KValue **a) {
  return kunit();
}
KValue *kpf___arrayIndexUnsafe(KValue **a) {
  KValue *v = a[0]; int64_t i = kas_int(a[1]);
    while (kis_cons(v)) { if (i <= 0) return kctor_arg(v, 0); v = kctor_arg(v, 1); i--; }
    krt_fail("__arrayIndexUnsafe: index out of range");
}
KValue *kpf___rangeEnum(KValue **a) {
  int ex = kas_bool(a[2]); KValue *acc = knil();
    if (!kis_imm(a[0]) && a[0]->tag == K_CHR) {   /* Char range; else Int (immediate) */
      int64_t lo = (int64_t)a[0]->as.chr, hi = (int64_t)a[1]->as.chr, top = ex ? hi - 1 : hi;
      for (int64_t c = top; c >= lo; c--) { if (c >= 0xD800 && c <= 0xDFFF) continue; acc = kcons(kchr((uint32_t)c), acc); }
    } else {
      int64_t lo = kas_int(a[0]), hi = kas_int(a[1]), top = ex ? hi - 1 : hi;
      for (int64_t n = top; n >= lo; n--) acc = kcons(kint(n), acc);
    }
    return acc;
}
KValue *kpf___intAnd(KValue **a) {
  return kp_intAnd(a[0], a[1]);
}
KValue *kpf___intOr(KValue **a) {
  return kp_intOr(a[0], a[1]);
}
KValue *kpf___intXor(KValue **a) {
  return kp_intXor(a[0], a[1]);
}
KValue *kpf___hashMixInt(KValue **a) {
  return ku64(fnv_mix_u64(kint_low64(a[0]), kint_low64(a[1])));
}
KValue *kpf___hashMixDouble(KValue **a) {
  uint64_t bits; double d = a[1]->as.d; memcpy(&bits, &d, sizeof bits);
    return ku64(fnv_mix_u64(kint_low64(a[0]), bits));
}
KValue *kpf___hashMixString(KValue **a) {
  return ku64(fnv_mix_bytes(kint_low64(a[0]), (const unsigned char *)a[1]->as.str.p, a[1]->as.str.len));
}
KValue *kpf___hashMixBytes(KValue **a) {
  return ku64(fnv_mix_bytes(kint_low64(a[0]), a[1]->as.bytes.p, a[1]->as.bytes.len));
}
KValue *kpf___newStringBuilder(KValue **a) {
  return kstr0("");
}
KValue *kpf___stringBuilderString(KValue **a) {
  return str_append(a[1], a[0]);
}
KValue *kpf___stringBuilderScalar(KValue **a) {
  sbuf b; sb_init(&b); utf8_encode(a[0]->as.chr, &b); return str_append(a[1], sb_to_str(&b));
}
KValue *kpf___stringBuilderGrapheme(KValue **a) {
  return str_append(a[1], a[0]);
}
KValue *kpf___finishStringBuilder(KValue **a) {
  return a[0];
}
KValue *kpf___stringStart(KValue **a) {
  return kint(0);
}
KValue *kpf___stringEnd(KValue **a) {
  return kint((int64_t)utf8_scalar_count((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len));
}
KValue *kpf___stringCursorOffset(KValue **a) {
  int64_t i = kas_int(a[1]); if (i < 0) i = 0;
    return kint((int64_t)utf8_scalar_byte_offset((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, (size_t)i));
}
KValue *kpf___stringNextScalar(KValue **a) {
  const unsigned char *p = (const unsigned char *)a[0]->as.str.p; size_t len = a[0]->as.str.len;
    int64_t i = kas_int(a[1]); size_t cnt = utf8_scalar_count(p, len);
    if (i >= 0 && i < (int64_t)cnt) {
      size_t off = utf8_scalar_byte_offset(p, len, (size_t)i);
      uint32_t cp; utf8_next(p + off, p + len, &cp);
      static const char *nm[2] = {"next", "scalar"};
      KValue *vals[2]; vals[0] = kint(i + 1); vals[1] = kchr(cp);
      return ksome(krec(2, nm, vals));
    }
    return knone();
}
KValue *kpf___stringPrevScalar(KValue **a) {
  const unsigned char *p = (const unsigned char *)a[0]->as.str.p; size_t len = a[0]->as.str.len;
    int64_t i = kas_int(a[1]); size_t cnt = utf8_scalar_count(p, len);
    if (i > 0 && i <= (int64_t)cnt) {
      size_t off = utf8_scalar_byte_offset(p, len, (size_t)(i - 1));
      uint32_t cp; utf8_next(p + off, p + len, &cp);
      static const char *nm[2] = {"prev", "scalar"};
      KValue *vals[2]; vals[0] = kint(i - 1); vals[1] = kchr(cp);
      return ksome(krec(2, nm, vals));
    }
    return knone();
}
KValue *kpf___stringSpan(KValue **a) {
  const unsigned char *p = (const unsigned char *)a[0]->as.str.p; size_t len = a[0]->as.str.len;
    int64_t aa = kas_int(a[1]), bb = kas_int(a[2]); size_t cnt = utf8_scalar_count(p, len);
    if (aa >= 0 && bb <= (int64_t)cnt && aa <= bb) {
      size_t oa = utf8_scalar_byte_offset(p, len, (size_t)aa);
      size_t ob = utf8_scalar_byte_offset(p, len, (size_t)bb);
      return ksome(kstr((const char *)(p + oa), ob - oa));
    }
    return knone();
}
KValue *kpf___newUtf8Decoder(KValue **a) {
  return kbytes((const unsigned char *)"", 0);
}
KValue *kpf___decodeUtf8Chunk(KValue **a) {
  size_t pl = a[1]->as.bytes.len, cl = a[0]->as.bytes.len, total = pl + cl;
    unsigned char *comb = (unsigned char *)kgc_alloc_atomic(total ? total : 1);
    if (pl) memcpy(comb, a[1]->as.bytes.p, pl);
    if (cl) memcpy(comb + pl, a[0]->as.bytes.p, cl);
    size_t plen = utf8_valid_prefix_len(comb, total), rlen = total - plen;
    if (rlen > 0 && !utf8_is_incomplete_tail(comb + plen, rlen)) return knone();
    static const char *nm[2] = {"decoder", "text"};
    KValue *vals[2]; vals[0] = kbytes(comb + plen, rlen); vals[1] = kstr((const char *)comb, plen);
    return ksome(krec(2, nm, vals));
}
KValue *kpf___finishUtf8Decoder(KValue **a) {
  return a[0]->as.bytes.len == 0 ? ksome(kstr0("")) : knone();
}
KValue *kpf___atomicRepEq(KValue **a) {
  return kbool(kvalue_rep_eq(a[0], a[1]));
}
KValue *kpf___normalize(KValue **a) {
  return ku_normalize((int)kas_int(a[0]), (const unsigned char *)a[1]->as.str.p, a[1]->as.str.len);
}
KValue *kpf___caseFold(KValue **a) {
  cpbuf in; cp_init(&in); ku_decode((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, &in);
    cpbuf out; cp_init(&out);
    for (size_t i = 0; i < in.len; i++) ku_casefold_scalar(in.p[i], &out);
    sbuf b; sb_init(&b); for (size_t i = 0; i < out.len; i++) utf8_encode(out.p[i], &b); return sb_to_str(&b);
}
KValue *kpf___graphemeCount(KValue **a) {
  cpbuf in; cp_init(&in); ku_decode((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, &in);
    return kint((int64_t)ku_grapheme_count(in.p, in.len));
}
KValue *kpf___graphemeValid(KValue **a) {
  cpbuf in; cp_init(&in); ku_decode((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, &in);
    return kbool(ku_grapheme_count(in.p, in.len) == 1);
}
KValue *kpf___graphemeOfString(KValue **a) {
  cpbuf in; cp_init(&in); ku_decode((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, &in);
    if (ku_grapheme_count(in.p, in.len) == 1) return a[0];
    krt_fail("__graphemeOfString: string is not a single grapheme");
}
KValue *kpf___stringGraphemes(KValue **a) {
  cpbuf in; cp_init(&in); ku_decode((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, &in);
    cpbuf bounds; cp_init(&bounds);
    size_t i = 0; while (i < in.len) { cp_push(&bounds, (uint32_t)i); size_t l = ku_grapheme_len(in.p, in.len, i); i += (l ? l : 1); }
    KValue *acc = knil();
    for (size_t b = bounds.len; b > 0; b--) {
      size_t st = bounds.p[b - 1], en = (b < bounds.len) ? bounds.p[b] : in.len;
      acc = kcons(ku_encode_range(in.p, st, en), acc);
    }
    return acc;
}
KValue *kpf___stringNextGrapheme(KValue **a) {
  cpbuf in; cp_init(&in); ku_decode((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, &in);
    int64_t i = kas_int(a[1]);
    if (i >= 0 && i < (int64_t)in.len) {
      size_t l = ku_grapheme_len(in.p, in.len, (size_t)i); if (l == 0) l = 1;
      static const char *nm[2] = {"grapheme", "next"};
      KValue *vals[2]; vals[0] = ku_encode_range(in.p, (size_t)i, (size_t)i + l); vals[1] = kint(i + (int64_t)l);
      return ksome(krec(2, nm, vals));
    }
    return knone();
}
KValue *kpf___stringWords(KValue **a) {
  cpbuf in; cp_init(&in); ku_decode((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, &in);
    cpbuf ws, we; cp_init(&ws); cp_init(&we);
    size_t i = 0;
    while (i < in.len) {
      while (i < in.len && ku_is_space(in.p[i])) i++;
      if (i >= in.len) break;
      size_t st = i; while (i < in.len && !ku_is_space(in.p[i])) i++;
      cp_push(&ws, (uint32_t)st); cp_push(&we, (uint32_t)i);
    }
    KValue *acc = knil();
    for (size_t b = ws.len; b > 0; b--) acc = kcons(ku_encode_range(in.p, ws.p[b - 1], we.p[b - 1]), acc);
    return acc;
}
KValue *kpf___stringSentences(KValue **a) {
  cpbuf in; cp_init(&in); ku_decode((const unsigned char *)a[0]->as.str.p, a[0]->as.str.len, &in);
    cpbuf ps, pe; cp_init(&ps); cp_init(&pe);
    size_t start = 0, i = 0;
    while (i < in.len) {
      if (in.p[i] == '.' || in.p[i] == '!' || in.p[i] == '?') { cp_push(&ps, (uint32_t)start); cp_push(&pe, (uint32_t)(i + 1)); start = i + 1; }
      i++;
    }
    if (start < in.len) { cp_push(&ps, (uint32_t)start); cp_push(&pe, (uint32_t)in.len); }
    KValue *acc = knil();
    for (size_t b = ps.len; b > 0; b--) {
      size_t st = ps.p[b - 1], en = pe.p[b - 1];
      while (st < en && ku_is_space(in.p[st])) st++;
      while (en > st && ku_is_space(in.p[en - 1])) en--;
      if (en > st) acc = kcons(ku_encode_range(in.p, st, en), acc);
    }
    return acc;
}

/* ── IO execution ──────────────────────────────────────────────────── */

/* A heap stack of pending §18.7 finalizers (see kio_finally / krun_io). */
struct kdefer_frame { KValue **defers; int n; struct kdefer_frame *next; };

/* Run the accumulated finalizers LIFO (innermost scope first, last-
 * registered first within a scope) once a tail recursion reaches a value,
 * then return that value (or Unit when a K_IOEFFECT discarded it). */
static KValue *krun_finish(KValue *v, int discard, struct kdefer_frame *fr) {
  KValue *result = v;
  for (; fr; fr = fr->next) {
    for (int i = fr->n - 1; i >= 0; i--) {
      KValue *dr = krun_io(fr->defers[i]);
      if (!kis_fail(result) && kis_fail(dr)) result = dr;
    }
  }
  if (kis_fail(result)) return result;
  return discard ? kunit() : result;
}

KValue *krun_io(KValue *action) {
  /* Trampoline: a do-block's tail action (K_IOTAIL), a discarded tail
   * statement-`if` branch action (K_IOEFFECT → final result is Unit), and
   * the tail leg of ioBind/ioThen all continue this loop instead of
   * re-entering krun_io, so any sequenced IO tail-recursion runs in
   * constant C stack (§27.5A.3).  `discard` records that a K_IOEFFECT was
   * crossed, so the loop's final value is Unit (matching the interpreter,
   * whose KIf completion discards the branch value). */
  int discard = 0;
  /* heap stack of pending §18.7 finalizers, accumulated across a tail
   * recursion and run (LIFO) once the recursion reaches a value. */
  struct kdefer_frame *defers = NULL;
  while (1) {
  /* UNBOXING Stage 1: an immediate value in IO position is a `return`ed result
   * (e.g. `do { …; pure n }` yielding a small Int) — never an IO node — so it
   * finishes the loop directly, never dereferencing the odd word. */
  if (kis_imm(action)) return krun_finish(action, discard, defers);
  switch (action->tag) {
    case K_IOTAIL:
      action = action->as.bounce.fn;
      continue;
    case K_IOEFFECT:
      discard = 1;
      action = action->as.bounce.fn;
      continue;
    case K_IOFINALLY: {
      struct kdefer_frame *f = (struct kdefer_frame *)kgc_alloc(sizeof *f);
      f->defers = action->as.iofin.defers; f->n = action->as.iofin.n; f->next = defers;
      defers = f;
      action = action->as.iofin.action;
      continue;
    }
    case K_IO: {
      KValue *r = action->as.io.fn(action->as.io.env);
      if (kis_imm(r)) return krun_finish(r, discard, defers); /* immediate result */
      if (r->tag == K_IOTAIL) { action = r->as.bounce.fn; continue; }
      if (r->tag == K_IOEFFECT) { discard = 1; action = r->as.bounce.fn; continue; }
      if (r->tag == K_IOFINALLY) {
        struct kdefer_frame *f = (struct kdefer_frame *)kgc_alloc(sizeof *f);
        f->defers = r->as.iofin.defers; f->n = r->as.iofin.n; f->next = defers;
        defers = f; action = r->as.iofin.action; continue;
      }
      return krun_finish(r, discard, defers);
    }
    case K_NATIVE: {
      /* §27.1.1: fire the manifest symbol by calling the codegen-emitted
       * wrapper DIRECTLY — no name lookup, no strcmp, no dispatch table. */
      if (action->as.native.argc < action->as.native.arity)
        krt_fail("internal: native action run before saturation");
      KValue *r = action->as.native.fn(action->as.native.args);
      return krun_finish(r, discard, defers);
    }
    default:
      /* A pure value used in IO position (a `return`ed result, a data ctor) —
       * OR a CK-machine action node (krt2_bind/then/pure/catch/throw) that
       * reached the bridge because its do-bind action is an IO combinator
       * building a krt2_* tree (liftA2/<*>/traverse via the Applicative (IO e)
       * dictionary, which the §3.3 analysis cannot see through; see rt.c).
       * krt2_run_op_sync drives the non-suspending OPs to a value and returns
       * any non-OP value unchanged. */
      return krun_finish(krt2_run_op_sync(action), discard, defers);
  }
  }
}

KValue *krun_io_checked(KValue *action) {
  KValue *result = krun_io(action);
  if (kis_fail(result)) krt_fail("__runIO: uncaught typed IO failure");
  return result;
}
