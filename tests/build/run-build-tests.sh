#!/usr/bin/env bash
# Build-manifest test suite (Spec §35.13 config-mode evaluation, §36
# build schema). Drives `kappa build --manifest` over fixtures:
#   * valid/*          — must load, config-check and reify (exit 0);
#   * invalid/*        — must fail, emitting the expected §35.11 config
#                        diagnostic declared on the fixture's first line;
#   * reproducibility/ — two manifests with different source structure but
#                        identical semantic BuildConfig must render the
#                        same resolved configuration (§36.2.1 semantic
#                        identity is provenance-independent).
# No C toolchain is needed: manifest evaluation performs no build-plan
# resolution or codegen (§35.13).
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
DIR="$ROOT/tests/build"
KAPPA="cabal run -v0 kappa --"
fails=0

cd "$ROOT"
echo "== building the kappa CLI =="
timeout 600 cabal build -v0 exe:kappa || { echo "FAIL: cabal build"; exit 1; }

echo "== valid manifests (must load + reify; --check = no build) =="
for f in "$DIR"/valid/*.kappa.build.kp; do
  name="$(basename "$f")"
  if out="$(timeout 120 $KAPPA build --manifest "$f" --check 2>&1)"; then
    echo "PASS $name"
  else
    echo "FAIL $name (expected exit 0)"; echo "$out" | sed 's/^/    /'; fails=$((fails+1))
  fi
done

echo "== invalid manifests (must fail with the expected diagnostic) =="
for f in "$DIR"/invalid/*.kappa.build.kp; do
  name="$(basename "$f")"
  want="$(sed -n 's/^-- expect: //p' "$f" | head -1)"
  out="$(timeout 120 $KAPPA build --manifest "$f" --check 2>&1)"; rc=$?
  if [ "$rc" -eq 0 ]; then
    echo "FAIL $name (expected failure, got exit 0)"; fails=$((fails+1))
  elif [ -n "$want" ] && ! grep -q "$want" <<<"$out"; then
    echo "FAIL $name (expected $want)"; echo "$out" | sed 's/^/    /'; fails=$((fails+1))
  else
    echo "PASS $name ($want)"
  fi
done

echo "== native bindings: codegen + diagnostics driven by manifest providers (§36.28) =="
# Each fixture dir holds a kappa.build.kp whose first line is
# '-- expect: E_CODE' (the build must fail with that code) or
# '-- expect: BUILD_OK' (must build to C, emitting the provider's prims).
# --emit-c so no C toolchain/native lib is required.
for d in "$DIR"/native/*/; do
  name="native/$(basename "$d")"
  want="$(sed -n 's/^-- expect: //p' "$d/kappa.build.kp" | head -1)"
  out="$(timeout 120 $KAPPA build --manifest "$d" --emit-c -o /tmp/kbuild-out 2>&1)"; rc=$?
  if [ "$want" = "BUILD_OK" ]; then
    # a fixture that selects the sqlite host binding must emit its prim;
    # otherwise just require that codegen produced a .c
    needprim=0; grep -q "host.native.sqlite3" "$d/kappa.build.kp" && needprim=1
    primok=1; [ "$needprim" = 1 ] && { find "$d" -name '*.kappa.c' -exec grep -ql "__sqlite" {} \; || primok=0; }
    if [ "$rc" -eq 0 ] && [ -n "$(find "$d" -name '*.kappa.c')" ] && [ "$primok" = 1 ]; then
      echo "PASS $name (built$([ "$needprim" = 1 ] && echo '; provider prim emitted'))"
    else
      echo "FAIL $name (expected build + prim)"; echo "$out" | sed 's/^/    /'; fails=$((fails+1))
    fi
    find "$d" -name '*.kappa.c' -delete 2>/dev/null
  else
    if [ "$rc" -eq 0 ]; then
      echo "FAIL $name (expected $want, got exit 0)"; fails=$((fails+1))
    elif ! grep -q "$want" <<<"$out"; then
      echo "FAIL $name (expected $want)"; echo "$out" | sed 's/^/    /'; fails=$((fails+1))
    else
      echo "PASS $name ($want)"
    fi
  fi
  # a path-dep build creates kappa.lock in the fixture dir; clean it
  find "$d" -name 'kappa.lock' -delete 2>/dev/null
done

echo "== kappa.lock lifecycle: create / --locked match / drift / missing (§36.4, §36.23.2) =="
LW="${TMPDIR:-/tmp}/kappa-lock-test"; rm -rf "$LW"; mkdir -p "$LW"
cp -r "$DIR/native/pathdep/." "$LW/"   # a path-dep project (app + dep/)
if timeout 120 $KAPPA build --manifest "$LW" --emit-c >/dev/null 2>&1 && [ -f "$LW/kappa.lock" ]; then
  echo "PASS lock/create (kappa.lock written on first build)"
else
  echo "FAIL lock/create (no kappa.lock after build)"; fails=$((fails+1))
fi
if timeout 120 $KAPPA build --manifest "$LW" --emit-c --locked >/dev/null 2>&1; then
  echo "PASS lock/match (--locked succeeds against a current lock)"
else
  echo "FAIL lock/match (--locked rejected a current lock)"; fails=$((fails+1))
fi
# mutate the dependency's source → content identity changes → drift
printf 'module codec.util\ntag : String -> String\nlet tag s = stringAppend "CHANGED" s' > "$LW/dep/src/codec/util.kp"
lout="$(timeout 120 $KAPPA build --manifest "$LW" --emit-c --locked 2>&1)"
if [ $? -ne 0 ] && grep -q "E_DEPENDENCY_LOCK_MISMATCH" <<<"$lout"; then
  echo "PASS lock/drift (changed dependency -> E_DEPENDENCY_LOCK_MISMATCH)"
else
  echo "FAIL lock/drift (expected E_DEPENDENCY_LOCK_MISMATCH)"; echo "$lout" | sed 's/^/    /'; fails=$((fails+1))
fi
rm -f "$LW/kappa.lock"
lout="$(timeout 120 $KAPPA build --manifest "$LW" --emit-c --locked 2>&1)"
if [ $? -ne 0 ] && grep -q "E_DEPENDENCY_LOCK_MISMATCH" <<<"$lout"; then
  echo "PASS lock/missing (--locked with no lock -> E_DEPENDENCY_LOCK_MISMATCH)"
else
  echo "FAIL lock/missing (expected E_DEPENDENCY_LOCK_MISMATCH)"; echo "$lout" | sed 's/^/    /'; fails=$((fails+1))
fi
rm -rf "$LW"

echo "== git dependency resolution (§36.23): clone + checkout + lock SHA =="
if command -v git >/dev/null 2>&1; then
  GW="${TMPDIR:-/tmp}/kappa-gitdep-test"; rm -rf "$GW"; mkdir -p "$GW"
  ( cd "$GW" && mkdir -p codecrepo/src/codec && cd codecrepo && git init -q \
      && git config user.email t@t && git config user.name t \
      && printf 'module codec.util\ntag : String -> String\nlet tag s = stringAppend "<" s' > src/codec/util.kp \
      && printf 'let buildConfig : BuildConfig = package { name="codec", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[], targets=[library { name="codec", backend=native { toolchain="cc", targetTriple="t" }, fragments=tags [], modules=modulesUnder "codec", dependencies=[] }] }' > kappa.build.kp \
      && git add -A && git commit -q -m v1 )
  REV="$(cd "$GW/codecrepo" && git rev-parse HEAD)"
  mkdir -p "$GW/app/src"
  printf 'module app\nimport codec.util.(tag)\nlet main = printlnString (tag "hi")' > "$GW/app/src/app.kp"
  printf 'let buildConfig : BuildConfig = package { name="app", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[git { name="codec", url="%s/codecrepo", rev="%s" }], hostBindings=[], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="t" }, fragments=tags [], main=module "app", modules=modulesUnder "app", dependencies=["codec"], hostBindings=[] }] }' "$GW" "$REV" > "$GW/app/kappa.build.kp"
  if timeout 120 $KAPPA build --manifest "$GW/app" --emit-c >/dev/null 2>&1 \
     && grep -q "^git $REV " "$GW/app/kappa.lock" 2>/dev/null; then
    echo "PASS git/resolve (cloned + checked out + lock records git SHA)"
  else
    echo "FAIL git/resolve"; fails=$((fails+1))
  fi
  if timeout 120 $KAPPA build --manifest "$GW/app" --emit-c --locked >/dev/null 2>&1; then
    echo "PASS git/locked (--locked matches the pinned SHA)"
  else
    echo "FAIL git/locked"; fails=$((fails+1))
  fi
  printf 'let buildConfig : BuildConfig = package { name="app", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[git { name="codec", url="%s/codecrepo", rev="deadbeefdeadbeefdeadbeefdeadbeefdeadbeef" }], hostBindings=[], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="t" }, fragments=tags [], main=module "app", modules=modulesUnder "app", dependencies=["codec"], hostBindings=[] }] }' "$GW" > "$GW/app/kappa.build.kp"
  rm -rf "$GW/app/.kappa" "$GW/app/kappa.lock"
  brout="$(timeout 120 $KAPPA build --manifest "$GW/app" --emit-c 2>&1)"
  if grep -q "E_DEPENDENCY_GIT_FAILED" <<<"$brout"; then
    echo "PASS git/bad-rev (unresolvable revision -> E_DEPENDENCY_GIT_FAILED)"
  else
    echo "FAIL git/bad-rev (expected E_DEPENDENCY_GIT_FAILED)"; echo "$brout" | sed 's/^/    /'; fails=$((fails+1))
  fi
  rm -rf "$GW"
else
  echo "SKIP git dependency tests (git not on PATH)"
fi

echo "== registry dependency resolution (§36.23.1 vendored registry + semver) =="
RW="${TMPDIR:-/tmp}/kappa-reg-test"; rm -rf "$RW"; mkdir -p "$RW/reg/codec"
for v in 0.1.0 0.1.5 0.2.0; do
  mkdir -p "$RW/reg/codec/$v/src/codec"
  printf 'module codec.util\ntag : String -> String\nlet tag s = stringAppend "%s" s' "$v" > "$RW/reg/codec/$v/src/codec/util.kp"
  printf 'let buildConfig : BuildConfig = package { name="codec", version=semver "%s", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[], targets=[library { name="codec", backend=native { toolchain="cc", targetTriple="t" }, fragments=tags [], modules=modulesUnder "codec", dependencies=[] }] }' "$v" > "$RW/reg/codec/$v/kappa.build.kp"
done
mkdir -p "$RW/app/src"; printf 'module app\nimport codec.util.(tag)\nlet main = printlnString (tag "hi")' > "$RW/app/src/app.kp"
regmanifest() { printf 'let buildConfig : BuildConfig = package { name="app", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[registry { name="codec", version="%s" }], hostBindings=[], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="t" }, fragments=tags [], main=module "app", modules=modulesUnder "app", dependencies=["codec"], hostBindings=[] }] }' "$1" > "$RW/app/kappa.build.kp"; }
regmanifest "^0.1"; rm -f "$RW/app/kappa.lock"
if KAPPA_REGISTRY="$RW/reg" timeout 120 $KAPPA build --manifest "$RW/app" --emit-c >/dev/null 2>&1 \
   && grep -qE "^registry 0\.1\.5(\+| )" "$RW/app/kappa.lock" 2>/dev/null; then
  echo "PASS registry/resolve (^0.1 -> highest 0.1.x; lock pins resolved version)"
else
  echo "FAIL registry/resolve"; fails=$((fails+1))
fi
if KAPPA_REGISTRY="$RW/reg" timeout 120 $KAPPA build --manifest "$RW/app" --emit-c --locked >/dev/null 2>&1; then
  echo "PASS registry/locked (--locked matches the pinned version)"
else
  echo "FAIL registry/locked"; fails=$((fails+1))
fi
regmanifest "^9"; rm -f "$RW/app/kappa.lock"
nvout="$(KAPPA_REGISTRY="$RW/reg" timeout 120 $KAPPA build --manifest "$RW/app" --emit-c 2>&1)"
if grep -q "E_DEPENDENCY_VERSION_UNSATISFIED" <<<"$nvout"; then
  echo "PASS registry/no-version (^9 -> E_DEPENDENCY_VERSION_UNSATISFIED)"
else
  echo "FAIL registry/no-version"; echo "$nvout" | sed 's/^/    /'; fails=$((fails+1))
fi
regmanifest "^0.1"
ucout="$(timeout 120 $KAPPA build --manifest "$RW/app" --emit-c 2>&1)"
if grep -q "E_DEPENDENCY_UNRESOLVED" <<<"$ucout"; then
  echo "PASS registry/unconfigured (no \$KAPPA_REGISTRY -> E_DEPENDENCY_UNRESOLVED)"
else
  echo "FAIL registry/unconfigured"; echo "$ucout" | sed 's/^/    /'; fails=$((fails+1))
fi
rm -rf "$RW"

echo "== url dependency resolution (§36.23): fetch + unpack archive =="
if command -v curl >/dev/null 2>&1 && command -v tar >/dev/null 2>&1; then
  UW="${TMPDIR:-/tmp}/kappa-urldep-test"; rm -rf "$UW"; mkdir -p "$UW/codecpkg/src/codec" "$UW/app/src"
  printf 'module codec.util\ntag : String -> String\nlet tag s = stringAppend "<" s' > "$UW/codecpkg/src/codec/util.kp"
  printf 'let buildConfig : BuildConfig = package { name="codec", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[], hostBindings=[], targets=[library { name="codec", backend=native { toolchain="cc", targetTriple="t" }, fragments=tags [], modules=modulesUnder "codec", dependencies=[] }] }' > "$UW/codecpkg/kappa.build.kp"
  ( cd "$UW" && tar -czf codec.tgz codecpkg )
  printf 'module app\nimport codec.util.(tag)\nlet main = printlnString (tag "hi")' > "$UW/app/src/app.kp"
  printf 'let buildConfig : BuildConfig = package { name="app", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[urlDependency { name="codec", url="file://%s/codec.tgz" }], hostBindings=[], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="t" }, fragments=tags [], main=module "app", modules=modulesUnder "app", dependencies=["codec"], hostBindings=[] }] }' "$UW" > "$UW/app/kappa.build.kp"
  if timeout 120 $KAPPA build --manifest "$UW/app" --emit-c >/dev/null 2>&1 \
     && grep -q "^url " "$UW/app/kappa.lock" 2>/dev/null; then
    echo "PASS url/resolve (fetched + unpacked archive; lock records content id)"
  else
    echo "FAIL url/resolve"; fails=$((fails+1))
  fi
  ufout="$(timeout 60 $KAPPA build --manifest "$UW/app" --emit-c 2>&1)"  # warm cache, then bad url
  printf 'let buildConfig : BuildConfig = package { name="app", version=semver "1", sourceRoots=[sourceRoot "src"], fragmentAxes=[], dependencies=[urlDependency { name="codec", url="file://%s/nope.tgz" }], hostBindings=[], targets=[executable { name="app", backend=native { toolchain="cc", targetTriple="t" }, fragments=tags [], main=module "app", modules=modulesUnder "app", dependencies=["codec"], hostBindings=[] }] }' "$UW" > "$UW/app/kappa.build.kp"
  rm -rf "$UW/app/.kappa"
  ufout="$(timeout 60 $KAPPA build --manifest "$UW/app" --emit-c 2>&1)"
  if grep -q "E_DEPENDENCY_URL_FAILED" <<<"$ufout"; then
    echo "PASS url/bad (missing archive -> E_DEPENDENCY_URL_FAILED)"
  else
    echo "FAIL url/bad"; echo "$ufout" | sed 's/^/    /'; fails=$((fails+1))
  fi
  rm -rf "$UW"
else
  echo "SKIP url dependency tests (curl/tar not on PATH)"
fi

echo "== test target (§36.31): build pipeline runs the Appendix-T suite =="
TT="${TMPDIR:-/tmp}/kappa-testtgt"; rm -rf "$TT"; mkdir -p "$TT/test/spec"
cat > "$TT/kappa.build.kp" <<'EOF'
let buildConfig : BuildConfig = package { name = "demo", version = semver "1.0.0", sourceRoots = [sourceRoot "test"], fragmentAxes = [], dependencies = [], hostBindings = [], targets = [test { name = "unit", modules = modulesUnder "spec" }] }
EOF
printf -- '--! mode check\n--! assertNoErrors\nmodule spec.ok\nlet x : Int = 42' > "$TT/test/spec/ok.kp"
if timeout 120 $KAPPA build --manifest "$TT" --target unit >/dev/null 2>&1; then
  echo "PASS test-target/pass (passing suite -> exit 0)"
else
  echo "FAIL test-target/pass"; fails=$((fails+1))
fi
printf -- '--! mode check\n--! assertNoErrors\nmodule spec.bad\nlet y : Int = notInScope' > "$TT/test/spec/bad.kp"
if timeout 120 $KAPPA build --manifest "$TT" --target unit >/dev/null 2>&1; then
  echo "FAIL test-target/fail (failing suite should exit non-zero)"; fails=$((fails+1))
else
  echo "PASS test-target/fail (failing suite -> non-zero exit)"
fi
rm -rf "$TT"

echo "== aggregate target (§36.3): build/run a group of member targets =="
AG="${TMPDIR:-/tmp}/kappa-aggtest"; rm -rf "$AG"; mkdir -p "$AG/src/app" "$AG/test/spec"
cat > "$AG/kappa.build.kp" <<'EOF'
let buildConfig : BuildConfig = package { name = "demo", version = semver "1.0.0", sourceRoots = [sourceRoot "src", sourceRoot "test"], fragmentAxes = [], dependencies = [], hostBindings = [], targets = [executable { name = "cli", backend = native { toolchain = "cc", targetTriple = "t" }, fragments = tags [], main = module "app.main", modules = modulesUnder "app", dependencies = [], hostBindings = [] }, test { name = "unit", modules = modulesUnder "spec" }, aggregate { name = "all", members = ["cli", "unit"] }, aggregate { name = "cyc1", members = ["cyc2"] }, aggregate { name = "cyc2", members = ["cyc1"] }] }
EOF
printf 'module app.main\nlet main = printlnString "hi"' > "$AG/src/app/main.kp"
printf -- '--! mode check\n--! assertNoErrors\nmodule spec.ok\nlet x : Int = 1' > "$AG/test/spec/ok.kp"
if timeout 120 $KAPPA build --manifest "$AG" --target all --emit-c >/dev/null 2>&1; then
  echo "PASS aggregate/run (builds executable member + runs test member)"
else
  echo "FAIL aggregate/run"; fails=$((fails+1))
fi
agout="$(timeout 120 $KAPPA build --manifest "$AG" --target cyc1 --emit-c 2>&1)"
if grep -q "E_BUILD_TARGET_CYCLE" <<<"$agout"; then
  echo "PASS aggregate/cycle (cyclic membership -> E_BUILD_TARGET_CYCLE)"
else
  echo "FAIL aggregate/cycle"; echo "$agout" | sed 's/^/    /'; fails=$((fails+1))
fi
find "$AG" -name '*.kappa.c' -delete 2>/dev/null; rm -rf "$AG"

echo "== aliasTarget (§36.3): build/run the aliased target =="
AL="${TMPDIR:-/tmp}/kappa-aliastest"; rm -rf "$AL"; mkdir -p "$AL/test/spec"
cat > "$AL/kappa.build.kp" <<'EOF'
let buildConfig : BuildConfig = package { name = "demo", version = semver "1.0.0", sourceRoots = [sourceRoot "test"], fragmentAxes = [], dependencies = [], hostBindings = [], targets = [test { name = "unit", modules = modulesUnder "spec" }, aliasTarget { name = "check", target = "unit" }, aliasTarget { name = "lp1", target = "lp2" }, aliasTarget { name = "lp2", target = "lp1" }] }
EOF
printf -- '--! mode check\n--! assertNoErrors\nmodule spec.ok\nlet x : Int = 1' > "$AL/test/spec/ok.kp"
if timeout 120 $KAPPA build --manifest "$AL" --target check >/dev/null 2>&1; then
  echo "PASS alias/run (alias resolves to and runs its target)"
else
  echo "FAIL alias/run"; fails=$((fails+1))
fi
alout="$(timeout 120 $KAPPA build --manifest "$AL" --target lp1 2>&1)"
if grep -q "E_BUILD_TARGET_CYCLE" <<<"$alout"; then
  echo "PASS alias/cycle (alias loop -> E_BUILD_TARGET_CYCLE)"
else
  echo "FAIL alias/cycle"; echo "$alout" | sed 's/^/    /'; fails=$((fails+1))
fi
rm -rf "$AL"

echo "== value provenance (§35.7): buildConfig provenance graph =="
PV="${TMPDIR:-/tmp}/kappa-prov-test"; rm -rf "$PV"; mkdir -p "$PV"
cat > "$PV/kappa.build.kp" <<'EOF'
let pkgVersion = semver "0.1.0"
let buildConfig : BuildConfig = package { name = "demo"
    , version = pkgVersion
    , sourceRoots = [sourceRoot "src"]
    , fragmentAxes = []
    , dependencies = []
    , hostBindings = []
    , targets = [executable { name = "app", backend = native { toolchain = "cc", targetTriple = "t" }, fragments = tags [], main = module "app", modules = modulesUnder "app", dependencies = [], hostBindings = [] }]
    }
EOF
pvout="$(timeout 60 $KAPPA build --manifest "$PV" --provenance 2>&1)"; pvrc=$?
# whole value is a composite (named application); a list field is a sequence;
# a literal is a source; the `version` field references the pkgVersion
# binding (a derived edge through to the semver call's string literal).
if [ "$pvrc" -eq 0 ] \
   && grep -q "^composite " <<<"$pvout" \
   && grep -q "sequence " <<<"$pvout" \
   && grep -q "source " <<<"$pvout" \
   && grep -q "derived " <<<"$pvout"; then
  echo "PASS provenance (composite/sequence/source + reference edge)"
else
  echo "FAIL provenance"; echo "$pvout" | sed 's/^/    /'; fails=$((fails+1))
fi
rm -rf "$PV"

echo "== reproducibility: semantic identity is provenance-independent (§36.2.1) =="
a="$(timeout 120 $KAPPA build --manifest "$DIR/reproducibility/direct.kappa.build.kp" --check 2>&1)"
b="$(timeout 120 $KAPPA build --manifest "$DIR/reproducibility/helpers.kappa.build.kp" --check 2>&1)"
if [ "$a" = "$b" ] && [ -n "$a" ]; then
  echo "PASS reproducibility (direct == helpers)"
else
  echo "FAIL reproducibility (resolved configs differ)"
  diff <(echo "$a") <(echo "$b") | sed 's/^/    /'
  fails=$((fails+1))
fi

echo "== manifest not found (§35.13) =="
if out="$(timeout 60 $KAPPA build --manifest "$DIR/does-not-exist" 2>&1)"; then
  echo "FAIL not-found (expected failure)"; fails=$((fails+1))
elif grep -q "E_BUILD_MANIFEST_NOT_FOUND" <<<"$out"; then
  echo "PASS manifest-not-found (E_BUILD_MANIFEST_NOT_FOUND)"
else
  echo "FAIL not-found (expected E_BUILD_MANIFEST_NOT_FOUND)"; echo "$out" | sed 's/^/    /'; fails=$((fails+1))
fi

echo
if [ "$fails" -eq 0 ]; then echo "build-manifest suite: ALL PASS"; exit 0
else echo "build-manifest suite: $fails FAILED"; exit 1; fi
