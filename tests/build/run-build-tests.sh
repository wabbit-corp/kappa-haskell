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
