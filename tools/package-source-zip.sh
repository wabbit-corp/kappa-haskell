#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage:
  tools/package-source-zip.sh [--output PATH] [--prefix NAME/] [--include-untracked]

Create a source zip for this repository.

Default contents are Git-tracked files, which is the reproducible source state:
source, tests, examples, Cabal files, docs, runtime files, tools, and committed
metadata. Build outputs, .git, and ignored files are not included.

Options:
  --output PATH          Zip path. Defaults to dist-source/<repo>-source-<sha>.zip.
  --prefix NAME/         Archive root prefix. Defaults to <repo>/.
  --include-untracked    Also include untracked files that are not ignored by Git.
                         Use this only after checking `git status`: non-ignored
                         local build artifacts will be included.
  -h, --help             Show this help.
USAGE
}

die() {
  printf 'error: %s\n' "$*" >&2
  exit 1
}

include_untracked=0
output=""
prefix=""

while (($#)); do
  case "$1" in
    --output)
      [[ $# -ge 2 ]] || die "--output needs a value"
      output="$2"
      shift 2
      ;;
    --prefix)
      [[ $# -ge 2 ]] || die "--prefix needs a value"
      prefix="$2"
      shift 2
      ;;
    --include-untracked)
      include_untracked=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      die "unknown argument: $1"
      ;;
  esac
done

command -v git >/dev/null 2>&1 || die "git not found"
command -v python3 >/dev/null 2>&1 || die "python3 not found"

repo_root="$(git rev-parse --show-toplevel)"
repo_name="$(basename "$repo_root")"
commit="$(git -C "$repo_root" rev-parse --short=12 HEAD)"

if [[ -z "$prefix" ]]; then
  prefix="${repo_name}/"
fi
case "$prefix" in
  */) ;;
  *) prefix="${prefix}/" ;;
esac

if [[ -z "$output" ]]; then
  output="$repo_root/dist-source/${repo_name}-source-${commit}.zip"
elif [[ "$output" != /* ]]; then
  output="$PWD/$output"
fi

mkdir -p "$(dirname "$output")"

tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/kappa-source-zip.XXXXXX")"
trap 'rm -rf "$tmpdir"' EXIT
manifest="$tmpdir/manifest.zlist"

(
  cd "$repo_root"
  git ls-files -z --cached --deduplicate > "$manifest"
  if [[ "$include_untracked" -eq 1 ]]; then
    git ls-files -z --others --exclude-standard >> "$manifest"
  fi
)

REPO_ROOT="$repo_root" \
OUTPUT="$output" \
PREFIX="$prefix" \
MANIFEST="$manifest" \
python3 - <<'PY'
import os
import stat
import sys
import zipfile
from pathlib import Path

repo = Path(os.environ["REPO_ROOT"]).resolve()
output = Path(os.environ["OUTPUT"]).resolve()
prefix = os.environ["PREFIX"]
manifest = Path(os.environ["MANIFEST"])

raw = manifest.read_bytes()
names = [p.decode("utf-8") for p in raw.split(b"\0") if p]

seen = set()
written = 0
with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as zf:
    for rel in names:
        if rel in seen:
            continue
        seen.add(rel)

        path = repo / rel
        if not path.is_file() and not path.is_symlink():
            continue
        if path.resolve() == output:
            continue

        arcname = prefix + rel
        info = zipfile.ZipInfo.from_file(path, arcname)
        mode = path.lstat().st_mode
        if stat.S_ISLNK(mode):
            info.create_system = 3
            info.external_attr = (stat.S_IFLNK | 0o777) << 16
            zf.writestr(info, os.readlink(path))
        else:
            info.compress_type = zipfile.ZIP_DEFLATED
            info._compresslevel = 9
            with path.open("rb") as f:
                zf.writestr(info, f.read())
        written += 1

print(f"wrote {output}")
print(f"files {written}")
PY

