#!/bin/bash
# Restore the compiled Lake artifacts of this repository from the published build cache
# (see ../../BUILD-CACHE.md). Unpacks .lake/build and vendor/*/.lake/build.
#
#   scripts/build-cache/restore.sh                 # from the orphan branch `build-cache` of origin
#   scripts/build-cache/restore.sh --release TAG   # from the assets of GitHub release TAG (gh CLI)
#   scripts/build-cache/restore.sh --dir DIR       # from MANIFEST + chunk.* already downloaded to DIR
#
# Every chunk is checked against the sha256 in MANIFEST before anything is unpacked. The chunks are
# streamed through `xz -d | tar -x`; besides the download (release/dir modes) only the unpacked
# size (about 3.5 GB) of free disk is needed.
#
# Mathlib and its dependencies are not part of the cache: run `lake exe cache get` (before or after
# this script). In an environment that already provides the Mathlib packages
# at the pinned revisions, set MATHLIB_PACKAGES=/path/to/.lake/packages to symlink them instead.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
MODE=branch SRC=""
case "${1:-}" in
  --release) MODE=release; SRC=${2:?release tag} ;;
  --dir) MODE=dir; SRC=$(cd "${2:?directory}" && pwd) ;;
  "") ;;
  *) echo "usage: restore.sh [--release TAG | --dir DIR]" >&2; exit 2 ;;
esac
cd "$ROOT"

if [ "$MODE" = release ]; then
  DL=$(mktemp -d "${TMPDIR:-/tmp}/build-cache.XXXXXX"); trap 'rm -rf "$DL"' EXIT
  gh release download "$SRC" --dir "$DL" --pattern 'MANIFEST' --pattern 'chunk.*'
  MODE=dir SRC=$DL
fi

if [ "$MODE" = branch ]; then
  ok=0
  for try in 1 2 3 4; do git fetch --depth=1 origin build-cache && { ok=1; break; }; sleep $((2**try)); done
  [ $ok = 1 ] || { echo "could not fetch the build-cache branch from origin" >&2; exit 1; }
  ref=$(git rev-parse FETCH_HEAD)
  manifest() { git show "$ref:MANIFEST"; }
  chunks=$(git ls-tree --name-only "$ref" chunks/ | sed 's|^chunks/||' | sort)
  emit() { git cat-file blob "$ref:chunks/$1"; }
else
  manifest() { cat "$SRC/MANIFEST"; }
  chunks=$(cd "$SRC" && ls chunk.* | sort)
  emit() { cat "$SRC/$1"; }
fi

manifest | sed -n '1,7p'
expected=$(manifest | grep -E '^[0-9a-f]{64}  chunk\.' | sort -k2)
n_exp=$(echo "$expected" | grep -c . || true)
n_got=$(echo "$chunks" | grep -c . || true)
[ "$n_exp" = "$n_got" ] || { echo "MANIFEST lists $n_exp chunks, found $n_got" >&2; exit 1; }
for c in $chunks; do
  want=$(echo "$expected" | awk -v c="$c" '$2 == c {print $1}')
  got=$(emit "$c" | sha256sum | cut -d' ' -f1)
  [ "$want" = "$got" ] || { echo "sha256 mismatch for $c" >&2; exit 1; }
done
echo "all $n_got chunks verified; unpacking" >&2
for c in $chunks; do emit "$c"; done | xz -d -T0 | tar -xf - -C "$ROOT"

if [ -n "${MATHLIB_PACKAGES:-}" ] && [ ! -e .lake/packages ]; then
  mkdir -p .lake && ln -s "$MATHLIB_PACKAGES" .lake/packages
fi
if [ ! -d .lake/packages/mathlib/.lake/build ]; then
  echo "note: Mathlib oleans not found; run: lake exe cache get" >&2
fi
echo "restored; check with: lake build --no-build" >&2
