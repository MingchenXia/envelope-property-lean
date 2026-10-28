# Build cache

Compiling the release from scratch (about 6200 modules of this repository on top of Mathlib) takes
many hours on a small machine. The compiled Lake artifacts of this repository are therefore
published separately, as a **build cache**: an xz-compressed tar of `<package>/.lake/build/{lib,ir}`
of every package of the release, split into 45 MB chunks, with a `MANIFEST` that records the source
revisions and the sha256 of every chunk. Mathlib's own artifacts are not included: they come from
Mathlib's cache (`lake exe cache get`).

## Using it

```sh
cd EnvelopeProperty
lake exe cache get                # Mathlib and its dependencies, at the revisions of lake-manifest.json
cd ..
scripts/build-cache/restore.sh    # this repository's artifacts (from the `build-cache` branch)
cd EnvelopeProperty
lake build --no-build             # checks that everything is up to date; no compilation
lake env lean ../scripts/Axioms.lean
```

`restore.sh --release TAG` takes the chunks from the assets of a GitHub release instead of the
branch, and `restore.sh --dir DIR` from chunks downloaded by hand. The chunks are verified against
`MANIFEST` before anything is unpacked.

Lake's up-to-date check compares content hashes (source files, options, the toolchain, and the
artifacts of all imports), not paths or timestamps. A restored cache is therefore valid exactly when
the sources are those of the cache's `release-commit`, the toolchain is the one in `lean-toolchain`
and Mathlib is at the revision of `EnvelopeProperty/lake-manifest.json` with Mathlib's official
cache. If a source file was changed, `lake build` recompiles only that module and the modules that
import it. Do **not** run `lake update`: it may move Mathlib and invalidate the cache.

## Publishing it (maintainers)

`scripts/build-cache/make.sh OUTDIR` packs the artifacts of the current checkout (run it only after
`lake build --no-build` succeeds). Two ways to publish, both within GitHub's limits (100 MB per file,
2 GB per push):

* **orphan branch `build-cache`** (`make.sh --push-branch OUTDIR`): one root commit chain, unrelated
  to `main`, holding `MANIFEST`, `README.md` and `chunks/chunk.NNNN`; pushed in batches of at most
  20 chunks (900 MB). Works the same for a private and a public repository, and for anyone who can
  clone it. Cost: `git clone` without `--single-branch` downloads the cache too; use
  `git clone --single-branch -b main …` to avoid it. Refresh by force-pushing a new chain.
* **GitHub release assets** (`make.sh --release TAG OUTDIR`, needs `gh` and an existing release
  `TAG`): keeps the git history small; assets of a private repository need an authenticated `gh`.

Both are content-identical; `restore.sh` accepts either.
