# Build cache

Compiling this repository from scratch (about 6200 modules on top of Mathlib) takes several hours.
The compiled Lake artifacts are therefore published as a **build cache**: an xz-compressed tar of
`.lake/build` and `vendor/*/.lake/build`, split into 45 MB chunks, with a `MANIFEST` that records
the commit, the toolchain, the Mathlib revision and the sha256 of every chunk. Mathlib's own
artifacts are not included; they come from Mathlib's cache (`lake exe cache get`).

## Using it

```sh
lake exe cache get                # Mathlib and its dependencies, at the revisions of lake-manifest.json
scripts/build-cache/restore.sh    # this repository's artifacts (from the `build-cache` branch)
lake build --no-build             # checks that everything is up to date; nothing is compiled
lake env lean scripts/Axioms.lean # the axiom audit
```

`restore.sh --release TAG` takes the chunks from the assets of a GitHub release instead of the
branch, and `restore.sh --dir DIR` from chunks downloaded by hand. The chunks are verified against
`MANIFEST` before anything is unpacked.

Lake's up-to-date check compares content hashes (source files, options, the toolchain and the
artifacts of all imports), not paths or timestamps. A restored cache is valid exactly when the
sources are those of the cache's `release-commit`, the toolchain is the one in `lean-toolchain` and
Mathlib is at the revision of `lake-manifest.json` with Mathlib's official cache. If a source file
is changed, `lake build` recompiles only that module and the modules that import it. Do **not** run
`lake update`: it may move Mathlib and invalidate the cache.

## Publishing it (maintainers)

`scripts/build-cache/make.sh OUTDIR` packs the artifacts of the current checkout (run it only after
`lake build --no-build` succeeds). Two ways to publish, both within GitHub's limits (100 MB per file,
2 GB per push):

* **orphan branch `build-cache`** (`make.sh --push-branch OUTDIR`): a commit chain unrelated to
  `main`, holding `MANIFEST`, `README.md` and `chunks/chunk.NNNN`, pushed in batches of at most 20
  chunks. `git clone` without `--single-branch` downloads the cache too; use
  `git clone --single-branch -b main …` to avoid it. Refresh by force-pushing a new chain.
* **GitHub release assets** (`make.sh --release TAG OUTDIR`, needs `gh` and an existing release
  `TAG`): keeps the git history small.

`restore.sh` accepts either.
