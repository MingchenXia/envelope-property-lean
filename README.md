# The envelope property for unibranch projective varieties — Lean 4 formalization

A Lean 4 / Mathlib formalization of the main results of

> Yanbo Fang, Jiyuan Han and Mingchen Xia, *The envelope property for unibranch projective
> varieties* (FHX), [`paper/`](paper/).

The headline theorems are the main theorem of FHX — the envelope property for every real numerical
class on an integral unibranch projective variety over an algebraically closed, trivially valued
field, conjectured by Boucksom–Jonsson (BJ22, Conjecture 5.14) — and its corollary characterizing
unibranch varieties, with **no hypothesis beyond those of the paper**. Everything the proofs use is
proved here, down to Mathlib (standard axioms only, see [Axioms](#axioms)).

Numbering: the paper in `paper/` (revision of 2026-10-28) calls them Theorem A
(`thm:intro-main`) and Corollary 1.1 (`cor:intro-characterization`); the Lean docstrings and
`ERRATA.md` cite the revision `832e086`, where they are Theorem 1.1 and Corollary 1.2. The
statements are the same in both revisions.

## What is formalized

Let `k` be an algebraically closed field with the trivial absolute value, `X` an integral
projective `k`-scheme with structure morphism `p : X ⟶ Spec k`, `X^an = Variety.An p` its Berkovich
analytification, `N¹(X)_ℝ = NativeRealNumericalClasses.Space p` the real numerical classes, and
`PSH(X, θ) = Variety.IsPSH p θ` the θ-plurisubharmonic functions of Boucksom–Jonsson (BJ22,
Definition 4.1). `EP_X(θ) = Variety.HasEnvelopeProperty p θ` is the *envelope property*: for every
nonempty family in `PSH(X, θ)` bounded above, the usc regularization of its supremum is θ-psh.
`X` is *unibranch* (`Variety.IsUnibranch X`) if its normalization is bijective.

All names below are in the namespace `EnvelopeProperty`; the file is
[`EnvelopeProperty/EnvelopeProperty/MainTheoremFullyUnconditional.lean`](EnvelopeProperty/EnvelopeProperty/MainTheoremFullyUnconditional.lean).

| FHX (832e086 / 2026-10-28) | Lean | Statement |
|---|---|---|
| Theorem 1.1 / Theorem A | `Variety.hasEnvelopeProperty_of_isUnibranch_fully_unconditional` | `X` unibranch ⇒ `EP_X(θ)` for every `θ ∈ N¹(X)_ℝ` |
| Theorem 1.1 / Theorem A, family form (as stated in the paper) | `Variety.isPSH_uscReg_iSup_of_isUnibranch_fully_unconditional` | `X` unibranch, `(φ_i)` a nonempty family in `PSH(X, θ)` uniformly bounded above ⇒ `(sup_i φ_i)^⋆ ∈ PSH(X, θ)` |
| Corollary 1.2 / Corollary 1.1 | `Variety.isUnibranch_tfae_hasEnvelopeProperty_fully_unconditional` | equivalent: (1) `X` unibranch; (1′) every local ring `𝒪_{X,x}` unibranch; (1″) every `𝒪_{X,x}` geometrically unibranch; (2) `EP_X(θ)` for all `θ ∈ N¹(X)_ℝ`; (3) `EP_X(ω)` for some ample `ω` |

In the 2026-10-28 revision "unibranch" is defined by the local rings (every `𝒪_{X,x}` has one
branch); Theorem A in exactly that form is
`Variety.hasEnvelopeProperty_of_forall_isUnibranchLocalRing_stalk_fully_unconditional` and
`Variety.isPSH_uscReg_iSup_of_forall_isUnibranchLocalRing_stalk_fully_unconditional`.

The same file states the theorems for the multiprojective models of the proof
(`MultiModel.*_fully_unconditional`, including FHX Corollary 7.5 of `832e086`, `cor:normal-EP`, for
normal models) and for
`X = V(I) ⊆ ∏_c ℙ^{M_c}` given by a prime ideal (`MultiModel.*quotModel*_fully_unconditional`).

All theorems of `MainTheoremFullyUnconditional.lean`: `ProjSubvariety.hasEnvelopeProperty_one_of_isProjNormal_of_subfield_fully_unconditional`, `MultiModel.hasEnvelopeProperty_of_isNormal_of_forall_countable_fully_unconditional`, `MultiModel.hasEnvelopeProperty_of_isUnibranch_fully_unconditional`, `MultiModel.isPSH_uscReg_iSup_of_isUnibranch_fully_unconditional`, `MultiModel.isPSH_of_antitone_of_isUnibranch_fully_unconditional`, `MultiModel.isUnibranch_tfae_hasEnvelopeProperty_fully_unconditional`, `MultiModel.hasEnvelopeProperty_quotModel_of_isUnibranch_fully_unconditional`, `MultiModel.isPSH_uscReg_iSup_quotModel_of_isUnibranch_fully_unconditional`, `MultiModel.quotModel_isUnibranch_tfae_fully_unconditional`, `Variety.hasEnvelopeProperty_of_isUnibranch_fully_unconditional`, `Variety.isPSH_uscReg_iSup_of_isUnibranch_fully_unconditional`, `Variety.hasEnvelopeProperty_of_forall_isUnibranchLocalRing_stalk_fully_unconditional`, `Variety.isPSH_uscReg_iSup_of_forall_isUnibranchLocalRing_stalk_fully_unconditional`, `Variety.isUnibranch_tfae_hasEnvelopeProperty_fully_unconditional`.

The other release roots contain the earlier forms of the same theorems, in which the (meanwhile
proved) inputs appear as explicit hypotheses — FHX Lemma 5.5 (`LocalPositivity`), FHX Theorem 3.1
in characteristic 0 (`SmoothEnvelopeCharZero`), and fibre constancy (FHX Theorem 6.1, Step 1) —
quantified over countable algebraically closed subfields:
`EnvelopeProperty/MainTheorem.lean`, `EnvelopeProperty/Global/MainTheorem.lean`,
`EnvelopeProperty/MainTheoremUnconditional.lean`, `EnvelopeProperty/Source/MainTheorem.lean`,
`EnvelopeProperty/Source/Characterization.lean` (all under `EnvelopeProperty/`).

**Certificates for the errata** ([`ERRATA.md`](ERRATA.md)):

* `not_bj22Lemma46 : ¬ BJ22Lemma46Statement` — Lemma 4.6 of Boucksom–Jonsson (BJ22) is false
  (`Global/Lemma46Counterexample.lean`; ERRATA EP-1.1);
* `MultiModel.isPSH_of_antitone_of_homMajorant` — BJ22's PSH2 holds on every model for a decreasing
  limit dominated by one homogeneous psh function (`Global/PSH2HomogeneousMajorant.lean`; EP-1.1);
* `ProjBerk.bj621_counterexample` — FHX Remark 7.3: on `ℙ¹` the monotonicity step of the proof of
  BJ22 Theorem 6.21 fails (`Projective/Remark73ProjectiveLine.lean`; EP-4.1).

### Formalization conventions

* Convergence of classes in `N¹(X)_ℝ` (in the definition of `IsPSH`) is `Variety.AmpleTendsto`:
  convergence in the order of the ample cone. When `N¹(X)_ℝ` is finite dimensional this is
  convergence in its Euclidean topology, so that `IsPSH` is literally BJ22's definition:
  `Variety.ampleTendsto_iff_tendsto` and `Variety.isPSH_iff_isCurveWeakPSH`
  (`EnvelopeProperty/Source/FiniteDimensionalTopology.lean`), under the explicit assumption
  `[FiniteDimensional ℝ (Space p)]`. Finite dimensionality of `N¹(X)_ℝ` (Néron–Severi) is not
  formalized; the main theorems do not assume it.
* Nets in the definition of `IsPSH` are indexed by directed preorders in the universe of `X`.
* The trivially valued field is `k` itself; no countability assumption is made on `k`.

## Building

Requirements: [elan](https://github.com/leanprover/elan) (the toolchain `leanprover/lean4:v4.33.1` is selected by
`lean-toolchain`), `git`, `xz`, and about 10 GB of disk (Mathlib's cache ≈ 5 GB, this repository's
cache ≈ 3.5 GB unpacked).

```sh
git clone --single-branch -b main <this repository> envelope-property-lean
cd envelope-property-lean/EnvelopeProperty
lake exe cache get                    # Mathlib 0df444a3 and its dependencies, prebuilt
cd .. && scripts/build-cache/restore.sh && cd EnvelopeProperty   # this repository, prebuilt
lake build --no-build                 # check: everything up to date, nothing compiled
lake env lean ../scripts/Axioms.lean  # the axiom audit below
```

Without the build cache, `lake build` (in `EnvelopeProperty/`) compiles all 6161
modules; expect many hours. See [`BUILD-CACHE.md`](BUILD-CACHE.md). Do not run `lake update`: the
dependency revisions are pinned in `EnvelopeProperty/lake-manifest.json` (Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, tag `v4.33.1`), and the build cache is valid only for them.

`lake build` builds the default target, the library `EnvelopeProperty`. Its `globs` select every
`EnvelopeProperty.*` module present in the repository, which is exactly the import closure below;
the other packages are built as dependencies. A single theorem file can be checked with e.g.
`lake build EnvelopeProperty.MainTheoremFullyUnconditional`.

## Axioms

`scripts/Axioms.lean` prints the axioms of the headline theorems, of the earlier forms and of the
errata certificates. Each depends exactly on `[propext, Classical.choice, Quot.sound]`.

Checked for workspace revision `322d15868e36b7aec63561aa2fc8cf98f038206c` (2026-10-28): `lake build --no-build` succeeded; all 141 `#print axioms` lines report `[propext, Classical.choice, Quot.sound]`.

## Layout

The repository is the import closure of the 12 release roots — the six theorem files listed
above, the three errata certificates, two supporting files (`Global/EPDecreasingLimits.lean`:
PSH2 for decreasing limits under the envelope property; `Global/HomogeneousCarrierLimit.lean`: FHX
Lemma 7.4 of the 2026-10-28 revision) and `Source/FiniteDimensionalTopology.lean` (the definition
of `IsPSH` is BJ22's when `N¹(X)_ℝ` is finite dimensional) — computed by [`scripts/closure.py`](scripts/closure.py)
(`python3 scripts/closure.py` re-checks it). It keeps the directory layout of the
development workspace, so that the Lake package names, options and the build cache are those of the
workspace build. Source revision: workspace `322d15868e36b7aec63561aa2fc8cf98f038206c` (see
[`RELEASE-MANIFEST.json`](RELEASE-MANIFEST.json), which lists every file with its sha256).

| Directory | Lake package | Modules | Content |
|---|---|---|---|
| `EnvelopeProperty/` | `EnvelopeProperty` | 3090 | FHX: definitions, the main theorems and their proofs |
| `EnvelopeProperty/deps/hironaka-ep33/` | `hironakaEp33` | 627 | Hironaka: principalization and resolution in characteristic 0 (port of resolutionorg/hironaka) |
| `EnvelopeProperty/deps/aintlib-ep33/` | `aintlibEp33` | 185 | AINTLIB `ModularCurves` / `Common`: sheaves of modules, Čech cohomology, projective space |
| `EnvelopeProperty/deps/tauceti-generic-ep33/` | `tauCetiGenericEp33` | 4 | Tau Ceti: generic freeness |
| `DeJongAlterations/` | `deJongProjectivityEp33` | 1114 | de Jong's alteration theorem via Temkin's stable modification (package config name `DeJongAlterations`) |
| `TranscendentalNakamaye/` | `TranscendentalNakamaye` | 1054 | complex-analytic infrastructure: complex manifolds, multiplier ideals, analytic resolution, Ohsawa–Takegoshi |
| `SGPTFormalization/` | `SGPTFormalization` | 34 | holomorphic germs of schemes over ℂ (from the SGPT formalization) |
| `BingWangEntropy/` | `BingWangEntropy` | 53 | the complex manifold of a smooth scheme over ℂ |
| **total** | | **6161** | |

Each package directory holds its `lakefile.toml`, `lean-toolchain` and `lake-manifest.json`. The
lakefiles are those of the workspace with exact-module globs that are not in the closure removed
(and, in `aintlibEp33`, the library `AintlibEp33`, whose root is not in the closure); options and
requirements are unchanged.

## Paper and errata

* [`paper/`](paper/): the authors' LaTeX source (`main.tex`, `ComplexGeometry.bib`,
  `cgeometry.sty`; revision of 2026-10-28) and the compiled `main.pdf`. The formalization was written against
  the revision `832e086`; in the later revision the main theorem and its corollary are unchanged,
  six intermediate statements are strengthened along the lines of ERRATA §1.3, and the
  formalization needs no change (ERRATA §1.4, EP-4.4).
* [`ERRATA.md`](ERRATA.md): the mistakes in the literature found while formalizing (BJ22, its
  addendum, Wu, the Stacks project, Roberts–Singh, Temkin 2010, de Jong 1996, and the sources of the
  analytic part), with their status, fixes and Lean certificates.

## Blueprint

[`blueprint/`](blueprint/) is a curated subset of the blueprint (the informal, node-by-node
mathematical route) of the formalization: the 1286 chapters (4617 statements)
containing the nodes of the headline theorems, of the `LocalPositivity` and
`SmoothEnvelopeCharZero` inputs, of the global theorems `thm:gl-*` and of the errata certificates,
closed under `\uses` and `\ref`. See [`blueprint/README.md`](blueprint/README.md) for how it was
selected and how to build it.

## Third-party code

The following directories contain code from other projects, with their original copyright headers
and license files; the compatibility changes are recorded in the patch files next to them.

* `EnvelopeProperty/deps/hironaka-ep33/` — from [resolutionorg/hironaka](https://github.com/resolutionorg/hironaka)
  (Apache-2.0), backported to Lean/Mathlib v4.33.1 (`UPSTREAM-CONE.json`, `compatibility.patch`).
* `EnvelopeProperty/deps/aintlib-ep33/` — the `ModularCurves` and `Common` libraries of
  [AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Apache-2.0; `UPSTREAM.json`,
  `COMPATIBILITY.patch`).
* `EnvelopeProperty/deps/tauceti-generic-ep33/` — generic freeness from
  [Tau Ceti](https://github.com/TauCetiProject/TauCeti) (Apache-2.0; `UPSTREAM.json`).
* Individual files elsewhere keep the headers of their origin, e.g.
  `TranscendentalNakamaye/TranscendentalNakamaye/Upstream/` (from zblore/csd-lean4, Apache-2.0)
  and some `DeJongAlterations/DeJongAlterations/Algebra/` files (from resolutionorg/hironaka).

## License

This repository is released under the Apache License, Version 2.0 ([`LICENSE`](LICENSE)). Every file
that does not carry another notice — including the files whose header is the placeholder
"Copyright (c) 2026. All rights reserved." and the files without a header — is released under
Apache-2.0 (see `LICENSE`). Vendored code keeps its upstream license: the packages under
`EnvelopeProperty/deps/` (Apache-2.0, with their own `LICENSE` files) and the individual files that
carry the header of their origin (see [Third-party code](#third-party-code)).

## Credits

* **Paper:** Yanbo Fang, Jiyuan Han and Mingchen Xia, *The envelope property for unibranch
  projective varieties, with an appendix on the singular Yau–Tian–Donaldson conjecture*
  ([`paper/`](paper/)).
* **Lean formalization:** carried out by the AI agents Claude (Anthropic) and Codex (OpenAI) in an
  Archon Horizon workspace.
* **Built on** [Mathlib](https://github.com/leanprover-community/mathlib4) (the Mathlib community)
  and the vendored upstream projects
  [resolutionorg/hironaka](https://github.com/resolutionorg/hironaka) (Resolution),
  [AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Chris Birkbeck and contributors),
  [Tau Ceti](https://github.com/TauCetiProject/TauCeti) (the Tau Ceti contributors) and
  [zblore/csd-lean4](https://github.com/zblore/csd-lean4) (Zayn Blore).
