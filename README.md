# The envelope property for unibranch projective varieties

A Lean 4 / Mathlib formalization of the main results of Yanbo Fang, Jiyuan Han and
Mingchen Xia, *The envelope property for unibranch projective varieties*
([paper and bibliography](paper/)).

The main theorem proves the envelope property for every real numerical class on
an integral unibranch projective variety over an algebraically closed, trivially
valued field. Its corollary characterizes unibranch varieties by the envelope
property. The statements use the hypotheses of the paper.

## Main theorems

Let `k` be an algebraically closed field with the trivial absolute value, and let
`p : X ⟶ Spec k` be an integral projective scheme. Write
`X^an = Variety.An p`, `N¹(X)_ℝ = NativeRealNumericalClasses.Space p`,
`PSH(X, θ) = Variety.IsPSH p θ` and
`EP_X(θ) = Variety.HasEnvelopeProperty p θ`.
The envelope property means that the upper semicontinuous regularization of the
supremum of every nonempty, uniformly bounded-above family of θ-psh functions is
θ-psh.

The declarations below are in namespace `EnvelopeProperty`, in
[`EnvelopeProperty/MainTheorem.lean`](EnvelopeProperty/MainTheorem.lean).
Numbering refers to the [paper in this repository](paper/main.tex).

| Paper | Lean declaration | Statement |
|---|---|---|
| Theorem A | `Variety.hasEnvelopeProperty_of_isUnibranch` | If `X` is unibranch, `EP_X(θ)` holds for every `θ ∈ N¹(X)_ℝ`. |
| Theorem A, family form | `Variety.isPSH_uscReg_iSup_of_isUnibranch` | For a nonempty uniformly bounded-above family `(φ_i)` in `PSH(X, θ)`, its regularized supremum belongs to `PSH(X, θ)`. |
| Theorem A, local-ring form | `Variety.hasEnvelopeProperty_of_forall_isUnibranchLocalRing_stalk`, `Variety.isPSH_uscReg_iSup_of_forall_isUnibranchLocalRing_stalk` | The same conclusions when every local ring `𝒪_{X,x}` is unibranch. |
| Corollary 1.1 | `Variety.isUnibranch_tfae_hasEnvelopeProperty` | Equivalent: `X` is unibranch; its local rings are unibranch; its local rings are geometrically unibranch; `EP_X(θ)` holds for every real numerical class; `EP_X(ω)` holds for some ample class. |
| Corollary 7.6, on multiprojective models | `MultiModel.hasEnvelopeProperty_of_isNormal` | A normal model has the envelope property at every real class. |
| Corollary 8.4, on multiprojective models | `MultiModel.isPSH_of_antitone_of_isUnibranch` | A nontrivial decreasing limit of psh functions whose classes converge is psh at the limiting class. |

`Variety.IsUnibranch X` means that the normalization of `X` is bijective; its
equivalence with the local-ring definition is proved in
[`Source/Unibranch.lean`](EnvelopeProperty/Source/Unibranch.lean).

The same file gives the envelope theorem, its family form and the characterization
for multiprojective models (`MultiModel.hasEnvelopeProperty_of_isUnibranch`,
`MultiModel.isPSH_uscReg_iSup_of_isUnibranch`,
`MultiModel.isUnibranch_tfae_hasEnvelopeProperty`) and for prime-ideal presentations
`X = V(I) ⊆ ∏_c ℙ^{M_c}`
(`MultiModel.hasEnvelopeProperty_quotModel_of_isUnibranch`,
`MultiModel.isPSH_uscReg_iSup_quotModel_of_isUnibranch`,
`MultiModel.quotModel_isUnibranch_tfae`).

## Formalization conventions

- Convergence of classes is `Variety.AmpleTendsto`, defined using the order of the
  ample cone. When `N¹(X)_ℝ` is finite dimensional, it is equivalent to Euclidean
  convergence: `Variety.ampleTendsto_iff_tendsto` and
  `Variety.isPSH_iff_isCurveWeakPSH` in
  [`Source/FiniteDimensionalTopology.lean`](EnvelopeProperty/Source/FiniteDimensionalTopology.lean).
  Finite dimensionality of the Néron–Severi space is not formalized; the main
  theorems do not assume it.
- Nets in the definition of `IsPSH` are indexed by directed preorders in the
  universe of `X`.
- The trivially valued field is `k` itself. No countability assumption is imposed
  on `k`.

## Errata certificates

[`ERRATA.md`](ERRATA.md) records corrections to the literature and the corresponding
formal results. In particular:

- `not_bj22Lemma46 : ¬ BJ22Lemma46Statement` is a counterexample to BJ22 Lemma 4.6
  ([source](EnvelopeProperty/Global/Lemma46Counterexample.lean)).
- `MultiModel.isPSH_of_antitone_of_homMajorant` proves decreasing-limit stability
  below a homogeneous majorant
  ([source](EnvelopeProperty/Global/PSH2HomogeneousMajorant.lean)).
- `ProjBerk.bj621_counterexample` formalizes the projective-line example of FHX
  Remark 7.3, refuting a monotonicity step in the proof of BJ22 Theorem 6.21
  ([source](EnvelopeProperty/Projective/Remark73ProjectiveLine.lean)).

## Counterexample to BJ22 Theorem 4.5

[`BJ45-counterexample.md`](BJ45-counterexample.md) gives a mathematical
counterexample to the original varying-class assertion (PSH2) in BJ22
Theorem 4.5. On an integral projective non-unibranch surface $X$, it constructs
an ample line bundle $A$, a class $\theta$, and a generically finite function $u$
such that

$$
u\in\operatorname{PSH}(X,\theta+n^{-1}[A])\quad\text{for every }n\ge1,
\qquad u\notin\operatorname{PSH}(X,\theta).
$$

Thus the constant sequence $u_n=u$ violates the varying-class assertion.
The note includes the construction and proof; **it is not formalized in Lean**.
It does not contradict the unibranch results stated above.

## Building

Install [elan](https://github.com/leanprover/elan), `git` and `xz`. The toolchain is
`leanprover/lean4:v4.33.1`; Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). Run from the repository root:

```sh
lake exe cache get
scripts/build-cache/restore.sh
lake build --no-build
lake env lean scripts/Axioms.lean
```

The first command downloads Mathlib and its dependencies; the second restores this
project's compiled artifacts. `lake build --no-build` checks that every module is
up to date without compiling anything. To compile from source, use `lake build`.
See [`BUILD-CACHE.md`](BUILD-CACHE.md) for cache requirements and options.
Do not run `lake update`: the dependency revisions are pinned.

A single module can be checked with `lake build EnvelopeProperty.MainTheorem`.
The default build includes every module under `EnvelopeProperty/`.

## Axioms

[`scripts/Axioms.lean`](scripts/Axioms.lean) audits the main theorems, the errata
certificates, decreasing-limit stability and the finite-dimensional topology
comparison. All 96 audited theorems depend exactly on
`[propext, Classical.choice, Quot.sound]`, Lean's standard axioms.

## Layout

One Lake project at the repository root contains the following library and
vendored source files:

| Directory | Lean modules | Contents |
|---|---:|---|
| `EnvelopeProperty/`, excluding the two parts below | 3,089 | Envelope properties, Berkovich geometry, local regularization, vanishing and the main theorems |
| `EnvelopeProperty/Alterations/` | 1,114 | Alterations and stable modification |
| `EnvelopeProperty/ComplexGeometry/` | 1,141 | Complex manifolds, pluripotential theory, resolution, analytic germs and schemes over ℂ |
| `vendor/hironaka/` | 627 | Principalization and resolution in characteristic zero |
| `vendor/aintlib/` | 185 | Sheaves of modules, Čech cohomology and projective geometry |
| `vendor/tauceti/` | 4 | Generic freeness |
| **Total** | **6,160** | |

[`blueprint/`](blueprint/) contains a curated mathematical blueprint;
[`paper/`](paper/) contains the paper, bibliography and compiled paper;
[`scripts/`](scripts/) contains the axiom audit and cache utilities.

## Third-party code

Vendored code retains its upstream license and attribution. Compatibility patches
and upstream information are stored alongside it:

- [`vendor/hironaka/`](vendor/hironaka/):
  [resolutionorg/hironaka](https://github.com/resolutionorg/hironaka), Apache-2.0.
- [`vendor/aintlib/`](vendor/aintlib/):
  [AINTLIB](https://github.com/CBirkbeck/AINTLIB), Apache-2.0.
- [`vendor/tauceti/`](vendor/tauceti/):
  [Tau Ceti](https://github.com/TauCetiProject/TauCeti), Apache-2.0.
- Individual files under `EnvelopeProperty/ComplexGeometry/Upstream/` include code
  from [zblore/csd-lean4](https://github.com/zblore/csd-lean4), Apache-2.0.
  Some files under `EnvelopeProperty/Alterations/Algebra/` include code from
  resolutionorg/hironaka. Their original headers are retained.

## License

The repository is released under the Apache License, Version 2.0
([`LICENSE`](LICENSE)). Files without a license header, and files with the
placeholder header “Copyright (c) 2026. All rights reserved.”, are included under
Apache-2.0. Vendored code retains its own license notices.

## Credits

The paper is by Yanbo Fang, Jiyuan Han and Mingchen Xia. The Lean formalization
was carried out by the AI agents Claude (Anthropic) and Codex (OpenAI).
It builds on Mathlib and the third-party projects credited above.

