/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.NonflatImport
import EnvelopeProperty.AlgGeom.AffineOpen

/-!
# FHX Lemma 5.23 (projections) as an explicit hypothesis

This file records, as an explicit `Prop`-valued hypothesis class `ProjectionExistence k`, the
statement of Fang–Han–Xia, *The envelope property for unibranch projective varieties*,
Lemma 5.23 (`lem:projection-existence`, Wu, Lemma 6.16, supplemented by generic étaleness):

> Let `Y` be an affine variety of dimension `n ≥ 1`, `Z ⊊ Y` a closed subset, and `z ∈ Z` a closed
> point at which `Z` is smooth. There are an affine open neighbourhood `U` of `z`, a principal
> open subset `S ⊆ 𝔸ⁿ` and a finite surjective generically étale morphism `π : U → S` whose
> restriction to `Z ∩ U` is a closed immersion.

It is **not** an axiom: every theorem using it lists `[ProjectionExistence k]` among its
hypotheses. Everything else that the proof of FHX Theorem 5.25 needs from algebraic geometry
(the shrinking of `U` to a principal open, generic smoothness, the choice of `g`, the partition of
unity) is proved from it in `EnvelopeProperty.Local.ProjectionPackageProof`.

## Encoding

* `Y = Spec A` with `A` a finitely generated `k`-domain (`k` algebraically closed); its dimension
  is the Krull dimension, `ringKrullDim A = n`, `1 ≤ n` (it is a natural number,
  `EnvelopeProperty.exists_ringKrullDim_eq_natCast`).
* `Z = V(I)` with its reduced structure: `I` a radical ideal, `A / I` the ring of `Z`. As `A` is a
  reduced domain, `Z ≠ Y` iff `I ≠ ⊥`.
* `z` a closed point of `Z`: a maximal ideal of `A / I`. `Z` is smooth at `z`:
  `Algebra.IsSmoothAt k z`, i.e. `(A / I)_z` is formally smooth over `k`; as `A / I` is of finite
  presentation over `k`, this is equivalent to the existence of `f ∉ z` with `(A / I)_f` smooth
  over `k` (Mathlib's `Algebra.IsSmoothAt.exists_notMem_smooth` and
  `Algebra.basicOpen_subset_smoothLocus_iff_smooth`), which is smoothness of `Z` at `z` in the
  sense of the Stacks project (Tag 00TB).
* `U` an affine open of `Y`: its coordinate ring `A'` (a `k`-algebra and an `A`-algebra
  compatibly) with `IsAffineOpenImmersion A A'`, i.e. `A → A'` identifies `Spec A'` with an open
  subscheme of `Spec A` (finitely many `D(a) ⊆ Spec A`, `a ∈ A`, cover `U` and `A'_a = A_a`; see
  `EnvelopeProperty.AlgGeom.AffineOpen` for why this is the same as an affine open subscheme).
  `z ∈ U`: some prime `z'` of `A'` contracts to the maximal ideal of `A` corresponding to `z`.
* `S = D(h₀) ⊆ 𝔸ⁿ`, `h₀ ≠ 0` in `k[x₁, …, xₙ]`, with ring `Localization.Away h₀`.
* `π = Spec φ` for `φ : k[S] →ₐ[k] A'`: finite (`(φ : _ →+* _).Finite`), surjective
  (`φ` injective: for domains, a finite morphism is surjective iff dominant, iff `φ` is injective),
  generically étale (`IsGenericallyEtale`: étale over a nonempty principal open of `S`, which for a
  finite morphism of varieties is étaleness at the generic point, see `NonflatImport`).
* `π|_{Z ∩ U}` is a closed immersion: `k[S] → A' / I A'` is surjective (`I A'` is the ideal of the
  reduced closed subscheme `Z ∩ U` of `U`, as `U → Y` is flat and `A / I` is reduced).

The statement is FHX's, with the dimension of `Y` its Krull dimension. The shrinking of `U` to a
principal open of `Y` (prime avoidance on the finite fibre over `π(z)`, then shrinking `S`) is
proved in `ProjectionExistence.exists_principal`.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

universe u v

/-- **FHX Lemma 5.23** (`lem:projection-existence`; Wu, Lemma 6.16), proved for every algebraically
closed `k` in `Local/ProjectionExistenceProof.lean` (`projectionExistence_of_isAlgClosed`).
Let `Y = Spec A` be an affine variety over the algebraically closed field `k` of dimension `n ≥ 1`
(`ringKrullDim A = n`), `Z = V(I) ⊊ Y` a closed subset (`I` radical, `I ≠ ⊥`) and `z` a closed
point of `Z` (a maximal ideal of `A / I`) at which `Z` is smooth (`Algebra.IsSmoothAt k z`).
There are an affine open neighbourhood `U = Spec A'` of `z` (`IsAffineOpenImmersion A A'`, and a
prime `z'` of `A'` over `z`), a principal open `S = D(h₀) ⊆ 𝔸ⁿ` (`h₀ ≠ 0`) and a finite
surjective generically étale `π = Spec φ : U → S` (`φ` injective, finite, `IsGenericallyEtale`)
restricting to a closed immersion on `Z ∩ U` (`k[S] → A' / I A'` surjective).

See the module docstring for the encoding. -/
class ProjectionExistence (k : Type u) [Field k] [IsAlgClosed k] : Prop where
  exists_projection : ∀ (A : Type v) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (n : ℕ), ringKrullDim A = n → 1 ≤ n →
    ∀ (I : Ideal A), I.IsRadical → I ≠ ⊥ →
    ∀ (z : Ideal (A ⧸ I)) [z.IsMaximal], Algebra.IsSmoothAt k z →
    ∃ (A' : Type v) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra k A')
      (_ : IsScalarTower k A A'), IsAffineOpenImmersion A A' ∧
      (∃ z' : Ideal A', z'.IsPrime ∧
        z'.comap (algebraMap A A') = z.comap (Ideal.Quotient.mk I)) ∧
      ∃ h₀ : MvPolynomial (Fin n) k, h₀ ≠ 0 ∧
      ∃ φ : Localization.Away h₀ →ₐ[k] A',
        Function.Injective φ ∧
        (φ : Localization.Away h₀ →+* A').Finite ∧
        IsGenericallyEtale (φ : Localization.Away h₀ →+* A') ∧
        Function.Surjective ((Ideal.Quotient.mk (I.map (algebraMap A A'))).comp
          (φ : Localization.Away h₀ →+* A'))

end EnvelopeProperty
