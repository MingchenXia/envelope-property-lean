/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.WeaklyPSH

/-!
# FHX Proposition 5.22 as an explicit hypothesis

This file records, as an explicit `Prop`-valued hypothesis class `NonflatNorms k`, the statement
of Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Proposition 5.22
(`prop:nonflat-norm`, "nonflat norms"):

> Let `Y` be a normal affine variety of dimension `n ≥ 1`, `S ⊆ 𝔸ⁿ` a principal open subset,
> `π : Y → S` a finite surjective generically étale morphism of degree `d`, and `Z ⊊ Y` closed.
> There are positive integers `m_y(π)`, `y ∈ Y^an`, with `∑_{π(y)=s} m_y(π) = d` for every
> `s ∈ S^an`, such that `N_π u(s) = ∑_{π(y)=s} m_y(π) u(y)` lies in `ℛ(S)` for every weakly psh
> `u` on `Y^an` of logarithmic growth that is regularizable on affine opens covering `Y \ Z`.

It is imported **temporarily**, to be proved later. It is **not** an axiom: every theorem using
it lists `[NonflatNorms k]` among its hypotheses, and `#print axioms` of such a theorem shows
only the standard axioms. Its proof in the source needs

* FHX Lemma 5.13 (`lem:finite-flat-norm`) over the étale locus, *with its base change
  compatibility* `(N_π u) ∘ r = N_{π_F}(u ∘ r)` for complete extensions `F/k`: the
  pointwise compatibility is `EnvelopeProperty.Berk.flatNormFun_scalarExtension`, and
  the regularizability result is `EnvelopeProperty.IsRegularizable.flatNormFun`;
* FHX Lemma 5.21 (`lem:curves`): subharmonic functions on analytic curves over complete
  non-Archimedean fields in the sense of Gubler–Rabinoff (norms along finite flat maps of curves,
  the maximum principle, pullbacks of weakly psh functions to curves);
* FHX Theorem 3.1 (the envelope property of `ℙⁿ`; in characteristic `p` FHX's own test-ideal proof, in
  characteristic 0 Boucksom–Jonsson Theorem 5.20), together with FHX
  Lemmas 5.8(2) (`lem:growth`), 5.10 (`lem:compactification`), 5.11(1),(4), 5.12
  (`lem:principal-extension`) and Proposition 5.20(2) (`prop:gluing`), to extend the norm from
  the étale locus to `S`;

The remaining producers are the analytic-curve statements of Lemma 5.21 and the full
nonflat norm argument. The projective-space envelope property of Theorem 3.1 is now proved
by `ProjBerk.hasEnvelopeProperty_of_countable` in `Projective/EnvelopePn.lean`, in every
characteristic under the countability hypothesis already required here. The finite-flat
pointwise norm base change and the local growth, principal-extension, gluing and extension
results listed above are also formalized. The local regularization results retain their
explicit `WuRegularization` hypotheses. The section of FHX containing Proposition 5.22
assumes `k` countable, and its proof uses Proposition 5.20(2), hence the strict exhaustion of
Lemma 5.18, which needs countability; so the class is stated for countable `k` only
(`[Countable k]` is a parameter of the class), algebraically closed and trivially valued as
in the source.

## Encoding

For `A` a finitely generated integrally closed domain over `k` (`Y = Spec A`), `B` a `k`-algebra
and `φ : B →ₐ[k] A` (`π = Spec φ`):

* **`S ⊆ 𝔸ⁿ` principal open**: `IsAffineSpacePrincipalOpen k B n`, i.e.
  `B ≃ₐ[k] k[x₁, …, xₙ]_h` for some `h ≠ 0`; and `1 ≤ n`. The dimension of `Y` is then `n`
  automatically, `π` being finite and surjective.
* **`π` finite surjective**: `φ` is finite (`(φ : B →+* A).Finite`) and injective. For domains,
  injectivity is dominance, and a dominant finite morphism is surjective (its image is closed and
  dense); conversely a surjective morphism of integral schemes is dominant, so `φ` is injective.
* **`π` generically étale**: `IsGenericallyEtale φ`, i.e. `B_h → A_{φ(h)}` is étale for some
  `h ≠ 0`, i.e. `π` is étale over the nonempty principal open `S_h` (`π⁻¹(S_h) = Y_{φ(h)}`).
  This is equivalent to étaleness at the generic point of `Y` (the only point over the generic
  point of `S`): the étale locus `U ⊆ Y` is open, `π(Y \ U)` is closed (`π` is finite) and misses
  the generic point of `S`, so it misses some nonempty `S_h`.
* **The degree** `d = [k(Y) : k(S)]` is `genericDegree φ = finrank_B A`, the rank of `A` as a
  `B`-module via `φ`; it equals `[Frac A : Frac B]` (`genericDegree_eq_finrank`, from Mathlib's
  `IsFractionRing.finrank_eq`).
* **`Z ⊊ Y` closed**: `Z = V(S)` for a finite `S ⊆ A` (every closed subset of the noetherian `Y`
  has this form) with a nonzero element (as `A` is a reduced domain, `V(S) = Y` iff `S ⊆ {0}`).
* **The conclusion** is `Nonempty (NormWeights φ S (IsWeaklyPSHOn Set.univ) (genericDegree φ))`:
  weights `m_y ≥ 1` with finite fibres and `∑_{π(y)=s} m_y = d`, such that the weighted norm of
  every `u` that is weakly psh with a blowup witness (`IsWeaklyPSHOn Set.univ u`), of logarithmic
  growth and regularizable on principal opens covering `Y^an \ Z^an` is regularizable on `S`.

## Why FHX Proposition 5.22 implies the encoded statement

* **Weakly psh functions.** `IsWeaklyPSHOn Set.univ u` asks that `u ∘ μ^an` be locally psh on
  each affine chart `Spec A[s/g]` of the blowup `μ : Y' → Y` along an ideal `(s)`. Blowups are
  proper and birational, the charts cover `Y'`, and local plurisubharmonicity is local, so such
  `u` is weakly psh in the sense of FHX Definition 5.6. The exact converse for arbitrary actual
  proper birational native witnesses is now proved by
  `isWeaklyPSHOn_iff_properBirational_nativeWitness` in `Local/ProperBirationalWeaklyPSH.lean`,
  using genuine finite Rees domination and the whole original scalar and chart maps.
  No external Chow hypothesis is needed for this encoding comparison. The analytic-curve
  inputs listed above remain separate.
* **The covering hypothesis.** In `NormWeights` it reads: every `x ∈ Y^an` with `|f|_x ≠ 0` for
  some `f ∈ S` has a principal open `Y_g ∋ x` (`|g|_x ≠ 0`) on which `u` is regularizable. This is
  equivalent to FHX's "regularizable on affine opens covering `Y \ Z`". Given FHX's cover `U_α`
  and such `x`, its support `p = ker x` is a point of `Y \ Z`, so `p ∈ Y_g ⊆ U_α` for some `g`
  (principal opens form a basis) and `u|_{Y_g}` is regularizable (FHX Lemma 5.11(4), restriction
  from the affine `U_α` to its principal open `Y_g`). Conversely, applying the Lean condition to
  the trivial valuations of the residue fields of the points `p ∈ Y \ Z` gives principal opens
  `Y_g ∋ p` with `u|_{Y_g}` regularizable, and the `Y_{g f} ⊆ Y \ Z`, `f ∈ S`, are affine opens
  covering `Y \ Z` on which `u` is regularizable (Lemma 5.11(4) again). So the hypotheses on `u`
  in the encoded statement imply those of FHX.
* **The weights.** The fibres of `π^an` are finite (`π` is finite), so `NormWeights.finite` is
  part of the meaning of `N_π`; positivity and the degree condition are as in FHX.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open Berk

universe u v w

/-! ### Principal opens of affine space, generic étaleness and the degree -/

section defs

variable (k : Type*) [Field k] (B : Type*) [CommRing B] [Algebra k B]

/-- `Spec B` is (isomorphic to) a principal open subset `D(h) ⊆ 𝔸ⁿ_k`, `h ≠ 0`:
`B ≃ₐ[k] k[x₁, …, xₙ]_h`. -/
def IsAffineSpacePrincipalOpen (n : ℕ) : Prop :=
  ∃ h : MvPolynomial (Fin n) k, h ≠ 0 ∧ Nonempty (B ≃ₐ[k] Localization.Away h)

variable {k B}

/-- A principal open of affine space is of finite type over `k`. -/
theorem IsAffineSpacePrincipalOpen.finiteType {n : ℕ} (hB : IsAffineSpacePrincipalOpen k B n) :
    Algebra.FiniteType k B := by
  obtain ⟨h, -, ⟨e⟩⟩ := hB
  have : Algebra.FiniteType (MvPolynomial (Fin n) k) (Localization.Away h) :=
    have := IsLocalization.Away.finitePresentation (S := Localization.Away h) h
    Algebra.FiniteType.of_finitePresentation
  have : Algebra.FiniteType k (Localization.Away h) :=
    Algebra.FiniteType.trans (S := MvPolynomial (Fin n) k) inferInstance inferInstance
  exact Algebra.FiniteType.equiv this e.symm

end defs

section generic

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B]

/-- `π = Spec φ : Spec A → Spec B` is **generically étale**: it is étale over a principal open
`D(h)`, `h ≠ 0`, i.e. `B_h → A_{φ(h)}` is étale. For `B` a domain and `φ` finite with `A` a
domain, this is étaleness at the generic point (the étale locus being open). -/
def IsGenericallyEtale (φ : B →+* A) : Prop :=
  ∃ h : B, h ≠ 0 ∧ (Localization.awayMap φ h).Etale

/-- The **degree** of `π = Spec φ`: the rank of `A` as a `B`-module via `φ`. For a finite
injective `φ` between domains this is `[Frac A : Frac B]` (`genericDegree_eq_finrank`). -/
def genericDegree (φ : B →+* A) : ℕ :=
  letI := φ.toAlgebra
  Module.finrank B A

/-- The degree is the degree of the extension of fraction fields: if `K = Frac B`, `L = Frac A`
and `K → L` extends `φ`, then `genericDegree φ = [L : K]`. -/
theorem genericDegree_eq_finrank (φ : B →+* A) (K L : Type*) [Field K] [Field L]
    [Algebra B K] [IsFractionRing B K] [Algebra A L] [IsFractionRing A L] [Algebra K L]
    (hKL : ∀ b, algebraMap K L (algebraMap B K b) = algebraMap A L (φ b)) :
    genericDegree φ = Module.finrank K L := by
  let := φ.toAlgebra
  let : Algebra B L := ((algebraMap A L).comp φ).toAlgebra
  have : IsScalarTower B K L := IsScalarTower.of_algebraMap_eq fun b => (hKL b).symm
  have : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (IsFractionRing.finrank_eq B K A L).symm

end generic

/-! ### The hypothesis class -/

/-- **Imported (FHX Proposition 5.22, `prop:nonflat-norm`), temporarily.** For every normal
affine variety `Y = Spec A` over the countable algebraically closed trivially valued field `k`,
every principal open `S = Spec B ⊆ 𝔸ⁿ` (`n ≥ 1`), every finite surjective generically étale
`π = Spec φ : Y → S` (`φ` injective and finite) and every closed `Z = V(S) ⊊ Y`, there are
weights `m_y ≥ 1` with `∑_{π(y)=s} m_y = d = genericDegree φ` such that the weighted norm
`N_π u = ∑ m_y u(y)` of every weakly psh `u` of logarithmic growth, regularizable on principal
opens covering `Y \ Z`, is regularizable on `S`. See the module docstring for the encoding and
why FHX Proposition 5.22 implies it; its proof needs FHX Lemma 5.13 with base change, Lemma 5.21
(Gubler–Rabinoff subharmonicity on curves) and Theorem 3.1. -/
class NonflatNorms (k : Type u) [Field k] [IsAlgClosed k] [Countable k] : Prop where
  exists_normWeights : ∀ (A : Type v) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [IsIntegrallyClosed A] (B : Type w) [CommRing B] [Algebra k B]
    (n : ℕ), 1 ≤ n → IsAffineSpacePrincipalOpen k B n →
    ∀ φ : B →ₐ[k] A, Function.Injective φ → (φ : B →+* A).Finite →
      IsGenericallyEtale (φ : B →+* A) →
    ∀ S : Finset A, (∃ f ∈ S, f ≠ 0) →
      Nonempty (NormWeights φ S (IsWeaklyPSHOn Set.univ) (genericDegree (φ : B →+* A)))

/-- The weights of FHX Proposition 5.22 (`prop:nonflat-norm`), from `NonflatNorms`. -/
theorem NonflatNorms.nonempty_normWeights {k : Type u} [Field k] [IsAlgClosed k] [Countable k]
    [NonflatNorms.{u, v, w} k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [IsIntegrallyClosed A] {B : Type w} [CommRing B] [Algebra k B]
    {n : ℕ} (hn : 1 ≤ n) (hB : IsAffineSpacePrincipalOpen k B n) (φ : B →ₐ[k] A)
    (hinj : Function.Injective φ) (hfin : (φ : B →+* A).Finite)
    (het : IsGenericallyEtale (φ : B →+* A)) (S : Finset A) (hS : ∃ f ∈ S, f ≠ 0) :
    Nonempty (NormWeights φ S (IsWeaklyPSHOn Set.univ) (genericDegree (φ : B →+* A))) :=
  NonflatNorms.exists_normWeights A B n hn hB φ hinj hfin het S hS

end EnvelopeProperty
