/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.LeafJacobianCoordinates
import EnvelopeProperty.Char0.PrincipalizationJacobianTree

/-!
# Actual principalization trees with literal monomial leaf Jacobians

Actual geometric neighborhood containment is upgraded to actual coordinates,
actual transformed ideals and actual unit-monomial Jacobian formulas in every
literal leaf subalgebra of the original field.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory Ideal
open scoped Classical

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Actual coordinates, actual pulled-back ideals and actual literal Jacobian formula on
a literal subalgebra leaf, with the original inclusion as its source-function map. -/
def EtaleMonomialJacobianLeafData (C D : Subalgebra k K) (hCD : C ≤ D)
    {Y : Scheme.{u}} (α : Spec (.of D) ⟶ Y) (F : Scheme.DivisorFamily Y)
    (n : ℕ) (J : (Spec (.of C)).IdealSheafData) (x : Y) (z : Fin n → C) : Prop :=
  ∃ (v : Fin n → D) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (c : {i : F.ι // x ∈ (F.component i).support} → Fin n),
    Function.Injective c ∧
    (∀ i, idealOfSpecSheaf ((F.component i.1).comap α) = span {v (c i)}) ∧
    ∃ (e a : {i : F.ι // x ∈ (F.component i).support} → ℕ) (u : Dˣ),
      idealOfSpecSheaf (J.comap (subalgebraSpecMap hCD)) = span {∏ i, v (c i) ^ e i} ∧
      etaleJacobian v hv (fun i => Subalgebra.inclusion hCD (z i)) =
        (u : D) * ∏ i, v (c i) ^ a i

/-- A literal actual finite Rees affine cover with genuine coordinate and Jacobian data on
every leaf, for the same actual SNC family and original ideal. -/
def EtaleMonomialJacobianReesCover (C : Subalgebra k K) {Y : Scheme.{u}}
    (π : Y ⟶ Spec (.of C)) (n : ℕ) (J : (Spec (.of C)).IdealSheafData)
    (z : Fin n → C) : Prop :=
  ∃ (F : Scheme.DivisorFamily Y) (e : F.ι → ℕ), F.IsSnc ∧
    J.comap π = ∏ i, F.component i ^ e i ∧
    ∃ (T : ReesChartTree k K C)
      (φ : (i : T.LeafIndex) → Spec (.of (T.leafAlgebra i)) ⟶ Y),
      (∀ i, IsOpenImmersion (φ i)) ∧
      (∀ i, φ i ≫ π =
        subalgebraSpecMap (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))) ∧
      (∀ y : Y, ∃ (i : T.LeafIndex) (x : Spec (.of (T.leafAlgebra i))), φ i x = y) ∧
      (∀ i : T.LeafIndex, ∃ x : Y, IsClosed ({x} : Set Y) ∧
        EtaleMonomialJacobianLeafData C (T.leafAlgebra i)
          (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i)) (φ i) F n J x z)

/-- Actual geometric neighborhood containment upgrades to literal etale coordinates,
boundary/transform ideals and unit-monomial Jacobians on all actual Rees leaves. -/
theorem exists_etale_monomial_jacobian_rees_cover (C : Subalgebra k K)
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of C)) (n : ℕ) (J : (Spec (.of C)).IdealSheafData)
    (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (h : SNCJacobianReesCover C π n J) : EtaleMonomialJacobianReesCover C π n J z := by
  obtain ⟨F, e, hF, hmon, T, φ, hopen, htriangle, hcover, hdata⟩ := h
  refine ⟨F, e, hF, hmon, T, φ, hopen, htriangle, hcover, ?_⟩
  intro i
  obtain ⟨x, W, hx, hW, hiW⟩ := hdata i
  let D := T.leafAlgebra i
  let hCD : C ≤ D := T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i)
  let _ : Algebra C D := (Subalgebra.inclusion hCD).toAlgebra
  have : IsScalarTower k C D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsOpenImmersion (φ i) := hopen i
  have hiπ : φ i ≫ π = Spec.map (CommRingCat.ofHom (algebraMap C D)) := htriangle i
  refine ⟨x, hx, ?_⟩
  exact exists_leaf_coordinates_jacobian_monomial (k := k) π (φ i) hiπ J F n x W hW hiW z hz

variable [CharZero k]

/-- The actual BP principalization itself produces a literal finite Rees cover with actual
etale coordinates and actual unit-monomial Jacobians on every leaf. -/
theorem exists_affinePrincipalization_literal_leaf_jacobians
    (C : Subalgebra k K) (hC : C.FG) (n : ℕ)
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (I : Ideal C) (hI : I ≠ ⊥)
    (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
    ∃ S : Scheme.BlowUpSequence (Spec (.of C)),
      S = Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI) ∧
      SmoothOfRelativeDimension n (S.composite ≫ f) ∧
      EtaleMonomialJacobianReesCover C S.composite n (specIdealSheaf I) z := by
  obtain ⟨S, hS, hsm, hcover⟩ := exists_affinePrincipalization_jacobian_rees_cover C hC n I hI z hz
  exact ⟨S, hS, hsm, exists_etale_monomial_jacobian_rees_cover C S.composite n
    (specIdealSheaf I) z hz hcover⟩

end EnvelopeProperty.Char0
