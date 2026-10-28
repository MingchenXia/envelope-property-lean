/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.AffineOpenChartMaps

/-!
# Genuine coordinate Jacobians on literal Rees leaf algebras

All affine factor maps, scalar towers, etaleness, principal unit images and
unit-monomial Jacobian formulas are derived from the actual leaf geometry.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory Module Ideal
open scoped Classical

universe u

variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
  [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A] {Y : Scheme.{u}}

/-- The actual original base triangle constructs the original-base scalar tower. -/
theorem isScalarTower_original_affineOpenChartRingHom (π : Y ⟶ Spec (.of R))
    (α : Spec (.of A) ⟶ Y) (U : Y.affineOpens) (hα : Set.range α ⊆ (U.1 : Set Y))
    (hπ : α ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    letI : Algebra R Γ(Y, U.1) := (sectionsHom π U.1).toAlgebra
    letI : Algebra Γ(Y, U.1) A := (affineOpenChartRingHom α U hα).toAlgebra
    IsScalarTower R Γ(Y, U.1) A := by
  let _ : Algebra R Γ(Y, U.1) := (sectionsHom π U.1).toAlgebra
  let _ : Algebra Γ(Y, U.1) A := (affineOpenChartRingHom α U hα).toAlgebra
  exact IsScalarTower.of_algebraMap_eq'
    (affineOpenChartRingHom_comp_sectionsHom π α U hα (algebraMap R A) hπ).symm

/-- Composing the actual original-base triangle constructs the field-base scalar tower
with the canonical scheme section algebra. -/
theorem isScalarTower_field_affineOpenChartRingHom (π : Y ⟶ Spec (.of R))
    (α : Spec (.of A) ⟶ Y) (U : Y.affineOpens) (hα : Set.range α ⊆ (U.1 : Set Y))
    (hπ : α ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    letI := (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))).sectionsAlgebra U.1
    letI : Algebra Γ(Y, U.1) A := (affineOpenChartRingHom α U hα).toAlgebra
    IsScalarTower k Γ(Y, U.1) A := by
  let _ := (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))).sectionsAlgebra U.1
  let _ : Algebra Γ(Y, U.1) A := (affineOpenChartRingHom α U hα).toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  change algebraMap k A = (affineOpenChartRingHom α U hα).comp
    (sectionsHom (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) U.1)
  rw [sectionsHom_comp_specMap, ← RingHom.comp_assoc,
    affineOpenChartRingHom_comp_sectionsHom π α U hα (algebraMap R A) hπ]
  exact IsScalarTower.algebraMap_eq k R A

/-- Actual pullback along the leaf map is the mapped native ideal of the original chart. -/
theorem idealOfSpecSheaf_comap_affineOpenChart (J : Y.IdealSheafData)
    (α : Spec (.of A) ⟶ Y) (U : Y.affineOpens) (hα : Set.range α ⊆ (U.1 : Set Y)) :
    idealOfSpecSheaf (J.comap α) = (J.ideal U).map (affineOpenChartRingHom α U hα) := by
  conv_lhs => rw [← affineOpenChartRingHom_spec_comp α U hα]
  rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_fromSpec]
  change idealOfSpecSheaf ((specIdealSheaf (J.ideal U)).comap
    (Spec.map (CommRingCat.ofHom (affineOpenChartRingHom α U hα)))) = _
  rw [Scheme.IdealSheafData.comap_ofIdealTop_Spec_map, idealOfSpecSheaf_specIdealSheaf]
  rfl

/-- An actual leaf contained in an actual SNC Jacobian neighborhood has actual etale
coordinates cutting out the pulled-back boundary, the exact original ideal monomial and
an actual unit-monomial formula for the literal original-base coordinate Jacobian. -/
theorem exists_leaf_coordinates_jacobian_monomial [IsDomain A]
    (π : Y ⟶ Spec (.of R)) (α : Spec (.of A) ⟶ Y) [IsOpenImmersion α]
    (hπ : α ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (J : (Spec (.of R)).IdealSheafData) (F : Scheme.DivisorFamily Y) (n : ℕ)
    (x : Y) (W : Y.affineOpens)
    (hW : SNCJacobianNeighbourhood (k := k) π F n J x W)
    (hαW : Set.range α ⊆ (W.1 : Set Y))
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    ∃ (v : Fin n → A) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
      (c : {i : F.ι // x ∈ (F.component i).support} → Fin n),
      Function.Injective c ∧
      (∀ i, idealOfSpecSheaf ((F.component i.1).comap α) = span {v (c i)}) ∧
      ∃ (e a : {i : F.ι // x ∈ (F.component i).support} → ℕ) (u : Aˣ),
        idealOfSpecSheaf (J.comap (Spec.map (CommRingCat.ofHom (algebraMap R A)))) =
          span {∏ i, v (c i) ^ e i} ∧
        etaleJacobian v hv (fun i => algebraMap R A (z i)) =
          (u : A) * ∏ i, v (c i) ^ a i := by
  obtain ⟨U, v, hxU, hv, c, hcinj, hc, _, e, hJ, s, rfl, _, a, hJac⟩ := hW
  have hαU : Set.range α ⊆ (U.1 : Set Y) := fun _ hy => Y.basicOpen_le s (hαW hy)
  let f := π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))
  let _ := f.sectionsAlgebra U.1
  let _ : Algebra R Γ(Y, U.1) := (sectionsHom π U.1).toAlgebra
  have := isScalarTower_base_resolutionSections (k := k) π U.1
  let φ := affineOpenChartRingHom α U hαU
  let _ : Algebra Γ(Y, U.1) A := φ.toAlgebra
  have := isScalarTower_original_affineOpenChartRingHom π α U hαU hπ
  have := isScalarTower_field_affineOpenChartRingHom (k := k) π α U hαU hπ
  have hφ : (algebraMap Γ(Y, U.1) A).Etale := etale_affineOpenChartRingHom α U hαU
  have : Algebra.Etale Γ(Y, U.1) A := RingHom.etale_algebraMap.mp hφ
  have hU : IsAffineOpen U.1 := U.2
  have hvR : (MvPolynomial.aeval (R := k) v).toRingHom.Etale :=
    (etale_toAffineSpace_iff f hU v).mp hv
  have hvA := etale_aeval_algebraMap (A := A) v hvR hφ
  have hs : IsUnit (algebraMap Γ(Y, U.1) A s) :=
    isUnit_affineOpenChartRingHom_of_range_basicOpen α U hαU s hαW
  have hJac' : (affineRelativeJacobianIdeal (R := R) (etaleDifferentialBasis v hvR)).map
        (algebraMap Γ(Y, U.1) (Localization.Away s)) =
      span {∏ i, algebraMap Γ(Y, U.1) (Localization.Away s) (v (c i)) ^ a i} :=
    hJac (Localization.Away s)
  obtain ⟨u, hu⟩ := exists_unit_etaleJacobian_eq_monomial_of_away
    z hz v hvR hvA s hs c a hJac'
  refine ⟨fun i => algebraMap Γ(Y, U.1) A (v i), hvA, c, hcinj, ?_, e, a, u, ?_, hu⟩
  · intro i
    rw [idealOfSpecSheaf_comap_affineOpenChart (F.component i.1) α U hαU, hc i,
      Ideal.map_span, Set.image_singleton]
    rfl
  · rw [← hπ, Scheme.IdealSheafData.comap_comp,
      idealOfSpecSheaf_comap_affineOpenChart (J.comap π) α U hαU, hJ,
      Ideal.map_span, Set.image_singleton, map_prod]
    simp only [map_pow]
    rfl

end EnvelopeProperty.Char0
