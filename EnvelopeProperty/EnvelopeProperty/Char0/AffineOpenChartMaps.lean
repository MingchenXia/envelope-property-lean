/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SNCJacobianCover
import EnvelopeProperty.Char0.JacobianMonomialPullback

/-!
# Actual ring maps from literal leaf spectra into affine neighborhoods

The factor map, ring map, actual spectrum triangle, etaleness and principal
unit images are constructed from the actual open immersion and its range.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory
open scoped Classical

universe u

variable {A : Type u} [CommRing A] {Y : Scheme.{u}}

/-- The actual affine factor of a literal leaf map gives its actual coordinate ring map. -/
def affineOpenChartRingHom (α : Spec (.of A) ⟶ Y) (U : Y.affineOpens)
    (hα : Set.range α ⊆ (U.1 : Set Y)) : Γ(Y, U.1) →+* A := by
  have hU : IsAffineOpen U.1 := U.2
  exact (Spec.preimage (IsOpenImmersion.lift hU.fromSpec α
    (by rwa [hU.range_fromSpec]))).hom

/-- The actual ring map has the exact original leaf-to-chart triangle. -/
theorem affineOpenChartRingHom_spec_comp (α : Spec (.of A) ⟶ Y) (U : Y.affineOpens)
    (hα : Set.range α ⊆ (U.1 : Set Y)) :
    Spec.map (CommRingCat.ofHom (affineOpenChartRingHom α U hα)) ≫ U.2.fromSpec = α := by
  have hU : IsAffineOpen U.1 := U.2
  change Spec.map (Spec.preimage (IsOpenImmersion.lift hU.fromSpec α _)) ≫ hU.fromSpec = α
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

/-- An actual leaf open immersion induces an actual open immersion of affine spectra. -/
theorem isOpenImmersion_affineOpenChartRingHom (α : Spec (.of A) ⟶ Y)
    [IsOpenImmersion α] (U : Y.affineOpens) (hα : Set.range α ⊆ (U.1 : Set Y)) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (affineOpenChartRingHom α U hα))) := by
  have hU : IsAffineOpen U.1 := U.2
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (affineOpenChartRingHom α U hα)) ≫ U.2.fromSpec) := by
    rw [affineOpenChartRingHom_spec_comp]
    infer_instance
  exact IsOpenImmersion.of_comp _ hU.fromSpec

/-- The actual affine chart ring map is etale, as a consequence of its actual open immersion. -/
theorem etale_affineOpenChartRingHom (α : Spec (.of A) ⟶ Y) [IsOpenImmersion α]
    (U : Y.affineOpens) (hα : Set.range α ⊆ (U.1 : Set Y)) :
    (affineOpenChartRingHom α U hα).Etale := by
  have := isOpenImmersion_affineOpenChartRingHom α U hα
  exact (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom (affineOpenChartRingHom α U hα))).mp inferInstance

/-- Containment of the actual leaf image in a principal neighborhood makes its defining
function an actual unit in the literal leaf ring. -/
theorem isUnit_affineOpenChartRingHom_of_range_basicOpen
    (α : Spec (.of A) ⟶ Y) (U : Y.affineOpens) (hα : Set.range α ⊆ (U.1 : Set Y))
    (s : Γ(Y, U.1)) (hs : Set.range α ⊆ (Y.basicOpen s : Set Y)) :
    IsUnit (affineOpenChartRingHom α U hα s) := by
  let φ := affineOpenChartRingHom α U hα
  have hrange : Set.range (Spec.map (CommRingCat.ofHom φ)) ⊆
      (PrimeSpectrum.basicOpen s).1 := by
    rintro y ⟨x, rfl⟩
    have hx : U.2.fromSpec ((Spec.map (CommRingCat.ofHom φ)) x) ∈ Y.basicOpen s := by
      change ((Spec.map (CommRingCat.ofHom φ)) ≫ U.2.fromSpec) x ∈ Y.basicOpen s
      rw [affineOpenChartRingHom_spec_comp]
      exact hs ⟨x, rfl⟩
    change (Spec.map (CommRingCat.ofHom φ)) x ∈ U.2.fromSpec ⁻¹ᵁ Y.basicOpen s at hx
    rwa [U.2.fromSpec_preimage_basicOpen] at hx
  have htop : PrimeSpectrum.basicOpen (φ s) = ⊤ := by
    apply top_unique
    intro x _
    exact hrange ⟨x, rfl⟩
  have hiSup : (⨆ _ : Unit, PrimeSpectrum.basicOpen (φ s)) = ⊤ := by simpa using htop
  have hspan : Ideal.span ({φ s} : Set A) = ⊤ := by
    simpa only [Set.range_const] using PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hiSup
  exact Ideal.span_singleton_eq_top.mp hspan

section Base

variable {R : Type u} [CommRing R]

/-- The actual original-base triangle gives actual compatibility of the constructed chart
ring map with the original section map. -/
theorem affineOpenChartRingHom_comp_sectionsHom (π : Y ⟶ Spec (.of R))
    (α : Spec (.of A) ⟶ Y) (U : Y.affineOpens) (hα : Set.range α ⊆ (U.1 : Set Y))
    (r : R →+* A) (hr : α ≫ π = Spec.map (CommRingCat.ofHom r)) :
    (affineOpenChartRingHom α U hα).comp (sectionsHom π U.1) = r := by
  have h : CommRingCat.ofHom ((affineOpenChartRingHom α U hα).comp (sectionsHom π U.1)) =
      CommRingCat.ofHom r := by
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom (sectionsHom π U.1) ≫
      CommRingCat.ofHom (affineOpenChartRingHom α U hα)) = _
    rw [Spec.map_comp, ← fromSpec_comp_eq_specMap_sectionsHom π U,
      ← Category.assoc, affineOpenChartRingHom_spec_comp, hr]
  exact congrArg (fun f => f.hom) h

end Base

section Coordinates

variable {k A₀ : Type u} [CommRing k] [CommRing A₀]
  [Algebra k A₀] [Algebra k A] [Algebra A₀ A] [IsScalarTower k A₀ A] {n : ℕ}

/-- Actual etaleness of a refining ring map and of the original coordinate map produces
actual etaleness of the image coordinates. -/
theorem etale_aeval_algebraMap (v : Fin n → A₀)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (hA : (algebraMap A₀ A).Etale) :
    (MvPolynomial.aeval (R := k) (fun i => algebraMap A₀ A (v i))).toRingHom.Etale := by
  have hcomp : (MvPolynomial.aeval (R := k) (fun i => algebraMap A₀ A (v i))).toRingHom =
      (algebraMap A₀ A).comp (MvPolynomial.aeval (R := k) v).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change (MvPolynomial.aeval (R := k) (fun i => algebraMap A₀ A (v i))) (MvPolynomial.C c) =
        algebraMap A₀ A ((MvPolynomial.aeval (R := k) v) (MvPolynomial.C c))
      rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
      exact IsScalarTower.algebraMap_apply k A₀ A c
    · intro i
      change (MvPolynomial.aeval (R := k) (fun i => algebraMap A₀ A (v i))) (MvPolynomial.X i) =
        algebraMap A₀ A ((MvPolynomial.aeval (R := k) v) (MvPolynomial.X i))
      rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  rw [hcomp]
  exact RingHom.Etale.stableUnderComposition _ _ hv hA

end Coordinates

end EnvelopeProperty.Char0
