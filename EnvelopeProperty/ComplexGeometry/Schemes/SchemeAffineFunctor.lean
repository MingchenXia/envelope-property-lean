import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAffineComplexPoints

/-! # Analytic continuity of actual affine scheme point maps

The actual contravariant Spec morphism induces the continuous algebra point
pullback under the proved affine point homeomorphism.
-/

open CategoryTheory AlgebraicGeometry

namespace ComplexSchemes

noncomputable section

variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

/-- The actual Spec morphism of a complex algebra map respects the structural maps. -/
theorem affineSchemeMap_overComplex (h : A →ₐ[ℂ] B) :
    Spec.map (CommRingCat.ofHom h.toRingHom) ≫ complexAffineStructureMap A =
      complexAffineStructureMap B := by
  rw [complexAffineStructureMap, complexAffineStructureMap, ← Spec.map_comp]
  congr 1
  ext c
  exact h.commutes c

/-- The actual affine scheme point pullback under the proved point homeomorphisms. -/
def affineSchemePointPullback (h : A →ₐ[ℂ] B) :
    SchemeComplexPoint (complexAffineStructureMap B) →
      SchemeComplexPoint (complexAffineStructureMap A) :=
  fun p => (affineSchemeComplexPointHomeomorph A).symm
    (((affineSchemeComplexPointHomeomorph B) p).comp h)

/-- This map is literally composition with the native contravariant Spec morphism. -/
theorem affineSchemePointPullback_val (h : A →ₐ[ℂ] B)
    (p : SchemeComplexPoint (complexAffineStructureMap B)) :
    (affineSchemePointPullback h p).val =
      p.val ≫ Spec.map (CommRingCat.ofHom h.toRingHom) := by
  change (complexAlgebraPoint_toScheme A ((affineSchemePoint_toAlgebra B p).comp h)).val = _
  have hnat := complexAlgebraPoint_toScheme_naturality A h (affineSchemePoint_toAlgebra B p)
  have hp : complexAlgebraPoint_toScheme B (affineSchemePoint_toAlgebra B p) = p :=
    (affineSchemeComplexPointEquiv B).left_inv p
  rw [hp] at hnat
  exact hnat

/-- The affine analytic pullback equals the intrinsic scheme-point map. -/
theorem affineSchemePointPullback_eq_schemeComplexPointMap (h : A →ₐ[ℂ] B) :
    affineSchemePointPullback h = schemeComplexPointMap
      (complexAffineStructureMap B) (complexAffineStructureMap A)
      (Spec.map (CommRingCat.ofHom h.toRingHom)) (affineSchemeMap_overComplex h) := by
  funext p
  apply Subtype.ext
  exact affineSchemePointPullback_val h p

/-- Actual affine scheme morphisms act continuously on the analytic point spaces. -/
theorem affineSchemePointPullback_continuous (h : A →ₐ[ℂ] B) :
    Continuous (affineSchemePointPullback h) :=
  (affineSchemeComplexPointHomeomorph A).symm.continuous.comp
    ((complexPoint_pullback_continuous h).comp
      (affineSchemeComplexPointHomeomorph B).continuous)

end

end ComplexSchemes
