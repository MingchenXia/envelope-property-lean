/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.SchemeFunctionFieldSubalgebras
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Actual original smooth affine section rings in the actual function field -/

noncomputable section
namespace AlgebraicGeometry.Scheme.Hom
open CategoryTheory TopologicalSpace
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k)) [Smooth f]

omit [IsIntegral X] in
/-- Actual original scheme smoothness gives smoothness of its whole original
affine section ring for the actual structure-morphism algebra structure. -/
theorem smooth_sectionsAlgebra {U : X.Opens} (hU : IsAffineOpen U) :
    letI := f.sectionsAlgebra U
    Algebra.Smooth k Γ(X, U) := by
  let _ := f.sectionsAlgebra U
  rw [← RingHom.smooth_algebraMap]
  exact (RingHom.Smooth.of_bijective
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.bijective).comp
      (f.smooth_appLE (isAffineOpen_top _) hU le_top)

/-- The literal actual generic-germ image of a nonempty affine open is a
smooth source, with smoothness derived from the original scheme. -/
theorem smooth_sectionsFunctionFieldSubalgebra (U : X.Opens) [Nonempty U]
    (hU : IsAffineOpen U) :
    letI := f.stalkAlgebra (genericPoint X)
    Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap k (f.sectionsFunctionFieldSubalgebra U)))) := by
  let _ := f.stalkAlgebra (genericPoint X)
  let _ := f.sectionsAlgebra U
  have : Algebra.Smooth k Γ(X, U) := f.smooth_sectionsAlgebra hU
  have : Algebra.Smooth k (f.sectionsFunctionFieldSubalgebra U) :=
    Algebra.Smooth.of_equiv (f.sectionsFunctionFieldEquiv U)
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)

end AlgebraicGeometry.Scheme.Hom
