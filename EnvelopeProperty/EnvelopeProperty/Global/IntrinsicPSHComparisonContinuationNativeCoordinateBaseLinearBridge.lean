import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationIsoLineBaseLinearSections

/-! True native structural actions before expanding a concrete original model.
Route: owned `native-coordinate-base-linear-bridge-route.tex`. -/
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGlobalSections
open Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (M : MultiModel k K 1) (j : Fin (M.M 0 + 1)) {X : Scheme.{u}}
  (e : X ≅ M.nativeRankOneScheme) (p : X ⟶ Spec (CommRingCat.of k))
  (h : e.hom ≫ M.nativeRankOneStructure = p) (P : X.Modules)
  (a : (pullback e.hom).obj (M.nativeRankOneCoordinateLine j) ≅ P)

/-- True independently native structural H0 action agrees with the genuine whole base-linear comparison. -/
def nativeCoordinateOverBaseH0LinearEquiv :
    letI := M.nativeRankOneH0BaseModule j
    letI := structureH0BaseModule p P
    Γ(M.nativeRankOneCoordinateLine j, ⊤) ≃ₗ[k] Γ(P, ⊤) :=
  isoLineBaseSectionsLinearEquiv e p M.nativeRankOneStructure h
    (M.nativeRankOneCoordinateLine j) P a

/-- The whole native linear comparison retains the SAME literal original additive forward map. -/
theorem nativeCoordinateOverBaseH0LinearEquiv_apply (s : Γ(M.nativeRankOneCoordinateLine j, ⊤)) :
    nativeCoordinateOverBaseH0LinearEquiv M j e p h P a s =
      ((isoPullbackTopSections e (M.nativeRankOneCoordinateLine j)).symm ≪≫
        asIso (a.hom.app ⊤)).hom s := rfl

/-- Its whole inverse is the SAME literal original additive inverse map. -/
theorem nativeCoordinateOverBaseH0LinearEquiv_symm_apply (s : Γ(P, ⊤)) :
    (nativeCoordinateOverBaseH0LinearEquiv M j e p h P a).symm s =
      ((isoPullbackTopSections e (M.nativeRankOneCoordinateLine j)).symm ≪≫
        asIso (a.hom.app ⊤)).inv s := rfl

end EnvelopeProperty.ClosedProjectiveGlobalSections

#check @EnvelopeProperty.ClosedProjectiveGlobalSections.nativeCoordinateOverBaseH0LinearEquiv
#print axioms EnvelopeProperty.ClosedProjectiveGlobalSections.nativeCoordinateOverBaseH0LinearEquiv
#check @EnvelopeProperty.ClosedProjectiveGlobalSections.nativeCoordinateOverBaseH0LinearEquiv_apply
#print axioms EnvelopeProperty.ClosedProjectiveGlobalSections.nativeCoordinateOverBaseH0LinearEquiv_apply
#check @EnvelopeProperty.ClosedProjectiveGlobalSections.nativeCoordinateOverBaseH0LinearEquiv_symm_apply
#print axioms EnvelopeProperty.ClosedProjectiveGlobalSections.nativeCoordinateOverBaseH0LinearEquiv_symm_apply
