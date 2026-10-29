import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveCoordinateLines

/-!
# Actual ORIGINAL O(1) whole sections and SAME saturated model sections

Actual restriction/pullback and the genuine scheme and coordinate-line isos
produce these maps. No section or coefficient matching is supplied.
Route: owned `closed-projective-global-sections-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Alterations Alterations.Geometry Alterations.Geometry.Segre
  Alterations.Geometry.ProjectiveIdeal MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGlobalSections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual whole pullback sections along a genuine scheme isomorphism are the original whole sections. -/
def isoPullbackTopSections {Z Y : Scheme.{u}} (e : Z ≅ Y) (L : Y.Modules) :
    Γ((Scheme.Modules.pullback e.hom).obj L, ⊤) ≅ Γ(L, ⊤) := by
  have ht : e.hom ''ᵁ (⊤ : Z.Opens) = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  exact asIso (((Scheme.Modules.restrictFunctorIsoPullback e.hom).inv.app L).app ⊤) ≪≫
    L.restrictAppIso e.hom ⊤ ≪≫ L.presheaf.mapIso (eqToIso ht.symm).op

end EnvelopeProperty.ClosedProjectiveGlobalSections
namespace EnvelopeProperty.ClosedProjectiveGenericCoefficients
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {n : ℕ}
variable (i : X ⟶ projectiveSpace k n) [IsClosedImmersion i] (j : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)]

/-- The actual native coordinate H0 is the actual ORIGINAL pulled projective O(1) H0. -/
def fixedOriginalNativeCoordinateH0Iso :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let M := originalRankOneCoordinateModel i j
    Γ(M.nativeRankOneCoordinateLine j, ⊤) ≅
      Γ((Scheme.Modules.pullback i).obj (coordinateHyperplanePoleSheaf (R := k) j), ⊤) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  exact (ClosedProjectiveGlobalSections.isoPullbackTopSections
      (fixedOriginalNativeIso i j) (M.nativeRankOneCoordinateLine j)).symm ≪≫
    asIso ((fixedOriginalNativeCoordinateLinePullbackIso i j).hom.app ⊤)

/-- The ORIGINAL O(1) whole H0 is additively equivalent to the SAME genuine all-chart saturated sections. -/
def originalCoordinateH0SaturatedSectionsAddEquiv :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let M := originalRankOneCoordinateModel i j
    Γ((Scheme.Modules.pullback i).obj (coordinateHyperplanePoleSheaf (R := k) j), ⊤) ≃+
      M.sections (1 : Fin 1 → ℤ) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  letI := M.nativeRankOneH0BaseModule j
  exact (fixedOriginalNativeCoordinateH0Iso i j).symm.addCommGroupIsoToAddEquiv.trans
    (M.nativeRankOneH0OriginalSectionsLinearEquiv (fun _ => j)
      (fun c => fixedOriginalCoordinateModel_pivot_ne_zero i j j c) j
      (fixedOriginalCoordinateModel_pivot_ne_zero i j j 0)).toAddEquiv

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGlobalSections.isoPullbackTopSections
#print axioms EnvelopeProperty.ClosedProjectiveGlobalSections.isoPullbackTopSections
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateH0Iso
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateH0Iso
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalCoordinateH0SaturatedSectionsAddEquiv
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalCoordinateH0SaturatedSectionsAddEquiv
