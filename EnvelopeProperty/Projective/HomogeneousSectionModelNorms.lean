import EnvelopeProperty.Berkovich.SchemeLineLocalSectionEvaluation
import EnvelopeProperty.Projective.NativeHomogeneousSectionValues
import EnvelopeProperty.Projective.NativeBridge

/-! # Actual original O(d) model norms are the original homogeneous functions -/
open scoped Classical NNReal ENNReal Topology
open CategoryTheory AlgebraicGeometry MvPolynomial
open EnvelopeProperty.Berkovich
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] (v : Valuation R ℝ≥0) {n : ℕ}
private local instance nativeHomogeneousSectionProper :
    IsProper (ProjBerk.nativeStructureMap (R := R) (n := n)) :=
  ProjBerk.nativeStructureMap_isProper

/-- The ACTUAL original model norm of the ORIGINAL homogeneous global O(d)
section is its SAME original full homogeneous seminorm value. -/
theorem homogeneousSection_modelLineNorm (hb : ∀ r, v r ≤ 1)
    (x : RelativeNormalizedProjectiveSpectrum v n) (j : Fin (n + 1)) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d) :
    RelativeSchemeValuedPoint.modelLineNorm hb (nativeHomeomorph v x)
      (coordinateHyperplanePoleSheafPower_isInvertible (R := R) j d)
      (RelativeSchemeValuedPoint.fibreSection (nativeHomeomorph v x)
        (ProjectiveHomogeneousSections.sectionHom j d F hF)) = x.1.1.val F := by
  obtain ⟨i, hi⟩ := NormalizedProjectiveSpectrum.exists_val_X_eq_one x.1
  let M := coordinateHyperplanePoleSheafPower (R := R) j d
  let U : (ProjBerk.NativeProjectiveScheme R n).affineOpens :=
    ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen (R := R) i⟩
  let e := coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j d
  have hc : RelativeSchemeValuedPoint.center hb (nativeHomeomorph v x) ∈ U.1 :=
    center_nativeHomeomorph_mem_coordinateOpen v hb x i hi
  have hcoeff : ModularCurves.localTrivializationCoefficient M U e
      (ProjectiveHomogeneousSections.homogeneousSection j d F hF) =
      ProjectiveHomogeneousSections.coefficient i d F hF :=
    (ModularCurves.overTrivializationCoefficient_overTrivializationOfRestrictIso M U e _).symm.trans
      (ProjectiveHomogeneousSections.section_coefficient i j d F hF)
  have hr := SchemeLineSectionEvaluation.sectionHom_localScalar M U e
    (ProjectiveHomogeneousSections.homogeneousSection j d F hF)
  rw [hcoeff] at hr
  exact (RelativeSchemeValuedPoint.modelLineNorm_fibreSection_eq_localEval hb
    (nativeHomeomorph v x) (coordinateHyperplanePoleSheafPower_isInvertible (R := R) j d)
    U.1 hc (Scheme.Modules.pullbackIsoOfRestrictIso M U.1 e)
    (ProjectiveHomogeneousSections.sectionHom j d F hF)
    (ProjectiveHomogeneousSections.coefficient i d F hF) hr).trans
      (nativeHomeomorph_eval_homogeneousSection_coefficient v x i hi d F hF)
end EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
