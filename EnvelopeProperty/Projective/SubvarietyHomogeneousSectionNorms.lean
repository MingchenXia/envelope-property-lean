import EnvelopeProperty.Berkovich.SchemeLinePullbackSections
import EnvelopeProperty.Berkovich.SchemeCenterBaseChange
import EnvelopeProperty.AlgGeom.NativeProjectiveVarietyAnalytic
import EnvelopeProperty.Projective.HomogeneousSectionFubiniStudy

/-! # Actual original closed-variety line sections retain the original homogeneous norm -/
open scoped Classical NNReal ENNReal Topology
open CategoryTheory AlgebraicGeometry MvPolynomial
open EnvelopeProperty.Berkovich
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ProjSubvariety
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)
private local instance originalAmbientStructureProper :
    IsProper (ProjBerk.nativeStructureMap (R := k) (n := n)) := ProjBerk.nativeStructureMap_isProper
private local instance originalClosedStructureProper : IsProper X.nativeStructure := by
  change IsProper (X.nativeInclusion ≫ ProjBerk.nativeStructureMap)
  infer_instance

private theorem originalEval_congr {Y : Scheme.{u}} (y z : SchemeValuedPoint Y)
    (h : y = z) (U : Y.Opens) (hy : y.point ∈ U) (hz : z.point ∈ U) (s : Γ(Y, U)) :
    y.eval U hy s = z.eval U hz s := by subst z; rfl

/-- The SAME original homogeneous coefficient pulled to the EXISTING original
closed scheme has exactly the SAME original full homogeneous seminorm value. -/
theorem nativeAnalyticHomeomorph_eval_homogeneousCoefficient (x : X.an)
    (i : Fin (n + 1)) (hi : x.1.1.val (MvPolynomial.X i) = 1) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) :
    SchemeValuedPoint.eval (X.nativeAnalyticHomeomorph x).1
      (X.nativeInclusion ⁻¹ᵁ ProjBerk.nativeCoordinateOpen i)
      ((X.nativeAnalyticHomeomorph_mem_coordinateOpen x i).mpr
        (by change x.1.1.val (MvPolynomial.X i) ≠ 0; rw [hi]; exact one_ne_zero))
      ((X.nativeInclusion.app (ProjBerk.nativeCoordinateOpen i)).hom
        (ProjectiveHomogeneousSections.coefficient i d F hF)) = x.1.1.val F := by
  have hx : x.1 ∈ ProjBerk.chartOpen i := by
    change x.1.1.val (MvPolynomial.X i) ≠ 0; rw [hi]; exact one_ne_zero
  have heq := congrArg Subtype.val (X.nativeAnalyticHomeomorph_inclusion x)
  have hv := originalEval_congr _ _ heq (ProjBerk.nativeCoordinateOpen i)
    ((X.nativeAnalyticHomeomorph_mem_coordinateOpen x i).mpr hx) hx
    (ProjectiveHomogeneousSections.coefficient i d F hF)
  exact (SchemeValuedPoint.eval_map X.nativeInclusion (X.nativeAnalyticHomeomorph x).1
    (ProjBerk.nativeCoordinateOpen i)
    ((X.nativeAnalyticHomeomorph_mem_coordinateOpen x i).mpr hx)
    (ProjectiveHomogeneousSections.coefficient i d F hF)).symm.trans
      (hv.trans (RelativeNormalizedProjectiveSpectrum.nativeHomeomorph_eval_homogeneousSection_coefficient
        (1 : Valuation k ℝ≥0) (ProjBerk.normalizedSpectrumHomeomorph x.1) i hi d F hF))

/-- The ACTUAL original closed-variety line norm of the actual pullback of the
SAME original whole homogeneous global section, on its SAME original residue fibre. -/
def homogeneousSectionNorm (j : Fin (n + 1)) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) (x : X.an) : ℝ≥0 :=
  RelativeSchemeValuedPoint.modelLineNorm Valuation.one_apply_le_one (X.nativeAnalyticHomeomorph x)
    ((coordinateHyperplanePoleSheafPower_isInvertible (R := k) j d).pullback X.nativeInclusion)
    (RelativeSchemeValuedPoint.fibreSection (X.nativeAnalyticHomeomorph x)
      (SchemeLineSectionEvaluation.pullbackSectionHom X.nativeInclusion
        (ProjectiveHomogeneousSections.sectionHom j d F hF)))

/-- The ACTUAL original closed-variety section model norm equals its SAME
original homogeneous polynomial seminorm; every local comparison is derived. -/
theorem homogeneousSectionNorm_eq_val (j : Fin (n + 1)) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) (x : X.an) :
    X.homogeneousSectionNorm j d F hF x = x.1.1.val F := by
  let hb : ∀ r : k, (1 : Valuation k ℝ≥0) r ≤ 1 := Valuation.one_apply_le_one
  let y := X.nativeAnalyticHomeomorph x
  obtain ⟨i, hi⟩ := ProjBerk.exists_val_X_eq_one x.1
  let M := coordinateHyperplanePoleSheafPower (R := k) j d
  let U : (ProjBerk.NativeProjectiveScheme k n).affineOpens :=
    ⟨coordinateOpen (R := k) i, coordinateOpen_isAffineOpen (R := k) i⟩
  let e := coordinateHyperplanePoleSheafPowerTrivialization (R := k) i j d
  have hm0 := RelativeSchemeValuedPoint.center_map_overBase
    (fY := ProjBerk.nativeStructureMap (R := k) (n := n))
    (RingHom.id k) (fun _ => rfl) X.nativeInclusion
    (by simp only [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]; rfl) hb hb y
  have hm1 : X.nativeInclusion (RelativeSchemeValuedPoint.center hb y) =
      RelativeSchemeValuedPoint.center hb
        (RelativeSchemeValuedPoint.map X.nativeInclusion rfl y) := by
    exact hm0.trans (congrArg (RelativeSchemeValuedPoint.center hb)
      (RelativeSchemeValuedPoint.mapOverBase_id
        (fY := ProjBerk.nativeStructureMap (R := k) (n := n)) X.nativeInclusion rfl y))
  have hm : X.nativeInclusion (RelativeSchemeValuedPoint.center hb y) =
      RelativeSchemeValuedPoint.center hb (ProjBerk.nativeHomeomorph x.1) :=
    hm1.trans (congrArg (RelativeSchemeValuedPoint.center hb)
      (X.nativeAnalyticHomeomorph_inclusion x))
  have hc : RelativeSchemeValuedPoint.center hb y ∈ X.nativeInclusion ⁻¹ᵁ U.1 := by
    change X.nativeInclusion (RelativeSchemeValuedPoint.center hb y) ∈ U.1
    rw [hm]
    exact RelativeNormalizedProjectiveSpectrum.center_nativeHomeomorph_mem_coordinateOpen
      (1 : Valuation k ℝ≥0) hb (ProjBerk.normalizedSpectrumHomeomorph x.1) i hi
  have hcoeff : ModularCurves.localTrivializationCoefficient M U e
      (ProjectiveHomogeneousSections.homogeneousSection j d F hF) =
      ProjectiveHomogeneousSections.coefficient i d F hF :=
    (ModularCurves.overTrivializationCoefficient_overTrivializationOfRestrictIso M U e _).symm.trans
      (ProjectiveHomogeneousSections.section_coefficient i j d F hF)
  have hr := SchemeLineSectionEvaluation.sectionHom_localScalar M U e
    (ProjectiveHomogeneousSections.homogeneousSection j d F hF)
  rw [hcoeff] at hr
  exact (RelativeSchemeValuedPoint.modelLineNorm_pullbackSection_eq_localEval hb y X.nativeInclusion
    (coordinateHyperplanePoleSheafPower_isInvertible (R := k) j d) U.1 hc
    (Scheme.Modules.pullbackIsoOfRestrictIso M U.1 e)
    (ProjectiveHomogeneousSections.sectionHom j d F hF)
    (ProjectiveHomogeneousSections.coefficient i d F hF) hr).trans
      (X.nativeAnalyticHomeomorph_eval_homogeneousCoefficient x i hi d F hF)

/-- The original closed-variety logAbs is the genuine original line-section model norm logarithm. -/
theorem homogeneousSectionNorm_log (j : Fin (n + 1)) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) (x : X.an) :
    ENNReal.log (X.homogeneousSectionNorm j d F hF x : ℝ≥0∞) = ProjBerk.logAbs F x.1 := by
  rw [homogeneousSectionNorm_eq_val]
  rfl
end EnvelopeProperty.ProjSubvariety
