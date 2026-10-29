import EnvelopeProperty.AlgGeom.ProjectiveNativeHomogeneousModelSections
import EnvelopeProperty.AlgGeom.Canonical.NativeLineSectionRatios

/-! # Actual original whole pulled projective lines and EVERY native chart coefficient -/
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Opposite
open Alterations
open Scheme.Modules
open scoped Classical NNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.NativePulledProjectiveLineFrames
open Berkovich SchemeLineSectionEvaluation CanonicalGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}}

private theorem unitHomExtTop {Y : Scheme.{u}} {L : Y.Modules} (α β : unitObj Y ⟶ L)
    (h : sectionAtOne α = sectionAtOne β) : α = β := by
  apply SheafOfModules.hom_ext
  ext V
  let a := (homOfLE (le_top : V.unop ≤ (⊤ : Y.Opens))).op
  have ha := PresheafOfModules.naturality_apply α.val a (1 : Γ(Y,⊤))
  have hb := PresheafOfModules.naturality_apply β.val a (1 : Γ(Y,⊤))
  change α.val.app V (Y.presheaf.map a (1 : Γ(Y,⊤))) =
    L.presheaf.map a (sectionAtOne α) at ha
  change β.val.app V (Y.presheaf.map a (1 : Γ(Y,⊤))) =
    L.presheaf.map a (sectionAtOne β) at hb
  rw [map_one] at ha hb
  exact ha.trans ((congrArg (L.presheaf.map a) h).trans hb.symm)

private theorem sectionHom_sectionAtOne {Y : Scheme.{u}} {L : Y.Modules} (α : unitObj Y ⟶ L) :
    SchemeModuleGlobalSections.sectionHom L (sectionAtOne α) = α := by
  apply unitHomExtTop
  change sectionAtOne (topSectionHom L (sectionAtOne α)) = _
  exact topSectionHom_app_top_apply_one L (sectionAtOne α)

private theorem unitScalar_sectionAtOne {Y : Scheme.{u}} (a : Γ(Y,⊤)) :
    sectionAtOne (ModularCurves.unitEndomorphismOfTopSection a) = a := by
  rw [sectionAtOne,ModularCurves.unitEndomorphismOfTopSection_app_apply]
  simp only [homOfLE_refl,op_id,one_mul]
  erw [CategoryTheory.Functor.map_id]
  rfl

private theorem openTopSection_eq_topIso {Y : Scheme.{u}} (U : Y.Opens) (c : Γ(Y,U)) :
    openTopSection U c = U.topIso.inv c := by
  rw [openTopSection,Scheme.Opens.ι_appIso]
  rfl

variable (f : X ⟶ projectiveSpace k m) (t : Fin (m + 1)) (d : ℕ) [IsClosedImmersion f]

/-- The SAME actual whole original pulled O(d) line module. -/
def line : X.Modules :=
  (Scheme.Modules.pullback f).obj (coordinateHyperplanePoleSheafPower (R := k) t d)

omit [IsClosedImmersion f] in
/-- Genuine invertibility of the SAME whole actual original pulled line. -/
theorem line_isInvertible : IsInvertible (line f t d) :=
  (coordinateHyperplanePoleSheafPower_isInvertible (R := k) t d).pullback f

/-- The actual native restriction frame, pulled from the original whole projective frame. -/
def chartFrame (j : Fin (m + 1)) :
    (line f t d).restrict (f ⁻¹ᵁ coordinateOpen (R := k) j).ι ≅
      unitObj (f ⁻¹ᵁ coordinateOpen (R := k) j).toScheme :=
  restrictIsoOfPullbackIso (line f t d) (f ⁻¹ᵁ coordinateOpen (R := k) j)
    (localPullbackFrame f (coordinateOpen (R := k) j)
      (pullbackIsoOfRestrictIso (coordinateHyperplanePoleSheafPower (R := k) t d)
        (coordinateOpen (R := k) j) (coordinateHyperplanePoleSheafPowerTrivialization (R := k) j t d)))

/-- The TRUE whole original chart coefficient of EVERY actual original global section. -/
def chartCoefficient (j : Fin (m + 1)) (s : Γ(line f t d,⊤)) :
    Γ(X,f ⁻¹ᵁ coordinateOpen (R := k) j) :=
  ModularCurves.localTrivializationCoefficient (line f t d)
    ⟨f ⁻¹ᵁ coordinateOpen (R := k) j,(coordinateOpen_isAffineOpen j).preimage f⟩
    (chartFrame f t d j) s

/-- The actual original homogeneous whole section pulled to the SAME original line. -/
def formSection (F : MvPolynomial (Fin (m + 1)) k) (hF : F.IsHomogeneous d) : Γ(line f t d,⊤) :=
  sectionAtOne (pullbackSectionHom f (ProjectiveHomogeneousSections.sectionHom t d F hF))

omit [IsClosedImmersion f] in
private theorem pullback_chartFrame (j : Fin (m + 1)) :
    pullbackIsoOfRestrictIso (line f t d) (f ⁻¹ᵁ coordinateOpen (R := k) j) (chartFrame f t d j) =
      localPullbackFrame f (coordinateOpen (R := k) j)
        (pullbackIsoOfRestrictIso (coordinateHyperplanePoleSheafPower (R := k) t d)
          (coordinateOpen (R := k) j) (coordinateHyperplanePoleSheafPowerTrivialization (R := k) j t d)) := by
  apply Iso.ext
  simp [chartFrame,restrictIsoOfPullbackIso,pullbackIsoOfRestrictIso]

omit [IsClosedImmersion f] in
private theorem coefficient_eq_of_scalar {Y : Scheme.{u}} {L : Y.Modules}
    (U : Y.affineOpens) (e : L.restrict U.1.ι ≅ unitObj U.1.toScheme)
    (α : unitObj Y ⟶ L) (c : Γ(Y,U.1))
    (h : pullbackSectionHom U.1.ι α ≫ (pullbackIsoOfRestrictIso L U.1 e).hom =
      ModularCurves.unitEndomorphismOfTopSection (openTopSection U.1 c)) :
    ModularCurves.localTrivializationCoefficient L U e (sectionAtOne α) = c := by
  have hl := SchemeLineSectionEvaluation.sectionHom_localScalar L U e (sectionAtOne α)
  rw [sectionHom_sectionAtOne] at hl
  have he := congrArg sectionAtOne (hl.symm.trans h)
  rw [unitScalar_sectionAtOne,unitScalar_sectionAtOne,
    ModularCurves.affineOpenTopSection_eq_topIso_inv,openTopSection_eq_topIso] at he
  exact (ConcreteCategory.bijective_of_isIso U.1.topIso.inv).1 he

omit [IsClosedImmersion f] in
private theorem pullbackFrameCoefficient {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsAffineHom g]
    (M : Z.Modules) (U : Z.affineOpens) (e : M.restrict U.1.ι ≅ unitObj U.1.toScheme)
    (s : Γ(M,⊤)) :
    ModularCurves.localTrivializationCoefficient ((Scheme.Modules.pullback g).obj M)
      ⟨g ⁻¹ᵁ U.1,U.2.preimage g⟩
      (restrictIsoOfPullbackIso ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U.1)
        (localPullbackFrame g U.1 (pullbackIsoOfRestrictIso M U.1 e)))
      (sectionAtOne (pullbackSectionHom g (SchemeModuleGlobalSections.sectionHom M s))) =
      g.app U.1 (ModularCurves.localTrivializationCoefficient M U e s) := by
  let V : Y.affineOpens := ⟨g ⁻¹ᵁ U.1,U.2.preimage g⟩
  let E := restrictIsoOfPullbackIso ((Scheme.Modules.pullback g).obj M) V.1
    (localPullbackFrame g U.1 (pullbackIsoOfRestrictIso M U.1 e))
  apply coefficient_eq_of_scalar V E
  have he : pullbackIsoOfRestrictIso ((Scheme.Modules.pullback g).obj M) V.1 E =
      localPullbackFrame g U.1 (pullbackIsoOfRestrictIso M U.1 e) := by
    apply Iso.ext
    simp [E,restrictIsoOfPullbackIso,pullbackIsoOfRestrictIso]
  rw [he]
  exact localPullbackFrame_sectionHom_scalar g U.1 (pullbackIsoOfRestrictIso M U.1 e)
    (SchemeModuleGlobalSections.sectionHom M s) (ModularCurves.localTrivializationCoefficient M U e s)
    (SchemeLineSectionEvaluation.sectionHom_localScalar M U e s)

omit [IsClosedImmersion f] in
private theorem originalFormCoefficient (j : Fin (m + 1))
    (F : MvPolynomial (Fin (m + 1)) k) (hF : F.IsHomogeneous d) :
    ModularCurves.localTrivializationCoefficient
      (coordinateHyperplanePoleSheafPower (R := k) t d)
      ⟨coordinateOpen (R := k) j,coordinateOpen_isAffineOpen j⟩
      (coordinateHyperplanePoleSheafPowerTrivialization (R := k) j t d)
      (ProjectiveHomogeneousSections.homogeneousSection t d F hF) =
      ProjectiveHomogeneousSections.coefficient j d F hF :=
  (ModularCurves.overTrivializationCoefficient_overTrivializationOfRestrictIso
    (coordinateHyperplanePoleSheafPower (R := k) t d)
    ⟨coordinateOpen (R := k) j,coordinateOpen_isAffineOpen j⟩
    (coordinateHyperplanePoleSheafPowerTrivialization (R := k) j t d) _).symm.trans
    (ProjectiveHomogeneousSections.section_coefficient j t d F hF)

/-- EVERY entire original homogeneous-section coefficient is retained by the actual
whole original pulled-line global section, with no scalar/frame comparison premise. -/
theorem chartCoefficient_formSection (j : Fin (m + 1))
    (F : MvPolynomial (Fin (m + 1)) k) (hF : F.IsHomogeneous d) :
    chartCoefficient f t d j (formSection f t d F hF) =
      f.app (coordinateOpen (R := k) j) (ProjectiveHomogeneousSections.coefficient j d F hF) := by
  change X ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) k) at f
  let M := coordinateHyperplanePoleSheafPower (R := k) t d
  let U : (Proj (homogeneousSubmodule (Fin (m + 1)) k)).affineOpens :=
    ⟨coordinateOpen (R := k) j,coordinateOpen_isAffineOpen j⟩
  let e := coordinateHyperplanePoleSheafPowerTrivialization (R := k) j t d
  exact (pullbackFrameCoefficient f M U e (ProjectiveHomogeneousSections.homogeneousSection t d F hF)).trans
    (congrArg (f.app U.1) (originalFormCoefficient t d j F hF))

variable [IsIntegral X]

/-- The generic germ of the actual coefficient is its original polynomial evaluated
at the SAME true original native projective coordinate ratios. -/
theorem germ_chartCoefficient_formSection (j : Fin (m + 1))
    [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j)]
    (F : MvPolynomial (Fin (m + 1)) k) (hF : F.IsHomogeneous d) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    X.germToFunctionField (f ⁻¹ᵁ coordinateOpen (R := k) j)
      (chartCoefficient f t d j (formSection f t d F hF)) =
      MvPolynomial.aeval (ProjectiveChartFunctionFieldGeneration.coordinate f j) F := by
  rw [chartCoefficient_formSection]
  exact ProjectiveNativeHomogeneousModelSections.germ_homogeneousCoefficient_eq_aeval f j d F hF

/-- The SAME actual original whole global section of the original pivot power. -/
def coordinatePowerSection (j : Fin (m + 1)) : Γ(line f t d,⊤) :=
  formSection f t d (MvPolynomial.X j ^ d) (by simpa using (MvPolynomial.isHomogeneous_X k j).pow d)

/-- Every actual original pivot-power section retains its exact native generic
coefficient in EVERY original nonempty chart, without a scalar matching premise. -/
theorem germ_chartCoefficient_coordinatePowerSection (j l : Fin (m + 1))
    [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j)] :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    X.germToFunctionField (f ⁻¹ᵁ coordinateOpen (R := k) j)
      (chartCoefficient f t d j (coordinatePowerSection f t d l)) =
      (ProjectiveChartFunctionFieldGeneration.coordinate f j l) ^ d := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  have h := germ_chartCoefficient_formSection f t d j (MvPolynomial.X l ^ d)
    (by simpa using (MvPolynomial.isHomogeneous_X k l).pow d)
  change X.germToFunctionField (f ⁻¹ᵁ coordinateOpen (R := k) j)
    (chartCoefficient f t d j (coordinatePowerSection f t d l)) =
      MvPolynomial.aeval (ProjectiveChartFunctionFieldGeneration.coordinate f j) (MvPolynomial.X l ^ d) at h
  simpa only [map_pow,MvPolynomial.aeval_X] using h

/-- Every original nonempty chart internally supplies its actual nonzero global
pivot-power section of the SAME original pulled line, including degree zero. -/
theorem coordinatePowerSection_ne_zero (j : Fin (m + 1))
    [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j)] : coordinatePowerSection f t d j ≠ 0 := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  have h := germ_chartCoefficient_coordinatePowerSection f t d j j
  change X.germToFunctionField (f ⁻¹ᵁ coordinateOpen (R := k) j)
    (chartCoefficient f t d j (coordinatePowerSection f t d j)) =
      (ProjectiveChartFunctionFieldGeneration.coordinate f j j) ^ d at h
  rw [ProjectiveChartFunctionFieldGeneration.coordinate_self,one_pow] at h
  intro hz
  rw [hz] at h
  have hc : chartCoefficient f t d j 0 = 0 := by
    simp [chartCoefficient,ModularCurves.localTrivializationCoefficient,
      ModularCurves.localTrivializationTopSection,ModularCurves.localTrivializationRestriction]
  rw [hc,map_zero] at h
  exact zero_ne_one h

end EnvelopeProperty.NativePulledProjectiveLineFrames
