import EnvelopeProperty.AlgGeom.FiniteOriginalProjectivePowerFrames
import EnvelopeProperty.AlgGeom.Canonical.NativeLineSectionRatios

/-! # Actual original whole finite tensor-form chart coefficients -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.OriginalProjectiveTensorPivotCoefficients
open SchemeLineSectionEvaluation FiniteOriginalProjectivePowerFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem unitHomExt {Y : Scheme.{u}} {L : Y.Modules} (α β : unitObj Y ⟶ L)
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
  apply unitHomExt
  exact topSectionHom_app_top_apply_one L _

private theorem unitScalar_sectionAtOne {Y : Scheme.{u}} (a : Γ(Y,⊤)) :
    sectionAtOne (ModularCurves.unitEndomorphismOfTopSection a) = a := by
  rw [sectionAtOne,ModularCurves.unitEndomorphismOfTopSection_app_apply]
  simp only [homOfLE_refl,op_id,one_mul]
  erw [CategoryTheory.Functor.map_id]
  rfl

/-- A genuine whole original scalar identity computes its SAME actual native coefficient. -/
theorem frame_coefficient_of_scalar {Y : Scheme.{u}} (L : Y.Modules) (U : Y.affineOpens)
    (E : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme)
    (α : unitObj Y ⟶ L) (c : Γ(Y,U.1))
    (hc : pullbackSectionHom U.1.ι α ≫ E.hom =
      ModularCurves.unitEndomorphismOfTopSection (ModularCurves.affineOpenTopSection U c)) :
    ModularCurves.localTrivializationCoefficient L U (restrictIsoOfPullbackIso L U.1 E)
      (sectionAtOne α) = c := by
  let e := restrictIsoOfPullbackIso L U.1 E
  have he : pullbackIsoOfRestrictIso L U.1 e = E := by
    apply Iso.ext
    simp [e,restrictIsoOfPullbackIso,pullbackIsoOfRestrictIso]
  have hl := SchemeLineSectionEvaluation.sectionHom_localScalar L U e (sectionAtOne α)
  rw [sectionHom_sectionAtOne,he] at hl
  have hh := congrArg sectionAtOne (hl.symm.trans hc)
  rw [unitScalar_sectionAtOne,unitScalar_sectionAtOne,
    ModularCurves.affineOpenTopSection_eq_topIso_inv,
    ModularCurves.affineOpenTopSection_eq_topIso_inv] at hh
  exact (ConcreteCategory.bijective_of_isIso U.1.topIso.inv).1 hh

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {X : Scheme.{u}} {r : ℕ}
    (d : Fin (r+1) → ℕ)
    (q : ∀ j,X ⟶ Proj (homogeneousSubmodule (Fin (d j+1)) k))
    (t : ∀ j,Fin (d j+1)) (n : Fin (r+1) → ℕ)
    (a : ∀ j,Fin (d j+1)) (U : X.affineOpens)
    (hU : ∀ j,U.1 ≤ q j ⁻¹ᵁ coordinateOpen (R := k) (a j))

/-- The SAME actual finite pulled projective tensor frame, on the original restricted module. -/
def chartFrame : (projectiveLine d q t n).restrict U.1.ι ≅ unitObj U.1.toScheme :=
  restrictIsoOfPullbackIso (projectiveLine d q t n) U.1
    (FiniteOriginalProjectivePowerFrames.projectiveFrame d q t n a U.1 hU)

/-- The actual coefficient of EVERY original whole tensor-line section on the original joint chart. -/
def coefficient (s : Γ(projectiveLine d q t n,⊤)) : Γ(X,U.1) :=
  ModularCurves.localTrivializationCoefficient (projectiveLine d q t n) U (chartFrame d q t n a U hU) s

/-- The SAME actual whole original finite tensor-form section. -/
def formSection (F : ∀ j,MvPolynomial (Fin (d j+1)) k) (hF : ∀ j,(F j).IsHomogeneous (n j)) :
    Γ(projectiveLine d q t n,⊤) :=
  sectionAtOne (projectiveHomogeneousSection d q t n F hF)

/-- EVERY true original tensor-form coefficient is the product of its original affine pullbacks. -/
theorem coefficient_formSection (F : ∀ j,MvPolynomial (Fin (d j+1)) k)
    (hF : ∀ j,(F j).IsHomogeneous (n j)) :
    coefficient d q t n a U hU (formSection d q t n F hF) =
      ∏ j,ModularCurves.affinePullbackSection (q j) U
        ⟨coordinateOpen (R := k) (a j),coordinateOpen_isAffineOpen (a j)⟩ (hU j)
        (ProjectiveHomogeneousSections.coefficient (a j) (n j) (F j) (hF j)) := by
  apply frame_coefficient_of_scalar
  have h := FiniteOriginalProjectivePowerFrames.projectiveFrame_forms_scalar d q t n a U.1 hU F hF
  have hp : ModularCurves.affineOpenTopSection U
      (∏ j,ModularCurves.affinePullbackSection (q j) U
        ⟨coordinateOpen (R := k) (a j),coordinateOpen_isAffineOpen (a j)⟩ (hU j)
          (ProjectiveHomogeneousSections.coefficient (a j) (n j) (F j) (hF j))) =
      ∏ j,((q j).resLE (coordinateOpen (R := k) (a j)) U.1 (hU j)).appTop.hom
        (ModularCurves.affineOpenTopSection
          ⟨coordinateOpen (R := k) (a j),coordinateOpen_isAffineOpen (a j)⟩
          (ProjectiveHomogeneousSections.coefficient (a j) (n j) (F j) (hF j))) := by
    rw [ModularCurves.affineOpenTopSection_eq_topIso_inv,map_prod]
    apply Finset.prod_congr rfl
    intro j _
    simpa only [ModularCurves.affineOpenTopSection_eq_topIso_inv] using
      (ModularCurves.affineOpenTopSection_affinePullbackSection (q j) U
        ⟨coordinateOpen (R := k) (a j),coordinateOpen_isAffineOpen (a j)⟩ (hU j)
        (ProjectiveHomogeneousSections.coefficient (a j) (n j) (F j) (hF j)))
  exact h.trans (congrArg ModularCurves.unitEndomorphismOfTopSection hp.symm)

private theorem nonempty_of_le {Y : Scheme.{u}} {V W : Y.Opens} [Nonempty V]
    (h : V ≤ W) : Nonempty W := by
  obtain ⟨x⟩ := (inferInstance : Nonempty V)
  exact ⟨⟨x.1,h x.2⟩⟩

private theorem germ_affinePullbackSection {Y Z : Scheme.{u}} [IsIntegral Y]
    (f : Y ⟶ Z) (V : Y.affineOpens) (W : Z.affineOpens)
    [Nonempty V.1] [Nonempty (f ⁻¹ᵁ W.1)] (h : V.1 ≤ f ⁻¹ᵁ W.1) (b : Γ(Z,W.1)) :
    Y.germToFunctionField V.1 (ModularCurves.affinePullbackSection f V W h b) =
      Y.germToFunctionField (f ⁻¹ᵁ W.1) (f.app W.1 b) := by
  rw [ModularCurves.affinePullbackSection_eq_appLE]
  change Y.germToFunctionField V.1 (Y.presheaf.map (homOfLE h).op (f.app W.1 b)) = _
  exact CanonicalGeometry.germToFunctionField_restrict (homOfLE h) (f.app W.1 b)

/-- On the SAME original integral scheme EVERY original tensor-form coefficient has its exact original native generic value. -/
theorem germ_coefficient_formSection [IsIntegral X] [Nonempty U.1]
    (F : ∀ j,MvPolynomial (Fin (d j+1)) k) (hF : ∀ j,(F j).IsHomogeneous (n j)) :
    X.germToFunctionField U.1 (coefficient d q t n a U hU (formSection d q t n F hF)) =
      ∏ j,letI := nonempty_of_le (hU j)
        letI := (q j ≫ DeJongAlterations.projectiveSpaceStructure k (d j)).stalkAlgebra (genericPoint X)
        MvPolynomial.aeval (ProjectiveChartFunctionFieldGeneration.coordinate (q j) (a j)) (F j) := by
  rw [coefficient_formSection,map_prod]
  apply Finset.prod_congr rfl
  intro j _
  let := nonempty_of_le (hU j)
  let := (q j ≫ DeJongAlterations.projectiveSpaceStructure k (d j)).stalkAlgebra (genericPoint X)
  exact (germ_affinePullbackSection (q j) U
    ⟨coordinateOpen (R := k) (a j),coordinateOpen_isAffineOpen (a j)⟩ (hU j) _).trans
      (ProjectiveNativeHomogeneousModelSections.germ_homogeneousCoefficient_eq_aeval
        (q j) (a j) (n j) (F j) (hF j))

/-- The actual original whole pivot tensor section, without any supplied section or nonvanishing witness. -/
def pivotSection (i : ∀ j,Fin (d j+1)) : Γ(projectiveLine d q t n,⊤) :=
  formSection d q t n (fun j => MvPolynomial.X (i j) ^ n j)
    (fun j => by simpa using (MvPolynomial.isHomogeneous_X k (i j)).pow (n j))

/-- EVERY original joint-frame coefficient of the SAME whole pivot tensor section retains the product of SAME actual original ratios. -/
theorem germ_coefficient_pivotSection [IsIntegral X] [Nonempty U.1]
    (i : ∀ j,Fin (d j+1)) :
    X.germToFunctionField U.1 (coefficient d q t n a U hU (pivotSection d q t n i)) =
      ∏ j,letI := nonempty_of_le (hU j)
        ProjectiveChartFunctionFieldGeneration.coordinate (q j) (a j) (i j) ^ n j := by
  have h := germ_coefficient_formSection d q t n a U hU
    (fun j => MvPolynomial.X (i j) ^ n j)
    (fun j => by simpa using (MvPolynomial.isHomogeneous_X k (i j)).pow (n j))
  simpa only [pivotSection,map_pow,MvPolynomial.aeval_X] using h

/-- Nonempty original pivot charts internally DERIVE nonvanishing of the SAME actual whole pivot tensor section. -/
theorem pivotSection_ne_zero [IsIntegral X] (i : ∀ j,Fin (d j+1))
    (hi : ∀ j,Nonempty (q j ⁻¹ᵁ coordinateOpen (R := k) (i j))) :
    pivotSection d q t n i ≠ 0 := by
  let V : X.Opens := ⨅ j,q j ⁻¹ᵁ coordinateOpen (R := k) (i j)
  have hx : genericPoint X ∈ V := by
    change genericPoint X ∈ ((⨅ j,q j ⁻¹ᵁ coordinateOpen (R := k) (i j) : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    apply Set.mem_iInter.mpr
    intro j
    let := hi j
    exact CanonicalGeometry.genericPoint_mem_nonempty_open _
  obtain ⟨W,hW,hxW,hWV⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := V) (x := genericPoint X) hx
  let U : X.affineOpens := ⟨W,hW⟩
  let : Nonempty U.1 := ⟨⟨genericPoint X,hxW⟩⟩
  have hU : ∀ j,U.1 ≤ q j ⁻¹ᵁ coordinateOpen (R := k) (i j) :=
    fun j x hx => (iInf_le (fun j => q j ⁻¹ᵁ coordinateOpen (R := k) (i j)) j) (hWV hx)
  have hg := germ_coefficient_pivotSection d q t n i U hU i
  have hone : (∏ j,letI := nonempty_of_le (hU j)
      ProjectiveChartFunctionFieldGeneration.coordinate (q j) (i j) (i j) ^ n j) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    exact (congrArg (fun z => z ^ n j)
      (ProjectiveChartFunctionFieldGeneration.coordinate_self (q j) (i j))).trans (one_pow _)
  rw [hone] at hg
  intro hz
  rw [hz] at hg
  have hzero : coefficient d q t n i U hU 0 = 0 := by
    simp [coefficient,ModularCurves.localTrivializationCoefficient,
      ModularCurves.localTrivializationTopSection,ModularCurves.localTrivializationRestriction]
  rw [hzero,map_zero] at hg
  exact zero_ne_one hg

end EnvelopeProperty.OriginalProjectiveTensorPivotCoefficients
