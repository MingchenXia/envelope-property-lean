import EnvelopeProperty.Char0.EnvelopeGradedBaseIdealsCore
import EnvelopeProperty.AlgGeom.InvertibleBaseIdealFrameCoefficients
import EnvelopeProperty.AlgGeom.BaseIdealPullbackGeneratingSections
import EnvelopeProperty.Projective.NativeHomogeneousSectionValues

/-! # Homogeneous section images generate the base-ideal sheaf

Homogeneous sections generate the base-ideal sheaf through their frame coefficients
and evaluation maps.
-/

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierOriginalGenerationCore
open ProjBerk Scheme.Modules ModularCurves InvertibleSheafBaseIdeal
open InvertibleBaseIdealFrameCoefficients InvertibleSectionFamilyImage
attribute [local instance] MvPolynomial.gradedAlgebra Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {n : ℕ}

private theorem frameCoefficient_eq_overTrivializationCoefficient
    {X : Scheme.{u}} (L : X.Modules) (U : X.affineOpens)
    (e : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (s : Γ(L, ⊤)) :
    frameCoefficient L U e s = overTrivializationCoefficient L U.1 e s := by
  have hs : (SchemeModuleGlobalSections.sectionHom L s).val.app (.op U.1)
      (1 : Γ(X, U.1)) = L.presheaf.map
        (homOfLE (le_top : U.1 ≤ ⊤)).op s := by
    change (1 : Γ(X, U.1)) •
      (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s) = _
    exact one_smul _ _
  exact congrArg (e.hom.val.app (.op (Over.mk (𝟙 U.1)))) hs

private theorem sectionIdeal_ideal_of_overCoefficient {X : Scheme.{u}}
    (L : X.Modules) (hL : IsInvertible L) (U : X.affineOpens)
    (e : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (s : Γ(L, ⊤)) (c : Γ(X, U.1))
    (h : overTrivializationCoefficient L U.1 e s = c) :
    (sectionIdeal hL s).ideal U = Ideal.span ({c} : Set Γ(X, U.1)) := by
  rw [sectionIdeal_ideal_of_frame hL U e,
    frameCoefficient_eq_overTrivializationCoefficient L U e s, h]

/-- The original homogeneous section has its true principal coefficient ideal
on EVERY whole native coordinate chart. -/
theorem homogeneousSection_sectionIdeal (i j : Fin (n + 1)) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d) :
    (sectionIdeal (coordinateHyperplanePoleSheafPower_isInvertible (R := R) j d)
      (ProjectiveHomogeneousSections.homogeneousSection j d F hF)).ideal
      ⟨nativeCoordinateOpen i, nativeCoordinateOpen_isAffine i⟩ =
      Ideal.span { (nativeCoordinateSectionsIso (R := R) i).hom (coordinateDehom i F) } :=
  sectionIdeal_ideal_of_overCoefficient
    (coordinateHyperplanePoleSheafPower (R := R) j d)
    (coordinateHyperplanePoleSheafPower_isInvertible (R := R) j d)
    ⟨nativeCoordinateOpen i, nativeCoordinateOpen_isAffine i⟩
    (Scheme.Modules.overTrivializationOfRestrictIso
      (coordinateHyperplanePoleSheafPower (R := R) j d) (nativeCoordinateOpen i)
      (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j d))
    (ProjectiveHomogeneousSections.homogeneousSection j d F hF) _
    ((ProjectiveHomogeneousSections.section_coefficient i j d F hF).trans
      (homogeneousSection_coefficient_eq_coordinate i d F hF))

private theorem iSup_span_subtype {A B : Type u} [CommRing B]
    (G : Finset A) (c : A → B) :
    (⨆ a : G, Ideal.span ({c a.1} : Set B)) = Ideal.span (c '' (G : Set A)) := by
  apply le_antisymm
  · refine iSup_le fun a => Ideal.span_le.mpr ?_
    intro b hb
    obtain rfl := Set.mem_singleton_iff.mp hb
    exact Ideal.subset_span ⟨a.1, a.2, rfl⟩
  · apply Ideal.span_le.mpr
    rintro b ⟨a, ha, rfl⟩
    exact Ideal.mem_iSup_of_mem (R := B) ⟨a, ha⟩ (Ideal.mem_span_singleton_self _)

/-- The actual evaluation of SAME original finite homogeneous forms has
EXACTLY the whole original quotient-kernel ideal as image. -/
theorem homogeneousEvaluation_imageIdeal (j : Fin (n + 1)) (d : ℕ)
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (G : Finset (MvPolynomial (Fin (n + 1)) R))
    (hG : ∀ F ∈ G, F.IsHomogeneous d) (hspan : J.toIdeal = Ideal.span (G : Set _)) :
    let hL := coordinateHyperplanePoleSheafPower_isInvertible (R := R) j d
    let s := fun F : G => ProjectiveHomogeneousSections.homogeneousSection j d F.1 (hG F.1 F.2)
    let _ := freeTensorDual_isQuasicoherent hL G
    QuasicoherentImageIdeal.imageIdeal _ (familyEvaluation hL s) =
      GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J := by
  dsimp only
  rw [familyEvaluation_imageIdeal]
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun i : Fin (n + 1) => ⟨nativeCoordinateOpen i, nativeCoordinateOpen_isAffine i⟩)
    iSup_nativeCoordinateOpen_eq_top
  intro i
  let U : (NativeProjectiveScheme R n).affineOpens :=
    ⟨nativeCoordinateOpen i, nativeCoordinateOpen_isAffine i⟩
  let c := fun F : MvPolynomial (Fin (n + 1)) R =>
    (nativeCoordinateSectionsIso (R := R) i).hom (coordinateDehom i F)
  have hp : (⨆ F : G, sectionIdeal
      (coordinateHyperplanePoleSheafPower_isInvertible (R := R) j d)
      (ProjectiveHomogeneousSections.homogeneousSection j d F.1 (hG F.1 F.2))).ideal U =
      Ideal.span (c '' (G : Set _)) := by
    calc
      _ = ⨆ F : G, (sectionIdeal
          (coordinateHyperplanePoleSheafPower_isInvertible (R := R) j d)
          (ProjectiveHomogeneousSections.homogeneousSection j d F.1 (hG F.1 F.2))).ideal U := by
        rw [Scheme.IdealSheafData.ideal_iSup, iSup_apply]
      _ = ⨆ F : G, Ideal.span ({c F.1} : Set Γ(NativeProjectiveScheme R n, U.1)) :=
        iSup_congr fun F => homogeneousSection_sectionIdeal i j d F.1 (hG F.1 F.2)
      _ = Ideal.span (c '' (G : Set _)) := iSup_span_subtype G c
  refine hp.trans ?_
  rw [Char0.EnvelopeGradedBaseIdealsCore.quotientIdealSheaf_coordinateIdeal,
    hspan, Ideal.map_span, Ideal.map_span, Set.image_image]
  rfl

/-- Every actual pulled original homogeneous ideal polarization has finite
whole global generators, internally from its finite ORIGINAL homogeneous forms. -/
theorem exists_pullback_generatingSections_of_homogeneous_span
    {Y : Scheme.{u}} (μ : Y ⟶ NativeProjectiveScheme R n)
    (j : Fin (n + 1)) (d : ℕ)
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (G : Finset (MvPolynomial (Fin (n + 1)) R))
    (hG : ∀ F ∈ G, F.IsHomogeneous d) (hspan : J.toIdeal = Ideal.span (G : Set _)) :
    ∃ H : ((tensorRight ((pullback μ).obj (coordinateHyperplanePoleSheafPower (R := R) j d))).obj
      ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap μ).toModules).GeneratingSections,
      H.IsFiniteType := by
  let L := coordinateHyperplanePoleSheafPower (R := R) j d
  let hL := coordinateHyperplanePoleSheafPower_isInvertible (R := R) j d
  let s := fun F : G => ProjectiveHomogeneousSections.homogeneousSection j d F.1 (hG F.1 F.2)
  let _ := freeTensorDual_isQuasicoherent hL G
  let I := GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J
  have hi := homogeneousEvaluation_imageIdeal j d J G hG hspan
  let p := ProjectiveBaseIdealEpimorphism.imageFactorOfEq (familyEvaluation hL s) I hi
  let _ : Epi p := ProjectiveBaseIdealEpimorphism.imageFactorOfEq_epi _ I hi
  let M₀ := SheafOfModules.free (R := (NativeProjectiveScheme R n).ringCatSheaf) G
  let q := BaseIdealPullbackGeneratingSections.dividedEpimorphism μ M₀ L hL I p
  have hq : Epi q := BaseIdealPullbackGeneratingSections.dividedEpimorphism_epi μ M₀ L hL I p
  let G₀ := SheafOfModules.free.generatingSections (R := (NativeProjectiveScheme R n).ringCatSheaf) G
  let _ : G₀.IsFiniteType := ⟨inferInstanceAs (Finite G)⟩
  let H₀ := ClosedProjectiveGlobalGeneration.pullback_generatingSections μ G₀
  let _ : H₀.IsFiniteType := ClosedProjectiveGlobalGeneration.pullback_generatingSections_isFiniteType μ G₀
  let H := @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _ H₀ q hq
  exact ⟨H, ⟨inferInstanceAs (Finite G)⟩⟩

end EnvelopeProperty.ProjSubvariety.MultiplierOriginalGenerationCore
