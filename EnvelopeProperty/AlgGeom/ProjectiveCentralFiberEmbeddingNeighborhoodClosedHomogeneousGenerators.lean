import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedPadding
import EnvelopeProperty.AlgGeom.ProjectiveHomogeneousSections
import ModularCurves.ForMathlib.SchemeModuleEpiCover

/-! # Actual homogeneous forms with original diagonal powers generate the same twist -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
open Opposite
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedHomogeneousGenerators
open ProjectiveHomogeneousSections
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {m : ℕ} {ι : Type u}

private theorem diagonalCoefficient_one (d : ℕ)
    (F : ι → MvPolynomial (Fin (m + 1)) R) (hF : ∀ a, (F a).IsHomogeneous d)
    (b : Fin (m + 1) → ι) (hb : ∀ i, F (b i) = MvPolynomial.X i ^ d) (i : Fin (m + 1)) :
    coefficient i d (F (b i)) (hF (b i)) = 1 := by
  have hfraction : fraction i d (F (b i)) (hF (b i)) = 1 := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_one]
    change Localization.mk (S := Submonoid.powers (MvPolynomial.X i)) (F (b i))
      ⟨MvPolynomial.X i ^ d, ⟨d, rfl⟩⟩ = 1
    rw [hb]
    exact @Localization.mk_self (MvPolynomial (Fin (m + 1)) R) inferInstance
      (Submonoid.powers (MvPolynomial.X (R := R) i))
      ⟨MvPolynomial.X (R := R) i ^ d, ⟨d, rfl⟩⟩
  change (Proj.awayToSection (homogeneousSubmodule (Fin (m + 1)) R) (MvPolynomial.X i)).hom
    (fraction i d (F (b i)) (hF (b i))) = 1
  rw [hfraction, map_one]

private def evaluationMap (j : Fin (m + 1)) (d : ℕ)
    (F : ι → MvPolynomial (Fin (m + 1)) R) (hF : ∀ a, (F a).IsHomogeneous d) :
    SheafOfModules.free ι ⟶ coordinateHyperplaneTwist (R := R) j (d : ℤ) :=
  (coordinateHyperplaneTwist (R := R) j (d : ℤ)).freeHomEquiv.symm
    (fun a => (coordinateHyperplaneTwist (R := R) j (d : ℤ)).unitHomEquiv
      (ProjectiveHomogeneousSections.sectionHom j d (F a) (hF a)))

private theorem evaluationMap_basis (j : Fin (m + 1)) (d : ℕ)
    (F : ι → MvPolynomial (Fin (m + 1)) R) (hF : ∀ a, (F a).IsHomogeneous d) (a : ι) :
    SheafOfModules.ιFree a ≫ evaluationMap j d F hF =
      ProjectiveHomogeneousSections.sectionHom j d (F a) (hF a) := by
  apply (coordinateHyperplaneTwist (R := R) j (d : ℤ)).unitHomEquiv.injective
  exact congrFun ((coordinateHyperplaneTwist (R := R) j (d : ℤ)).freeHomEquiv.apply_symm_apply
    (fun a => (coordinateHyperplaneTwist (R := R) j (d : ℤ)).unitHomEquiv
      (ProjectiveHomogeneousSections.sectionHom j d (F a) (hF a)))) a

private theorem diagonal_restrict_isIso (j : Fin (m + 1)) (d : ℕ)
    (F : ι → MvPolynomial (Fin (m + 1)) R) (hF : ∀ a, (F a).IsHomogeneous d)
    (b : Fin (m + 1) → ι) (hb : ∀ i, F (b i) = MvPolynomial.X i ^ d) (i : Fin (m + 1)) :
    IsIso ((restrictFunctor (coordinateOpen (R := R) i).ι).map
      (ProjectiveHomogeneousSections.sectionHom j d (F (b i)) (hF (b i)))) := by
  let M := coordinateHyperplanePoleSheafPower (R := R) j d
  let U : (Proj (homogeneousSubmodule (Fin (m + 1)) R)).affineOpens :=
    ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
  let e := coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j d
  have hcoeff : ModularCurves.localTrivializationCoefficient M U e
      (homogeneousSection j d (F (b i)) (hF (b i))) = 1 :=
    (ModularCurves.overTrivializationCoefficient_overTrivializationOfRestrictIso M U e _).symm.trans
      ((section_coefficient i j d (F (b i)) (hF (b i))).trans
        (diagonalCoefficient_one d F hF b hb i))
  have ht := congrArg (ModularCurves.affineOpenTopSection U) hcoeff
  change ModularCurves.affineOpenTopSection U (ModularCurves.affineOpenAmbientSection U
      (ModularCurves.localTrivializationTopSection M U e
        (homogeneousSection j d (F (b i)) (hF (b i))))) =
    ModularCurves.affineOpenTopSection U 1 at ht
  rw [ModularCurves.affineOpenTopSection_ambientSection] at ht
  have hone : ModularCurves.affineOpenTopSection U (1 : Γ(Proj (homogeneousSubmodule
      (Fin (m + 1)) R), U.1)) = 1 := by
    rw [ModularCurves.affineOpenTopSection_eq_topIso_inv]
    exact map_one _
  exact SchemeModuleGlobalSections.isIso_restrict_sectionHom_of_coefficient_one M U e
    (homogeneousSection j d (F (b i)) (hF (b i))) (ht.trans hone)

private theorem epi_of_iso_factor {C : Type*} [Category C] {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) (hh : IsIso h) (hw : f ≫ g = h) :
    Epi g := by
  let : IsIso h := hh
  exact epi_of_epi_fac hw

private theorem evaluationMap_epi (j : Fin (m + 1)) (d : ℕ)
    (F : ι → MvPolynomial (Fin (m + 1)) R) (hF : ∀ a, (F a).IsHomogeneous d)
    (b : Fin (m + 1) → ι) (hb : ∀ i, F (b i) = MvPolynomial.X i ^ d) :
    Epi (evaluationMap j d F hF) := by
  apply Scheme.Modules.epi_of_restrictFunctor_map_epi_of_iSup_eq_top
    (fun i : Fin (m + 1) => coordinateOpen (R := R) i) (iSup_coordinateOpen_eq_top (R := R))
  intro i
  exact epi_of_iso_factor
    ((restrictFunctor (coordinateOpen (R := R) i).ι).map
      (SheafOfModules.ιFree (R := (Proj (homogeneousSubmodule (Fin (m + 1)) R)).ringCatSheaf) (b i)))
    ((restrictFunctor (coordinateOpen (R := R) i).ι).map (evaluationMap j d F hF))
    ((restrictFunctor (coordinateOpen (R := R) i).ι).map
      (ProjectiveHomogeneousSections.sectionHom j d (F (b i)) (hF (b i))))
    (diagonal_restrict_isIso j d F hF b hb i)
    (((restrictFunctor (coordinateOpen (R := R) i).ι).map_comp _ _).symm.trans
      (congrArg (fun α => (restrictFunctor (coordinateOpen (R := R) i).ι).map α)
        (evaluationMap_basis j d F hF (b i))))

/-- The SAME actual original homogeneous section morphisms genuinely generate
the WHOLE original twist, with the literal original index and an internally
proved original evaluation epimorphism. -/
def homogeneousGeneratingSections (j : Fin (m + 1)) (d : ℕ)
    (F : ι → MvPolynomial (Fin (m + 1)) R) (hF : ∀ a, (F a).IsHomogeneous d)
    (b : Fin (m + 1) → ι) (hb : ∀ i, F (b i) = MvPolynomial.X i ^ d) :
    (coordinateHyperplaneTwist (R := R) j (d : ℤ)).GeneratingSections where
  I := ι
  s a := (coordinateHyperplaneTwist (R := R) j (d : ℤ)).unitHomEquiv
    (ProjectiveHomogeneousSections.sectionHom j d (F a) (hF a))
  epi := evaluationMap_epi j d F hF b hb

/-- Every ORIGINAL generator-Hom is the SAME original prescribed homogeneous
section-Hom, as an equality of the WHOLE actual module morphisms. -/
theorem homogeneousGeneratingSections_generatorHom (j : Fin (m + 1)) (d : ℕ)
    (F : ι → MvPolynomial (Fin (m + 1)) R) (hF : ∀ a, (F a).IsHomogeneous d)
    (b : Fin (m + 1) → ι) (hb : ∀ i, F (b i) = MvPolynomial.X i ^ d) (a : ι) :
    SchemeGeneratingSectionsUnit.generatorHom (homogeneousGeneratingSections j d F hF b hb) a =
      ProjectiveHomogeneousSections.sectionHom j d (F a) (hF a) :=
  evaluationMap_basis j d F hF a

/-- The actual family retains the SAME original finite index, without any
additional central generators or a chosen basis of all global sections. -/
theorem homogeneousGeneratingSections_isFiniteType [Fintype ι] (j : Fin (m + 1)) (d : ℕ)
    (F : ι → MvPolynomial (Fin (m + 1)) R) (hF : ∀ a, (F a).IsHomogeneous d)
    (b : Fin (m + 1) → ι) (hb : ∀ i, F (b i) = MvPolynomial.X i ^ d) :
    (homogeneousGeneratingSections j d F hF b hb).IsFiniteType := by
  constructor
  change Finite ι
  infer_instance

/-- Every actual original coefficient in the actual original coordinate frame
is the WHOLE original homogeneous ratio, retaining nilpotent coefficients. -/
theorem localCoefficient_eq_fraction (j : Fin (m + 1)) (d : ℕ)
    (F : ι → MvPolynomial (Fin (m + 1)) R) (hF : ∀ a, (F a).IsHomogeneous d)
    (b : Fin (m + 1) → ι) (hb : ∀ i, F (b i) = MvPolynomial.X i ^ d)
    (i : Fin (m + 1)) (a : ι) :
    GeneratedLineLocalCoefficients.localCoefficient (homogeneousGeneratingSections j d F hF b hb)
        (coordinateOpen (R := R) i)
        (pullbackIsoOfRestrictIso (coordinateHyperplaneTwist (R := R) j (d : ℤ))
          (coordinateOpen (R := R) i)
          (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j d)) a =
      ModularCurves.affineOpenTopSection
        ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
        (coefficient i d (F a) (hF a)) := by
  let M := coordinateHyperplanePoleSheafPower (R := R) j d
  let U : (Proj (homogeneousSubmodule (Fin (m + 1)) R)).affineOpens :=
    ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
  let e := coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j d
  let E := pullbackIsoOfRestrictIso M U.1 e
  let G := homogeneousGeneratingSections j d F hF b hb
  have hcoeff : ModularCurves.localTrivializationCoefficient M U e
      (homogeneousSection j d (F a) (hF a)) = coefficient i d (F a) (hF a) :=
    (ModularCurves.overTrivializationCoefficient_overTrivializationOfRestrictIso M U e _).symm.trans
      (section_coefficient i j d (F a) (hF a))
  have hs := SchemeLineSectionEvaluation.sectionHom_localScalar M U e
    (homogeneousSection j d (F a) (hF a))
  rw [hcoeff] at hs
  have hl := GeneratedLineLocalCoefficients.localCoefficient_scalar G U.1 E a
  have hg := homogeneousGeneratingSections_generatorHom j d F hF b hb a
  have hl' : SchemeLineSectionEvaluation.pullbackSectionHom U.1.ι
      (ProjectiveHomogeneousSections.sectionHom j d (F a) (hF a)) ≫ E.hom =
      ModularCurves.unitEndomorphismOfTopSection
        (GeneratedLineLocalCoefficients.localCoefficient G U.1 E a) :=
    (congrArg (fun α => SchemeLineSectionEvaluation.pullbackSectionHom U.1.ι α ≫ E.hom)
      hg.symm).trans hl
  have hv := congrArg SchemeLineSectionEvaluation.sectionAtOne (hl'.symm.trans hs)
  exact (Scheme.Modules.topSectionHom_app_top_apply_one _ _).symm.trans
    (hv.trans (Scheme.Modules.topSectionHom_app_top_apply_one _ _))

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedHomogeneousGenerators
