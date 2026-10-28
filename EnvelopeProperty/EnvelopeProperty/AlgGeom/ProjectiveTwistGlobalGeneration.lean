import EnvelopeProperty.AlgGeom.SchemeModuleGlobalSections
import EnvelopeProperty.AlgGeom.ProjectiveTwistCoordinateComparison
import ModularCurves.ForMathlib.SchemeModuleEpiCover

/-! # Actual coordinate powers globally generate every original nonnegative twist -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveTwistGlobalGeneration
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem isIso_mapped_comp_iso {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B C' : C} (f : A ⟶ B) (e : B ≅ C')
    (hf : IsIso (F.map f)) : IsIso (F.map (f ≫ e.hom)) := by
  rw [F.map_comp]
  exact IsIso.comp_isIso' hf (F.mapIso e).isIso_hom

private theorem epi_of_iso_factor {C : Type*} [Category C] {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) (hh : IsIso h) (hw : f ≫ g = h) :
    Epi g := by
  let : IsIso h := hh
  exact epi_of_epi_fac hw

/-- The actual ith coordinate-power section of the SAME original fixed twist,
formed from the genuine original coordinate section and the proved whole comparison. -/
def coordinateSectionHom (j i : σ) (n : ℕ) :
    unitObj (Proj (homogeneousSubmodule σ R)) ⟶
      coordinateHyperplaneTwist (R := R) j (n : ℤ) :=
  SchemeModuleGlobalSections.sectionHom
    (coordinateHyperplanePoleSheafPower (R := R) i n)
    (coordinateHyperplanePoleSectionPower (R := R) i n) ≫
      (ProjectiveTwistCoordinateComparison.coordinateIso i j (n : ℤ)).hom

private theorem originalPower_isIso_on_own_chart (i : σ) (n : ℕ) :
    IsIso ((restrictFunctor (coordinateOpen (R := R) i).ι).map
      (SchemeModuleGlobalSections.sectionHom
        (coordinateHyperplanePoleSheafPower (R := R) i n)
        (coordinateHyperplanePoleSectionPower (R := R) i n))) := by
  apply SchemeModuleGlobalSections.isIso_restrict_sectionHom_of_coefficient_one
    (coordinateHyperplanePoleSheafPower (R := R) i n)
    ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen (R := R) i⟩
    (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i i n)
  rw [coordinateHyperplanePoleSectionPower_localTrivializationTopSection,
    coordinateHyperplaneLocalEquation_self]
  simp [ModularCurves.affineOpenTopSection]

/-- The original ith coordinate section trivializes the actual original twist
on its SAME original standard open. -/
theorem coordinateSectionHom_isIso_on_own_chart (j i : σ) (n : ℕ) :
    IsIso ((restrictFunctor (coordinateOpen (R := R) i).ι).map
      (coordinateSectionHom (R := R) j i n)) := by
  exact isIso_mapped_comp_iso (restrictFunctor (coordinateOpen (R := R) i).ι)
    (SchemeModuleGlobalSections.sectionHom
      (coordinateHyperplanePoleSheafPower (R := R) i n)
      (coordinateHyperplanePoleSectionPower (R := R) i n))
    (ProjectiveTwistCoordinateComparison.coordinateIso i j (n : ℤ))
    (originalPower_isIso_on_own_chart i n)

/-- The genuine evaluation morphism from the free structure module indexed
by the actual original coordinate powers, with their universe lift only. -/
def generatingMap (j : σ) (n : ℕ) :
    SheafOfModules.free (ULift.{u} σ) ⟶
      coordinateHyperplaneTwist (R := R) j (n : ℤ) :=
  (coordinateHyperplaneTwist (R := R) j (n : ℤ)).freeHomEquiv.symm
    (fun i => (coordinateHyperplaneTwist (R := R) j (n : ℤ)).unitHomEquiv
      (coordinateSectionHom (R := R) j i.down n))

/-- Every original basis summand evaluates to the SAME original coordinate section. -/
theorem generatingMap_ι (j i : σ) (n : ℕ) :
    SheafOfModules.ιFree (R := (Proj (homogeneousSubmodule σ R)).ringCatSheaf)
        (ULift.up i : ULift.{u} σ) ≫ generatingMap (R := R) j n =
      coordinateSectionHom (R := R) j i n := by
  apply (coordinateHyperplaneTwist (R := R) j (n : ℤ)).unitHomEquiv.injective
  exact congrFun ((coordinateHyperplaneTwist (R := R) j (n : ℤ)).freeHomEquiv.apply_symm_apply
    (fun k : ULift.{u} σ => (coordinateHyperplaneTwist (R := R) j (n : ℤ)).unitHomEquiv
      (coordinateSectionHom (R := R) j k.down n))) (ULift.up i)

/-- The actual coordinate sections generate the original nonnegative twist;
local surjectivity is derived on the genuine original standard coordinate cover. -/
theorem generatingMap_epi (j : σ) (n : ℕ) : Epi (generatingMap (R := R) j n) := by
  apply Scheme.Modules.epi_of_restrictFunctor_map_epi_of_iSup_eq_top
    (fun i : σ => coordinateOpen (R := R) i) (iSup_coordinateOpen_eq_top (R := R))
  intro i
  exact epi_of_iso_factor
    ((restrictFunctor (coordinateOpen (R := R) i).ι).map
      (SheafOfModules.ιFree (R := (Proj (homogeneousSubmodule σ R)).ringCatSheaf)
        (ULift.up i : ULift.{u} σ)))
    ((restrictFunctor (coordinateOpen (R := R) i).ι).map (generatingMap (R := R) j n))
    ((restrictFunctor (coordinateOpen (R := R) i).ι).map (coordinateSectionHom (R := R) j i n))
    (coordinateSectionHom_isIso_on_own_chart j i n)
    (((restrictFunctor (coordinateOpen (R := R) i).ι).map_comp _ _).symm.trans
      (congrArg (fun f => (restrictFunctor (coordinateOpen (R := R) i).ι).map f)
        (generatingMap_ι (R := R) j i n)))


/-- The SAME actual original coordinate sections are a genuine generating family. -/
def generatingSections (j : σ) (n : ℕ) :
    (coordinateHyperplaneTwist (R := R) j (n : ℤ)).GeneratingSections where
  I := ULift.{u} σ
  s i := (coordinateHyperplaneTwist (R := R) j (n : ℤ)).unitHomEquiv
    (coordinateSectionHom (R := R) j i.down n)
  epi := generatingMap_epi j n

/-- On genuine finite-dimensional projective space the original coordinate
family is finite, giving an actual finite free structure-sheaf epimorphism. -/
theorem generatingSections_isFiniteType [Fintype σ] (j : σ) (n : ℕ) :
    (generatingSections (R := R) j n).IsFiniteType := by
  constructor
  change Finite (ULift.{u} σ)
  infer_instance

end EnvelopeProperty.ProjectiveTwistGlobalGeneration
