import EnvelopeProperty.Algebra.LeftExactHomologyComparison
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Actual section homology and actual whole original coefficient restriction -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.SchemeSectionHomology
open AlgebraicGeometry CategoryTheory Opposite

universe u
variable {X : Scheme.{u}}

private abbrev evaluation (U : X.Opens) : X.Modules ⥤ ModuleCat Γ(X, U) :=
  Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)

private instance evaluationAdditive (U : X.Opens) : (evaluation U).Additive where
  map_add := by intro M N α β; rfl

private instance evaluationPreservesZero (U : X.Opens) :
    (evaluation U).PreservesZeroMorphisms where
  map_zero _ _ := rfl

private instance evaluationPreservesFiniteLimits (U : X.Opens) :
    Limits.PreservesFiniteLimits (evaluation U) := by
  exact SheafOfModules.Finite.evaluationPreservesFiniteLimits (R := X.ringCatSheaf) (op U)

private instance mixedEvaluationPreservesFiniteLimits {U V : X.Opens} (j : U ⟶ V) :
    Limits.PreservesFiniteLimits
      (evaluation U ⋙ ModuleCat.restrictScalars (X.presheaf.map j.op).hom) :=
  Limits.comp_preservesFiniteLimits _ _

/-- Every term and differential is evaluated on the SAME original open. -/
def sectionComplex (K : CochainComplex X.Modules ℕ) (U : X.Opens) :
    CochainComplex (ModuleCat Γ(X, U)) ℕ :=
  ((evaluation U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- Canonical comparison, without any exactness assertion for H0. -/
def comparison (K : CochainComplex X.Modules ℕ) (U : X.Opens) (q : ℕ) :
    (sectionComplex K U).homology q ⟶ (K.homology q).val.obj (op U) :=
  LeftExactHomologyComparison.map (K.sc q) (evaluation U)

/-- The actual native projection of EVERY original cycle is retained. -/
theorem comparison_cycle (K : CochainComplex X.Modules ℕ) (U : X.Opens) (q : ℕ) :
    ((sectionComplex K U).sc q).homologyπ ≫ comparison K U q =
      (LeftExactHomologyComparison.cyclesIso (K.sc q) (evaluation U)).hom ≫
        (evaluation U).map (K.sc q).homologyπ :=
  LeftExactHomologyComparison.homologyπ_map (K.sc q) (evaluation U)

/-- The actual original coefficient-linear restriction transformation. -/
def restriction {U V : X.Opens} (j : U ⟶ V) :
    evaluation V ⟶ evaluation U ⋙ ModuleCat.restrictScalars (X.presheaf.map j.op).hom :=
  Functor.whiskerLeft (Scheme.Modules.toPresheafOfModules X)
    (PresheafOfModules.restriction X.ringCatSheaf.obj j.op)

/-- The ENTIRE original section complex restriction is derived from actual sheaf maps. -/
def restrictionComplexMap (K : CochainComplex X.Modules ℕ) {U V : X.Opens} (j : U ⟶ V) :
    sectionComplex K V ⟶
      (((evaluation U ⋙ ModuleCat.restrictScalars (X.presheaf.map j.op).hom).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K) where
  f q := (restriction j).app (K.X q)
  comm' q r _ := ((restriction j).naturality (K.d q r)).symm

/-- Every form/section keeps precisely its original whole coefficient restriction. -/
theorem restrictionComplexMap_f_apply (K : CochainComplex X.Modules ℕ)
    {U V : X.Opens} (j : U ⟶ V) (q : ℕ) (a : (K.X q).val.obj (op V)) :
    (restrictionComplexMap K j).f q a = (K.X q).presheaf.map j.op a := rfl

/-- The actual native homology square commutes with the SAME whole original restriction. -/
theorem comparison_restriction (K : CochainComplex X.Modules ℕ)
    {U V : X.Opens} (j : U ⟶ V) (q : ℕ) :
    HomologicalComplex.homologyMap (restrictionComplexMap K j) q ≫
        LeftExactHomologyComparison.map (K.sc q)
          (evaluation U ⋙ ModuleCat.restrictScalars (X.presheaf.map j.op).hom) =
      comparison K V q ≫ (restriction j).app (K.homology q) :=
  LeftExactHomologyComparison.natTrans_naturality _ (restriction j)

end EnvelopeProperty.SchemeSectionHomology
