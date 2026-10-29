import ModularCurves.ForMathlib.SchemeModuleRestrictLimits
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Native homology of the SAME original open restriction -/
noncomputable section
namespace EnvelopeProperty.SchemeOpenRestrictionHomology
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g]

private instance restrictionAdditive : (Scheme.Modules.restrictFunctor g).Additive where
  map_add := by
    intro M N α β
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- Genuine native homology preservation by the SAME original open restriction. -/
theorem preservesHomology : (Scheme.Modules.restrictFunctor g).PreservesHomology := by
  let : PreservesLimits (Scheme.Modules.restrictFunctor g) :=
    Scheme.Modules.restrictFunctor_preservesLimits g
  let : (Scheme.Modules.restrictFunctor g).IsLeftAdjoint :=
    (Scheme.Modules.restrictAdjunction g).isLeftAdjoint
  infer_instance

/-- The ACTUAL native open restriction of EVERY SAME original complex. -/
def restrictedComplex (K : CochainComplex Y.Modules ℕ) : CochainComplex X.Modules ℕ :=
  ((Scheme.Modules.restrictFunctor g).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- The genuine native homology comparison, on the SAME original complex. -/
def homologyIso (K : CochainComplex Y.Modules ℕ) (q : ℕ) :
    (restrictedComplex g K).homology q ≅
      (Scheme.Modules.restrictFunctor g).obj (K.homology q) := by
  let : (Scheme.Modules.restrictFunctor g).PreservesHomology := preservesHomology g
  exact ShortComplex.mapHomologyIso (K.sc q) (Scheme.Modules.restrictFunctor g)

end EnvelopeProperty.SchemeOpenRestrictionHomology
