import EnvelopeProperty.AlgGeom.SchemeInvertibleHomSectionNaturality

/-! # The whole original Hom-section recovery uses actual canonical evaluation -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace EnvelopeProperty.SchemeInvertibleHomSection

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}
noncomputable local instance : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X
noncomputable local instance : SymmetricCategory X.Modules := Scheme.Modules.symmetricCategory X

/-- The actual inverse Hom-section correspondence, retaining the SAME
original section, tensor comparison and ENTIRE actual tensor counit. -/
theorem equiv_symm_tensor_counit (A : X.Modules) (hA : Scheme.Modules.IsInvertible A)
    (B : X.Modules) (s : Scheme.Modules.unitObj X ⟶
      Scheme.Modules.tensorObj B (Scheme.Modules.dualObj A)) :
    (equiv A hA B).symm s =
      (λ_ A).inv ≫
        ((ModularCurves.monoidalUnitObjIso X).hom ≫ s ≫
          (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A)).inv) ▷ A ≫
        (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA).counit.app B := by
  let E := SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA
  change (λ_ A).inv ≫
      (E.toAdjunction.homEquiv _ _).symm
        ((ModularCurves.monoidalUnitObjIso X).hom ≫ s ≫
          (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A)).inv) = _
  rw [Adjunction.homEquiv_counit]
  rfl

/-- The ENTIRE actual tensor counit in that recovery is built from the
SAME canonical dual evaluation, with true associativity/braiding/unit maps. -/
theorem invertibleTensor_counit_evaluation (A : X.Modules) (hA : Scheme.Modules.IsInvertible A)
    (B : X.Modules) :
    (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA).counit.app B =
      (α_ B (Scheme.Modules.dualObj A) A).hom ≫
        B ◁ ((β_ (Scheme.Modules.dualObj A) A).hom ≫ hA.monoidalEvaluationIso.hom) ≫
          (ρ_ B).hom := by
  rfl

end
end EnvelopeProperty.SchemeInvertibleHomSection
