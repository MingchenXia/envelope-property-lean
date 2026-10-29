import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorEquivalence

/-! # Actual whole homomorphisms as sections of the original tensor-dual sheaf -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
noncomputable section
namespace EnvelopeProperty.SchemeInvertibleHomSection
universe u
variable {X : Scheme.{u}}
noncomputable local instance : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

/-- Genuine adjunction for tensoring the SAME original line converts whole maps to actual
sections of the SAME original tensor with the actual sheaf dual. -/
def equiv (A : X.Modules) (hA : Scheme.Modules.IsInvertible A) (B : X.Modules) :
    (A ⟶ B) ≃ (Scheme.Modules.unitObj X ⟶
      Scheme.Modules.tensorObj B (Scheme.Modules.dualObj A)) :=
  by
    let E := SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA
    have e := E.toAdjunction.homEquiv (𝟙_ X.Modules) B
    change ((𝟙_ X.Modules ⊗ A) ⟶ B) ≃
      (𝟙_ X.Modules ⟶ B ⊗ Scheme.Modules.dualObj A) at e
    exact ((Iso.homCongr (λ_ A).symm (Iso.refl B)).trans e).trans
      (Iso.homCongr (ModularCurves.monoidalUnitObjIso X)
        (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A)))

/-- The exact inverse recovers the WHOLE original map, not only its image or a chart scalar. -/
theorem recover (A : X.Modules) (hA : Scheme.Modules.IsInvertible A)
    (B : X.Modules) (φ : A ⟶ B) : (equiv A hA B).symm (equiv A hA B φ) = φ :=
  (equiv A hA B).symm_apply_apply φ

/-- Conversely every actual whole section is recovered by the same genuine Hom correspondence. -/
theorem section_recover (A : X.Modules) (hA : Scheme.Modules.IsInvertible A)
    (B : X.Modules) (s : Scheme.Modules.unitObj X ⟶
      Scheme.Modules.tensorObj B (Scheme.Modules.dualObj A)) :
    equiv A hA B ((equiv A hA B).symm s) = s := (equiv A hA B).apply_symm_apply s

end EnvelopeProperty.SchemeInvertibleHomSection
