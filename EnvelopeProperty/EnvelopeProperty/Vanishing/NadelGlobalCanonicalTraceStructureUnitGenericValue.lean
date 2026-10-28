import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureRationalValues

/-! # Actual original structural-unit coefficients on the generic field

The native structural unit is the actual pullback on functions. The
original generic-point triangle identifies its entire value with the
same original chart germ coefficient, without a supplied square match.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} [IsIntegral X] {π : Y ⟶ X} {D : ℕ}
    (C : WholeFreeChart π D) [Nonempty C.base.1]

private theorem generic_base_preimage_top :
    (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ (C.base.2.fromSpec ''ᵁ ⊤) = ⊤ := by
  rw [← C.genericBaseMap_over_original, Scheme.Hom.comp_preimage,
    C.base.2.fromSpec.preimage_image_eq, Scheme.Hom.preimage_top]

/-- The ACTUAL original structural unit sends EVERY original local
regular section to its SAME original chart germ in the actual field. -/
theorem genericTargetRead_unit
    (r : Γ((restrictFunctor C.base.2.fromSpec).obj (unitObj X), ⊤)) :
    C.genericTargetRead
      (((restrictFunctor C.base.2.fromSpec).map
        (SheafOfModules.unitToPushforwardObjUnit
          (X.fromSpecStalk (genericPoint X)).toRingCatSheafHom)).app ⊤ r) =
    algebraMap Γ(X, C.base.1) X.functionField
      ((Scheme.ΓSpecIso Γ(X, C.base.1)).hom
        ((restrictUnitIso C.base.2.fromSpec).hom.app ⊤ r)) := by
  have hm : (C.base.2.fromSpec.appIso ⊤).hom ≫ C.genericBaseMap.appTop =
      (X.fromSpecStalk (genericPoint X)).appLE (C.base.2.fromSpec ''ᵁ ⊤) ⊤
        C.generic_base_preimage_top.ge := by
    simp only [Scheme.Hom.appIso_hom', Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.preimage_top, Scheme.Hom.appLE_comp_appLE, C.genericBaseMap_over_original]
  have hv : C.genericTargetRead
      (((restrictFunctor C.base.2.fromSpec).map
        (SheafOfModules.unitToPushforwardObjUnit
          (X.fromSpecStalk (genericPoint X)).toRingCatSheafHom)).app ⊤ r) =
      (Scheme.ΓSpecIso X.functionField).hom
        ((X.fromSpecStalk (genericPoint X)).appLE (C.base.2.fromSpec ''ᵁ ⊤) ⊤
          C.generic_base_preimage_top.ge (show Γ(X, C.base.2.fromSpec ''ᵁ ⊤) from r)) := by
    rfl
  have hc := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (X.germToFunctionField C.base.1))
      ((C.base.2.fromSpec.appIso ⊤).hom (show Γ(X, C.base.2.fromSpec ''ᵁ ⊤) from r))
  exact hv.trans ((congrArg (Scheme.ΓSpecIso X.functionField).hom
    (ConcreteCategory.congr_hom hm (show Γ(X, C.base.2.fromSpec ''ᵁ ⊤) from r)).symm).trans hc)

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
