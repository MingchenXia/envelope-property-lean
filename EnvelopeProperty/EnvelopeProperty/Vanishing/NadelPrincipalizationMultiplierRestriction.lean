import EnvelopeProperty.Vanishing.NadelPrincipalizationMultiplierChart
import EnvelopeProperty.Char0.MultiplierIdealSheaves
import EnvelopeProperty.AlgGeom.IdealModuleOpenRestriction
import ModularCurves.ForMathlib.PullbackUnitMonoidal

/-! # The whole original scheme multiplier ideal on its same actual field chart -/

open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationMultiplierRestriction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem ideal_eq_inclusion {X : Scheme.{u}} (I J : X.IdealSheafData) (e : I = J) :
    (eqToIso (congrArg Scheme.IdealSheafData.toModules e)).hom ≫ J.toModulesInclusion =
      I.toModulesInclusion := by
  subst J
  exact Category.id_comp _

private theorem exists_ideal_openIso {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (g : X ⟶ Y) [IsOpenImmersion g] (J : X.IdealSheafData) (hJ : I.comap g = J) :
    ∃ e : (Scheme.Modules.pullback g).obj I.toModules ≅ J.toModules,
      e.hom ≫ J.toModulesInclusion =
        (Scheme.Modules.pullback g).map I.toModulesInclusion ≫ (Scheme.Modules.pullbackUnitIso g).hom := by
  subst J
  exact ⟨I.openPullbackModuleIso g, I.toModulesComapPullbackMap_inclusion g⟩

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥) (q : ℚ)
    (U : X.affineOpens) [Nonempty U.1]

attribute [local instance] NadelPrincipalizationAffineChart.algebra_isFractionRing

/-- The WHOLE original multiplier ideal pulls back to the native full
multiplier sheaf on the SAME actual original coefficient algebra and ideal. -/
theorem comap_eq :
    letI := f.stalkAlgebra (genericPoint X)
    (Char0.schemeMultiplierIdealSheaf f I hI q).comap (NadelPrincipalizationAffineChart.map f U) =
      Char0.multiplierIdealSheaf (k := k) (K := X.functionField) (NadelPrincipalizationAffineChart.algebra f U)
        (NadelPrincipalizationAffineChart.ideal f I U)
        (NadelPrincipalizationAffineChart.ideal_ne_bot f I hI U) q := by
  let := f.stalkAlgebra (genericPoint X)
  rw [NadelPrincipalizationAffineChart.comap_ideal]
  change specIdealSheaf (((Char0.schemeMultiplierIdealSheaf f I hI q).ideal U).map
      (NadelPrincipalizationAffineChart.ringEquiv f U).toRingHom) = _
  rw [Char0.schemeMultiplierIdealSheaf_ideal,
    NadelPrincipalizationAffineChart.multiplierAffineIdeal_eq_comap]
  change specIdealSheaf _ = specIdealSheaf _
  congr 1
  exact Ideal.map_comap_of_surjective _ (NadelPrincipalizationAffineChart.ringEquiv f U).surjective _

/-- The original whole multiplier MODULE has an internally constructed
actual native pullback isomorphism retaining its ENTIRE original inclusion. -/
theorem exists_moduleIso :
    letI := f.stalkAlgebra (genericPoint X)
    ∃ e : (Scheme.Modules.pullback (NadelPrincipalizationAffineChart.map f U)).obj
          (Char0.schemeMultiplierIdealSheaf f I hI q).toModules ≅
        (Char0.multiplierIdealSheaf (k := k) (K := X.functionField)
          (NadelPrincipalizationAffineChart.algebra f U)
          (NadelPrincipalizationAffineChart.ideal f I U)
          (NadelPrincipalizationAffineChart.ideal_ne_bot f I hI U) q).toModules,
      e.hom ≫ (Char0.multiplierIdealSheaf (k := k) (K := X.functionField)
          (NadelPrincipalizationAffineChart.algebra f U)
          (NadelPrincipalizationAffineChart.ideal f I U)
          (NadelPrincipalizationAffineChart.ideal_ne_bot f I hI U) q).toModulesInclusion =
        (Scheme.Modules.pullback (NadelPrincipalizationAffineChart.map f U)).map
            (Char0.schemeMultiplierIdealSheaf f I hI q).toModulesInclusion ≫
          (Scheme.Modules.pullbackUnitIso (NadelPrincipalizationAffineChart.map f U)).hom := by
  let := f.stalkAlgebra (genericPoint X)
  exact exists_ideal_openIso (Char0.schemeMultiplierIdealSheaf f I hI q)
    (NadelPrincipalizationAffineChart.map f U) _ (comap_eq f I hI q U)

end EnvelopeProperty.Vanishing.NadelPrincipalizationMultiplierRestriction
