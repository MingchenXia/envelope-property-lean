/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SchemeAsymptoticMultiplierIdeal

/-! # Original ideal containment and actual global asymptotic nonvanishing -/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical
universe u
variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k)) [Smooth f]

/-- The WHOLE original ideal sheaf lies in its ACTUAL full multiplier ideal
at exponent one on the ORIGINAL smooth integral scheme. -/
theorem le_schemeMultiplierIdealSheaf_one
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥) :
    I ≤ schemeMultiplierIdealSheaf f I hI 1 := by
  intro U
  change I.ideal U ≤ schemeMultiplierAffineIdeal f I hI 1 U
  by_cases hU : Nonempty U.1
  · let _ := hU
    let _ := f.stalkAlgebra (genericPoint X)
    let _ := f.sectionsAlgebra U.1
    let C := f.sectionsFunctionFieldSubalgebra U.1
    let e := f.sectionsFunctionFieldEquiv U.1
    have : IsFractionRing C X.functionField := f.sectionsFunctionFieldSubalgebra_isFractionRing U.1 U.2
    have hIC : (I.ideal U).map e.toRingHom ≠ ⊥ :=
      (Ideal.map_eq_bot_iff_of_injective e.injective).mp.mt
        (affineIdeal_ne_bot_of_generic_stalk_ne_bot I hI U)
    simp only [schemeMultiplierAffineIdeal, dif_pos hU]
    intro a ha
    exact le_valuativeMultiplierIdeal_one C _ hIC (Ideal.mem_map_of_mem e.toRingHom ha)
  · simp only [schemeMultiplierAffineIdeal, dif_neg hU, le_top]

/-- Every positive original sequence ideal is contained in its actual
global asymptotic multiplier ideal sheaf, retaining the original scheme. -/
theorem le_schemeAsymptoticMultiplierIdealSheaf
    (J : ℕ → X.IdealSheafData)
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint X) ≠ ⊥)
    {m : ℕ} (hm : 0 < m) : J m ≤ schemeAsymptoticMultiplierIdealSheaf f J hne m := by
  refine le_trans (le_schemeMultiplierIdealSheaf_one f (J m) (hne m hm)) ?_
  have h := schemeMultiplierIdealSheaf_le_asymptotic f J hne m hm
  rw [div_self (show (m : ℚ) ≠ 0 from Nat.cast_ne_zero.mpr hm.ne')] at h
  exact h

/-- The actual full global asymptotic ideal has a genuinely nonzero
ORIGINAL generic stalk at every positive degree. -/
theorem schemeAsymptoticMultiplierIdealSheaf_generic_stalk_ne_bot
    (J : ℕ → X.IdealSheafData)
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint X) ≠ ⊥)
    {m : ℕ} (hm : 0 < m) :
    (schemeAsymptoticMultiplierIdealSheaf f J hne m).stalkIdeal (genericPoint X) ≠ ⊥ := by
  intro hzero
  apply hne m hm
  exact le_bot_iff.mp (hzero ▸ Scheme.IdealSheafData.stalkIdeal_mono
    (le_schemeAsymptoticMultiplierIdealSheaf f J hne hm) (genericPoint X))

end EnvelopeProperty.Char0
