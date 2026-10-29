/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SchemeAsymptoticMultiplierIdeal
import EnvelopeProperty.Char0.AsymptoticMultiplierSubadditivity

/-!
# Subadditivity of the original global asymptotic multiplier ideals

The full original asymptotic ideal sheaves satisfy additive subadditivity and
the resulting power bound on the same smooth integral scheme over any
characteristic-zero field. No gradedness or compactness assumption is needed.
-/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical
universe u
variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k)) [Smooth f]

/-- Additive subadditivity of the actual full asymptotic multiplier ideal
sheaves of the original family on the original smooth integral scheme. -/
theorem schemeAsymptoticMultiplierIdealSheaf_add_le
    (J : ℕ → X.IdealSheafData)
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint X) ≠ ⊥) (m n : ℕ) :
    schemeAsymptoticMultiplierIdealSheaf f J hne (m + n) ≤
      schemeAsymptoticMultiplierIdealSheaf f J hne m *
        schemeAsymptoticMultiplierIdealSheaf f J hne n := by
  intro U
  change (schemeAsymptoticMultiplierIdealSheaf f J hne (m + n)).ideal U ≤
    (schemeAsymptoticMultiplierIdealSheaf f J hne m).ideal U *
      (schemeAsymptoticMultiplierIdealSheaf f J hne n).ideal U
  by_cases hU : Nonempty U.1
  · let _ := hU
    let _ := f.stalkAlgebra (genericPoint X)
    let _ := f.sectionsAlgebra U.1
    let C := f.sectionsFunctionFieldSubalgebra U.1
    let e := f.sectionsFunctionFieldEquiv U.1
    let : IsFractionRing C X.functionField :=
      f.sectionsFunctionFieldSubalgebra_isFractionRing U.1 U.2
    let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C))) :=
      f.smooth_sectionsFunctionFieldSubalgebra U.1 U.2
    let A : ℕ → Ideal C := fun q => ((J q).ideal U).map e.toRingHom
    have hA (q : ℕ) (hq : 0 < q) : A q ≠ ⊥ :=
      (Ideal.map_eq_bot_iff_of_injective e.injective).mp.mt
        (affineIdeal_ne_bot_of_generic_stalk_ne_bot (J q) (hne q hq) U)
    have hcomap (P Q : Ideal C) : (P * Q).comap e.toRingHom =
        P.comap e.toRingHom * Q.comap e.toRingHom := by
      have he (L : Ideal C) : L.comap e.toRingHom = L.map e.symm.toRingHom :=
        (Ideal.map_comap_of_equiv e.toRingEquiv.symm).symm
      rw [he, Ideal.map_mul, he, he]
    rw [schemeAsymptoticMultiplierIdealSheaf_ideal_nonempty f J hne (m + n) U,
      schemeAsymptoticMultiplierIdealSheaf_ideal_nonempty f J hne m U,
      schemeAsymptoticMultiplierIdealSheaf_ideal_nonempty f J hne n U]
    have h := Ideal.comap_mono (f := e.toRingHom)
      (asymptoticMultiplierIdeal_add_le C A hA m n)
    rw [hcomap] at h
    exact h
  · have htop (r : ℕ) :
        (schemeAsymptoticMultiplierIdealSheaf f J hne r).ideal U = ⊤ := by
      apply top_unique
      have h := (schemeMultiplierIdealSheaf_le_asymptotic f J hne r
        (show 0 < 1 from one_pos)) U
      simpa only [schemeMultiplierIdealSheaf_ideal, schemeMultiplierAffineIdeal,
        dif_neg hU] using h
    rw [htop m, htop n, Ideal.top_mul]
    exact le_top

/-- The original full global asymptotic multiplier ideal at `m * ℓ` is
contained in the actual `ℓ`th power at `m`, including all zero indices. -/
theorem schemeAsymptoticMultiplierIdealSheaf_mul_le_pow
    (J : ℕ → X.IdealSheafData)
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint X) ≠ ⊥) (m ℓ : ℕ) :
    schemeAsymptoticMultiplierIdealSheaf f J hne (m * ℓ) ≤
      schemeAsymptoticMultiplierIdealSheaf f J hne m ^ ℓ := by
  induction ℓ with
  | zero =>
      simp only [Nat.mul_zero, pow_zero, Scheme.IdealSheafData.one_eq_top, le_top]
  | succ ℓ ih =>
      rw [Nat.mul_succ, pow_succ]
      refine le_trans (schemeAsymptoticMultiplierIdealSheaf_add_le f J hne (m * ℓ) m) ?_
      intro U
      exact Ideal.mul_mono (ih U) le_rfl

end EnvelopeProperty.Char0
