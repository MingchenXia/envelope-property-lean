/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SchemeAsymptoticMultiplierIdeal

/-! # Genuine global divisible-index stabilization for the original graded sequence -/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical
universe u
variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k)) [Smooth f]

/-- For the ORIGINAL graded ideal-sheaf sequence, the actual FULL global
multiplier constituents increase under divisibility of their ORIGINAL indices. -/
theorem schemeMultiplierIdealSheaf_le_of_dvd
    {J : ℕ → X.IdealSheafData} (hJ : ∀ a b, J a * J b ≤ J (a + b))
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint X) ≠ ⊥) (m : ℕ)
    {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') (hdvd : q ∣ q') :
    schemeMultiplierIdealSheaf f (J q) (hne q hq) ((m : ℚ) / q) ≤
      schemeMultiplierIdealSheaf f (J q') (hne q' hq') ((m : ℚ) / q') := by
  intro U
  change schemeMultiplierAffineIdeal f (J q) (hne q hq) ((m : ℚ) / q) U ≤
    schemeMultiplierAffineIdeal f (J q') (hne q' hq') ((m : ℚ) / q') U
  by_cases hU : Nonempty U.1
  · let _ := hU
    let _ := f.stalkAlgebra (genericPoint X)
    let _ := f.sectionsAlgebra U.1
    let C := f.sectionsFunctionFieldSubalgebra U.1
    let e := f.sectionsFunctionFieldEquiv U.1
    have : IsFractionRing C X.functionField := f.sectionsFunctionFieldSubalgebra_isFractionRing U.1 U.2
    let A : ℕ → Ideal C := fun a => ((J a).ideal U).map e.toRingHom
    have hA (a b : ℕ) : A a * A b ≤ A (a + b) := by
      dsimp only [A]
      rw [← Ideal.map_mul]
      exact Ideal.map_mono ((hJ a b) U)
    have hneA (a : ℕ) (ha : 0 < a) : A a ≠ ⊥ :=
      (Ideal.map_eq_bot_iff_of_injective e.injective).mp.mt
        (affineIdeal_ne_bot_of_generic_stalk_ne_bot (J a) (hne a ha) U)
    simp only [schemeMultiplierAffineIdeal, dif_pos hU]
    exact Ideal.comap_mono (valuativeMultiplierIdeal_le_of_dvd C hA hneA m hq hq' hdvd)
  · simp only [schemeMultiplierAffineIdeal, dif_neg hU, le_refl]

/-- On the ORIGINAL quasi-compact smooth integral scheme, actual gradedness
derives global attainment at EVERY sufficiently divisible ORIGINAL index.
Neither a maximal multiplier ideal nor stabilization is supplied. -/
theorem exists_schemeAsymptoticMultiplierIdealSheaf_eq [CompactSpace X]
    {J : ℕ → X.IdealSheafData} (hJ : ∀ a b, J a * J b ≤ J (a + b))
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint X) ≠ ⊥) (m : ℕ) :
    ∃ q₀, 0 < q₀ ∧ ∀ q (hq : 0 < q), q₀ ∣ q →
      schemeAsymptoticMultiplierIdealSheaf f J hne m =
        schemeMultiplierIdealSheaf f (J q) (hne q hq) ((m : ℚ) / q) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let P := {q : ℕ // 0 < q}
  have : Nonempty P := ⟨⟨1, one_pos⟩⟩
  let F : P → X.IdealSheafData := fun q =>
    schemeMultiplierIdealSheaf f (J q.val) (hne q.val q.property) ((m : ℚ) / q.val)
  have hdir : Directed (· ≤ ·) F := by
    intro q r
    have hqr : 0 < q.val * r.val := Nat.mul_pos q.property r.property
    refine ⟨⟨q.val * r.val, hqr⟩, ?_, ?_⟩
    · exact schemeMultiplierIdealSheaf_le_of_dvd f hJ hne m q.property hqr (dvd_mul_right q.val r.val)
    · exact schemeMultiplierIdealSheaf_le_of_dvd f hJ hne m r.property hqr (dvd_mul_left r.val q.val)
  obtain ⟨q₀, hq₀⟩ := Scheme.IdealSheafData.exists_eq_iSup_of_directed F hdir
  have hB : schemeAsymptoticMultiplierIdealSheaf f J hne m = F q₀ := by
    rw [← hq₀]
    apply le_antisymm
    · apply iSup₂_le
      intro q hq
      exact le_iSup F ⟨q, hq⟩
    · apply iSup_le
      intro q
      exact schemeMultiplierIdealSheaf_le_asymptotic f J hne m q.property
  refine ⟨q₀.val, q₀.property, fun q hq hdvd => le_antisymm ?_ ?_⟩
  · rw [hB]
    exact schemeMultiplierIdealSheaf_le_of_dvd f hJ hne m q₀.property hq hdvd
  · exact schemeMultiplierIdealSheaf_le_asymptotic f J hne m hq

end EnvelopeProperty.Char0
