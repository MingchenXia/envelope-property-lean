import TranscendentalNakamaye.Pending.MonicGermMultiplierIntegrability
import TranscendentalNakamaye.Pending.HolomorphicGermNoetherian
import TranscendentalNakamaye.Pending.StrongOpennessSliceInduction

set_option autoImplicit false

/-! # Actual weighted holomorphic germ ideals are integrally closed -/

open Set Filter MeasureTheory
open scoped Topology

namespace TranscendentalNakamaye.Pending.WeightedHolomorphicGermIdealIntegralClosure

open FirstPass

noncomputable section

variable {n : ℕ} {φ : ComplexModel n → EReal} {c : ℝ}
  {μ : Measure (ComplexModel n)}

/-- The actual ideal of holomorphic germs possessing the original weighted
multiplier representative. No coherence or presentation is assumed. -/
def weightedGermIdeal (hc : 0 < c) (hφ : QuasiPlurisubharmonicAt φ 0)
    (μ : Measure (ComplexModel n)) : Ideal (HolGerm (ComplexModel n)) where
  carrier := {g | ∃ (f : ComplexModel n → ℂ)
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z),
    HolGerm.mk f hf = g ∧ MultiplierIntegrableAt φ c f 0 μ}
  zero_mem' := ⟨0, eventually_differentiableAt_zero, HolGerm.mk_zero,
    multiplierIntegrableAt_zero φ hc 0 μ⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl, hint⟩ ⟨g, hg, rfl, hgint⟩
    exact ⟨fun z => f z + g z, eventually_differentiableAt_add hf hg,
      HolGerm.mk_add _ _ _ _, multiplierIntegrableAt_add hφ hint hgint⟩
  smul_mem' := by
    rintro a _ ⟨f, hf, rfl, hint⟩
    obtain ⟨u, hu, rfl⟩ := HolGerm.exists_eq_mk a
    refine ⟨fun z => u z * f z, eventually_differentiableAt_mul hu hf, ?_,
      multiplierIntegrableAt_differentiable_mul hint hu⟩
    simpa only [smul_eq_mul] using HolGerm.mk_mul _ _ _ _

/-- Membership in the actual germ ideal reads the literal original function's
weighted multiplier predicate. -/
theorem mem_weightedGermIdeal_iff (hc : 0 < c) (hφ : QuasiPlurisubharmonicAt φ 0)
    {F : ComplexModel n → ℂ} (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) :
    HolGerm.mk F hF ∈ weightedGermIdeal hc hφ μ ↔
      MultiplierIntegrableAt φ c F 0 μ := by
  constructor
  · rintro ⟨f, hf, heq, hint⟩
    exact hint.congr EventuallyEq.rfl (HolGerm.mk_eq_mk_iff.mp heq)
  · intro hint
    exact ⟨F, hF, rfl, hint⟩

/-- The true monic-coefficient integral-closure criterion for the actual
weighted ideal, with the finite weighted family supplied internally. -/
theorem mem_of_monic_relation (hc : 0 < c) (hφ : QuasiPlurisubharmonicAt φ 0)
    {d : ℕ} (hd : 0 < d) (F : ComplexModel n → ℂ)
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) (b : Fin d → HolGerm (ComplexModel n))
    (hb : ∀ i, b i ∈ weightedGermIdeal hc hφ μ ^ (d - i.val))
    (hrel : HolGerm.mk F hF ^ d + ∑ i, b i * HolGerm.mk F hF ^ i.val = 0) :
    HolGerm.mk F hF ∈ weightedGermIdeal hc hφ μ := by
  classical
  let : IsNoetherianRing (HolGerm (ComplexModel n)) :=
    isNoetherianRing_holGerm_euclidean n
  let J : Ideal (HolGerm (ComplexModel n)) := weightedGermIdeal hc hφ μ
  obtain ⟨N, g, hgen⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    J.fg_of_isNoetherianRing
  change Ideal.span (range g) = J at hgen
  have hg : ∀ j, g j ∈ J := fun j => hgen ▸ Ideal.subset_span ⟨j, rfl⟩
  choose G hG heqG hintG using hg
  have hspan : Ideal.span (range fun j => HolGerm.mk (G j) (hG j)) = J := by
    simpa only [heqG] using hgen
  apply (mem_weightedGermIdeal_iff hc hφ hF).mpr
  apply MonicGermMultiplierIntegrability.multiplierIntegrableAt_of_monic_germ_relation
    hc hφ hd G hG hintG F hF b
  · intro i
    simpa only [hspan] using hb i
  · exact hrel

end
end TranscendentalNakamaye.Pending.WeightedHolomorphicGermIdealIntegralClosure
