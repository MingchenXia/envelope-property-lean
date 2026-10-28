import TranscendentalNakamaye.Pending.HolomorphicCoordinateFactorization

set_option autoImplicit false

/-! # Actual holomorphic quotients of the full principal germ ideal -/

open Set Filter
open scoped Topology

namespace TranscendentalNakamaye.Pending.PrincipalHolomorphicGeneratorQuotients

open FirstPass

noncomputable section

/-- A full principal span cannot have every quotient in the kernel of evaluation. -/
theorem exists_eval_ne_zero_of_mem_span_multiples
    {R : Type*} [CommRing R] [IsDomain R] {ι : Type*}
    (e : R →+* ℂ) {h : R} (hh : h ≠ 0) (q : ι → R)
    (hmem : h ∈ Ideal.span (Set.range fun i => h * q i)) :
    ∃ i, e (q i) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hprop : ∃ a : R, e a = 0 ∧ h = h * a := by
    refine Submodule.span_induction
      (p := fun x _ => ∃ a : R, e a = 0 ∧ x = h * a) ?_ ?_ ?_ ?_ hmem
    · rintro x ⟨i, rfl⟩
      exact ⟨q i, hn i, rfl⟩
    · exact ⟨0, by simp, by simp⟩
    · rintro x y _ _ ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩
      refine ⟨a + b, by simp [ha, hb], ?_⟩
      rw [hxa, hyb, mul_add]
    · rintro r x _ ⟨a, ha, hxa⟩
      refine ⟨r * a, by simp [ha], ?_⟩
      simp only [smul_eq_mul, hxa]
      ring
  obtain ⟨a, ha, hea⟩ := hprop
  have ha1 : a = 1 := mul_left_cancel₀ hh (by simpa only [mul_one] using hea.symm)
  have h10 : (1 : ℂ) = 0 := by simpa only [ha1, map_one] using ha
  exact one_ne_zero h10

/-- The actual full principal holomorphic germ ideal supplies all quotients and a nonzero value. -/
theorem exists_holomorphic_quotients_of_principal_span {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G i) z)
    {H : ComplexModel n → ℂ} (hH : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z)
    (hHnon : ∃ᶠ z in 𝓝 (0 : ComplexModel n), H z ≠ 0)
    (hspan : Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) =
      Ideal.span {HolGerm.mk H hH}) :
    ∃ Q : Fin s → ComplexModel n → ℂ,
      (∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (Q i) z) ∧
      (∀ i, G i =ᶠ[𝓝 0] fun z => H z * Q i z) ∧
      ∃ i, Q i 0 ≠ 0 := by
  classical
  have hdiv : ∀ i, HolGerm.mk H hH ∣ HolGerm.mk (G i) (hG i) := by
    intro i
    apply Ideal.mem_span_singleton.mp
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  choose q hq using hdiv
  choose Q hQ hrep using fun i => HolGerm.exists_eq_mk (q i)
  have hnon : HolGerm.mk H hH ≠ 0 := by
    intro h
    have heq : H =ᶠ[𝓝 0] (0 : ComplexModel n → ℂ) :=
      HolGerm.mk_eq_mk_iff.mp (h.trans HolGerm.mk_zero.symm)
    obtain ⟨z, hz, hz0⟩ := (hHnon.and_eventually heq).exists
    exact hz hz0
  have hmem : HolGerm.mk H hH ∈ Ideal.span (Set.range fun i => HolGerm.mk H hH * q i) := by
    have hm : HolGerm.mk H hH ∈ Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) := by
      rw [hspan]
      exact Ideal.subset_span (Set.mem_singleton _)
    have heq : (fun i => HolGerm.mk (G i) (hG i)) =
        (fun i => HolGerm.mk H hH * q i) := funext hq
    rwa [heq] at hm
  obtain ⟨i, hi⟩ := exists_eval_ne_zero_of_mem_span_multiples HolGerm.eval hnon q hmem
  refine ⟨Q, hQ, ?_, i, ?_⟩
  · intro j
    apply (HolGerm.mk_eq_mk_iff (hf := hG j)
      (hg := eventually_differentiableAt_mul hH (hQ j))).mp
    calc
      HolGerm.mk (G j) (hG j) = HolGerm.mk H hH * q j := hq j
      _ = HolGerm.mk H hH * HolGerm.mk (Q j) (hQ j) := by rw [hrep j]
      _ = HolGerm.mk (fun z => H z * Q j z)
          (eventually_differentiableAt_mul hH (hQ j)) :=
        (HolGerm.mk_mul H (Q j) hH (hQ j)).symm
  · simpa only [hrep i, HolGerm.eval_mk] using hi

end
end TranscendentalNakamaye.Pending.PrincipalHolomorphicGeneratorQuotients
