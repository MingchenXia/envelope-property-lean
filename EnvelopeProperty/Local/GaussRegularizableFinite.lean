/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.Regularizable
import EnvelopeProperty.Berkovich.NormIdentity

/-!
# Regularizable functions at positive-radius weighted Gauss points

The reflected-radius inequality proves genuine finiteness for every positive-radius
weighted Gauss valuation on a polynomial algebra with trivial coefficient valuation.
This is the monomial case of FHX `lem:regularizable-closure`(1). Arbitrary divisorial
valuations are not asserted to have this presentation.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

namespace Berk

variable {k B σ : Type*} [Field k] [CommRing B] [IsDomain B] [Algebra k B]

/-- The weighted Gauss point with trivial coefficient valuation. -/
def trivialWeightedGauss (r : σ → ℝ≥0) : Berk k (MvPolynomial σ B) where
  val := wgaussValuation (triv : Berk k B).val r
  val_algebraMap c hc := by
    change wgaussValuation (triv : Berk k B).val r
      (MvPolynomial.C (algebraMap k B c)) = 1
    rw [wgaussValuation_C, Berk.val_algebraMap _ c hc]

@[simp]
theorem trivialWeightedGauss_val (r : σ → ℝ≥0) (P : MvPolynomial σ B) :
    (trivialWeightedGauss r : Berk k (MvPolynomial σ B)).val P =
      wgaussValuation (triv : Berk k B).val r P := rfl

/-- Positive radii give positive monomial weights. -/
theorem monoWeight_pos {r : σ → ℝ≥0} (hr : ∀ i, 0 < r i) (α : σ →₀ ℕ) :
    0 < monoWeight r α := by
  classical
  exact Finset.prod_pos fun i _ => pow_pos (hr i) _

/-- Reflection of the radii inverts every monomial weight. -/
theorem monoWeight_inv (r : σ → ℝ≥0) (α : σ →₀ ℕ) :
    monoWeight (fun i => (r i)⁻¹) α = (monoWeight r α)⁻¹ := by
  classical
  simp only [monoWeight, Finsupp.prod, inv_pow, Finset.prod_inv_distrib]

/-- The actual Gauss seminorm is nonzero on every nonzero polynomial. -/
theorem trivialWeightedGauss_val_pos {r : σ → ℝ≥0} (hr : ∀ i, 0 < r i)
    {P : MvPolynomial σ B} (hP : P ≠ 0) :
    0 < (trivialWeightedGauss r : Berk k (MvPolynomial σ B)).val P := by
  obtain ⟨α, hα⟩ := Finset.nonempty_iff_ne_empty.mpr
    (mt MvPolynomial.support_eq_empty.mp hP)
  have hα := MvPolynomial.mem_support_iff.mp hα
  have h := le_wgaussValuation (triv : Berk k B).val r P α
  rw [triv_val_of_ne_zero hα, one_mul] at h
  exact (monoWeight_pos hr α).trans_le h

/-- A polynomial and its reflected Gauss norm have product at least one. -/
theorem one_le_trivialWeightedGauss_mul_inv {r : σ → ℝ≥0} (hr : ∀ i, 0 < r i)
    {P : MvPolynomial σ B} (hP : P ≠ 0) :
    1 ≤ (trivialWeightedGauss r : Berk k (MvPolynomial σ B)).val P *
      (trivialWeightedGauss (k := k) (fun i => (r i)⁻¹)).val P := by
  obtain ⟨α, hα⟩ := Finset.nonempty_iff_ne_empty.mpr
    (mt MvPolynomial.support_eq_empty.mp hP)
  have hα := MvPolynomial.mem_support_iff.mp hα
  have h := le_wgaussValuation (triv : Berk k B).val r P α
  have h' := le_wgaussValuation (triv : Berk k B).val (fun i => (r i)⁻¹) P α
  rw [triv_val_of_ne_zero hα, one_mul] at h h'
  calc
    1 = monoWeight r α * monoWeight (fun i => (r i)⁻¹) α := by
      rw [monoWeight_inv, mul_inv_cancel₀ (monoWeight_pos hr α).ne']
    _ ≤ _ := mul_le_mul h h' (by positivity) (by positivity)

/-- Reflected radii bound the sum of the actual polynomial logarithms from below. -/
theorem zero_le_logAbs_trivialWeightedGauss_add_inv {r : σ → ℝ≥0}
    (hr : ∀ i, 0 < r i) {P : MvPolynomial σ B} (hP : P ≠ 0) :
    0 ≤ logAbs P (trivialWeightedGauss r : Berk k (MvPolynomial σ B)) +
      logAbs P (trivialWeightedGauss (k := k) (fun i => (r i)⁻¹)) := by
  have h := one_le_trivialWeightedGauss_mul_inv (k := k) hr hP
  have hlog := ENNReal.log_monotone (show (1 : ℝ≥0∞) ≤
      ((trivialWeightedGauss r : Berk k (MvPolynomial σ B)).val P : ℝ≥0∞) *
        ((trivialWeightedGauss (k := k) (fun i => (r i)⁻¹)).val P : ℝ≥0∞) by
    exact_mod_cast h)
  simpa only [ENNReal.log_one, ENNReal.log_mul_add, logAbs] using hlog

end Berk

namespace FSData

variable {k B σ : Type*} [Field k] [CommRing B] [IsDomain B] [Algebra k B]

/-- Every original affine FS function satisfies the reflected-radius midpoint inequality. -/
theorem two_mul_eval_triv_le_gauss_add_inv (g : FSData k (MvPolynomial σ B))
    {r : σ → ℝ≥0} (hr : ∀ i, 0 < r i) :
    2 * g.eval (Berk.triv : Berk k (MvPolynomial σ B)) ≤
      g.eval (Berk.trivialWeightedGauss (k := k) r) +
        g.eval (Berk.trivialWeightedGauss (k := k) (fun i => (r i)⁻¹)) := by
  classical
  have hterm : ∀ t ∈ g.terms,
      2 * fsTerm t (Berk.triv : Berk k (MvPolynomial σ B)) ≤
        fsTerm t (Berk.trivialWeightedGauss (k := k) r) +
          fsTerm t (Berk.trivialWeightedGauss (k := k) (fun i => (r i)⁻¹)) := by
    intro t ht
    by_cases hf : t.1 = 0
    · rw [fsTerm_eq_bot (g.pos t ht) (by simp [hf]),
        show (2 : EReal) = ((2 : ℝ) : EReal) from rfl,
        EReal.coe_mul_bot_of_pos two_pos]
      exact bot_le
    · have hlog := Berk.zero_le_logAbs_trivialWeightedGauss_add_inv (k := k) hr hf
      have hpos := Berk.trivialWeightedGauss_val_pos (k := k) hr hf
      have hpos' := Berk.trivialWeightedGauss_val_pos (k := k)
        (fun i => inv_pos.mpr (hr i)) hf
      unfold fsTerm
      rw [Berk.logAbs_triv_of_ne_zero hf, mul_zero, zero_add,
        Berk.logAbs_eq_coe_log hpos.ne', Berk.logAbs_eq_coe_log hpos'.ne',
        show (2 : EReal) = ((2 : ℝ) : EReal) from rfl]
      rw [Berk.logAbs_eq_coe_log hpos.ne', Berk.logAbs_eq_coe_log hpos'.ne'] at hlog
      norm_cast at hlog ⊢
      have ha : (0 : ℝ) ≤ t.2.1 := by exact_mod_cast (g.pos t ht).le
      push_cast
      nlinarith [mul_nonneg ha hlog]
  have hb : ∀ y : Berk k (MvPolynomial σ B), ((g.const : ℝ) : EReal) ≤
      max ((g.const : ℝ) : EReal) (g.terms.sup fun t => fsTerm t y) := fun _ => le_max_left _ _
  have hs : ∀ y : Berk k (MvPolynomial σ B), ∀ t ∈ g.terms, fsTerm t y ≤
      max ((g.const : ℝ) : EReal) (g.terms.sup fun t => fsTerm t y) := fun _ _ ht =>
    (Finset.le_sup (f := fun t => fsTerm t _) ht).trans (le_max_right _ _)
  unfold eval
  rcases le_total (g.terms.sup fun t => fsTerm t (Berk.triv : Berk k (MvPolynomial σ B)))
      ((g.const : ℝ) : EReal) with hle | hle
  · rw [max_eq_left hle]
    calc 2 * ((g.const : ℝ) : EReal) =
          ((g.const : ℝ) : EReal) + ((g.const : ℝ) : EReal) := by
            rw [show (2 : EReal) = ((2 : ℝ) : EReal) from rfl,
              ← EReal.coe_mul, ← EReal.coe_add]
            congr 1
            ring
      _ ≤ _ := add_le_add (hb _) (hb _)
  · rw [max_eq_right hle]
    by_cases hne : g.terms.Nonempty
    · obtain ⟨t, ht, hteq⟩ := Finset.exists_mem_eq_sup g.terms hne
        fun t => fsTerm t (Berk.triv : Berk k (MvPolynomial σ B))
      rw [hteq]
      exact (hterm t ht).trans (add_le_add (hs _ t ht) (hs _ t ht))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne] at hle
      simp only [Finset.sup_empty] at hle
      exact absurd hle (not_le.mpr (EReal.bot_lt_coe _))

end FSData

variable {k B σ : Type*} [Field k] [CommRing B] [IsDomain B] [Algebra k B]

/-- Original regularizable functions are finite at every positive-radius weighted Gauss point.
This proves the monomial case without a countability, degree-bound, or finiteness certificate. -/
theorem IsRegularizable.trivialWeightedGauss_ne_bot
    {u : Berk k (MvPolynomial σ B) → EReal} (hu : IsRegularizable u)
    {r : σ → ℝ≥0} (hr : ∀ i, 0 < r i) :
    u (Berk.trivialWeightedGauss (k := k) r) ≠ ⊥ := by
  have htriv := hu.triv_ne_bot
  have htrivtop := hu.triv_ne_top
  obtain ⟨_, g, hanti, hlim⟩ := hu
  set m := (u (Berk.triv : Berk k (MvPolynomial σ B))).toReal with hm
  have hmcoe : (m : EReal) = u Berk.triv := EReal.coe_toReal htrivtop htriv
  set C := (g 0).evalReal (Berk.trivialWeightedGauss (k := k) (fun i => (r i)⁻¹)) with hC
  have key : ∀ j, ((2 * m - C : ℝ) : EReal) ≤
      (g j).eval (Berk.trivialWeightedGauss (k := k) r) := by
    intro j
    have h₁ : (m : EReal) ≤ (g j).eval Berk.triv := by
      rw [hmcoe, hlim]
      exact iInf_le _ j
    have h₂ := (g j).two_mul_eval_triv_le_gauss_add_inv hr
    have h₃ : (g j).eval (Berk.trivialWeightedGauss (k := k) (fun i => (r i)⁻¹)) ≤
        (g 0).eval (Berk.trivialWeightedGauss (k := k) (fun i => (r i)⁻¹)) :=
      hanti _ (Nat.zero_le j)
    rw [← (g j).coe_evalReal Berk.triv] at h₁ h₂
    rw [← (g j).coe_evalReal (Berk.trivialWeightedGauss (k := k) r)] at h₂ ⊢
    rw [← (g j).coe_evalReal (Berk.trivialWeightedGauss (k := k) (fun i => (r i)⁻¹))] at h₂
    rw [← (g j).coe_evalReal (Berk.trivialWeightedGauss (k := k) (fun i => (r i)⁻¹)),
      ← (g 0).coe_evalReal (Berk.trivialWeightedGauss (k := k) (fun i => (r i)⁻¹))] at h₃
    rw [show (2 : EReal) = ((2 : ℝ) : EReal) from rfl,
      ← EReal.coe_mul, ← EReal.coe_add] at h₂
    norm_cast at h₁ h₂ h₃ ⊢
    rw [← hC] at h₃
    linarith
  have hbound : ((2 * m - C : ℝ) : EReal) ≤ u (Berk.trivialWeightedGauss (k := k) r) := by
    rw [hlim]
    exact le_iInf key
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hbound

/-- The upper finite bound at the same actual Gauss point comes from the first FS approximant. -/
theorem IsRegularizable.trivialWeightedGauss_ne_top
    {u : Berk k (MvPolynomial σ B) → EReal} (hu : IsRegularizable u)
    (r : σ → ℝ≥0) : u (Berk.trivialWeightedGauss (k := k) r) ≠ ⊤ := by
  obtain ⟨_, g, _, hlim⟩ := hu
  rw [hlim]
  exact ne_top_of_le_ne_top ((g 0).eval_ne_top _) (iInf_le _ 0)

/-- Finiteness also holds at the images of actual Gauss points under every dominant
morphism from a finite-type polynomial algebra. Dominance supplies the nontrivial pullback. -/
theorem IsRegularizable.comap_trivialWeightedGauss_ne_bot
    {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k (MvPolynomial σ B)]
    {u : Berk k A → EReal} (hu : IsRegularizable u)
    (φ : A →ₐ[k] MvPolynomial σ B) (hφ : Function.Injective φ)
    {r : σ → ℝ≥0} (hr : ∀ i, 0 < r i) :
    u (Berk.comap φ (Berk.trivialWeightedGauss r)) ≠ ⊥ := by
  have heq : Berk.comap φ (Berk.triv : Berk k (MvPolynomial σ B)) = Berk.triv := by
    apply Berk.ext
    apply Valuation.ext
    intro f
    by_cases hf : f = 0
    · simp [hf]
    · rw [Berk.comap_val_apply, Berk.triv_val_of_ne_zero hf,
        Berk.triv_val_of_ne_zero (map_ne_zero_iff φ hφ |>.mpr hf)]
  have hpull := hu.comp_comap φ ⟨Berk.triv, by rw [heq]; exact hu.triv_ne_bot⟩
  exact hpull.trivialWeightedGauss_ne_bot hr

end EnvelopeProperty
