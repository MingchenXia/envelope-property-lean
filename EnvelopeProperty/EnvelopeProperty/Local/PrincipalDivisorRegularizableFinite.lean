/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.GaussRegularizableFinite
import EnvelopeProperty.Global.Divisorial

/-!
# Actual polynomial principal-divisor orders and regularizable finiteness

The genuine principal-prime DVR order is bounded by the original polynomial total degree.
Expanding weighted Gauss points then supply a reflected midpoint and finiteness without
Wu regularization, countability, or a supplied linear-growth/finiteness certificate.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open MvPolynomial IsDiscreteValuationRing

section PolynomialDegree

variable {k σ : Type*} [Field k]

private theorem totalDegree_pow_eq {p : MvPolynomial σ k} (hp : p ≠ 0) (m : ℕ) :
    (p ^ m).totalDegree = m * p.totalDegree := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, totalDegree_mul_of_isDomain (pow_ne_zero _ hp) hp, ih]
    ring

/-- Positive polynomial degree bounds every exponent of a power dividing a nonzero polynomial. -/
theorem pow_dvd_exponent_le_totalDegree {p f : MvPolynomial σ k}
    (hp : 0 < p.totalDegree) (hf : f ≠ 0) {m : ℕ} (hdiv : p ^ m ∣ f) :
    m ≤ f.totalDegree := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have h := totalDegree_le_of_dvd_of_isDomain hdiv hf
  rw [totalDegree_pow_eq hp0] at h
  nlinarith

/-- The largest actual polynomial prime power factor exists by the degree bound. -/
theorem exists_eq_prime_pow_mul_not_dvd {p f : MvPolynomial σ k}
    (hp : 0 < p.totalDegree) (hf : f ≠ 0) :
    ∃ (m : ℕ) (g : MvPolynomial σ k), f = p ^ m * g ∧ ¬ p ∣ g := by
  have hfinite : FiniteMultiplicity p f :=
    ⟨f.totalDegree + 1, fun h => by
      have := pow_dvd_exponent_le_totalDegree hp hf h
      omega⟩
  obtain ⟨g, hg, hnot⟩ := hfinite.exists_eq_pow_mul_and_not_dvd
  exact ⟨_, g, hg, hnot⟩

/-- A prime polynomial over a field has positive total degree. -/
theorem totalDegree_pos_of_prime {p : MvPolynomial σ k} (hp : Prime p) :
    0 < p.totalDegree := by
  by_contra h
  have heq := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_not_pos h)
  have hc : p.coeff 0 ≠ 0 := by
    intro hc
    exact hp.ne_zero (by rw [heq, hc, map_zero])
  apply hp.not_isUnit
  rw [heq]
  exact (isUnit_iff_ne_zero.mpr hc).map C

end PolynomialDegree

section PolynomialPrimeDVR

variable {k σ : Type*} [Field k] [Finite σ]

/-- The genuine principal-prime localization, embedded in the original fraction field. -/
def polynomialPrimeDVR (p : MvPolynomial σ k) (hp : Prime p) :
    BirationalDVR k (MvPolynomial σ k) := by
  letI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  exact {
    ring := atPrimeRange (P := Ideal.span {p})
      (IsScalarTower.toAlgHom k _ (FractionRing (MvPolynomial σ k)))
      (IsFractionRing.injective _ _)
    isDVR := isDiscreteValuationRing_atPrimeRange _ _ rfl hp.ne_zero
    essFiniteType := essFiniteType_atPrimeRange _ _
    algebraMap_mem f := mem_atPrimeRange _ _ f }

/-- Actual normalized order in the polynomial principal-prime DVR is at most total degree. -/
theorem polynomialPrimeDVR_ord_le_totalDegree {p f : MvPolynomial σ k}
    (hp : Prime p) (hf : f ≠ 0) :
    (polynomialPrimeDVR p hp).ord f ≤ (f.totalDegree : ℕ∞) := by
  have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have : IsDiscreteValuationRing (atPrimeRange (P := Ideal.span {p})
      (IsScalarTower.toAlgHom k _ (FractionRing (MvPolynomial σ k)))
      (IsFractionRing.injective _ _)) := (polynomialPrimeDVR p hp).isDVR
  obtain ⟨m, g, heq, hg⟩ := exists_eq_prime_pow_mul_not_dvd (totalDegree_pos_of_prime hp) hf
  have hm : m ≤ f.totalDegree :=
    pow_dvd_exponent_le_totalDegree (totalDegree_pos_of_prime hp) hf ⟨g, heq⟩
  have hord : (polynomialPrimeDVR p hp).ord f = m := by
    rw [heq]
    exact addVal_atPrimeRange _ _ rfl hp.ne_zero m hg
  rw [hord]
  exact_mod_cast hm

end PolynomialPrimeDVR

namespace Berk

variable {k σ : Type*} [Field k]

/-- The original weighted Gauss monomial product at constant radii is the radius to total size. -/
theorem monoWeight_const (R : ℝ≥0) (α : σ →₀ ℕ) :
    monoWeight (fun _ : σ => R) α = R ^ (α.sum fun _ n => n) := by
  classical
  exact Finset.prod_pow_eq_pow_sum _ _ R

/-- Expanding Gauss norms compute the actual polynomial total degree. -/
theorem trivialWeightedGauss_const_val {R : ℝ≥0} (hR : 1 ≤ R)
    {f : MvPolynomial σ k} (hf : f ≠ 0) :
    (trivialWeightedGauss (k := k) (fun _ : σ => R)).val f = R ^ f.totalDegree := by
  classical
  obtain ⟨α, hα, heq⟩ := Finset.exists_mem_eq_sup f.support
    (Finset.nonempty_iff_ne_empty.mpr (mt support_eq_empty.mp hf))
    (fun α => α.sum fun _ n => n)
  have hdegree : f.totalDegree = α.sum fun _ n => n := heq
  rw [trivialWeightedGauss_val, wgaussValuation_apply]
  refine le_antisymm (Finset.sup_le fun β hβ => ?_) ?_
  · rw [triv_val_of_ne_zero (mem_support_iff.mp hβ), one_mul, monoWeight_const]
    exact pow_le_pow_right₀ hR (le_totalDegree hβ)
  · have h := le_wgaussValuation (triv : Berk k k).val (fun _ : σ => R) f α
    rw [triv_val_of_ne_zero (mem_support_iff.mp hα), one_mul, monoWeight_const,
      ← hdegree] at h
    exact h

variable [Finite σ]

/-- The actual principal-divisor point of the polynomial affine space. -/
def polynomialPrimePoint (p : MvPolynomial σ k) (hp : Prime p) (c : ℝ) (hc : 0 < c) :
    Berk k (MvPolynomial σ k) :=
  (polynomialPrimeDVR p hp).berkPoint (expNeg c) (ProjBerk.expNeg_le_one hc.le)

/-- The genuine principal-divisor norm and a single expanding Gauss norm have product
at least one on every nonzero polynomial. -/
theorem one_le_polynomialPrimePoint_mul_gauss {p f : MvPolynomial σ k}
    (hp : Prime p) {c : ℝ} (hc : 0 < c) (hf : f ≠ 0) :
    1 ≤ (polynomialPrimePoint p hp c hc).val f *
      (trivialWeightedGauss (k := k) (fun _ : σ => (expNeg c)⁻¹)).val f := by
  have hq : 0 < expNeg c := by
    change (0 : ℝ) < Real.exp (-c)
    exact Real.exp_pos _
  have hR : 1 ≤ (expNeg c)⁻¹ := (one_le_inv₀ hq).mpr (ProjBerk.expNeg_le_one hc.le)
  have hlo : expNeg c ^ f.totalDegree ≤ (polynomialPrimePoint p hp c hc).val f := by
    have h := expOrd_antitone (ProjBerk.expNeg_le_one hc.le)
      (polynomialPrimeDVR_ord_le_totalDegree hp hf)
    simpa only [polynomialPrimePoint, BirationalDVR.berkPoint_val, expOrd_coe] using h
  rw [trivialWeightedGauss_const_val hR hf]
  calc
    1 = expNeg c ^ f.totalDegree * (expNeg c)⁻¹ ^ f.totalDegree := by
      rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hq.ne')]
    _ ≤ _ := mul_le_mul_of_nonneg_right hlo (by positivity)

/-- The original polynomial logarithms satisfy the genuine principal-divisor/Gauss
reflection inequality. -/
theorem zero_le_polynomialPrimePoint_logAbs_add_gauss {p f : MvPolynomial σ k}
    (hp : Prime p) {c : ℝ} (hc : 0 < c) (hf : f ≠ 0) :
    0 ≤ logAbs f (polynomialPrimePoint p hp c hc) +
      logAbs f (trivialWeightedGauss (k := k) (fun _ : σ => (expNeg c)⁻¹)) := by
  have h := one_le_polynomialPrimePoint_mul_gauss hp hc hf
  have hlog := ENNReal.log_monotone (show (1 : ℝ≥0∞) ≤
      ((polynomialPrimePoint p hp c hc).val f : ℝ≥0∞) *
        ((trivialWeightedGauss (k := k) (fun _ : σ => (expNeg c)⁻¹)).val f : ℝ≥0∞) by
    exact_mod_cast h)
  simpa only [ENNReal.log_one, ENNReal.log_mul_add, logAbs] using hlog

end Berk

namespace FSData

variable {k A : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]

/-- A polynomial logarithm reflection inequality passes to every actual affine FS maximum. -/
theorem two_mul_eval_triv_le_of_logAbs_pair (g : FSData k A) {x y : Berk k A}
    (hpair : ∀ f : A, f ≠ 0 → 0 ≤ Berk.logAbs f x + Berk.logAbs f y) :
    2 * g.eval Berk.triv ≤ g.eval x + g.eval y := by
  classical
  have hterm : ∀ t ∈ g.terms, 2 * fsTerm t (Berk.triv : Berk k A) ≤
      fsTerm t x + fsTerm t y := by
    intro t ht
    by_cases hf : t.1 = 0
    · rw [fsTerm_eq_bot (g.pos t ht) (by simp [hf]),
        show (2 : EReal) = ((2 : ℝ) : EReal) from rfl,
        EReal.coe_mul_bot_of_pos two_pos]
      exact bot_le
    · have hlog := hpair t.1 hf
      have hx : x.val t.1 ≠ 0 := by
        intro h
        rw [(Berk.logAbs_eq_bot_iff _ _).mpr h, EReal.bot_add] at hlog
        exact EReal.bot_ne_zero (bot_unique hlog).symm
      have hy : y.val t.1 ≠ 0 := by
        intro h
        rw [(Berk.logAbs_eq_bot_iff _ _).mpr h, EReal.add_bot] at hlog
        exact EReal.bot_ne_zero (bot_unique hlog).symm
      unfold fsTerm
      rw [Berk.logAbs_triv_of_ne_zero hf, mul_zero, zero_add,
        Berk.logAbs_eq_coe_log hx, Berk.logAbs_eq_coe_log hy,
        show (2 : EReal) = ((2 : ℝ) : EReal) from rfl]
      rw [Berk.logAbs_eq_coe_log hx, Berk.logAbs_eq_coe_log hy] at hlog
      norm_cast at hlog ⊢
      have ha : (0 : ℝ) ≤ t.2.1 := by exact_mod_cast (g.pos t ht).le
      push_cast
      nlinarith [mul_nonneg ha hlog]
  have hb : ∀ z : Berk k A, ((g.const : ℝ) : EReal) ≤
      max ((g.const : ℝ) : EReal) (g.terms.sup fun t => fsTerm t z) := fun _ => le_max_left _ _
  have hs : ∀ z : Berk k A, ∀ t ∈ g.terms, fsTerm t z ≤
      max ((g.const : ℝ) : EReal) (g.terms.sup fun t => fsTerm t z) := fun _ _ ht =>
    (Finset.le_sup (f := fun t => fsTerm t _) ht).trans (le_max_right _ _)
  unfold eval
  rcases le_total (g.terms.sup fun t => fsTerm t (Berk.triv : Berk k A))
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
        fun t => fsTerm t (Berk.triv : Berk k A)
      rw [hteq]
      exact (hterm t ht).trans (add_le_add (hs _ t ht) (hs _ t ht))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne] at hle
      simp only [Finset.sup_empty] at hle
      exact absurd hle (not_le.mpr (EReal.bot_lt_coe _))

end FSData

/-- The actual logarithmic reflection inequality gives a uniform lower bound along the
original decreasing FS sequence. -/
theorem IsRegularizable.ne_bot_of_logAbs_pair {k A : Type*} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] {u : Berk k A → EReal} (hu : IsRegularizable u)
    {x y : Berk k A} (hpair : ∀ f : A, f ≠ 0 → 0 ≤ Berk.logAbs f x + Berk.logAbs f y) :
    u x ≠ ⊥ := by
  have htriv := hu.triv_ne_bot
  have htop := hu.triv_ne_top
  obtain ⟨_, g, hanti, hlim⟩ := hu
  set m := (u (Berk.triv : Berk k A)).toReal with hm
  have hmcoe : (m : EReal) = u Berk.triv := EReal.coe_toReal htop htriv
  set C := (g 0).evalReal y with hC
  have key : ∀ j, ((2 * m - C : ℝ) : EReal) ≤ (g j).eval x := by
    intro j
    have h₁ : (m : EReal) ≤ (g j).eval Berk.triv := by
      rw [hmcoe, hlim]
      exact iInf_le _ j
    have h₂ := (g j).two_mul_eval_triv_le_of_logAbs_pair hpair
    have h₃ : (g j).eval y ≤ (g 0).eval y := hanti _ (Nat.zero_le j)
    rw [← (g j).coe_evalReal Berk.triv] at h₁ h₂
    rw [← (g j).coe_evalReal x] at h₂ ⊢
    rw [← (g j).coe_evalReal y] at h₂ h₃
    rw [← (g 0).coe_evalReal y, ← hC] at h₃
    rw [show (2 : EReal) = ((2 : ℝ) : EReal) from rfl,
      ← EReal.coe_mul, ← EReal.coe_add] at h₂
    norm_cast at h₁ h₂ h₃ ⊢
    linarith
  have hbound : ((2 * m - C : ℝ) : EReal) ≤ u x := by
    rw [hlim]
    exact le_iInf key
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hbound

/-- FHX regularizable finiteness at every genuine principal-divisor valuation of affine space.
The degree and reflection inequalities are produced internally from the prime polynomial. -/
theorem IsRegularizable.polynomialPrimePoint_ne_bot {k σ : Type*} [Field k] [Finite σ]
    {u : Berk k (MvPolynomial σ k) → EReal} (hu : IsRegularizable u)
    {p : MvPolynomial σ k} (hp : Prime p) {c : ℝ} (hc : 0 < c) :
    u (Berk.polynomialPrimePoint p hp c hc) ≠ ⊥ :=
  hu.ne_bot_of_logAbs_pair (fun _ hf =>
    Berk.zero_le_polynomialPrimePoint_logAbs_add_gauss hp hc hf)

end EnvelopeProperty
