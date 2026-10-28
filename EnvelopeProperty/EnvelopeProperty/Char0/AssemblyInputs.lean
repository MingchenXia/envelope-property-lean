/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.BergmanFinite
import EnvelopeProperty.Projective.Divisorial

/-!
# The analytic inputs of the characteristic-zero assembly

The characteristic-zero proof of Fang–Han–Xia, *The envelope property for unibranch projective
varieties*, Theorem 3.1 on `ℙⁿ` (blueprint chapter `char0.tex`, `thm:c0-pn-ep`) uses two analytic
results over `ℂ`:

* the **valuative bound** `prop:c0-valuative-bound` and its corollary `cor:c0-valuative-upper`
  (analytic lower bounds give valuative upper bounds), proved in coordinates at a general point of
  the divisor of a divisorial valuation ring;
* the **Bergman lower bound** `cor:c0-bergman-lower` (finitely many square integrable polynomials
  dominating a fractional power `|g|^c`), obtained from the Ohsawa–Takegoshi theorem at a point and
  Hörmander's `L²` estimate (`prop:c0-l2-extension`).

This file states them, literally as in the blueprint, as the `Prop`-valued structures
`EnvelopeProperty.Char0.ValuativeUpperBound` and `EnvelopeProperty.Char0.BergmanLowerBound`. The
assembly (`EnvelopeProperty.Projective.EnvelopeChar0`) takes them as explicit hypotheses; they are
not axioms and no instance of them is declared here.

## Conventions (`conv:c0`)

Coordinates on `ℂ^{n+2}` are `z : Fin (n + 2) → ℂ` with `t = z 0` and `x_i = z i.succ`
(`EnvelopeProperty.Char0.xWeightFin`, `EnvelopeProperty.Char0.tWeightFin`), with Lebesgue measure
`volume`. A finite family `g = (g_j)` of polynomials is a function `g : ι → MvPolynomial _ ℂ` on a
finite type `ι`, `|g|² = normSqFam g = ∑_j |g_j|²`, and `ord_V(g) = min_j ord_V(g_j)` is
`⨅ j, V.ord (g j)`. A divisorial valuation ring over `ℂ` in `N = n + 2` variables
(`def:c0-dvr`) is a `BirationalDVR ℂ (MvPolynomial (Fin (n + 2)) ℂ)`.

## Main definitions

* `EnvelopeProperty.Char0.IsSqIntegrableAgainst f g c`: `f` is square integrable against
  `|g|^{-2c}`, i.e. `∫_K |f|² |g|^{-2c} dλ < ∞` for every compact `K` (`conv:c0`).
* `EnvelopeProperty.Char0.ValuativeUpperBound`: `prop:c0-valuative-bound` and
  `cor:c0-valuative-upper`.
* `EnvelopeProperty.Char0.BergmanLowerBound`: `cor:c0-bergman-lower`.

## Main results

* `EnvelopeProperty.Char0.ValuativeUpperBound.of_valuative_bound`: the field `valuative_upper`
  (`cor:c0-valuative-upper`) follows from the field `valuative_bound` (`prop:c0-valuative-bound`),
  by the blueprint proof of the corollary (`valuativeUpper_isSqIntegrableAgainst_pow`,
  `valuativeUpper_exists_ne_zero`, `valuativeUpper_nsmul_le_nsmul`). So a `ValuativeUpperBound`
  only requires `prop:c0-valuative-bound`.

## Implementation notes

* The constant `A(V) = 1 + ord_V(Jac_V)` of `prop:c0-valuative-bound` depends only on `V` (and on
  the coordinates chosen at `V`, `lem:c0-dvr-jacobian`); the structure only records that some real
  constant depending only on `V` works, which is what the assembly uses.
* In `IsSqIntegrableAgainst`, `|g|^{-2c}` is the real power `(∑_j |g_j|²)^{-c}`, which is `0` on the
  zero set `Z(g)` of `g`. Since `Z(g)` is Lebesgue-null when some `g_j ≠ 0`
  (`EnvelopeProperty.Char0.volume_normSqFam_eq_zero`), this agrees with the blueprint's convention
  (the integrand `|f|²|g|^{-2c}` is `+∞` on `Z(g) \ Z(f)`) up to a null set.
* All three statements are made for `N = n + 2` variables and every `n ≥ 0` (the blueprint's
  standing assumption `n ≥ 1` of `conv:c0` plays no role in these nodes).
-/

open scoped NNReal ENNReal

open MeasureTheory

noncomputable section

namespace EnvelopeProperty.Char0

/-- **Square integrability against `|g|^{-2c}`** (`conv:c0`): `∫_K |f|² |g|^{-2c} dλ < ∞` for every
compact `K ⊆ ℂ^{n+2}`, where `|g|² = ∑_j |g_j|²` (`normSqFam`). -/
def IsSqIntegrableAgainst {n : ℕ} {ι : Type*} [Fintype ι] (f : MvPolynomial (Fin (n + 2)) ℂ)
    (g : ι → MvPolynomial (Fin (n + 2)) ℂ) (c : ℝ) : Prop :=
  ∀ K : Set (Fin (n + 2) → ℂ), IsCompact K →
    ∫⁻ z in K, ENNReal.ofReal (normSqFam g z ^ (-c)) * ‖MvPolynomial.eval z f‖ₑ ^ 2 < ⊤

/-- **The valuative input** of the characteristic-zero assembly (`char0.tex`):

* `valuative_bound` (`prop:c0-valuative-bound`): for every divisorial valuation ring `V` over `ℂ`
  in `n + 2` variables there is a constant `A = A(V)` such that
  `ord_V(f) > c ord_V(g) - A` whenever `g = (g_j)` is a family of polynomials, not all zero,
  `c > 0`, and the polynomial `f` is square integrable against `|g|^{-2c}`;
* `valuative_upper` (`cor:c0-valuative-upper`): if `P = (P_i)` and `G = (G_j)` are polynomials,
  `G` not all zero, `a, b ∈ ℤ_{>0}`, and for every compact `K` there is `c_K > 0` with
  `|P|^b ≥ c_K |G|^a` on `K`, then `b ord_V(P) ≤ a ord_V(G)` for every divisorial valuation ring
  `V` over `ℂ` in `n + 2` variables. -/
structure ValuativeUpperBound : Prop where
  /-- `prop:c0-valuative-bound`. -/
  valuative_bound : ∀ (n : ℕ) (V : BirationalDVR ℂ (MvPolynomial (Fin (n + 2)) ℂ)), ∃ A : ℝ,
    ∀ (ι : Type) [Fintype ι] (g : ι → MvPolynomial (Fin (n + 2)) ℂ), (∃ j, g j ≠ 0) →
      ∀ c : ℝ, 0 < c → ∀ f : MvPolynomial (Fin (n + 2)) ℂ, IsSqIntegrableAgainst f g c →
        (c : EReal) * ((⨅ j, V.ord (g j) : ℕ∞) : EReal) - (A : EReal) < (V.ord f : EReal)
  /-- `cor:c0-valuative-upper`. -/
  valuative_upper : ∀ (n : ℕ) (ι κ : Type) [Fintype ι] [Fintype κ]
    (P : ι → MvPolynomial (Fin (n + 2)) ℂ) (G : κ → MvPolynomial (Fin (n + 2)) ℂ),
      (∃ j, G j ≠ 0) → ∀ a b : ℕ, 0 < a → 0 < b →
      (∀ K : Set (Fin (n + 2) → ℂ), IsCompact K → ∃ cK : ℝ, 0 < cK ∧ ∀ y ∈ K,
        cK * Real.sqrt (normSqFam G y) ^ a ≤ Real.sqrt (normSqFam P y) ^ b) →
      ∀ V : BirationalDVR ℂ (MvPolynomial (Fin (n + 2)) ℂ),
        b • (⨅ i, V.ord (P i)) ≤ a • (⨅ j, V.ord (G j))

/-- **The Bergman input** of the characteristic-zero assembly (`cor:c0-bergman-lower`, Demailly's
lower bound for Bergman kernels): let `g = (g_j)` be bihomogeneous polynomials of `x`-degree `D`
(`IsXTBihomogeneous`), not all zero, and `c > 0`. There are finitely many `x`-homogeneous
polynomials `P_1, …, P_r` of `x`-degree `≤ c D + 2`, each square integrable against `|g|^{-2c}`,
such that for every compact `K` there is `c_K > 0` with `|P| ≥ c_K |g|^c` on `K`, where
`|P| = (∑_k |P_k|²)^{1/2}` and `|g|^c = (normSqFam g)^{c/2}`.

The conclusion has the form of the conclusion of
`EnvelopeProperty.Char0.exists_homogeneous_lower_bound`, with the membership
`P ∈ bergmanSpace ω (c D + 2) B` replaced by the two properties of the blueprint statement that it
implies (the bound on the `x`-degree and square integrability against `|g|^{-2c}`, see
`EnvelopeProperty.Char0.setLIntegral_le_wNormSq`). -/
structure BergmanLowerBound : Prop where
  /-- `cor:c0-bergman-lower`. -/
  exists_lower_bound : ∀ (n : ℕ) (ι : Type) [Fintype ι] (g : ι → MvPolynomial (Fin (n + 2)) ℂ)
    (D : ℕ), (∀ j, ∃ l, IsXTBihomogeneous D l (g j)) → (∃ j, g j ≠ 0) → ∀ c : ℝ, 0 < c →
      ∃ s : Finset (MvPolynomial (Fin (n + 2)) ℂ),
        (∀ P ∈ s, (∀ m ∈ P.support, ((∑ i : Fin (n + 1), m i.succ : ℕ) : ℝ) ≤ c * D + 2) ∧
          IsSqIntegrableAgainst P g c ∧ ∃ e : ℕ, P.IsWeightedHomogeneous xWeightFin e) ∧
        ∀ K : Set (Fin (n + 2) → ℂ), IsCompact K → ∃ cK : ℝ, 0 < cK ∧ ∀ y ∈ K,
          cK * normSqFam g y ^ (c / 2) ≤ Real.sqrt (∑ P ∈ s, ‖MvPolynomial.eval y P‖ ^ 2)

/-! ### `cor:c0-valuative-upper` from `prop:c0-valuative-bound`

The field `ValuativeUpperBound.valuative_upper` is a consequence of the field
`ValuativeUpperBound.valuative_bound`, by the proof of `cor:c0-valuative-upper`; we record this as
`ValuativeUpperBound.of_valuative_bound`, so that only `prop:c0-valuative-bound` has to be
supplied. -/

section OfValuativeBound

variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] {P : ι → MvPolynomial (Fin (n + 2)) ℂ}
  {G : κ → MvPolynomial (Fin (n + 2)) ℂ}

/-- The pointwise estimate of `cor:c0-valuative-upper`: if `c_K |G|^a ≤ |P|^b`, then
`|G_j|^{2aℓ} |P|^{-2bℓ} ≤ c_K^{-2ℓ}` (the left side is `0` where `P = 0`). -/
theorem valuativeUpper_rpow_neg_mul_le {a b ℓ : ℕ} (hb : 0 < b) (hℓ : 0 < ℓ) {cK : ℝ} (hcK : 0 < cK)
    {y : Fin (n + 2) → ℂ}
    (hy : cK * Real.sqrt (normSqFam G y) ^ a ≤ Real.sqrt (normSqFam P y) ^ b) (j : κ) :
    normSqFam P y ^ (-(((b * ℓ : ℕ) : ℝ))) * ‖MvPolynomial.eval y (G j ^ (a * ℓ))‖ ^ 2 ≤
      ((cK ^ 2)⁻¹) ^ ℓ := by
  have hNP := normSqFam_nonneg P y
  have hNG := normSqFam_nonneg G y
  have hbl : (((b * ℓ : ℕ) : ℝ)) ≠ 0 := by positivity
  rcases hNP.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (neg_ne_zero.2 hbl), zero_mul]
    positivity
  -- `‖G_j‖² ≤ |G|²` and `c_K² |G|^{2a} ≤ |P|^{2b}`
  have hGj : ‖MvPolynomial.eval y (G j)‖ ^ 2 ≤ normSqFam G y :=
    Finset.single_le_sum (f := fun j => ‖MvPolynomial.eval y (G j)‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ j)
  have hsq : cK ^ 2 * normSqFam G y ^ a ≤ normSqFam P y ^ b := by
    have h2 := pow_le_pow_left₀ (by positivity) hy 2
    rwa [mul_pow, ← pow_mul, ← pow_mul, mul_comm a 2, mul_comm b 2, pow_mul, pow_mul,
      Real.sq_sqrt hNG, Real.sq_sqrt hNP] at h2
  have hc2 : 0 < cK ^ 2 := by positivity
  rw [Real.rpow_neg hNP, Real.rpow_natCast, map_pow, norm_pow, ← pow_mul, mul_comm (a * ℓ) 2,
    pow_mul, inv_mul_le_iff₀ (by positivity)]
  calc ‖MvPolynomial.eval y (G j)‖ ^ (2 * (a * ℓ))
      = (‖MvPolynomial.eval y (G j)‖ ^ 2) ^ (a * ℓ) := pow_mul _ _ _
    _ ≤ normSqFam G y ^ (a * ℓ) := pow_le_pow_left₀ (by positivity) hGj _
    _ = (normSqFam G y ^ a) ^ ℓ := pow_mul _ _ _
    _ ≤ ((cK ^ 2)⁻¹ * normSqFam P y ^ b) ^ ℓ := by
        refine pow_le_pow_left₀ (by positivity) ?_ _
        rw [le_inv_mul_iff₀ hc2]
        exact hsq
    _ = (normSqFam P y ^ b) ^ ℓ * ((cK ^ 2)⁻¹) ^ ℓ := by
        rw [mul_pow, mul_comm]

/-- In `cor:c0-valuative-upper`, `f = G_j^{aℓ}` is square integrable against `|P|^{-2bℓ}`. -/
theorem valuativeUpper_isSqIntegrableAgainst_pow {a b ℓ : ℕ} (hb : 0 < b) (hℓ : 0 < ℓ)
    (hK : ∀ K : Set (Fin (n + 2) → ℂ), IsCompact K → ∃ cK : ℝ, 0 < cK ∧ ∀ y ∈ K,
      cK * Real.sqrt (normSqFam G y) ^ a ≤ Real.sqrt (normSqFam P y) ^ b) (j : κ) :
    IsSqIntegrableAgainst (G j ^ (a * ℓ)) P ((b * ℓ : ℕ) : ℝ) := by
  intro K hKc
  obtain ⟨cK, hcK, hy⟩ := hK K hKc
  calc ∫⁻ z in K, ENNReal.ofReal (normSqFam P z ^ (-(((b * ℓ : ℕ) : ℝ)))) *
        ‖MvPolynomial.eval z (G j ^ (a * ℓ))‖ₑ ^ 2
      ≤ ∫⁻ _ in K, ENNReal.ofReal (((cK ^ 2)⁻¹) ^ ℓ) := by
        refine setLIntegral_mono measurable_const fun z hz => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
          ← ENNReal.ofReal_mul (Real.rpow_nonneg (normSqFam_nonneg P z) _)]
        exact ENNReal.ofReal_le_ofReal (valuativeUpper_rpow_neg_mul_le hb hℓ hcK (hy z hz) j)
    _ = ENNReal.ofReal (((cK ^ 2)⁻¹) ^ ℓ) * volume K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKc.measure_lt_top

/-- In `cor:c0-valuative-upper`, `P` is not identically zero. -/
theorem valuativeUpper_exists_ne_zero {a b : ℕ} (hb : 0 < b) (hG : ∃ j, G j ≠ 0)
    (hK : ∀ K : Set (Fin (n + 2) → ℂ), IsCompact K → ∃ cK : ℝ, 0 < cK ∧ ∀ y ∈ K,
      cK * Real.sqrt (normSqFam G y) ^ a ≤ Real.sqrt (normSqFam P y) ^ b) : ∃ i, P i ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := hG
  refine hj (MvPolynomial.funext fun y => ?_)
  obtain ⟨cK, hcK, hy⟩ := hK {y} isCompact_singleton
  have hP0 : normSqFam P y = 0 := by simp [normSqFam, h]
  have h1 := hy y rfl
  rw [hP0, Real.sqrt_zero, zero_pow hb.ne'] at h1
  have h2 : Real.sqrt (normSqFam G y) ^ a = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right h1 hcK) (by positivity)
  have h3 : normSqFam G y = 0 := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp at h2
    · exact (Real.sqrt_eq_zero'.1 ((pow_eq_zero_iff ha).1 h2)).antisymm
        (normSqFam_nonneg G y)
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h3 j
    (Finset.mem_univ j)
  simpa using h4

/-- The archimedean step of `cor:c0-valuative-upper`: `b ℓ p - A < a ℓ g` for all `ℓ ≥ 1` gives
`b p ≤ a g`. -/
theorem valuativeUpper_nsmul_le_nsmul {a b : ℕ} {oP oG : ℕ∞} (hoG : oG ≠ ⊤) {A : ℝ}
    (h : ∀ ℓ : ℕ, 0 < ℓ →
      ((((b * ℓ : ℕ) : ℝ)) : EReal) * (oP : EReal) - (A : EReal) < (((a * ℓ) • oG : ℕ∞) : EReal)) :
    b • oP ≤ a • oG := by
  obtain ⟨g, rfl⟩ := ENat.ne_top_iff_exists.1 hoG
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have hcast : ∀ N : ℕ, ((N : ℕ∞) : EReal) = ((N : ℝ) : EReal) := fun N => by norm_cast
  have hsmul : ∀ ℓ : ℕ, (((a * ℓ) • (g : ℕ∞) : ℕ∞) : EReal) = (((a * ℓ * g : ℕ) : ℝ) : EReal) :=
    fun ℓ => by rw [nsmul_eq_mul, ← Nat.cast_mul, hcast]
  induction oP using ENat.recTopCoe with
  | top =>
    exfalso
    have h1 := h 1 one_pos
    rw [hsmul, show (((⊤ : ℕ∞)) : EReal) = ⊤ by simp,
      EReal.coe_mul_top_of_pos (by positivity), EReal.top_sub_coe] at h1
    exact not_top_lt h1
  | coe p =>
    rw [nsmul_eq_mul, nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_le]
    by_contra hlt
    push Not at hlt
    obtain ⟨ℓ, hℓ⟩ := exists_nat_gt (max A 0)
    have hℓ0 : 0 < ℓ := by exact_mod_cast (le_max_right A 0).trans_lt hℓ
    have hAℓ : A < ℓ := (le_max_left A 0).trans_lt hℓ
    have h2 := h ℓ hℓ0
    rw [hcast, hsmul, ← EReal.coe_mul, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at h2
    push_cast at h2
    have h3 : (a * g : ℝ) + 1 ≤ b * p := by exact_mod_cast hlt
    have h4 : (ℓ : ℝ) * (a * g + 1) ≤ ℓ * (b * p) :=
      mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg ℓ)
    nlinarith

/-- **`cor:c0-valuative-upper` from `prop:c0-valuative-bound`**: the valuative bound alone yields a
`ValuativeUpperBound`. For `j₀` with `ord_V(G_{j₀}) = ord_V(G)` and `ℓ ≥ 1`, the polynomial
`f = G_{j₀}^{aℓ}` is square integrable against `|P|^{-2bℓ}`, so
`a ℓ ord_V(G) > b ℓ ord_V(P) - A(V)`; let `ℓ → ∞`. -/
theorem ValuativeUpperBound.of_valuative_bound
    (h : ∀ (n : ℕ) (V : BirationalDVR ℂ (MvPolynomial (Fin (n + 2)) ℂ)), ∃ A : ℝ,
      ∀ (ι : Type) [Fintype ι] (g : ι → MvPolynomial (Fin (n + 2)) ℂ), (∃ j, g j ≠ 0) →
        ∀ c : ℝ, 0 < c → ∀ f : MvPolynomial (Fin (n + 2)) ℂ, IsSqIntegrableAgainst f g c →
          (c : EReal) * ((⨅ j, V.ord (g j) : ℕ∞) : EReal) - (A : EReal) < (V.ord f : EReal)) :
    ValuativeUpperBound where
  valuative_bound := h
  valuative_upper := by
    intro n ι κ _ _ P G hG a b _ hb hK V
    obtain ⟨A, hA⟩ := h n V
    have : Nonempty κ := let ⟨j, _⟩ := hG; ⟨j⟩
    obtain ⟨j₀, hj₀⟩ := ciInf_mem (fun j => V.ord (G j))
    simp only at hj₀
    have hoG : (⨅ j, V.ord (G j)) ≠ ⊤ := by
      obtain ⟨j, hj⟩ := hG
      exact ne_top_of_le_ne_top (V.ord_eq_top_iff.not.2 hj) (iInf_le _ j)
    have hP := valuativeUpper_exists_ne_zero hb hG hK
    refine valuativeUpper_nsmul_le_nsmul hoG (A := A) fun ℓ hℓ => ?_
    have h' := hA ι P hP _ (by positivity) _ (valuativeUpper_isSqIntegrableAgainst_pow hb hℓ hK j₀)
    rwa [V.ord_pow, hj₀] at h'

end OfValuativeBound

end EnvelopeProperty.Char0
