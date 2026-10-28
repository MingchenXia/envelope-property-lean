/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.CompactificationDivisibility
import EnvelopeProperty.Projective.EnvelopeCriterion
import EnvelopeProperty.Projective.Order

/-!
# The counterexample of FHX Remark 7.3 on the projective line

This file implements the blueprint chapter `remark-7-3-projective-line.tex`
(`prop:r73-p1-example`) of the formalization of Fang–Han–Xia, *The envelope property for unibranch
projective varieties* (FHX, revision `832e086`), Remark 7.3 (`rem:BJ-6-21`).

FHX Theorem 7.2 (homogeneous Siu division, `thm:nn-homogeneous-siu`) is the nontrivial implication
of Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field* (BJ22),
Theorem 6.21. The published proof of BJ22 Theorem 6.21 takes a decreasing regularization `ψᵢ` of
`ψ ≤ e_E` and rationals `tᵢ → 1` with `ψᵢ ≤ tᵢ e_E`, and asserts that `ψᵢ' = ψᵢ - tᵢ e_E` decreases.
FHX Remark 7.3 refutes this on `ℙ¹`; this file verifies the example on the model `ProjBerk k 1` of
`(ℙ¹)^an` (`EnvelopeProperty.Projective.Basic`), over any field `k` with the trivial absolute value.

Let `E = {x₀ = 0}` and `ℓ = e_E = log|x₀|` (`ProjBerk.logAbs (X 0)`). Indexing from `0` (the
source's `ψ_{n+1}`, `t_{n+1}`), put `aₙ = (2n+1)/(2n+2) = 1 - 1/(2(n+1))` (`ProjBerk.bj621Coeff`),
`ψₙ = aₙ ℓ` (`ProjBerk.bj621Psi`), `tₙ = n/(n+1) = 1 - 1/(n+1)` (`ProjBerk.bj621Time`) and
`ψₙ' = ψₙ - tₙ ℓ` (`ProjBerk.bj621PsiShift`).

## Main statements

* `ProjBerk.exists_homFSData_bj621Psi`, `ProjBerk.isScaleHomogeneous_bj621Psi`,
  `ProjBerk.isPSH_bj621Psi`: `ψₙ = (2n+2)⁻¹ log|x₀^{2n+1}|` is a homogeneous Fubini–Study function
  for `O(aₙ)` (all weights `0`), homogeneous for the scaling action, and `aₙ`-psh.
* `ProjBerk.antitone_bj621Psi`, `ProjBerk.iInf_bj621Psi`: `(ψₙ)` decreases to `ℓ`.
* `ProjBerk.bj621Time_lt_one`, `ProjBerk.tendsto_bj621Time`, `ProjBerk.bj621Psi_le`:
  `tₙ < 1`, `tₙ → 1` and `ψₙ ≤ tₙ ℓ`.
* `ProjBerk.bj621PsiShift_eq`, `ProjBerk.strictMono_bj621PsiShift`: where `-∞ < ℓ(v) < 0`,
  `ψₙ'(v) = ℓ(v)/(2n+2)` is strictly increasing in `n`.
* `ProjBerk.logAbs_X_zero_ordPoint`, `ProjBerk.strictMono_bj621PsiShift_ordPoint`: the points
  `v_s = e^{-s ord_{x₀}}` (`ProjBerk.ordPoint`; the divisorial points `s ord_E` for `s > 0`) have
  `ℓ(v_s) = -s`, so `ψₙ'(v_s)` strictly increases for every `s > 0`.
* `ProjBerk.bj621_counterexample`: all of the above in one statement; in particular `(ψₙ')` is
  not decreasing although `(ψₙ)` is.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter MvPolynomial

noncomputable section

namespace EnvelopeProperty
namespace ProjBerk

universe u

variable {k : Type u} [Field k]

/-! ### The data of the example -/

/-- The coefficients `aₙ = (2n+1)/(2n+2) = 1 - 1/(2(n+1))` of FHX Remark 7.3 (the source's
`1 - 1/(2n)`, shifted to start at `n = 0`); `aₙ` is also the class of `ψₙ`. -/
def bj621Coeff (n : ℕ) : ℚ := (2 * n + 1) / (2 * n + 2)

/-- The rationals `tₙ = n/(n+1) = 1 - 1/(n+1)` of FHX Remark 7.3 (the source's `1 - 1/n`, shifted
to start at `n = 0`). -/
def bj621Time (n : ℕ) : ℚ := n / (n + 1)

/-- The functions `ψₙ = aₙ ℓ`, `ℓ = log|x₀|`, of FHX Remark 7.3 on `(ℙ¹)^an`. -/
def bj621Psi (n : ℕ) (v : ProjBerk k 1) : EReal :=
  ((bj621Coeff n : ℝ) : EReal) * logAbs (X 0) v

/-- The functions `ψₙ' = ψₙ - tₙ ℓ` of FHX Remark 7.3, claimed decreasing in the proof of BJ22
Theorem 6.21. -/
def bj621PsiShift (n : ℕ) (v : ProjBerk k 1) : EReal :=
  bj621Psi n v - ((bj621Time n : ℝ) : EReal) * logAbs (X 0) v

theorem bj621Coeff_cast (n : ℕ) : (bj621Coeff n : ℝ) = (2 * n + 1) / (2 * n + 2) := by
  simp only [bj621Coeff]
  push_cast
  ring

theorem bj621Time_cast (n : ℕ) : (bj621Time n : ℝ) = n / (n + 1) := by
  simp only [bj621Time]
  push_cast
  ring

theorem bj621Coeff_cast_eq_one_sub (n : ℕ) : (bj621Coeff n : ℝ) = 1 - 1 / (2 * n + 2) := by
  have h : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
  rw [bj621Coeff_cast]
  field_simp
  ring

theorem bj621Time_cast_eq_one_sub (n : ℕ) : (bj621Time n : ℝ) = 1 - 1 / (n + 1) := by
  have h : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [bj621Time_cast]
  field_simp
  ring

theorem bj621Coeff_cast_pos (n : ℕ) : (0 : ℝ) < bj621Coeff n := by
  rw [bj621Coeff_cast]
  positivity

theorem bj621Coeff_cast_le_one (n : ℕ) : (bj621Coeff n : ℝ) ≤ 1 := by
  rw [bj621Coeff_cast_eq_one_sub]
  have : (0 : ℝ) ≤ 1 / (2 * n + 2) := by positivity
  linarith

theorem bj621Coeff_cast_mono {m n : ℕ} (h : m ≤ n) : (bj621Coeff m : ℝ) ≤ bj621Coeff n := by
  rw [bj621Coeff_cast_eq_one_sub, bj621Coeff_cast_eq_one_sub]
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast h
  have : 1 / (2 * (n : ℝ) + 2) ≤ 1 / (2 * m + 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

theorem bj621Time_cast_nonneg (n : ℕ) : (0 : ℝ) ≤ bj621Time n := by
  rw [bj621Time_cast]
  positivity

/-- `aₙ - tₙ = 1/(2n+2)`. -/
theorem bj621Coeff_cast_sub_bj621Time_cast (n : ℕ) :
    (bj621Coeff n : ℝ) - bj621Time n = 1 / (2 * n + 2) := by
  have h₁ : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
  have h₂ : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [bj621Coeff_cast, bj621Time_cast]
  field_simp
  ring

/-- If `0 ≤ c ≤ c'` and `x ≤ 0` in `EReal`, then `c' x ≤ c x`. -/
private theorem ereal_coe_mul_le_coe_mul_of_nonpos {c c' : ℝ} (hc : 0 ≤ c) (hcc' : c ≤ c')
    {x : EReal} (hx : x ≤ 0) : (c' : EReal) * x ≤ (c : EReal) * x := by
  induction x using EReal.rec with
  | bot =>
    rcases (hc.trans hcc').lt_or_eq with h | h
    · rw [EReal.coe_mul_bot_of_pos h]
      exact bot_le
    · have hc0 : c = 0 := le_antisymm (hcc'.trans h.symm.le) hc
      rw [← h, hc0]
  | coe x =>
    rw [← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    have hx' : x ≤ 0 := by exact_mod_cast hx
    nlinarith
  | top => exact absurd (top_le_iff.1 hx) EReal.zero_ne_top

/-! ### `ψₙ` is a homogeneous Fubini–Study function for `O(aₙ)` -/

/-- **`ψₙ ∈ 𝓗_hom(O(aₙ))`** (`prop:r73-p1-example`(1)): `ψₙ = m⁻¹ log|s|` with `m = 2n+2` and
the form `s = x₀^{2n+1}` of degree `m aₙ = 2n+1`; its only weight is `0`. -/
theorem exists_homFSData_bj621Psi (n : ℕ) :
    ∃ D : FSData k 1 (bj621Coeff n), (∀ t ∈ D.terms, t.2 = 0) ∧ bj621Psi n = D.eval := by
  have hq : (2 * (n : ℚ) + 2) ≠ 0 := by positivity
  refine ⟨{ m := 2 * n + 2
            m_pos := by omega
            deg := 2 * n + 1
            deg_eq := by
              simp only [bj621Coeff]
              push_cast
              field_simp
            terms := {(X 0 ^ (2 * n + 1), 0)}
            isHomogeneous := fun t ht => by
              rw [Finset.mem_singleton.1 ht]
              exact isHomogeneous_X_pow _ _
            exists_ne_zero :=
              ⟨_, Finset.mem_singleton_self _, pow_ne_zero _ (X_ne_zero _)⟩ }, ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_singleton.1 ht]
  · funext v
    simp only [bj621Psi, FSData.eval, Finset.sup_singleton, logAbs_pow, EReal.coe_zero, add_zero]
    rw [← EReal.coe_natCast, ProjBerk.ereal_coe_mul_coe_mul]
    congr 2
    rw [bj621Coeff_cast]
    push_cast
    have hr : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
    field_simp

/-- `ψₙ` is homogeneous for the scaling action (`prop:r73-p1-example`(1)). -/
theorem isScaleHomogeneous_bj621Psi (n : ℕ) : IsScaleHomogeneous (bj621Psi (k := k) n) := by
  intro t ht v
  simp only [bj621Psi]
  rw [logAbs_rpow, ProjBerk.ereal_coe_mul_coe_mul, ProjBerk.ereal_coe_mul_coe_mul,
    mul_comm (bj621Coeff n : ℝ)]

/-- `ψₙ ∈ PSH(aₙ)` (`prop:r73-p1-example`(1)). -/
theorem isPSH_bj621Psi (n : ℕ) : IsPSH (bj621Coeff n : ℝ) (bj621Psi (k := k) n) := by
  obtain ⟨D, -, hD⟩ := exists_homFSData_bj621Psi (k := k) n
  exact IsFS.isPSH ⟨D, hD⟩

/-! ### `(ψₙ)` decreases to `ℓ`, and `ψₙ ≤ tₙ ℓ` -/

/-- `(ψₙ)` is decreasing (`prop:r73-p1-example`(2)), since `ℓ ≤ 0` and `aₙ` increases. -/
theorem antitone_bj621Psi (v : ProjBerk k 1) : Antitone fun n => bj621Psi n v := fun _ _ h =>
  ereal_coe_mul_le_coe_mul_of_nonpos (bj621Coeff_cast_pos _).le (bj621Coeff_cast_mono h)
    (logAbs_le_zero _ v)

/-- `infₙ ψₙ = ℓ` (`prop:r73-p1-example`(2)), since `aₙ → 1`. -/
theorem iInf_bj621Psi (v : ProjBerk k 1) : ⨅ n, bj621Psi n v = logAbs (X 0) v := by
  have hle : logAbs (X 0) v ≤ 0 := logAbs_le_zero _ v
  induction h : logAbs (X 0) v using EReal.rec with
  | bot =>
    simp only [bj621Psi, h, EReal.coe_mul_bot_of_pos (bj621Coeff_cast_pos _), iInf_const]
  | top => rw [h] at hle; exact absurd (top_le_iff.1 hle) EReal.zero_ne_top
  | coe x =>
    rw [h] at hle
    have hx : x ≤ 0 := by exact_mod_cast hle
    refine le_antisymm (ProjBerk.ereal_le_of_forall_pos_le_add fun ε hε => ?_)
      (le_iInf fun n => ?_)
    · obtain ⟨N, hN⟩ := exists_nat_gt (-x / ε)
      refine (iInf_le _ N).trans ?_
      simp only [bj621Psi, h]
      rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff, bj621Coeff_cast_eq_one_sub]
      have hD : (0 : ℝ) < 2 * N + 2 := by positivity
      rw [div_lt_iff₀ hε] at hN
      have h1 : -x / (2 * N + 2) ≤ ε := by
        rw [div_le_iff₀ hD]
        nlinarith
      have h2 : (1 - 1 / (2 * (N : ℝ) + 2)) * x = x + -x / (2 * N + 2) := by ring
      rw [h2]
      linarith
    · simp only [bj621Psi, h]
      rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
      have := bj621Coeff_cast_le_one n
      nlinarith

/-- `tₙ < 1` (`prop:r73-p1-example`(3)). -/
theorem bj621Time_lt_one (n : ℕ) : bj621Time n < 1 := by
  have h : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [bj621Time, div_lt_one (by positivity)]
  linarith

/-- `tₙ → 1` (`prop:r73-p1-example`(3)). -/
theorem tendsto_bj621Time : Tendsto (fun n => (bj621Time n : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [sub_zero] at h
  exact h.congr fun n => (bj621Time_cast_eq_one_sub n).symm

/-- `ψₙ ≤ tₙ ℓ` (`prop:r73-p1-example`(3)), since `aₙ ≥ tₙ ≥ 0` and `ℓ ≤ 0`. -/
theorem bj621Psi_le (n : ℕ) (v : ProjBerk k 1) :
    bj621Psi n v ≤ ((bj621Time n : ℝ) : EReal) * logAbs (X 0) v := by
  have h := bj621Coeff_cast_sub_bj621Time_cast n
  have hpos : (0 : ℝ) ≤ 1 / (2 * n + 2) := by positivity
  exact ereal_coe_mul_le_coe_mul_of_nonpos (bj621Time_cast_nonneg n) (by linarith)
    (logAbs_le_zero _ v)

/-! ### `ψₙ'` strictly increases where `ℓ` is finite and negative -/

/-- Where `ℓ` is finite, `ψₙ' = ℓ/(2n+2)` (`prop:r73-p1-example`(4)). -/
theorem bj621PsiShift_eq (n : ℕ) {v : ProjBerk k 1} (hv : logAbs (X 0) v ≠ ⊥) :
    bj621PsiShift n v = ((1 / (2 * n + 2) : ℝ) : EReal) * logAbs (X 0) v := by
  obtain ⟨x, hx⟩ : ∃ x : ℝ, logAbs (X 0) v = x :=
    ⟨(logAbs (X 0) v).toReal, (EReal.coe_toReal (logAbs_ne_top _ v) hv).symm⟩
  simp only [bj621PsiShift, bj621Psi, hx]
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_eq_coe_iff,
    ← sub_mul, bj621Coeff_cast_sub_bj621Time_cast]

/-- **`ψₙ'` strictly increases** at every point where `-∞ < ℓ(v) < 0`
(`prop:r73-p1-example`(4)). -/
theorem strictMono_bj621PsiShift {v : ProjBerk k 1} (hv0 : logAbs (X 0) v ≠ ⊥)
    (hv1 : logAbs (X 0) v < 0) : StrictMono fun n => bj621PsiShift n v := by
  obtain ⟨x, hx⟩ : ∃ x : ℝ, logAbs (X 0) v = x :=
    ⟨(logAbs (X 0) v).toReal, (EReal.coe_toReal (logAbs_ne_top _ v) hv0).symm⟩
  have hx0 : x < 0 := by
    rw [hx] at hv1
    exact_mod_cast hv1
  refine strictMono_nat_of_lt_succ fun n => ?_
  simp only [bj621PsiShift_eq _ hv0, hx]
  rw [← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_lt_coe_iff]
  have h : 1 / (2 * ((n + 1 : ℕ) : ℝ) + 2) < 1 / (2 * (n : ℝ) + 2) :=
    one_div_lt_one_div_of_lt (by positivity) (by push_cast; linarith)
  exact mul_lt_mul_of_neg_right h hx0

/-- The points `v_s = e^{-s ord_{x₀}}` (`ProjBerk.ordPoint`; the divisorial points `s ord_E`,
`s > 0`) satisfy `ℓ(v_s) = -s` (`prop:r73-p1-example`(5)). -/
theorem logAbs_X_zero_ordPoint {s : ℝ} (hs : 0 ≤ s) :
    logAbs (X 0) (ordPoint (k := k) (n := 1) one_ne_zero (X_prime (i := 0)) hs) =
      ((-s : ℝ) : EReal) := by
  have h := ordPoint_val_of_isHomogeneous (k := k) (n := 1) one_ne_zero (X_prime (i := 0)) hs
    (isHomogeneous_X k (0 : Fin (1 + 1)))
  rw [multiplicity_self, pow_one] at h
  rw [logAbs_def, h.resolve_right (X_ne_zero _), log_expNeg]

/-- `ψₙ'(v_s)` strictly increases for every `s > 0` (`prop:r73-p1-example`(5)). -/
theorem strictMono_bj621PsiShift_ordPoint {s : ℝ} (hs : 0 < s) :
    StrictMono fun n =>
      bj621PsiShift n (ordPoint (k := k) (n := 1) one_ne_zero (X_prime (i := 0)) hs.le) := by
  have h := logAbs_X_zero_ordPoint (k := k) hs.le
  refine strictMono_bj621PsiShift (by rw [h]; exact EReal.coe_ne_bot _) ?_
  rw [h, ← EReal.coe_zero, EReal.coe_lt_coe_iff]
  linarith

/-- **The counterexample of FHX Remark 7.3** (`prop:r73-p1-example`): on `(ℙ¹)^an`, the functions
`ψₙ = aₙ ℓ ∈ 𝓗_hom(O(aₙ))` are homogeneous and decrease to `ℓ = log|x₀|`, the rationals
`tₙ < 1` tend to `1` and `ψₙ ≤ tₙ ℓ`, but `ψₙ' = ψₙ - tₙ ℓ` strictly increases at a point (any
`v_s`, `s > 0`); so `(ψₙ')` is not decreasing, contrary to the claim in the proof of BJ22
Theorem 6.21. -/
theorem bj621_counterexample :
    (∀ n, ∃ D : FSData k 1 (bj621Coeff n), (∀ t ∈ D.terms, t.2 = 0) ∧ bj621Psi n = D.eval) ∧
      (∀ n, IsScaleHomogeneous (bj621Psi (k := k) n)) ∧
      (∀ v : ProjBerk k 1, Antitone fun n => bj621Psi n v) ∧
      (∀ v : ProjBerk k 1, ⨅ n, bj621Psi n v = logAbs (X 0) v) ∧
      (∀ n, bj621Time n < 1) ∧ Tendsto (fun n => (bj621Time n : ℝ)) atTop (𝓝 1) ∧
      (∀ n (v : ProjBerk k 1), bj621Psi n v ≤ ((bj621Time n : ℝ) : EReal) * logAbs (X 0) v) ∧
      ∃ v : ProjBerk k 1, StrictMono fun n => bj621PsiShift n v :=
  ⟨exists_homFSData_bj621Psi, isScaleHomogeneous_bj621Psi, antitone_bj621Psi, iInf_bj621Psi,
    bj621Time_lt_one, tendsto_bj621Time, bj621Psi_le,
    ⟨_, strictMono_bj621PsiShift_ordPoint one_pos⟩⟩

end ProjBerk
end EnvelopeProperty
