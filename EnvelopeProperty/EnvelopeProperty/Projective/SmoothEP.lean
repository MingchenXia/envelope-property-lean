/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SmoothEPTrace
import EnvelopeProperty.Projective.Comparison
import EnvelopeProperty.Projective.PSHBasic

/-!
# The envelope property of `ℙⁿ` in characteristic `p`

This file proves Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX),
Theorem 3.1 (`thm:smooth-EP`) for `X = ℙⁿ` over an algebraically closed field `k` of
characteristic `p > 0` (blueprint `thm:pn-ep`): every class `θ ≥ 0` has the envelope property
(`ProjBerk.hasEnvelopeProperty_of_charP`). The proof is the assembly `rmk:bj-pn-ep-assembly`
(`bj22.tex`), following FHX §3:

* (a) By `lem:bj-envppty` (`hasEnvelopeProperty_of_forall_rat_gt`) it suffices to treat rational
  `a > 0`; by the envelope criterion `prop:bj-envelope-criterion`
  (`hasEnvelopeProperty_of_forall_isRatPL`) it suffices that `P_a(φ)` is `a`-psh for rational PL
  `φ`; with `a = d/m`, `P_a(φ) = m⁻¹ P_d(m φ)` (`envelope_mul`) and
  `P_d(φ) = P_d(φ - C) + C` (`envelope_add_const`), so we may assume `a = d ∈ ℤ_{>0}` and `φ ≤ 0`
  (`ProjBerk.isPSH_envelope_rat`, `ProjBerk.isPSH_envelope_nat`).
* (b) `Q = P_d(φ) = sup_m m⁻¹ φ_{J_m}` (`envelope_eq_iSup_obstacleIdeal`); the asymptotic test
  ideals `B_m = τ(J_•^m)` of the graded sequence `J_m = J_m(φ)` give `u_m = m⁻¹ φ_{B_m} ∈ H^gf_ℚ(d)`
  (`ProjBerk.testApprox`, `ProjBerk.isRatFS_testApprox`).
* (c) `q⁻¹ φ_{J_q} ≤ (qm)⁻¹ φ_{J_{qm}} ≤ u_{qm} ≤ u_m`, so `Q ≤ u_m`
  (`ProjBerk.envelope_le_testApprox`); `u_{(j+1)!} ≤ u_{j!}` and `u = lim_j u_{j!}` is `d`-psh by
  PSH2 (`ProjBerk.testLimit`, `ProjBerk.isPSH_testLimit`).
* (d) At a divisorial point `v`, `u_m(v) ≤ Q(v) + A/m`
  (`ProjBerk.exists_testApprox_le_envelope_add`, from the trace estimate
  `ProjBerk.exists_phiIdeal_asymptoticTestIdeal_le` of `EnvelopeProperty.Projective.SmoothEPTrace`),
  hence `u = Q` on `(ℙⁿ)^div`
  (`ProjBerk.testLimit_le_envelope_of_isDivisorial`).
* (e) So `u ≤ φ` on `(ℙⁿ)^div`, hence everywhere by `lem:bj-sup-pl`
  (`IsPSH.le_of_forall_isDivisorial_le_isRatPL`), and `u ≤ P_d(φ) = Q ≤ u`
  (`ProjBerk.isPSH_envelope_nat_of_nonpos`).

## Main results

* `ProjBerk.isPSH_envelope_nat_of_nonpos`, `ProjBerk.isPSH_envelope_nat`,
  `ProjBerk.isPSH_envelope_rat`: `P_a(φ)` is `a`-psh for `a ∈ ℚ_{>0}` and `φ` rational PL.
* `ProjBerk.hasEnvelopeProperty_rat_of_charP`: rational classes `a > 0` have the envelope property.
* `ProjBerk.hasEnvelopeProperty_of_charP`: every `θ ≥ 0` has the envelope property.

## Deviations from the blueprint

* In (c) the finiteness of `u` comes from `u ≥ Q ≥ inf φ` (a constant is a competitor for `Q`)
  instead of `Q ≥ φ_{J_1}`.
* In (d) the bound `ord_{R'}(B_m) ≥ (m/q) ord_{R'}(J_q) - A` is proved directly for the
  generators `Φ_e(F)`, `F ∈ J_q^{⌈m p^e/q⌉}`, of `B_m`, with the sharp constant `A = c (1 + a)`,
  `a = ord_{R'}(dx/du)`; the step (d) estimate holds for every divisorial point, without the
  hypotheses `φ` lsc or `φ ≤ 0`.
-/

open scoped NNReal ENNReal Topology Polynomial

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

namespace ProjBerk

universe u

section Assembly

variable {k : Type u} [Field k] {n : ℕ}

section TestApprox

variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

variable (k n) in
/-- The functions `u_m = m⁻¹ φ_{B_m}` of `rmk:bj-pn-ep-assembly`, step (b), for the asymptotic test
ideals `B_m = τ(J_•^m)` of the graded sequence `J_m = J_m(φ)` (`obstacleIdeal`), transported to
`k[x₀, …, xₙ, t]` (`coneObstacleIdeal`). -/
def testApprox (d : ℕ) (φ : ProjBerk k n → ℝ) (m : ℕ) (v : ProjBerk k n) : EReal :=
  (((m : ℝ)⁻¹ : ℝ) : EReal) *
    phiIdeal ((asymptoticTestIdeal p (coneObstacleIdeal k n d φ) m).comap (coneEquiv k n)) v

variable {d : ℕ} {φ : ProjBerk k n → ℝ}

/-- `u_m ∈ H^gf_ℚ(d)` (step (b)), for `φ` bounded below and `m > 0`. -/
theorem isRatFS_testApprox {C : ℝ} (hC : ∀ v, C ≤ φ v) {m : ℕ} (hm : 0 < m) :
    IsRatFS (d : ℚ) (testApprox k n p d φ m) :=
  isRatFS_asymptoticTestIdeal_coneObstacleIdeal p hC hm

/-- `u_{ml} ≤ u_m` (step (c)), from subadditivity `B_{ml} ⊆ B_m^l`. -/
theorem testApprox_mul_le {C : ℝ} (hC : ∀ v, C ≤ φ v) {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    (v : ProjBerk k n) : testApprox k n p d φ (m * l) v ≤ testApprox k n p d φ m v := by
  have h := phiIdeal_comap_asymptoticTestIdeal_mul_le (d := d) p hC m l v
  have hl' : (l : EReal) = ((l : ℝ) : EReal) := rfl
  rw [hl'] at h
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hl'' : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hl.ne'
  calc testApprox k n p d φ (m * l) v
      ≤ ((((m * l : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * (((l : ℝ) : EReal) *
          phiIdeal ((asymptoticTestIdeal p (coneObstacleIdeal k n d φ) m).comap
            (coneEquiv k n)) v) :=
        ereal_coe_mul_monotone (inv_nonneg.2 (Nat.cast_nonneg _)) h
    _ = testApprox k n p d φ m v := by
        rw [ereal_coe_mul_coe_mul, testApprox]
        congr 2
        push_cast
        field_simp

/-- `m⁻¹ φ_{J_m} ≤ u_m`, from `J_m ⊆ B_m`. -/
theorem inv_mul_phiIdeal_obstacleIdeal_le_testApprox {m : ℕ} (hm : 0 < m) (v : ProjBerk k n) :
    (((m : ℝ)⁻¹ : ℝ) : EReal) * phiIdeal (obstacleIdeal k n d φ m) v ≤
      testApprox k n p d φ m v :=
  ereal_coe_mul_monotone (inv_nonneg.2 (Nat.cast_nonneg _))
    (phiIdeal_mono v (obstacleIdeal_le_comap_asymptoticTestIdeal p hm))

/-- `P_d(φ) ≤ u_m` (step (c)): `q⁻¹ φ_{J_q} ≤ (qm)⁻¹ φ_{J_{qm}} ≤ u_{qm} ≤ u_m`. -/
theorem envelope_le_testApprox (hd : 0 < d) (hφ : LowerSemicontinuous φ) (hφ0 : φ triv ≤ 0)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) {m : ℕ} (hm : 0 < m) (v : ProjBerk k n) :
    envelope (d : ℝ) (fun w => (φ w : EReal)) v ≤ testApprox k n p d φ m v := by
  rw [envelope_eq_iSup_obstacleIdeal hd hφ hφ0 v]
  refine iSup₂_le fun q hq => ?_
  calc (((q : ℝ)⁻¹ : ℝ) : EReal) * phiIdeal (obstacleIdeal k n d φ q) v
      ≤ ((((q * m : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * phiIdeal (obstacleIdeal k n d φ (q * m)) v :=
        inv_mul_phiIdeal_obstacleIdeal_le_mul hq hm v
    _ ≤ testApprox k n p d φ (q * m) v :=
        inv_mul_phiIdeal_obstacleIdeal_le_testApprox p (Nat.mul_pos hq hm) v
    _ = testApprox k n p d φ (m * q) v := by rw [mul_comm]
    _ ≤ testApprox k n p d φ m v := testApprox_mul_le p hC hm hq v

/-- Step (d): at a divisorial point `v` there is `A ≥ 0` (depending on `v`) with
`u_m(v) ≤ P_d(φ)(v) + A/m` for all `m > 0`. -/
theorem exists_testApprox_le_envelope_add {C : ℝ} (hC : ∀ v, C ≤ φ v) {v : ProjBerk k n}
    (hv : v.IsDivisorial) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, 0 < m →
      testApprox k n p d φ m v ≤
        envelope (d : ℝ) (fun w => (φ w : EReal)) v + ((A / m : ℝ) : EReal) := by
  obtain ⟨A, hA, h⟩ := exists_phiIdeal_asymptoticTestIdeal_le p (J := coneObstacleIdeal k n d φ)
    coneObstacleIdeal_mul_le (fun q _ => coneObstacleIdeal_ne_bot hC q) hv
  refine ⟨A, hA, fun m hm => ?_⟩
  obtain ⟨q, hq, hle⟩ := h m hm
  rw [comap_coneObstacleIdeal] at hle
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have e1 : (m : ℝ)⁻¹ * ((m : ℝ) / q) = (q : ℝ)⁻¹ := by field_simp
  have e2 : (m : ℝ)⁻¹ * A = A / m := inv_mul_eq_div _ _
  calc testApprox k n p d φ m v
      ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) * ((((m : ℝ) / q : ℝ) : EReal) *
          phiIdeal (obstacleIdeal k n d φ q) v + (A : EReal)) :=
        ereal_coe_mul_monotone (inv_nonneg.2 (Nat.cast_nonneg _)) hle
    _ = (((q : ℝ)⁻¹ : ℝ) : EReal) * phiIdeal (obstacleIdeal k n d φ q) v +
          ((A / m : ℝ) : EReal) := by
        rw [ereal_coe_mul_add (inv_nonneg.2 (Nat.cast_nonneg _)), ereal_coe_mul_coe_mul, e1,
          ← EReal.coe_mul, e2]
    _ ≤ envelope (d : ℝ) (fun w => (φ w : EReal)) v + ((A / m : ℝ) : EReal) := by
        gcongr
        exact inv_mul_phiIdeal_obstacleIdeal_le_envelope hq v

variable (k n) in
/-- The decreasing limit `u = lim_j u_{j!}` of step (c). -/
def testLimit (d : ℕ) (φ : ProjBerk k n → ℝ) (v : ProjBerk k n) : EReal :=
  ⨅ j : ℕ, testApprox k n p d φ (Nat.factorial j) v

/-- `u_{(j+1)!} ≤ u_{j!}`. -/
theorem antitone_testApprox_factorial {C : ℝ} (hC : ∀ v, C ≤ φ v) (v : ProjBerk k n) :
    Antitone fun j => testApprox k n p d φ (Nat.factorial j) v :=
  antitone_nat_of_succ_le fun j => by
    rw [Nat.factorial_succ, mul_comm]
    exact testApprox_mul_le p hC (Nat.factorial_pos j) (Nat.succ_pos j) v

/-- `P_d(φ) ≤ u` (step (c)). -/
theorem envelope_le_testLimit (hd : 0 < d) (hφ : LowerSemicontinuous φ) (hφ0 : φ triv ≤ 0)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) (v : ProjBerk k n) :
    envelope (d : ℝ) (fun w => (φ w : EReal)) v ≤ testLimit k n p d φ v :=
  le_iInf fun j => envelope_le_testApprox p hd hφ hφ0 hC (Nat.factorial_pos j) v

/-- `u ∈ PSH(d)` (step (c), by PSH2): the `u_{j!} ∈ H^gf_ℚ(d)` decrease to `u`, and
`u ≥ P_d(φ) ≥ inf φ > -∞`. -/
theorem isPSH_testLimit (hd : 0 < d) (hφ : LowerSemicontinuous φ) (hφ0 : φ triv ≤ 0)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) : IsPSH (d : ℝ) (testLimit k n p d φ) := by
  refine isPSH_of_antitone_seq (θ := fun _ => (d : ℝ)) tendsto_const_nhds (fun j => ?_)
    (fun v => antitone_testApprox_factorial p hC v) (fun v => rfl) ⟨triv, ?_⟩
  · have h := (isRatFS_testApprox p hC (d := d) (Nat.factorial_pos j)).isPSH
    rwa [Rat.cast_natCast] at h
  · have h1 : (C : EReal) ≤ envelope (d : ℝ) (fun w => (φ w : EReal)) triv :=
      le_envelope (isPSH_const (Nat.cast_nonneg d) C) (fun w => EReal.coe_le_coe_iff.2 (hC w))
        triv
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot C)
      (h1.trans (envelope_le_testLimit p hd hφ hφ0 hC triv))

/-- `u = P_d(φ)` on the divisorial points (step (d)): `u ≤ u_{j!} ≤ P_d(φ) + A/j!`. -/
theorem testLimit_le_envelope_of_isDivisorial {C : ℝ} (hC : ∀ v, C ≤ φ v) {v : ProjBerk k n}
    (hv : v.IsDivisorial) :
    testLimit k n p d φ v ≤ envelope (d : ℝ) (fun w => (φ w : EReal)) v := by
  obtain ⟨A, hA, h⟩ := exists_testApprox_le_envelope_add p hC hv
  refine ereal_le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨j, hj⟩ := exists_nat_gt (A / ε)
  have hfac : (j : ℝ) ≤ (Nat.factorial j : ℝ) := by exact_mod_cast Nat.self_le_factorial j
  have hfac0 : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hAε : A / (Nat.factorial j : ℝ) ≤ ε := by
    rw [div_le_iff₀ hfac0]
    rw [div_lt_iff₀ hε] at hj
    nlinarith
  calc testLimit k n p d φ v ≤ testApprox k n p d φ (Nat.factorial j) v := iInf_le _ j
    _ ≤ envelope (d : ℝ) (fun w => (φ w : EReal)) v +
          ((A / (Nat.factorial j : ℕ) : ℝ) : EReal) := h _ (Nat.factorial_pos j)
    _ ≤ envelope (d : ℝ) (fun w => (φ w : EReal)) v + (ε : EReal) := by
        gcongr

end TestApprox

/-- For `θ < 0` there are no `θ`-psh functions (`IsPSH.nonneg`), so `θ` has the envelope property
vacuously; together with `hasEnvelopeProperty_of_charP`, every class on `ℙⁿ` has it in
characteristic `p`. -/
theorem hasEnvelopeProperty_of_neg {θ : ℝ} (hθ : θ < 0) : HasEnvelopeProperty k n θ :=
  fun _ ⟨u, hu⟩ hS _ => absurd (hS u hu).nonneg (not_le.2 hθ)

section Main

variable [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]

include p

/-- **Theorem 3.1 on `ℙⁿ`, integer class, obstacle `≤ 0`** (`rmk:bj-pn-ep-assembly`, steps
(b)–(e)): for `d ∈ ℤ_{>0}` and a rational PL function `φ ≤ 0`, `P_d(φ)` is `d`-psh; in fact
`P_d(φ) = lim_j u_{j!}`. -/
theorem isPSH_envelope_nat_of_nonpos {d : ℕ} (hd : 0 < d) {φ : ProjBerk k n → ℝ}
    (hφ : IsRatPL φ) (hφ0 : ∀ v, φ v ≤ 0) :
    IsPSH (d : ℝ) (envelope (d : ℝ) fun v => (φ v : EReal)) := by
  obtain ⟨C₀, hC₀⟩ := hφ.exists_abs_le
  have hC : ∀ v, -C₀ ≤ φ v := fun v => neg_le_of_abs_le (hC₀ v)
  have hlsc := hφ.continuous.lowerSemicontinuous
  have hU := isPSH_testLimit p hd hlsc (hφ0 triv) hC
  have hUφ : ∀ v, testLimit k n p d φ v ≤ φ v :=
    hU.le_of_forall_isDivisorial_le_isRatPL hφ fun w hw =>
      (testLimit_le_envelope_of_isDivisorial p hC hw).trans
        (envelope_le _ _ w)
  have heq : envelope (d : ℝ) (fun v => (φ v : EReal)) = testLimit k n p d φ :=
    le_antisymm (fun v => envelope_le_testLimit p hd hlsc (hφ0 triv) hC v) (le_envelope hU hUφ)
  rw [heq]
  exact hU

/-- **Theorem 3.1 on `ℙⁿ`, integer class** (`rmk:bj-pn-ep-assembly`, step (a), subtracting a
constant): for `d ∈ ℤ_{>0}` and a rational PL function `φ`, `P_d(φ)` is `d`-psh. -/
theorem isPSH_envelope_nat {d : ℕ} (hd : 0 < d) {φ : ProjBerk k n → ℝ} (hφ : IsRatPL φ) :
    IsPSH (d : ℝ) (envelope (d : ℝ) fun v => (φ v : EReal)) := by
  obtain ⟨C₀, hC₀⟩ := hφ.exists_abs_le
  obtain ⟨N, hN⟩ := exists_nat_ge C₀
  set ψ : ProjBerk k n → ℝ := fun v => φ v - N with hψ_def
  have hψ : IsRatPL ψ := by simpa using hφ.sub (isRatPL_const (N : ℚ))
  have hψ0 : ∀ v, ψ v ≤ 0 := fun v => by
    simp only [hψ_def]
    linarith [le_abs_self (φ v), hC₀ v]
  have h := (isPSH_envelope_nat_of_nonpos p hd hψ hψ0).add_const (N : ℝ)
  have e := envelope_add_const (θ := (d : ℝ)) (fun v => (ψ v : EReal)) (N : ℝ)
  have e2 : (fun v => (ψ v : EReal) + ((N : ℝ) : EReal)) = fun v => (φ v : EReal) := by
    funext v
    rw [← EReal.coe_add, hψ_def, sub_add_cancel]
  rw [e2] at e
  rw [e]
  exact h

/-- **Theorem 3.1 on `ℙⁿ`, rational class** (`rmk:bj-pn-ep-assembly`, step (a), rescaling): for
`a ∈ ℚ_{>0}` and a rational PL function `φ`, `P_a(φ)` is `a`-psh; with `a = d/m`,
`P_a(φ) = m⁻¹ P_d(m φ)`. -/
theorem isPSH_envelope_rat {a : ℚ} (ha : 0 < a) {φ : ProjBerk k n → ℝ} (hφ : IsRatPL φ) :
    IsPSH (a : ℝ) (envelope (a : ℝ) fun v => (φ v : EReal)) := by
  have hm : (0 : ℝ) < a.den := by exact_mod_cast a.den_pos
  have hd : 0 < a.num.toNat := by have := Rat.num_pos.2 ha; omega
  have hmd : (a.den : ℝ) * a = (a.num.toNat : ℝ) := by
    have h1 : ((a.num.toNat : ℕ) : ℤ) = a.num := Int.toNat_of_nonneg (Rat.num_nonneg.2 ha.le)
    have h3 : ((a.den : ℚ) * a : ℚ) = ((a.num.toNat : ℕ) : ℚ) := by
      rw [Rat.den_mul_eq_num]
      exact_mod_cast h1.symm
    exact_mod_cast h3
  have hψ : IsRatPL fun v => (a.den : ℝ) * φ v := by simpa using hφ.smul (a.den : ℚ)
  have h := isPSH_envelope_nat p hd hψ
  have e := envelope_mul (θ := (a : ℝ)) (fun v => (φ v : EReal)) hm
  have e2 : (fun v => ((a.den : ℝ) : EReal) * (φ v : EReal)) =
      fun v => (((a.den : ℝ) * φ v : ℝ) : EReal) := by
    funext v
    rw [EReal.coe_mul]
  rw [e2, hmd] at e
  rw [e, ← hmd] at h
  exact (isPSH_smul_iff hm).1 h

/-- **The envelope property for rational classes** `a > 0` (`rmk:bj-pn-ep-assembly`, step (a), via
the envelope criterion `prop:bj-envelope-criterion`). -/
theorem hasEnvelopeProperty_rat_of_charP {a : ℚ} (ha : 0 < a) :
    HasEnvelopeProperty k n (a : ℝ) :=
  hasEnvelopeProperty_of_forall_isRatPL fun _ hφ => isPSH_envelope_rat p ha hφ

end Main

end Assembly

/-- **FHX Theorem 3.1 for `ℙⁿ` in characteristic `p`** (`thm:pn-ep`, FHX `thm:smooth-EP`,
assembled as in `rmk:bj-pn-ep-assembly`): over an algebraically closed field of characteristic
`p > 0`, every class `θ ≥ 0` on `ℙⁿ` has the envelope property. By `lem:bj-envppty` it suffices
to treat rational classes `a > θ`. -/
theorem hasEnvelopeProperty_of_charP {k : Type u} [Field k] [IsAlgClosed k] (p : ℕ)
    [Fact p.Prime] [CharP k p] (n : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    HasEnvelopeProperty k n θ :=
  hasEnvelopeProperty_of_forall_rat_gt fun a ha =>
    hasEnvelopeProperty_rat_of_charP p (by exact_mod_cast hθ.trans_lt ha)

end ProjBerk

end EnvelopeProperty
