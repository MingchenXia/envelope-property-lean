/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SmoothConeObstacle
import EnvelopeProperty.Projective.SubvarietyComparison
import EnvelopeProperty.Projective.EnvelopeCriterion

/-!
# The envelope property of smooth projectively normal `X = V(I)` in characteristic `p`

Let `k` be an algebraically closed field of characteristic `p > 0` and `X = V(I) ⊆ ℙᴹ` a
projectively normal projective subvariety (`ProjSubvariety.IsProjNormal`) with smooth charts
(`ProjSubvariety.HasSmoothCharts`). This file proves Fang–Han–Xia, *The envelope property for
unibranch projective varieties* (FHX), Theorem 3.1 (`thm:smooth-EP`) for `X` and the classes
`θ c₁(O_X(1))`, `θ ∈ ℝ` (blueprint `thm:sg-ep-charp`, chapter `smooth-general.tex`):
`ProjSubvariety.hasEnvelopeProperty_of_charP`. The proof is the assembly of the `ℙⁿ` case
(`rmk:bj-pn-ep-assembly`, `EnvelopeProperty.Projective.SmoothEP`), with the test ideals of the
punctured cone over `X × 𝔸¹` (`ProjSubvariety.ConeTraceData.testSeq`) in place of those of
`k[x₀, …, xₙ, t]`:

* If `n = dim X = 0`, then every chart algebra `A_j` is algebraic over `k`, hence equal to `k`,
  so `X^an` is the single point `⋆` (`ProjSubvariety.subsingleton_an_of_dim_eq_zero`) and every
  envelope `P_d(φ)` is the real constant `φ(⋆)`
  (`ProjSubvariety.isPSH_envelope_of_subsingleton`).
* Let `n ≥ 1`. By the reduction `thm:sg-reduction` (`ProjSubvariety.hasEnvelopeProperty_of_forall_nat`)
  and `lem:sg-pl-separate` (`ProjSubvariety.separatesPoints_isPL`) it suffices to show that
  `P_d(φ)` is `d`-psh for `d ∈ ℤ_{>0}` and a PL function `φ ≤ 0`. Fix cone trace data
  `D : X.ConeTraceData p` (`ProjSubvariety.ConeTraceData.nonempty`, `def:sg-charts`,
  `def:sg-forms`) and the twist `c₀ = D.c0` of `prop:sg-uniform-generation`.
* (a) With `J_m = J_m(φ)` (`def:sg-Jm`) and the asymptotic test ideals `B_m` of `(J_m T)`
  (`def:sg-test-X`), `u_m = m⁻¹ φ_{B_m} ∈ 𝓗(X, d + c₀/m)`
  (`ProjSubvariety.ConeTraceData.subvarietyTestApprox`,
  `ProjSubvariety.ConeTraceData.isFS_subvarietyTestApprox`).
* (b) `q⁻¹ φ_{J_q} ≤ (qm)⁻¹ φ_{J_{qm}} ≤ u_{qm} ≤ u_m`, so `P_d(φ) ≤ u_m`
  (`prop:sg-envelope-Jm`, `lem:sg-test-X`(3);
  `ProjSubvariety.ConeTraceData.envelope_le_subvarietyTestApprox`); `u_{(j+1)!} ≤ u_{j!}`, and
  `u = lim_j u_{j!}` is `d`-psh by PSH2 (`thm:pg-psh2`(3)) along the classes `d + c₀/j! → d`,
  since `u ≥ P_d(φ) ≥ inf φ > -∞` (`ProjSubvariety.ConeTraceData.subvarietyTestLimit`,
  `ProjSubvariety.ConeTraceData.isPSH_subvarietyTestLimit`).
* (c) At a divisorial point `v` (`def:sg-div`), `u_m(v) ≤ P_d(φ)(v) + A/m` with `A` independent
  of `m` (`prop:sg-valuative-bound`;
  `ProjSubvariety.ConeTraceData.exists_subvarietyTestApprox_le_envelope_add`), hence `u = P_d(φ)`
  on `X^div` (`ProjSubvariety.ConeTraceData.subvarietyTestLimit_le_envelope_of_isDivisorial`).
* (d) So `u ≤ φ` on `X^div`, hence on `X^an` by the divisorial comparison `thm:sg-comparison`
  (`ProjSubvariety.IsPSH.le_of_forall_isDivisorial_le`), and `u ≤ P_d(φ) ≤ u`
  (`ProjSubvariety.ConeTraceData.isPSH_envelope_nat_of_nonpos`).

## Main results

* `ProjSubvariety.isPSH_envelope_nat_of_charP`: `P_d(φ)` is `d`-psh for `d ∈ ℤ_{>0}` and every
  PL function `φ ≤ 0` on `X^an`.
* `ProjSubvariety.hasEnvelopeProperty_of_charP` (**`thm:sg-ep-charp`**): every `θ ∈ ℝ` has the
  envelope property on `X`.

## Deviations from the blueprint

* As on `ℙⁿ`, the finiteness of `u` in (b) comes from `u ≥ P_d(φ) ≥ inf φ` (a constant is a
  competitor), and (c) is proved for every divisorial point without using `φ ≤ 0`.
* In (b) `prop:sg-envelope-Jm` is used in the form `ProjSubvariety.envelope_eq_iSup_obstacleIdeal`
  (hypotheses `φ` lsc and `φ(⋆) ≤ 0`); `φ` is continuous, being PL.
* The case `n = 0` is proved as `X^an = {⋆}` through the chart at a coordinate `xⱼ` with
  `|xⱼ|_v = 1`: `A_j` is a domain algebraic over the algebraically closed field `k`, so
  `k → A_j` is bijective and `(Spec A_j)^an` is a point.
-/

open scoped NNReal ENNReal Topology Polynomial

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

open ProjBerk (phiIdeal QuotChartAlg)

universe u

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}

/-! ### Dimension zero -/

/-- If `k` is algebraically closed and `dim X = 0`, then `X^an` is a single point (the case
`n = 0` of the proof of `thm:sg-ep-charp`): every chart algebra `A_j` is a domain algebraic over
`k`, hence `k → A_j` is bijective and `(Spec A_j)^an` is a point, and every `v ∈ X^an` lies in the
chart `U_{xⱼ}` of a coordinate with `|xⱼ|_v = 1`, as does `⋆`. -/
theorem subsingleton_an_of_dim_eq_zero [IsAlgClosed k] (h0 : X.dim = 0) : Subsingleton X.an := by
  suffices h : ∀ v : X.an, v = X.triv from ⟨fun v w => (h v).trans (h w).symm⟩
  intro v
  obtain ⟨j, hj⟩ := ProjBerk.exists_val_X_eq_one v.1
  have hv : (v : ProjBerk k M).1.val (MvPolynomial.X j) ≠ 0 := by rw [hj]; exact one_ne_zero
  have hjI : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal :=
    notMem_ideal_of_val_ne_zero hv
  have : Fact ((MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal) := ⟨hjI⟩
  -- `A_j` is algebraic over `k`
  have htr : Algebra.trdeg k (X.ChartAlg j) = 0 := by
    rw [← trdeg_localization_eq (S := X.ChartField j) (nonZeroDivisors (X.ChartAlg j)) le_rfl,
      trdeg_chartField_eq_dim, h0]
    rfl
  have : Algebra.IsAlgebraic k (X.ChartAlg j) := trdeg_eq_zero_iff.1 htr
  have hsurj : Function.Surjective (algebraMap k (X.ChartAlg j)) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := X.ChartAlg j)).2
  -- `(Spec A_j)^an` is a point
  have hpt : ∀ y y' : Berk k (QuotChartAlg X.ideal (MvPolynomial.X j) 1), y = y' := by
    intro y y'
    refine Berk.toFun_injective (funext fun a => ?_)
    obtain ⟨c, hc⟩ := hsurj a
    change y.val a = y'.val a
    rw [show a = algebraMap k (QuotChartAlg X.ideal (MvPolynomial.X j) 1) c from hc.symm]
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    · rw [Berk.abs_algebraMap y hc0, Berk.abs_algebraMap y' hc0]
  have hσ : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X k j
  have htv : (X.triv : ProjBerk k M).1.val (MvPolynomial.X j) ≠ 0 := by
    rw [triv_val_of_notMem X hjI]; exact one_ne_zero
  rw [← chartInv_chartMap hσ one_pos v hv, ← chartInv_chartMap hσ one_pos X.triv htv,
    hpt (X.chartMap _ 1 v hv) (X.chartMap _ 1 X.triv htv)]

/-- If `X^an` is a single point, then for `θ ≥ 0` and every obstacle `φ : X^an → ℝ` the envelope
`P_θ(φ)` is the real constant `φ(⋆)`, hence `θ`-psh. -/
theorem isPSH_envelope_of_subsingleton [Subsingleton X.an] {θ : ℝ} (hθ : 0 ≤ θ)
    (φ : X.an → ℝ) : X.IsPSH θ (X.envelope θ fun v => (φ v : EReal)) := by
  have heq : (X.envelope θ fun v => (φ v : EReal)) = fun _ => (φ X.triv : EReal) := by
    funext v
    refine le_antisymm ?_ ?_
    · rw [Subsingleton.elim v X.triv]
      exact FSSystem.envelope_le X.fsSystem _ _ X.triv
    · exact FSSystem.le_envelope (F := X.fsSystem) (isPSH_const X hθ (φ X.triv))
        (fun w => by rw [Subsingleton.elim w X.triv]) v
  rw [heq]
  exact isPSH_const X hθ _

/-! ### The approximants `u_m = m⁻¹ φ_{B_m}` -/

namespace ConeTraceData

variable {p : ℕ} [Fact p.Prime] [CharP k p] [PerfectRing k p] (D : X.ConeTraceData p)

/-- The functions `u_m = m⁻¹ φ_{B_m}` of the proof of `thm:sg-ep-charp`, step (a), for the
asymptotic test ideals `B_m = D.testSeq J m` (`def:sg-test-X`) of the graded sequence
`J_m = J_m(φ) T` (`ProjSubvariety.coneObstacleIdeal`); `φ` of an ideal of `T` is computed on its
preimage in `R_M[t]`. -/
def subvarietyTestApprox (d : ℕ) (φ : X.an → ℝ) (m : ℕ) (v : X.an) : EReal :=
  (((m : ℝ)⁻¹ : ℝ) : EReal) *
    phiIdeal ((D.testSeq (X.coneObstacleIdeal d φ) m).comap X.coneMk) v.1

variable {D} {d : ℕ} {φ : X.an → ℝ}

/-- **Step (a)** (`prop:sg-uniform-generation`): `u_m ∈ 𝓗(X, d + c₀/m)` for `φ` bounded below
and `m > 0`. -/
theorem isFS_subvarietyTestApprox {C : ℝ} (hC : ∀ v, C ≤ φ v) {m : ℕ} (hm : 0 < m) :
    X.IsFS ((d : ℚ) + D.c0 / m) (D.subvarietyTestApprox d φ m) :=
  D.isFS_inv_mul_phiIdeal_testSeq_coneObstacleIdeal hC hm

/-- `u_m ∈ PSH(X, d + c₀/m)` for `φ` bounded below and `m > 0` (PSH1 applied to step (a)). -/
theorem isPSH_subvarietyTestApprox {C : ℝ} (hC : ∀ v, C ≤ φ v) {m : ℕ} (hm : 0 < m) :
    X.IsPSH ((d : ℝ) + (D.c0 : ℝ) / m) (D.subvarietyTestApprox d φ m) := by
  have h := (isFS_subvarietyTestApprox (D := D) (d := d) hC hm).isPSH
  have e : (((d : ℚ) + (D.c0 : ℚ) / (m : ℚ) : ℚ) : ℝ) = (d : ℝ) + (D.c0 : ℝ) / m := by
    push_cast; rfl
  rwa [e] at h

/-- `u_{ml} ≤ u_m` (step (b)), from `B_{ml} ⊆ (B_m^l)^sat` (`lem:sg-test-X`(3)). -/
theorem subvarietyTestApprox_mul_le {C : ℝ} (hC : ∀ v, C ≤ φ v) {m l : ℕ} (hm : 0 < m)
    (hl : 0 < l) (v : X.an) :
    D.subvarietyTestApprox d φ (m * l) v ≤ D.subvarietyTestApprox d φ m v := by
  have h := D.phiIdeal_testSeq_coneObstacleIdeal_mul_le (d := d) hC m l v
  have hl' : (l : EReal) = ((l : ℝ) : EReal) := rfl
  rw [hl'] at h
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hl'' : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hl.ne'
  calc D.subvarietyTestApprox d φ (m * l) v
      ≤ ((((m * l : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * (((l : ℝ) : EReal) *
          phiIdeal ((D.testSeq (X.coneObstacleIdeal d φ) m).comap X.coneMk) v.1) :=
        ProjBerk.ereal_coe_mul_monotone (inv_nonneg.2 (Nat.cast_nonneg _)) h
    _ = D.subvarietyTestApprox d φ m v := by
        rw [ProjBerk.ereal_coe_mul_coe_mul, subvarietyTestApprox]
        congr 2
        push_cast
        field_simp

/-- `m⁻¹ φ_{J_m} ≤ u_m` for `m > 0`, from `J_m ⊆ B_m` (`lem:sg-test-X`(3)). -/
theorem inv_mul_phiIdeal_obstacleIdeal_le_subvarietyTestApprox {m : ℕ} (hm : 0 < m)
    (v : X.an) :
    (((m : ℝ)⁻¹ : ℝ) : EReal) * phiIdeal (X.obstacleIdeal d φ m) v.1 ≤
      D.subvarietyTestApprox d φ m v :=
  ProjBerk.ereal_coe_mul_monotone (inv_nonneg.2 (Nat.cast_nonneg _))
    (D.phiIdeal_obstacleIdeal_le_testSeq hm v)

/-- **`P_d(φ) ≤ u_m`** (step (b)): `q⁻¹ φ_{J_q} ≤ (qm)⁻¹ φ_{J_{qm}} ≤ u_{qm} ≤ u_m`, with
`P_d(φ) = sup_q q⁻¹ φ_{J_q}` (`prop:sg-envelope-Jm`). -/
theorem envelope_le_subvarietyTestApprox (hd : 0 < d) (hφ : LowerSemicontinuous φ)
    (hφ0 : φ X.triv ≤ 0) {C : ℝ} (hC : ∀ v, C ≤ φ v) {m : ℕ} (hm : 0 < m) (v : X.an) :
    X.envelope (d : ℝ) (fun w => (φ w : EReal)) v ≤ D.subvarietyTestApprox d φ m v := by
  rw [envelope_eq_iSup_obstacleIdeal hd hφ hφ0 v]
  refine iSup₂_le fun q hq => ?_
  calc (((q : ℝ)⁻¹ : ℝ) : EReal) * phiIdeal (X.obstacleIdeal d φ q) v.1
      ≤ ((((q * m : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * phiIdeal (X.obstacleIdeal d φ (q * m)) v.1 :=
        inv_mul_phiIdeal_obstacleIdeal_le_mul hq hm v
    _ ≤ D.subvarietyTestApprox d φ (q * m) v :=
        inv_mul_phiIdeal_obstacleIdeal_le_subvarietyTestApprox (Nat.mul_pos hq hm) v
    _ = D.subvarietyTestApprox d φ (m * q) v := by rw [mul_comm]
    _ ≤ D.subvarietyTestApprox d φ m v := subvarietyTestApprox_mul_le hC hm hq v

/-- **Step (c)** (`prop:sg-valuative-bound`): at a divisorial point `v` there is `A ≥ 0`
(depending on `v`) with `u_m(v) ≤ P_d(φ)(v) + A/m` for all `m > 0`. -/
theorem exists_subvarietyTestApprox_le_envelope_add {C : ℝ} (hC : ∀ v, C ≤ φ v) {v : X.an}
    (hv : X.IsDivisorial v) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, 0 < m →
      D.subvarietyTestApprox d φ m v ≤
        X.envelope (d : ℝ) (fun w => (φ w : EReal)) v + ((A / m : ℝ) : EReal) := by
  obtain ⟨A, hA, h⟩ := D.exists_phiIdeal_testSeq_coneObstacleIdeal_le (d := d) hC hv
  refine ⟨A, hA, fun m hm => ?_⟩
  obtain ⟨q, hq, hle⟩ := h m
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have e1 : (m : ℝ)⁻¹ * ((m : ℝ) / q) = (q : ℝ)⁻¹ := by field_simp
  have e2 : (m : ℝ)⁻¹ * A = A / m := inv_mul_eq_div _ _
  calc D.subvarietyTestApprox d φ m v
      ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) * ((((m : ℝ) / q : ℝ) : EReal) *
          phiIdeal (X.obstacleIdeal d φ q) v.1 + (A : EReal)) :=
        ProjBerk.ereal_coe_mul_monotone (inv_nonneg.2 (Nat.cast_nonneg _)) hle
    _ = (((q : ℝ)⁻¹ : ℝ) : EReal) * phiIdeal (X.obstacleIdeal d φ q) v.1 +
          ((A / m : ℝ) : EReal) := by
        rw [ProjBerk.ereal_coe_mul_add (inv_nonneg.2 (Nat.cast_nonneg _)),
          ProjBerk.ereal_coe_mul_coe_mul, e1, ← EReal.coe_mul, e2]
    _ ≤ X.envelope (d : ℝ) (fun w => (φ w : EReal)) v + ((A / m : ℝ) : EReal) := by
        gcongr
        exact inv_mul_phiIdeal_obstacleIdeal_le_envelope hq v

variable (D) in
/-- The decreasing limit `u = lim_j u_{j!}` of step (b). -/
def subvarietyTestLimit (d : ℕ) (φ : X.an → ℝ) (v : X.an) : EReal :=
  ⨅ j : ℕ, D.subvarietyTestApprox d φ (Nat.factorial j) v

/-- `u_{(j+1)!} ≤ u_{j!}`. -/
theorem antitone_subvarietyTestApprox_factorial {C : ℝ} (hC : ∀ v, C ≤ φ v) (v : X.an) :
    Antitone fun j => D.subvarietyTestApprox d φ (Nat.factorial j) v :=
  antitone_nat_of_succ_le fun j => by
    rw [Nat.factorial_succ, mul_comm]
    exact subvarietyTestApprox_mul_le hC (Nat.factorial_pos j) (Nat.succ_pos j) v

/-- `P_d(φ) ≤ u` (step (b)). -/
theorem envelope_le_subvarietyTestLimit (hd : 0 < d) (hφ : LowerSemicontinuous φ)
    (hφ0 : φ X.triv ≤ 0) {C : ℝ} (hC : ∀ v, C ≤ φ v) (v : X.an) :
    X.envelope (d : ℝ) (fun w => (φ w : EReal)) v ≤ D.subvarietyTestLimit d φ v :=
  le_iInf fun j => envelope_le_subvarietyTestApprox hd hφ hφ0 hC (Nat.factorial_pos j) v

/-- The classes `d + c₀/j!` tend to `d`. -/
theorem tendsto_add_div_factorial (d c : ℝ) :
    Tendsto (fun j : ℕ => d + c / (Nat.factorial j : ℝ)) atTop (𝓝 d) := by
  have hfac : Tendsto Nat.factorial atTop atTop :=
    tendsto_atTop_mono Nat.self_le_factorial tendsto_id
  simpa using tendsto_const_nhds.add ((tendsto_const_div_atTop_nhds_zero_nat c).comp hfac)

/-- **`u ∈ PSH(X, d)`** (step (b), by PSH2 `thm:pg-psh2`(3)): the `u_{j!} ∈ PSH(X, d + c₀/j!)`
decrease to `u`, the classes tend to `d`, and `u ≥ P_d(φ) ≥ inf φ > -∞`. -/
theorem isPSH_subvarietyTestLimit (hd : 0 < d) (hφ : LowerSemicontinuous φ)
    (hφ0 : φ X.triv ≤ 0) {C : ℝ} (hC : ∀ v, C ≤ φ v) :
    X.IsPSH (d : ℝ) (D.subvarietyTestLimit d φ) := by
  refine isPSH_of_antitone_seq (tendsto_add_div_factorial (d : ℝ) (D.c0 : ℝ))
    (fun j => isPSH_subvarietyTestApprox hC (Nat.factorial_pos j))
    (fun v => antitone_subvarietyTestApprox_factorial hC v) (fun v => rfl) ⟨X.triv, ?_⟩
  have h1 : (C : EReal) ≤ X.envelope (d : ℝ) (fun w => (φ w : EReal)) X.triv :=
    FSSystem.le_envelope (F := X.fsSystem) (isPSH_const X (Nat.cast_nonneg d) C)
      (fun w => EReal.coe_le_coe_iff.2 (hC w)) X.triv
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot C)
    (h1.trans (envelope_le_subvarietyTestLimit hd hφ hφ0 hC X.triv))

/-- **`u = P_d(φ)` on the divisorial points** (step (c)): `u ≤ u_{j!} ≤ P_d(φ) + A/j!`. -/
theorem subvarietyTestLimit_le_envelope_of_isDivisorial {C : ℝ} (hC : ∀ v, C ≤ φ v)
    {v : X.an} (hv : X.IsDivisorial v) :
    D.subvarietyTestLimit d φ v ≤ X.envelope (d : ℝ) (fun w => (φ w : EReal)) v := by
  obtain ⟨A, hA, h⟩ := exists_subvarietyTestApprox_le_envelope_add (D := D) (d := d) hC hv
  refine ProjBerk.ereal_le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨j, hj⟩ := exists_nat_gt (A / ε)
  have hfac : (j : ℝ) ≤ (Nat.factorial j : ℝ) := by exact_mod_cast Nat.self_le_factorial j
  have hfac0 : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hAε : A / (Nat.factorial j : ℝ) ≤ ε := by
    rw [div_le_iff₀ hfac0]
    rw [div_lt_iff₀ hε] at hj
    nlinarith
  calc D.subvarietyTestLimit d φ v ≤ D.subvarietyTestApprox d φ (Nat.factorial j) v :=
        iInf_le _ j
    _ ≤ X.envelope (d : ℝ) (fun w => (φ w : EReal)) v +
          ((A / (Nat.factorial j : ℕ) : ℝ) : EReal) := h _ (Nat.factorial_pos j)
    _ ≤ X.envelope (d : ℝ) (fun w => (φ w : EReal)) v + (ε : EReal) := by
        gcongr

variable [IsAlgClosed k] (D) in
include D in
/-- **`thm:sg-ep-charp`, integer class, obstacle `≤ 0`** (steps (a)–(d)): given cone trace data
`D`, for `d ∈ ℤ_{>0}` and a PL function `φ ≤ 0` on `X^an`, `P_d(φ)` is `d`-psh; in fact
`P_d(φ) = lim_j u_{j!}`. -/
theorem isPSH_envelope_nat_of_nonpos (hd : 0 < d) (hφ : X.IsPL φ) (hφ0 : ∀ v, φ v ≤ 0) :
    X.IsPSH (d : ℝ) (X.envelope (d : ℝ) fun v => (φ v : EReal)) := by
  have hcont : Continuous φ := FSSystem.IsPL.continuous hφ
  obtain ⟨C₀, hC₀⟩ := FSSystem.exists_abs_le_of_continuous hcont
  have hC : ∀ v, -C₀ ≤ φ v := fun v => neg_le_of_abs_le (hC₀ v)
  have hlsc := hcont.lowerSemicontinuous
  have hU := isPSH_subvarietyTestLimit (D := D) hd hlsc (hφ0 X.triv) hC
  have hUφ : D.subvarietyTestLimit d φ ≤ fun v => (φ v : EReal) :=
    hU.le_of_forall_isDivisorial_le (continuous_coe_real_ereal.comp hcont).upperSemicontinuous
      (fun v => EReal.coe_ne_top _) fun w hw =>
        (subvarietyTestLimit_le_envelope_of_isDivisorial hC hw).trans
          (FSSystem.envelope_le X.fsSystem _ _ w)
  have heq : X.envelope (d : ℝ) (fun v => (φ v : EReal)) = D.subvarietyTestLimit d φ :=
    le_antisymm (fun v => envelope_le_subvarietyTestLimit hd hlsc (hφ0 X.triv) hC v)
      (FSSystem.le_envelope (F := X.fsSystem) hU hUφ)
  rw [heq]
  exact hU

end ConeTraceData

/-! ### The envelope property -/

section Main

variable [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]

include p in
/-- **`thm:sg-ep-charp`, integer class, obstacle `≤ 0`**: for `X` projectively normal with
smooth charts over an algebraically closed field of characteristic `p`, `d ∈ ℤ_{>0}` and a PL
function `φ ≤ 0` on `X^an`, `P_d(φ)` is `d`-psh. For `dim X = 0`, `X^an` is a point; otherwise
this is `ConeTraceData.isPSH_envelope_nat_of_nonpos` for cone trace data
(`ConeTraceData.nonempty`). -/
theorem isPSH_envelope_nat_of_charP (hX : X.IsProjNormal) (hs : X.HasSmoothCharts) {d : ℕ}
    (hd : 0 < d) {φ : X.an → ℝ} (hφ : X.IsPL φ) (hφ0 : ∀ v, φ v ≤ 0) :
    X.IsPSH (d : ℝ) (X.envelope (d : ℝ) fun v => (φ v : EReal)) := by
  rcases Nat.eq_zero_or_pos X.dim with h0 | hn
  · have := subsingleton_an_of_dim_eq_zero h0
    exact isPSH_envelope_of_subsingleton (Nat.cast_nonneg d) φ
  · obtain ⟨D⟩ := ConeTraceData.nonempty (X := X) (p := p) hX hs hn
    exact D.isPSH_envelope_nat_of_nonpos hd hφ hφ0

end Main

/-- **FHX Theorem 3.1 for smooth projectively normal `X` in characteristic `p`**
(**`thm:sg-ep-charp`**, FHX `thm:smooth-EP`): let `k` be algebraically closed of characteristic
`p > 0` and `X = V(I) ⊆ ℙᴹ` projectively normal with smooth charts. Then every `θ ∈ ℝ` has the
envelope property on `X` (for the classes `θ c₁(O_X(1))`). By `thm:sg-reduction` and
`lem:sg-pl-separate` it suffices that `P_d(φ)` is `d`-psh for `d ∈ ℤ_{>0}` and PL `φ ≤ 0`
(`isPSH_envelope_nat_of_charP`). -/
theorem hasEnvelopeProperty_of_charP {k : Type u} [Field k] [IsAlgClosed k] (p : ℕ)
    [Fact p.Prime] [CharP k p] {M : ℕ} (X : ProjSubvariety k M) (hX : X.IsProjNormal)
    (hs : X.HasSmoothCharts) (θ : ℝ) : X.HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_forall_nat (separatesPoints_isPL X)
    (fun _ hd _ hφ hφ0 => isPSH_envelope_nat_of_charP p hX hs hd hφ hφ0) θ

end ProjSubvariety

end EnvelopeProperty
