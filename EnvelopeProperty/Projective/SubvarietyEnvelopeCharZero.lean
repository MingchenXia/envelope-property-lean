/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroCore

/-!
# The analytic assembly step of the characteristic-zero envelope argument

The result below is a criterion using actual cone ideals and their algebraic
and raw valuative estimates. It proves the PSH limit and its equality to the
original envelope. A construction of those ideals from the genuine scheme
multiplier ideals is still needed before this criterion can prove
`SmoothEnvelopeCharZero`; this file does not assume or assert that construction.
-/

open scoped NNReal ENNReal Topology Polynomial

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty.ProjSubvariety

open ProjBerk (phiIdeal)

universe u

variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}
variable {B : ℕ → Ideal X.ConeRing} {d c : ℕ} {φ : X.an → ℝ}

/-- The factorial subsequence turns divisibility monotonicity into an ordinary
decreasing sequence. -/
def coneIdealLimit (X : ProjSubvariety k M) (B : ℕ → Ideal X.ConeRing)
    (v : X.an) : EReal :=
  ⨅ j : ℕ, X.coneIdealApprox B (Nat.factorial j) v

/-- Subadditivity up to saturation makes the factorial potentials decreasing. -/
theorem antitone_coneIdealApprox_factorial
    (hsub : ∀ m l : ℕ, 0 < m → 0 < l → B (m * l) ≤ X.saturation (B m ^ l))
    (v : X.an) : Antitone fun j => X.coneIdealApprox B (Nat.factorial j) v :=
  antitone_nat_of_succ_le fun j => by
    rw [Nat.factorial_succ, mul_comm]
    exact coneIdealApprox_mul_le hsub (Nat.factorial_pos j) (Nat.succ_pos j) v

/-- The cone ideal estimates imply domination of the envelope by the limit. -/
theorem envelope_le_coneIdealLimit
    (hinc : ∀ m : ℕ, 0 < m → X.coneObstacleIdeal d φ m ≤ B m)
    (hsub : ∀ m l : ℕ, 0 < m → 0 < l → B (m * l) ≤ X.saturation (B m ^ l))
    (hd : 0 < d) (hφ : LowerSemicontinuous φ) (hφ0 : φ X.triv ≤ 0) (v : X.an) :
    X.envelope (d : ℝ) (fun w => (φ w : EReal)) v ≤ X.coneIdealLimit B v :=
  le_iInf fun j => envelope_le_coneIdealApprox hinc hsub hd hφ hφ0 (Nat.factorial_pos j) v

/-- The classes of the normalized, uniformly generated ideals tend to `d`. -/
theorem tendsto_coneIdealClass (d c : ℝ) :
    Tendsto (fun j : ℕ => d + c / (Nat.factorial j : ℝ)) atTop (𝓝 d) := by
  have hfac : Tendsto Nat.factorial atTop atTop :=
    tendsto_atTop_mono Nat.self_le_factorial tendsto_id
  simpa using tendsto_const_nhds.add ((tendsto_const_div_atTop_nhds_zero_nat c).comp hfac)

/-- Bounded homogeneous generators and subadditivity produce a PSH limit in
the original class. Nontriviality follows from the original obstacle ideals. -/
theorem isPSH_coneIdealLimit
    (hgen : ∀ m : ℕ, 0 < m → X.HasBoundedConeGenerators (B m) (m * d + c))
    (hinc : ∀ m : ℕ, 0 < m → X.coneObstacleIdeal d φ m ≤ B m)
    (hsub : ∀ m l : ℕ, 0 < m → 0 < l → B (m * l) ≤ X.saturation (B m ^ l))
    (hd : 0 < d) (hφ : LowerSemicontinuous φ) (hφ0 : φ X.triv ≤ 0)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) : X.IsPSH (d : ℝ) (X.coneIdealLimit B) := by
  have hne (m : ℕ) (hm : 0 < m) : B m ≠ ⊥ :=
    ne_bot_of_le_ne_bot (coneObstacleIdeal_ne_bot hC m) (hinc m hm)
  have hPSH (m : ℕ) (hm : 0 < m) :
      X.IsPSH ((d : ℝ) + (c : ℝ) / m) (X.coneIdealApprox B m) := by
    have h := (isFS_coneIdealApprox_of_bounded_generators hm (hne m hm) (hgen m hm)).isPSH
    have heq : (((d : ℚ) + (c : ℚ) / m : ℚ) : ℝ) = (d : ℝ) + (c : ℝ) / m := by
      push_cast
      rfl
    rwa [heq] at h
  refine isPSH_of_antitone_seq (tendsto_coneIdealClass (d : ℝ) (c : ℝ))
    (fun j => hPSH (Nat.factorial j) (Nat.factorial_pos j))
    (fun v => antitone_coneIdealApprox_factorial hsub v) (fun _ => rfl) ⟨X.triv, ?_⟩
  have hconst : (C : EReal) ≤ X.envelope (d : ℝ) (fun w => (φ w : EReal)) X.triv :=
    FSSystem.le_envelope (F := X.fsSystem) (isPSH_const X (Nat.cast_nonneg d) C)
      (fun w => EReal.coe_le_coe_iff.2 (hC w)) X.triv
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot C)
    (hconst.trans (envelope_le_coneIdealLimit hinc hsub hd hφ hφ0 X.triv))

/-- The raw discrepancy bound identifies the limit at each original
divisorial point. Only a vanishing scalar error is used in this step. -/
theorem coneIdealLimit_le_envelope_of_divisorial_estimate {v : X.an}
    (hval : ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, 0 < m → ∃ q : ℕ, 0 < q ∧
      X.coneIdealPotential (B m) v ≤
        (((m : ℝ) / q : ℝ) : EReal) * phiIdeal (X.obstacleIdeal d φ q) v.1 + (A : EReal)) :
    X.coneIdealLimit B v ≤ X.envelope (d : ℝ) (fun w => (φ w : EReal)) v := by
  obtain ⟨A, _, h⟩ := exists_coneIdealApprox_le_envelope_add hval
  refine ProjBerk.ereal_le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨j, hj⟩ := exists_nat_gt (A / ε)
  have hfac : (j : ℝ) ≤ (Nat.factorial j : ℝ) := by
    exact_mod_cast Nat.self_le_factorial j
  have hfac0 : (0 : ℝ) < (Nat.factorial j : ℝ) := by
    exact_mod_cast Nat.factorial_pos j
  have hAε : A / (Nat.factorial j : ℝ) ≤ ε := by
    rw [div_le_iff₀ hfac0]
    rw [div_lt_iff₀ hε] at hj
    nlinarith
  calc X.coneIdealLimit B v ≤ X.coneIdealApprox B (Nat.factorial j) v := iInf_le _ j
    _ ≤ X.envelope (d : ℝ) (fun w => (φ w : EReal)) v +
          ((A / (Nat.factorial j : ℕ) : ℝ) : EReal) := h _ (Nat.factorial_pos j)
    _ ≤ X.envelope (d : ℝ) (fun w => (φ w : EReal)) v + (ε : EReal) := by
        gcongr

/-- Intermediate envelope criterion from actual cone ideals. Every supplied
estimate is on the ideals or their raw potentials; PSH approximation and the
envelope conclusion are proved by the preceding lemmas. This theorem does not
construct the ideals or discharge the scheme-to-cone geometric bridge. -/
theorem isPSH_envelope_of_coneIdealEstimates [IsAlgClosed k]
    (hgen : ∀ m : ℕ, 0 < m → X.HasBoundedConeGenerators (B m) (m * d + c))
    (hinc : ∀ m : ℕ, 0 < m → X.coneObstacleIdeal d φ m ≤ B m)
    (hsub : ∀ m l : ℕ, 0 < m → 0 < l → B (m * l) ≤ X.saturation (B m ^ l))
    (hval : ∀ v : X.an, X.IsDivisorial v → ∃ A : ℝ, 0 ≤ A ∧
      ∀ m : ℕ, 0 < m → ∃ q : ℕ, 0 < q ∧ X.coneIdealPotential (B m) v ≤
        (((m : ℝ) / q : ℝ) : EReal) * phiIdeal (X.obstacleIdeal d φ q) v.1 + (A : EReal))
    (hd : 0 < d) (hφ : X.IsPL φ) (hφ0 : ∀ v, φ v ≤ 0) :
    X.IsPSH (d : ℝ) (X.envelope (d : ℝ) fun v => (φ v : EReal)) := by
  have hcont : Continuous φ := FSSystem.IsPL.continuous hφ
  obtain ⟨C₀, hC₀⟩ := FSSystem.exists_abs_le_of_continuous hcont
  have hC : ∀ v, -C₀ ≤ φ v := fun v => neg_le_of_abs_le (hC₀ v)
  have hU := isPSH_coneIdealLimit hgen hinc hsub hd hcont.lowerSemicontinuous
    (hφ0 X.triv) hC
  have hUφ : X.coneIdealLimit B ≤ fun v => (φ v : EReal) :=
    hU.le_of_forall_isDivisorial_le (continuous_coe_real_ereal.comp hcont).upperSemicontinuous
      (fun _ => EReal.coe_ne_top _) fun w hw =>
        (coneIdealLimit_le_envelope_of_divisorial_estimate (hval w hw)).trans
          (FSSystem.envelope_le X.fsSystem _ _ w)
  have heq : (X.envelope (d : ℝ) fun v => (φ v : EReal)) = X.coneIdealLimit B :=
    le_antisymm
      (fun v => envelope_le_coneIdealLimit hinc hsub hd hcont.lowerSemicontinuous
        (hφ0 X.triv) v)
      (FSSystem.le_envelope (F := X.fsSystem) hU hUφ)
  rw [heq]
  exact hU

end EnvelopeProperty.ProjSubvariety
