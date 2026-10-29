/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZero

/-!
# Envelope assembly from actual relative polynomial generators

Relative sections over `k[t]` give arbitrary polynomials in `t` with
homogeneous `x`-coefficients. This file keeps those entire polynomials as
generators, so no assertion that individual `t`-components lie in the
multiplier ideal is needed. The final criterion takes actual finite
polynomials, their coefficient degrees, and saturated ideal bounds.
-/

open scoped NNReal ENNReal Topology Polynomial

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty.ProjSubvariety

open ProjBerk (phiIdeal)

universe u

variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}

/-- Actual finite polynomial generators with bounded homogeneous
`x`-coefficients, generating the cone ideal away from the vertex. -/
def HasBoundedPolynomialConeGenerators (X : ProjSubvariety k M)
    (B : Ideal X.ConeRing) (e : ℕ) : Prop :=
  ∃ G : Finset (MvPolynomial (Fin (M + 1)) k)[X],
    (∀ F ∈ G, ∀ ℓ : ℕ, ∃ b ≤ e, (F.coeff ℓ).IsHomogeneous b) ∧
    (Ideal.span (G : Set (MvPolynomial (Fin (M + 1)) k)[X])).map X.coneMk ≤ B ∧
    B ≤ X.saturation ((Ideal.span (G : Set (MvPolynomial (Fin (M + 1)) k)[X])).map X.coneMk)

/-- Actual polynomial generators give a Fubini–Study function in the
required class, retaining the entire polynomials throughout the proof. -/
theorem isFS_coneIdealApprox_of_polynomial_generators {B : ℕ → Ideal X.ConeRing}
    {d c m : ℕ} (hm : 0 < m) (hne : B m ≠ ⊥)
    (hgen : X.HasBoundedPolynomialConeGenerators (B m) (m * d + c)) :
    X.IsFS ((d : ℚ) + c / m) (X.coneIdealApprox B m) := by
  classical
  obtain ⟨G, hGdeg, hGle, hGsat⟩ := hgen
  have hφ (v : X.an) : X.coneIdealPotential (B m) v =
      phiIdeal (Ideal.span (G : Set (MvPolynomial (Fin (M + 1)) k)[X])) v.1 := by
    rw [coneIdealPotential_eq_of_saturationBounds hGle hGsat, coneIdealPotential,
      Ideal.comap_map_of_surjective' _ coneMk_surjective, phiIdeal_sup_ker_coneMk]
  have hne' : ∃ F ∈ (G : Set (MvPolynomial (Fin (M + 1)) k)[X]), X.coneMk F ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hbot : (Ideal.span (G : Set (MvPolynomial (Fin (M + 1)) k)[X])).map X.coneMk = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.span_le]
      exact fun F hF => RingHom.mem_ker.mpr (hzero F hF)
    apply hne
    rw [hbot, coneSaturation_bot] at hGsat
    exact le_bot_iff.mp hGsat
  have hcoeff : ∀ F ∈ (G : Set (MvPolynomial (Fin (M + 1)) k)[X]), ∀ ℓ : ℕ,
      ∃ b ≤ 1 * (m * d + c), (F.coeff ℓ).IsHomogeneous b := by
    intro F hF ℓ
    simpa only [one_mul] using hGdeg F hF ℓ
  obtain ⟨D, -, hD, hDeq⟩ := isFS_inv_mul_phiIdeal (X := X)
    (m := 1) (d := m * d + c) one_pos rfl hcoeff hne'
  have hFS : X.IsFS ((m * d + c : ℕ) : ℚ)
      (fun v => phiIdeal (Ideal.span (G : Set (MvPolynomial (Fin (M + 1)) k)[X])) v.1) :=
    ⟨D, hD, fun v => by rw [hDeq v.1]; simp⟩
  have h := hFS.smul (inv_pos.mpr (Nat.cast_pos.mpr hm) : (0 : ℚ) < (m : ℚ)⁻¹)
  have hclass : (m : ℚ)⁻¹ * ((m * d + c : ℕ) : ℚ) = (d : ℚ) + c / m := by
    have : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    push_cast
    field_simp
  rw [hclass] at h
  convert h using 2 with v
  rw [coneIdealApprox, hφ v]
  push_cast
  rfl

variable {B : ℕ → Ideal X.ConeRing} {d c : ℕ} {φ : X.an → ℝ}

private theorem isPSH_coneIdealLimit_of_fsApprox
    (hFS : ∀ m : ℕ, 0 < m → X.IsFS ((d : ℚ) + c / m) (X.coneIdealApprox B m))
    (hinc : ∀ m : ℕ, 0 < m → X.coneObstacleIdeal d φ m ≤ B m)
    (hsub : ∀ m l : ℕ, 0 < m → 0 < l → B (m * l) ≤ X.saturation (B m ^ l))
    (hd : 0 < d) (hφ : LowerSemicontinuous φ) (hφ0 : φ X.triv ≤ 0)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) : X.IsPSH (d : ℝ) (X.coneIdealLimit B) := by
  have hPSH (m : ℕ) (hm : 0 < m) :
      X.IsPSH ((d : ℝ) + (c : ℝ) / m) (X.coneIdealApprox B m) := by
    have h := (hFS m hm).isPSH
    have heq : (((d : ℚ) + (c : ℚ) / m : ℚ) : ℝ) = (d : ℝ) + (c : ℝ) / m := by
      push_cast
      rfl
    rwa [heq] at h
  refine isPSH_of_antitone_seq (tendsto_coneIdealClass (d : ℝ) (c : ℝ))
    (fun j => hPSH (Nat.factorial j) (Nat.factorial_pos j))
    (fun v => antitone_coneIdealApprox_factorial hsub v) (fun _ => rfl) ⟨X.triv, ?_⟩
  have hconst : (C : EReal) ≤ X.envelope (d : ℝ) (fun w => (φ w : EReal)) X.triv :=
    FSSystem.le_envelope (F := X.fsSystem) (isPSH_const X (Nat.cast_nonneg d) C)
      (fun w => EReal.coe_le_coe_iff.mpr (hC w)) X.triv
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot C)
    (hconst.trans (envelope_le_coneIdealLimit hinc hsub hd hφ hφ0 X.triv))

/-- Intermediate envelope criterion with actual finite relative polynomial
generators. All FS and PSH approximation assertions are conclusions of the
proof; the inputs are polynomial coefficients and ideal/valuation estimates. -/
theorem isPSH_envelope_of_polynomialConeIdealEstimates [IsAlgClosed k]
    (hgen : ∀ m : ℕ, 0 < m →
      X.HasBoundedPolynomialConeGenerators (B m) (m * d + c))
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
  have hne (m : ℕ) (hm : 0 < m) : B m ≠ ⊥ :=
    ne_bot_of_le_ne_bot (coneObstacleIdeal_ne_bot hC m) (hinc m hm)
  have hFS (m : ℕ) (hm : 0 < m) :
      X.IsFS ((d : ℚ) + c / m) (X.coneIdealApprox B m) :=
    isFS_coneIdealApprox_of_polynomial_generators hm (hne m hm) (hgen m hm)
  have hU := isPSH_coneIdealLimit_of_fsApprox hFS hinc hsub hd hcont.lowerSemicontinuous
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
