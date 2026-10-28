/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroChartTests
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroPolynomial

/-!
# Polynomial envelope assembly using only actual chart valuation tests

The discrepancy input is needed at the original trivial point and the
actual chart DVR points retained by the Shilov proof. All functions and
the envelope belong to the original analytification and FS system.
-/

open scoped NNReal ENNReal Topology Polynomial

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty.ProjSubvariety

open ProjBerk (phiIdeal)

universe u

variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}
variable {B : ℕ → Ideal X.ConeRing} {d c : ℕ} {φ : X.an → ℝ}

/-- The whole ideal potential is exactly the finite supremum of actual
chart DVR orders of its whole homogeneous polynomial generators. -/
theorem coneIdealPotential_chartTest_eq_finset_sup (j : X.ChartIdx)
    (V : BirationalDVR k (X.ChartRing j.1)) (b : ℕ) (hb : 0 < b)
    (htorus : ∀ F : X.ChartRing j.1, V.ord F = F.support.inf fun ℓ =>
      V.ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞))
    (C : Ideal X.ConeRing) (G : Finset (MvPolynomial (Fin (M + 1)) k)[X])
    (hhom : ∀ F ∈ G, ∃ e : ℕ, ∀ ℓ : ℕ, (F.coeff ℓ).IsHomogeneous e)
    (hle : (Ideal.span (G : Set (MvPolynomial (Fin (M + 1)) k)[X])).map X.coneMk ≤ C)
    (hsat : C ≤ X.saturation
      ((Ideal.span (G : Set (MvPolynomial (Fin (M + 1)) k)[X])).map X.coneMk)) :
    X.coneIdealPotential C (X.chartDivPoint j.1 V b) =
      G.sup fun F => -(((b : ℝ)⁻¹ : ℝ) : EReal) *
        (V.ord (F.map (X.quotDehom j.1).toRingHom) : EReal) := by
  rw [coneIdealPotential_eq_of_saturationBounds hle hsat, coneIdealPotential,
    Ideal.comap_map_of_surjective' _ coneMk_surjective, phiIdeal_sup_ker_coneMk,
    ProjBerk.phiIdeal_span_finset]
  apply Finset.sup_congr rfl
  intro F hF
  obtain ⟨e, he⟩ := hhom F hF
  exact logAbs_gaussExt_chartDivPoint V b hb htorus he

/-- Sectionwise extended-real bounds on actual homogeneous generators bound
the whole cone ideal at the witnessed chart test point. -/
theorem coneIdealPotential_chartTest_le_of_generator_orders (j : X.ChartIdx)
    (V : BirationalDVR k (X.ChartRing j.1)) (b : ℕ) (hb : 0 < b)
    (htorus : ∀ F : X.ChartRing j.1, V.ord F = F.support.inf fun ℓ =>
      V.ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞))
    (C : Ideal X.ConeRing) (G : Finset (MvPolynomial (Fin (M + 1)) k)[X])
    (hhom : ∀ F ∈ G, ∃ e : ℕ, ∀ ℓ : ℕ, (F.coeff ℓ).IsHomogeneous e)
    (hle : (Ideal.span (G : Set (MvPolynomial (Fin (M + 1)) k)[X])).map X.coneMk ≤ C)
    (hsat : C ≤ X.saturation
      ((Ideal.span (G : Set (MvPolynomial (Fin (M + 1)) k)[X])).map X.coneMk))
    {T : EReal} (horder : ∀ F ∈ G, -(((b : ℝ)⁻¹ : ℝ) : EReal) *
      (V.ord (F.map (X.quotDehom j.1).toRingHom) : EReal) ≤ T) :
    X.coneIdealPotential C (X.chartDivPoint j.1 V b) ≤ T := by
  rw [coneIdealPotential_chartTest_eq_finset_sup j V b hb htorus C G hhom hle hsat]
  exact Finset.sup_le horder

/-- Each genuine original obstacle generator gives a lower bound on the
original obstacle potential through its actual dehomogenized chart order. -/
theorem chartTest_order_le_phiIdeal_obstacleIdeal (j : X.ChartIdx)
    (V : BirationalDVR k (X.ChartRing j.1)) (b : ℕ) (hb : 0 < b)
    (htorus : ∀ F : X.ChartRing j.1, V.ord F = F.support.inf fun ℓ =>
      V.ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞))
    {q : ℕ} {F : (MvPolynomial (Fin (M + 1)) k)[X]}
    (hF : F ∈ X.obstacleSpace d φ q) :
    -(((b : ℝ)⁻¹ : ℝ) : EReal) *
      (V.ord (F.map (X.quotDehom j.1).toRingHom) : EReal) ≤
        phiIdeal (X.obstacleIdeal d φ q) (X.chartDivPoint j.1 V b).1 := by
  rw [← logAbs_gaussExt_chartDivPoint V b hb htorus (fun ℓ => hF.1 ℓ)]
  exact ProjBerk.le_phiIdeal _ _ (Ideal.subset_span hF)

private theorem isPSH_coneIdealLimit_of_polynomialGenerators
    (hgen : ∀ m : ℕ, 0 < m →
      X.HasBoundedPolynomialConeGenerators (B m) (m * d + c))
    (hinc : ∀ m : ℕ, 0 < m → X.coneObstacleIdeal d φ m ≤ B m)
    (hsub : ∀ m l : ℕ, 0 < m → 0 < l → B (m * l) ≤ X.saturation (B m ^ l))
    (hd : 0 < d) (hφ : LowerSemicontinuous φ) (hφ0 : φ X.triv ≤ 0)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) : X.IsPSH (d : ℝ) (X.coneIdealLimit B) := by
  have hne (m : ℕ) (hm : 0 < m) : B m ≠ ⊥ :=
    ne_bot_of_le_ne_bot (coneObstacleIdeal_ne_bot hC m) (hinc m hm)
  have hPSH (m : ℕ) (hm : 0 < m) :
      X.IsPSH ((d : ℝ) + (c : ℝ) / m) (X.coneIdealApprox B m) := by
    have h :=
      (isFS_coneIdealApprox_of_polynomial_generators hm (hne m hm) (hgen m hm)).isPSH
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

/-- Intermediate envelope criterion using actual finite polynomials and
raw discrepancy bounds only on the witnessed chart tests of the original
Shilov proof. No arbitrary cone-DVR restriction is an input or conclusion. -/
theorem isPSH_envelope_of_polynomialConeIdealChartTests [IsAlgClosed k]
    (hgen : ∀ m : ℕ, 0 < m →
      X.HasBoundedPolynomialConeGenerators (B m) (m * d + c))
    (hinc : ∀ m : ℕ, 0 < m → X.coneObstacleIdeal d φ m ≤ B m)
    (hsub : ∀ m l : ℕ, 0 < m → 0 < l → B (m * l) ≤ X.saturation (B m ^ l))
    (hval : ∀ v : X.an, X.IsChartTestPoint v → ∃ A : ℝ, 0 ≤ A ∧
      ∀ m : ℕ, 0 < m → ∃ q : ℕ, 0 < q ∧ X.coneIdealPotential (B m) v ≤
        (((m : ℝ) / q : ℝ) : EReal) * phiIdeal (X.obstacleIdeal d φ q) v.1 + (A : EReal))
    (hd : 0 < d) (hφ : X.IsPL φ) (hφ0 : ∀ v, φ v ≤ 0) :
    X.IsPSH (d : ℝ) (X.envelope (d : ℝ) fun v => (φ v : EReal)) := by
  have hcont : Continuous φ := FSSystem.IsPL.continuous hφ
  obtain ⟨C₀, hC₀⟩ := FSSystem.exists_abs_le_of_continuous hcont
  have hC : ∀ v, -C₀ ≤ φ v := fun v => neg_le_of_abs_le (hC₀ v)
  have hU := isPSH_coneIdealLimit_of_polynomialGenerators hgen hinc hsub hd
    hcont.lowerSemicontinuous (hφ0 X.triv) hC
  have hUφ : X.coneIdealLimit B ≤ fun v => (φ v : EReal) :=
    hU.le_of_forall_isChartTestPoint_le_isPL hφ fun w hw =>
      (coneIdealLimit_le_envelope_of_divisorial_estimate (hval w hw)).trans
        (FSSystem.envelope_le X.fsSystem _ _ w)
  have heq : (X.envelope (d : ℝ) fun v => (φ v : EReal)) = X.coneIdealLimit B :=
    le_antisymm
      (fun v => envelope_le_coneIdealLimit hinc hsub hd hcont.lowerSemicontinuous
        (hφ0 X.triv) v)
      (FSSystem.le_envelope (F := X.fsSystem) hU hUφ)
  rw [heq]
  exact hU

/-- The actual witness-facing producer interface: one raw estimate at the
original trivial point, and one at each original chart DVR point with its
genuine positive parameter order and torus identity retained. -/
theorem isPSH_envelope_of_polynomialConeIdealChartEstimates [IsAlgClosed k]
    (hgen : ∀ m : ℕ, 0 < m →
      X.HasBoundedPolynomialConeGenerators (B m) (m * d + c))
    (hinc : ∀ m : ℕ, 0 < m → X.coneObstacleIdeal d φ m ≤ B m)
    (hsub : ∀ m l : ℕ, 0 < m → 0 < l → B (m * l) ≤ X.saturation (B m ^ l))
    (htriv : ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, 0 < m → ∃ q : ℕ, 0 < q ∧
      X.coneIdealPotential (B m) X.triv ≤
        (((m : ℝ) / q : ℝ) : EReal) * phiIdeal (X.obstacleIdeal d φ q) X.triv.1 + (A : EReal))
    (hchart : ∀ (j : X.ChartIdx) (V : BirationalDVR k (X.ChartRing j.1)) (b : ℕ),
      0 < b → (∀ F : X.ChartRing j.1, V.ord F = F.support.inf fun ℓ =>
        V.ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞)) →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, 0 < m → ∃ q : ℕ, 0 < q ∧
        X.coneIdealPotential (B m) (X.chartDivPoint j.1 V b) ≤
          (((m : ℝ) / q : ℝ) : EReal) *
            phiIdeal (X.obstacleIdeal d φ q) (X.chartDivPoint j.1 V b).1 + (A : EReal))
    (hd : 0 < d) (hφ : X.IsPL φ) (hφ0 : ∀ v, φ v ≤ 0) :
    X.IsPSH (d : ℝ) (X.envelope (d : ℝ) fun v => (φ v : EReal)) := by
  apply isPSH_envelope_of_polynomialConeIdealChartTests hgen hinc hsub _ hd hφ hφ0
  intro v hv
  rcases hv with rfl | ⟨j, V, b, hb, htorus, rfl⟩
  · exact htriv
  · exact hchart j V b hb htorus

end EnvelopeProperty.ProjSubvariety
