/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietyJm
import EnvelopeProperty.Projective.SubvarietyComparison
import EnvelopeProperty.Projective.EnvelopeCriterion

/-!
# Cone ideal estimates for the characteristic-zero envelope argument

This file proves the Fubini–Study and arithmetic parts of the multiplier-ideal
argument on the original analytification of a projective subvariety. The ideals
are genuine ideals of the homogeneous cone ring; no envelope property is an
input. The geometric construction of a sequence satisfying the estimates is
separate from these characteristic-independent lemmas.
-/

open scoped NNReal ENNReal Topology Polynomial

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty.ProjSubvariety

open ProjBerk (phiIdeal)

universe u

variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}

/-- The ideal potential of a cone ideal, evaluated on the original `X.an`. -/
def coneIdealPotential (X : ProjSubvariety k M) (B : Ideal X.ConeRing) (v : X.an) : EReal :=
  phiIdeal (B.comap X.coneMk) v.1

/-- The normalized potential associated to the `m`th cone ideal. -/
def coneIdealApprox (X : ProjSubvariety k M) (B : ℕ → Ideal X.ConeRing) (m : ℕ)
    (v : X.an) : EReal :=
  (((m : ℝ)⁻¹ : ℝ) : EReal) * X.coneIdealPotential (B m) v

/-- Homogeneous generators of bounded degree which generate away from the vertex.
This is an algebraic property of the actual ideal, not a psh approximation assumption. -/
def HasBoundedConeGenerators (X : ProjSubvariety k M) (B : Ideal X.ConeRing) (e : ℕ) : Prop :=
  ∃ G : Set X.ConeRing,
    (∀ g ∈ G, ∃ (s : MvPolynomial (Fin (M + 1)) k) (b l : ℕ),
      b ≤ e ∧ s.IsHomogeneous b ∧ g = X.coneMk (Polynomial.C s * Polynomial.X ^ l)) ∧
    Ideal.span G ≤ B ∧ B ≤ X.saturation (Ideal.span G)

/-- A power of a cone ideal multiplies its potential by the exponent. -/
theorem coneIdealPotential_pow (B : Ideal X.ConeRing) (l : ℕ) (v : X.an) :
    X.coneIdealPotential (B ^ l) v = l * X.coneIdealPotential B v := by
  have h : B ^ l = ((B.comap X.coneMk) ^ l).map X.coneMk := by
    rw [Ideal.map_pow, Ideal.map_comap_of_surjective _ coneMk_surjective]
  dsimp only [coneIdealPotential]
  rw [h, Ideal.comap_map_of_surjective' _ coneMk_surjective, phiIdeal_sup_ker_coneMk,
    ProjBerk.phiIdeal_pow]

/-- Saturation bounds identify the potentials on `X.an`. -/
theorem coneIdealPotential_eq_of_saturationBounds {B C : Ideal X.ConeRing}
    (hBC : B ≤ C) (hCB : C ≤ X.saturation B) (v : X.an) :
    X.coneIdealPotential C v = X.coneIdealPotential B v :=
  le_antisymm ((ProjBerk.phiIdeal_mono v.1 (Ideal.comap_mono hCB)).trans_eq
      (phiIdeal_comap_saturation B v.1))
    (ProjBerk.phiIdeal_mono v.1 (Ideal.comap_mono hBC))

/-- Saturation of zero is zero, because the cone ring is a domain and a
nonzero homogeneous coordinate belongs to the irrelevant ideal. -/
theorem coneSaturation_bot : X.saturation (⊥ : Ideal X.ConeRing) = ⊥ := by
  refine le_bot_iff.1 fun f hf => ?_
  obtain ⟨r, hr⟩ := mem_saturation_iff.1 hf
  obtain ⟨j, hj⟩ := X.exists_X_notMem
  have hx : Polynomial.C (X.coordMk (MvPolynomial.X j)) ^ r ∈ X.coneIrrelevant ^ r :=
    Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self
      (f := fun i => Polynomial.C (X.coordMk (MvPolynomial.X i))) j)) r
  have h0 := hr _ hx
  rw [Ideal.mem_bot, mul_eq_zero] at h0
  rw [Ideal.mem_bot]
  exact h0.resolve_left (pow_ne_zero _ (by
    rw [Ne, Polynomial.C_eq_zero, coordMk_eq_zero_iff]
    exact hj))

/-- Bounded homogeneous generators on the punctured cone give the required
Fubini–Study function in the class `d + c / m`. -/
theorem isFS_coneIdealApprox_of_bounded_generators {B : ℕ → Ideal X.ConeRing}
    {d c m : ℕ} (hm : 0 < m) (hne : B m ≠ ⊥)
    (hgen : X.HasBoundedConeGenerators (B m) (m * d + c)) :
    X.IsFS ((d : ℚ) + c / m) (X.coneIdealApprox B m) := by
  classical
  obtain ⟨G, hGdeg, hGle, hGsat⟩ := hgen
  choose s b l hb hs hg using hGdeg
  let G' : Set (MvPolynomial (Fin (M + 1)) k)[X] :=
    Set.range fun g : G => Polynomial.C (s g.1 g.2) * Polynomial.X ^ l g.1 g.2
  have hG' : Ideal.span G = (Ideal.span G').map X.coneMk := by
    rw [Ideal.map_span]
    congr 1
    ext g
    constructor
    · intro hgG
      exact ⟨_, ⟨⟨g, hgG⟩, rfl⟩, (hg g hgG).symm⟩
    · rintro ⟨_, ⟨⟨g', hg'⟩, rfl⟩, rfl⟩
      rw [← hg g' hg']
      exact hg'
  have hφ : ∀ v : X.an, X.coneIdealPotential (B m) v =
      phiIdeal (Ideal.span G') v.1 := by
    intro v
    rw [coneIdealPotential_eq_of_saturationBounds hGle hGsat, coneIdealPotential, hG',
      Ideal.comap_map_of_surjective' _ coneMk_surjective, phiIdeal_sup_ker_coneMk]
  have hne' : ∃ F ∈ G', X.coneMk F ≠ 0 := by
    by_contra h0
    push Not at h0
    have hbot : Ideal.span G = ⊥ := by
      rw [hG', Ideal.map_eq_bot_iff_le_ker, Ideal.span_le]
      exact fun F hF => RingHom.mem_ker.2 (h0 F hF)
    apply hne
    rw [hbot, coneSaturation_bot] at hGsat
    exact le_bot_iff.1 hGsat
  have hdegG' : ∀ F ∈ G', ∀ ℓ, ∃ e ≤ 1 * (m * d + c),
      (F.coeff ℓ).IsHomogeneous e := by
    rintro _ ⟨⟨g, hgG⟩, rfl⟩ ℓ
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs
    · exact ⟨b g hgG, by rw [one_mul]; exact hb g hgG, hs g hgG⟩
    · exact ⟨0, Nat.zero_le _, MvPolynomial.isHomogeneous_zero _ _ _⟩
  obtain ⟨D, -, hD, hDeq⟩ := isFS_inv_mul_phiIdeal (X := X)
    (m := 1) (d := m * d + c) one_pos rfl hdegG' hne'
  have hFS : X.IsFS ((m * d + c : ℕ) : ℚ) fun v => phiIdeal (Ideal.span G') v.1 :=
    ⟨D, hD, fun v => by rw [hDeq v.1]; simp⟩
  have h := hFS.smul (inv_pos.2 (Nat.cast_pos.2 hm) : (0 : ℚ) < (m : ℚ)⁻¹)
  have hclass : (m : ℚ)⁻¹ * ((m * d + c : ℕ) : ℚ) = (d : ℚ) + c / m := by
    have : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    push_cast
    field_simp
  rw [hclass] at h
  convert h using 2 with v
  rw [coneIdealApprox, hφ v]
  push_cast
  rfl

variable {B : ℕ → Ideal X.ConeRing} {d : ℕ} {φ : X.an → ℝ}

/-- Convert an actual element-order estimate in a birational DVR to the raw
cone-ideal potential estimate. No PSH or envelope assertion is an input. -/
theorem coneIdealPotential_le_of_element_orders {v : X.an}
    (V : BirationalDVR k X.ConeRing) {a : ℚ} (ha : 0 < a)
    (hlog : ∀ g : (MvPolynomial (Fin (M + 1)) k)[X],
      Berk.logAbs g (ProjBerk.gaussExt v.1) =
        -((a : ℝ) : EReal) * (V.ord (X.coneMk g) : EReal))
    {J C : Ideal X.ConeRing} (hJ : J ≠ ⊥) {slope A : ℝ} (hslope : 0 ≤ slope)
    (hord : ∀ o : ℕ, (∀ g ∈ J, (o : ℕ∞) ≤ V.ord g) →
      ∀ f ∈ C, ∀ ν : ℕ, V.ord f = ν → slope * o - A ≤ ν) :
    X.coneIdealPotential C v ≤ (slope : EReal) * X.coneIdealPotential J v +
      (((a : ℝ) * A : ℝ) : EReal) := by
  classical
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hlogν (g : (MvPolynomial (Fin (M + 1)) k)[X]) (ν : ℕ)
      (hν : V.ord (X.coneMk g) = ν) :
      Berk.logAbs g (ProjBerk.gaussExt v.1) = ((-((a : ℝ) * ν) : ℝ) : EReal) := by
    rw [hlog, hν, show ((ν : ℕ∞) : EReal) = ((ν : ℝ) : EReal) by norm_cast,
      ← EReal.coe_neg, ← EReal.coe_mul, neg_mul]
  have hex : ∃ o : ℕ, ∃ f ∈ J, V.ord f = o := by
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    obtain ⟨o, ho⟩ := ENat.ne_top_iff_exists.1 (mt V.ord_eq_top_iff.1 hf0)
    exact ⟨o, f, hf, ho.symm⟩
  obtain ⟨f₀, hf₀, hf₀o⟩ := Nat.find_spec hex
  have ho : ∀ g ∈ J, ((Nat.find hex : ℕ) : ℕ∞) ≤ V.ord g := by
    intro g hg
    by_cases hg0 : g = 0
    · rw [hg0, BirationalDVR.ord_zero]
      exact le_top
    · obtain ⟨ν, hν⟩ := ENat.ne_top_iff_exists.1 (mt V.ord_eq_top_iff.1 hg0)
      rw [← hν]
      exact_mod_cast Nat.find_min' hex ⟨g, hg, hν.symm⟩
  let o : ℕ := Nat.find hex
  have hL : ((-((a : ℝ) * o) : ℝ) : EReal) ≤ X.coneIdealPotential J v := by
    obtain ⟨g₀, rfl⟩ := coneMk_surjective (X := X) f₀
    rw [← hlogν g₀ o hf₀o]
    exact ProjBerk.le_phiIdeal _ v.1 (Ideal.mem_comap.2 hf₀)
  have hbound : ((slope * (-((a : ℝ) * o)) + (a : ℝ) * A : ℝ) : EReal) ≤
      (slope : EReal) * X.coneIdealPotential J v + (((a : ℝ) * A : ℝ) : EReal) := by
    rw [EReal.coe_add, EReal.coe_mul]
    exact add_le_add (ProjBerk.ereal_coe_mul_monotone hslope hL) le_rfl
  refine le_trans (iSup₂_le fun g hg => ?_) hbound
  by_cases hg0 : X.coneMk g = 0
  · rw [Berk.logAbs, gaussExt_val_eq_zero_of_coneMk_eq_zero v hg0, ENNReal.coe_zero,
      ENNReal.log_zero]
    exact bot_le
  · obtain ⟨ν, hν⟩ := ENat.ne_top_iff_exists.1 (mt V.ord_eq_top_iff.1 hg0)
    have h1 := hord o ho _ (Ideal.mem_comap.1 hg) ν hν.symm
    rw [hlogν g ν hν.symm, EReal.coe_le_coe_iff]
    nlinarith

/-- Subadditivity up to saturation gives divisibility monotonicity after normalization. -/
theorem coneIdealApprox_mul_le
    (hsub : ∀ m l : ℕ, 0 < m → 0 < l → B (m * l) ≤ X.saturation (B m ^ l))
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) (v : X.an) :
    X.coneIdealApprox B (m * l) v ≤ X.coneIdealApprox B m v := by
  have h : X.coneIdealPotential (B (m * l)) v ≤ l * X.coneIdealPotential (B m) v := by
    calc X.coneIdealPotential (B (m * l)) v
        ≤ X.coneIdealPotential (X.saturation (B m ^ l)) v :=
          ProjBerk.phiIdeal_mono v.1 (Ideal.comap_mono (hsub m l hm hl))
      _ = X.coneIdealPotential (B m ^ l) v := phiIdeal_comap_saturation _ _
      _ = l * X.coneIdealPotential (B m) v := coneIdealPotential_pow _ _ _
  have hl' : (l : EReal) = ((l : ℝ) : EReal) := rfl
  rw [hl'] at h
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hl'' : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hl.ne'
  calc X.coneIdealApprox B (m * l) v
      ≤ ((((m * l : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
          (((l : ℝ) : EReal) * X.coneIdealPotential (B m) v) :=
        ProjBerk.ereal_coe_mul_monotone (inv_nonneg.2 (Nat.cast_nonneg _)) h
    _ = X.coneIdealApprox B m v := by
        rw [ProjBerk.ereal_coe_mul_coe_mul, coneIdealApprox]
        congr 2
        push_cast
        field_simp

/-- An inclusion of obstacle ideals gives the normalized lower estimate. -/
theorem obstacleIdeal_le_coneIdealApprox
    (hinc : ∀ m : ℕ, 0 < m → X.coneObstacleIdeal d φ m ≤ B m)
    {m : ℕ} (hm : 0 < m) (v : X.an) :
    (((m : ℝ)⁻¹ : ℝ) : EReal) * phiIdeal (X.obstacleIdeal d φ m) v.1 ≤
      X.coneIdealApprox B m v := by
  apply ProjBerk.ereal_coe_mul_monotone (inv_nonneg.2 (Nat.cast_nonneg _))
  rw [← phiIdeal_comap_coneObstacleIdeal]
  exact ProjBerk.phiIdeal_mono v.1 (Ideal.comap_mono (hinc m hm))

/-- The obstacle-ideal formula and ideal estimates imply envelope domination;
the domination is a conclusion, not a supplied approximation hypothesis. -/
theorem envelope_le_coneIdealApprox
    (hinc : ∀ m : ℕ, 0 < m → X.coneObstacleIdeal d φ m ≤ B m)
    (hsub : ∀ m l : ℕ, 0 < m → 0 < l → B (m * l) ≤ X.saturation (B m ^ l))
    (hd : 0 < d) (hφ : LowerSemicontinuous φ) (hφ0 : φ X.triv ≤ 0)
    {m : ℕ} (hm : 0 < m) (v : X.an) :
    X.envelope (d : ℝ) (fun w => (φ w : EReal)) v ≤ X.coneIdealApprox B m v := by
  rw [envelope_eq_iSup_obstacleIdeal hd hφ hφ0 v]
  refine iSup₂_le fun q hq => ?_
  calc (((q : ℝ)⁻¹ : ℝ) : EReal) * phiIdeal (X.obstacleIdeal d φ q) v.1
      ≤ ((((q * m : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
          phiIdeal (X.obstacleIdeal d φ (q * m)) v.1 :=
        inv_mul_phiIdeal_obstacleIdeal_le_mul hq hm v
    _ ≤ X.coneIdealApprox B (q * m) v :=
        obstacleIdeal_le_coneIdealApprox hinc (Nat.mul_pos hq hm) v
    _ = X.coneIdealApprox B (m * q) v := by rw [mul_comm]
    _ ≤ X.coneIdealApprox B m v := coneIdealApprox_mul_le hsub hm hq v

/-- A raw discrepancy estimate for cone ideals gives an `O(1/m)` error at the
original divisorial point. The comparison to the envelope is proved here. -/
theorem exists_coneIdealApprox_le_envelope_add {v : X.an}
    (hval : ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, 0 < m → ∃ q : ℕ, 0 < q ∧
      X.coneIdealPotential (B m) v ≤
        (((m : ℝ) / q : ℝ) : EReal) * phiIdeal (X.obstacleIdeal d φ q) v.1 + (A : EReal)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, 0 < m →
      X.coneIdealApprox B m v ≤
        X.envelope (d : ℝ) (fun w => (φ w : EReal)) v + ((A / m : ℝ) : EReal) := by
  obtain ⟨A, hA, h⟩ := hval
  refine ⟨A, hA, fun m hm => ?_⟩
  obtain ⟨q, hq, hle⟩ := h m hm
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have e1 : (m : ℝ)⁻¹ * ((m : ℝ) / q) = (q : ℝ)⁻¹ := by field_simp
  have e2 : (m : ℝ)⁻¹ * A = A / m := inv_mul_eq_div _ _
  calc X.coneIdealApprox B m v
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

end EnvelopeProperty.ProjSubvariety
