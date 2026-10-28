import EnvelopeProperty.Potential.CurvePieceLocalizedFubiniStudy
import EnvelopeProperty.Berkovich.SpectrumLocalPSH
import EnvelopeProperty.Projective.Jm

/-! # Signed rational tropical maxima as genuine localized finite FS functions -/
open scoped NNReal ENNReal Polynomial Classical
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- Every original factor is an actual unit after localization at their product. -/
theorem isUnit_tropProduct_factor {n : ℕ} (a : Fin n → B) (i : Fin n) :
    IsUnit (algebraMap B (Localization.Away (∏ j, a j)) (a i)) := by
  exact IsLocalization.Away.isUnit_of_dvd _
    (Finset.dvd_prod_of_mem a (Finset.mem_univ i))

/-- The actual original factor unit in the actual principal localization. -/
def tropProductUnit {n : ℕ} (a : Fin n → B) (i : Fin n) :
    (Localization.Away (∏ j, a j))ˣ := (isUnit_tropProduct_factor a i).unit

/-- These genuine units retain the entire original factor. -/
theorem tropProductUnit_val {n : ℕ} (a : Fin n → B) (i : Fin n) :
    (tropProductUnit a i : Localization.Away (∏ j, a j)) =
      algebraMap B (Localization.Away (∏ j, a j)) (a i) :=
  (isUnit_tropProduct_factor a i).unit_spec


/-- Every original localized Laurent monomial retains its exact signed log value. -/
theorem tropProductMonomial_log {n : ℕ} (a : Fin n → B) (z : Fin n → ℤ)
    (y : Spectrum B) (hy : y.val (∏ i, a i) ≠ 0) :
    Spectrum.logAbs (↑(∏ i, tropProductUnit a i ^ z i) : Localization.Away (∏ i, a i))
        (Spectrum.awayLift (∏ i, a i) y hy) =
      ((∑ i, (z i : ℝ) * Real.log (y.val (a i) : ℝ) : ℝ) : EReal) := by
  let C := Localization.Away (∏ i, a i)
  let q := Spectrum.awayLift (∏ i, a i) y hy
  let f : Cˣ →* ℝ≥0 := q.val.toMonoidWithZeroHom.toMonoidHom.comp (Units.coeHom C)
  have hf (u : Cˣ) : f u ≠ 0 := (u.isUnit.map q.val.toMonoidWithZeroHom).ne_zero
  have hprod : q.val (↑(∏ i, tropProductUnit a i ^ z i) : C) =
      ∏ i, f (tropProductUnit a i) ^ z i := by
    change f (∏ i, tropProductUnit a i ^ z i) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    exact f.map_zpow _ _
  change ENNReal.log ((f (∏ i, tropProductUnit a i ^ z i) : ℝ≥0) : ℝ≥0∞) = _
  rw [ENNReal.log_of_nnreal (hf (∏ i, tropProductUnit a i ^ z i))]
  congr 1
  change Real.log (q.val (↑(∏ i, tropProductUnit a i ^ z i) : C) : ℝ) = _
  rw [hprod, NNReal.coe_prod,
    Real.log_prod (fun i _ => by exact_mod_cast zpow_ne_zero (z i) (hf (tropProductUnit a i)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [NNReal.coe_zpow, Real.log_zpow]
  congr 2
  apply congrArg (fun r : ℝ≥0 => (r : ℝ))
  change q.val (tropProductUnit a i : C) = y.val (a i)
  rw [tropProductUnit_val]
  exact Spectrum.awayLift_val_algebraMap (∏ j, a j) y hy (a i)

/-- Clear all original rational slopes with one constructed positive denominator. -/
theorem exists_tropAffine_integral_slopes {n : ℕ}
    (s : Finset ((Fin n → ℚ) × ℚ)) :
    ∃ (N : ℕ), 0 < N ∧ ∃ z : s → Fin n → ℤ,
      ∀ p i, (z p i : ℝ) = (N : ℝ) * (p.1.1 i : ℝ) := by
  classical
  obtain ⟨N,hN,hz⟩ := EnvelopeProperty.ProjBerk.exists_pos_nat_mul_eq_int
    (Finset.univ : Finset (s × Fin n)) (fun t => (t.1.1.1 t.2 : ℝ))
    (fun t _ => ⟨t.1.1.1 t.2,rfl⟩)
  choose z hz using fun t : s × Fin n => hz t (Finset.mem_univ t)
  exact ⟨N,hN,(fun p i => z (p,i)),fun p i => (hz (p,i)).symm⟩


private theorem coe_sup'_eq_sup_subtype {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (f : α → ℝ) :
    (Finset.univ.sup (fun p : s => (f p.1 : EReal))) = ((s.sup' hs f : ℝ) : EReal) := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro p _
    exact EReal.coe_le_coe_iff.mpr (Finset.le_sup' f p.2)
  · obtain ⟨p,hp,heq⟩ := Finset.exists_mem_eq_sup' hs f
    rw [heq]
    exact Finset.le_sup (f := fun q : s => (f q.1 : EReal)) (Finset.mem_univ ⟨p,hp⟩)

/-- Every original signed rational tropical maximum is a genuine localized finite FS
function, with an internally constructed positive integral denominator. -/
theorem exists_tropAffine_localizedFubiniStudy {v : Valuation R ℝ≥0} {n : ℕ}
    (a : Fin n → B) (s : Finset ((Fin n → ℚ) × ℚ)) (hs : s.Nonempty) :
    ∃ (N : ℕ), 0 < N ∧ ∃ (b : s → Localization.Away (∏ i, a i)) (weight : s → ℝ),
      ∀ (y : RelativeSpectrum v B) (_hy : y.1.val (∏ i, a i) ≠ 0),
        FCStandardAffinoid.localizedFubiniStudy (∏ i, a i) b weight (N : ℝ) y.1 =
          ((s.sup' hs (fun p => tropAffine a p y) : ℝ) : EReal) := by
  classical
  obtain ⟨N,hN,z,hz⟩ := exists_tropAffine_integral_slopes s
  let b : s → Localization.Away (∏ i, a i) := fun p => ↑(∏ i, tropProductUnit a i ^ z p i)
  let weight : s → ℝ := fun p => (N : ℝ) * (p.1.2 : ℝ)
  refine ⟨N,hN,b,weight,fun y hy => ?_⟩
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hterm (p : s) :
      (((N : ℝ)⁻¹ : ℝ) : EReal) *
          (Spectrum.logAbs (b p) (Spectrum.awayLift (∏ i, a i) y.1 hy) + (weight p : EReal)) =
        (tropAffine a p.1 y : EReal) := by
    have hsum : (∑ i, (z p i : ℝ) * Real.log (y.1.val (a i) : ℝ)) + weight p =
        (N : ℝ) * tropAffine a p.1 y := by
      unfold tropAffine weight
      rw [mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hz]
      ring
    change (((N : ℝ)⁻¹ : ℝ) : EReal) *
      (Spectrum.logAbs (↑(∏ i, tropProductUnit a i ^ z p i) : Localization.Away (∏ i, a i))
        (Spectrum.awayLift (∏ i, a i) y.1 hy) + (weight p : EReal)) = _
    rw [tropProductMonomial_log, ← EReal.coe_add, hsum, ← EReal.coe_mul]
    congr 1
    rw [← mul_assoc, inv_mul_cancel₀ hNR.ne', one_mul]
  unfold FCStandardAffinoid.localizedFubiniStudy
  rw [dif_pos hy, EnvelopeProperty.FSData.coe_mul_sup _ _ (inv_pos.mpr hNR)]
  rw [Finset.sup_congr rfl (fun p _ => hterm p)]
  exact coe_sup'_eq_sup_subtype s hs (fun p => tropAffine a p y)

end EnvelopeProperty.Berkovich.RelativeSpectrum
