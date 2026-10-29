/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumFinite
import EnvelopeProperty.ArtinianIdempotentEvaluation

/-!
# Actual original-element peaks on finite seminorm fibres

Density of the actual residue field in its completion and genuine tensor
induction approximate every completed tensor in finitely many prescribed-norm
evaluations by one original algebra fraction. Actual common-denominator identities
retain every coefficient element. Real Artinian CRT idempotents and the proved
whole-point fibre classification then construct an original element peaking at
any chosen finite fibre point. No peak or approximation certificate is supplied.
The density producer needs no module-finiteness; only the final finite fibre
peak uses a genuinely finite algebra. No field bound or separability is assumed.
-/

open scoped TensorProduct NNReal Topology
open AlgebraicGeometry Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.Spectrum
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- Every actual residue-field element has an original-ring fraction whose denominator has nonzero original seminorm. -/
theorem residueToH_eq_original_fraction (x : Spectrum A) (q : x.ResidueField) :
    ∃ a d : A, x.val d ≠ 0 ∧ x.residueToH q = x.toH a / x.toH d := by
  obtain ⟨a, d, hd, hq⟩ := IsFractionRing.div_surjective (A ⧸ x.val.supp) q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
  refine ⟨a, d, ?_, ?_⟩
  · intro hzero
    apply nonZeroDivisors.ne_zero hd
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hzero
  · rw [← hq, map_div₀]
    rfl

/-- The true original fraction tensor, with its inverse only in the actual completed residue field. -/
def fractionTensor (x : Spectrum A) (d : A) (b : B) : H x ⊗[A] B :=
  (x.toH d)⁻¹ ⊗ₜ[A] b

@[simp] theorem fractionTensor_zero (x : Spectrum A) (d : A) :
    fractionTensor x d (0 : B) = 0 := by simp [fractionTensor]

/-- Genuine tensor balance moves the numerator of an original coefficient fraction into the original algebra. -/
theorem fractionTensor_coefficient (x : Spectrum A) (a d : A) (b : B) :
    (x.toH a / x.toH d) ⊗ₜ[A] b = fractionTensor x d (algebraMap A B a * b) := by
  rw [div_eq_mul_inv]
  change (a • (x.toH d)⁻¹) ⊗ₜ[A] b = _
  rw [TensorProduct.smul_tmul, Algebra.smul_def]
  rfl

/-- Whole original common-denominator identity inside the actual completed tensor algebra. -/
theorem fractionTensor_add (x : Spectrum A) {d e : A}
    (hd : x.val d ≠ 0) (he : x.val e ≠ 0) (b c : B) :
    fractionTensor x d b + fractionTensor x e c =
      fractionTensor x (d * e) (algebraMap A B e * b + algebraMap A B d * c) := by
  have hd' : x.toH d ≠ 0 := fun h => hd ((toH_eq_zero_iff x).mp h)
  have he' : x.toH e ≠ 0 := fun h => he ((toH_eq_zero_iff x).mp h)
  change _ = (x.toH (d * e))⁻¹ ⊗ₜ[A]
    (algebraMap A B e * b + algebraMap A B d * c)
  rw [TensorProduct.tmul_add]
  change _ = fractionTensor x (d * e) (algebraMap A B e * b) +
    fractionTensor x (d * e) (algebraMap A B d * c)
  rw [← fractionTensor_coefficient, ← fractionTensor_coefficient]
  have h1 : x.toH e / x.toH (d * e) = (x.toH d)⁻¹ := by
    rw [map_mul]
    field_simp
  have h2 : x.toH d / x.toH (d * e) = (x.toH e)⁻¹ := by
    rw [map_mul]
    field_simp
  rw [h1, h2]
  rfl


/-- Exact pure-tensor evaluation at an actual prescribed completed-field point. -/
theorem tensorPoint_val_tmul (x : Spectrum A)
    (z : RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] B))
    (h : H x) (b : B) :
    z.1.val (h ⊗ₜ[A] b) = ‖h‖₊ * z.1.val ((1 : H x) ⊗ₜ[A] b) := by
  have ht : h ⊗ₜ[A] b = (h ⊗ₜ[A] (1 : B)) * ((1 : H x) ⊗ₜ[A] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [ht, z.1.val.map_mul]
  congr 1
  exact z.2 h

/-- Genuine density of original algebra fractions in every finite family of completed-fibre seminorm evaluations. -/
theorem exists_fractionTensor_approx (x : Spectrum A)
    (s : Finset (RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] B)))
    (e : H x ⊗[A] B) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ d : A, ∃ b : B, x.val d ≠ 0 ∧
      ∀ z ∈ s, z.1.val (e - fractionTensor x d b) < ε := by
  classical
  induction e using TensorProduct.induction_on with
  | zero =>
      refine ⟨1, 0, by simp, ?_⟩
      intro z hz
      simpa using hε
  | tmul h b =>
      let M := s.sup fun z => z.1.val ((1 : H x) ⊗ₜ[A] b)
      let δ : ℝ≥0 := ε / (M + 1)
      have hδ : 0 < δ := div_pos hε (by positivity)
      obtain ⟨q, hq⟩ := (denseRange_residueToH x).exists_dist_lt h
        (show (0 : ℝ) < (δ : ℝ) from NNReal.coe_pos.mpr hδ)
      have herr : ‖h - x.residueToH q‖₊ < δ := by
        exact_mod_cast (show ‖h - x.residueToH q‖ < (δ : ℝ) from by
          simpa only [dist_eq_norm] using hq)
      obtain ⟨a, d, hd, hf⟩ := residueToH_eq_original_fraction x q
      refine ⟨d, algebraMap A B a * b, hd, ?_⟩
      intro z hz
      rw [← fractionTensor_coefficient, ← hf, ← TensorProduct.sub_tmul,
        tensorPoint_val_tmul]
      have hM : z.1.val ((1 : H x) ⊗ₜ[A] b) ≤ M := Finset.le_sup (f := fun z => z.1.val ((1 : H x) ⊗ₜ[A] b)) hz
      calc
        ‖h - x.residueToH q‖₊ * z.1.val ((1 : H x) ⊗ₜ[A] b) ≤ δ * M := by gcongr
        _ < δ * (M + 1) := mul_lt_mul_of_pos_left (lt_add_one M) hδ
        _ = ε := by dsimp [δ]; field_simp
  | add e f he hf =>
      obtain ⟨d, b, hd, hb⟩ := he
      obtain ⟨t, c, ht, hc⟩ := hf
      refine ⟨d * t, algebraMap A B t * b + algebraMap A B d * c, ?_, ?_⟩
      · rw [x.val.map_mul]
        exact mul_ne_zero hd ht
      · intro z hz
        rw [← fractionTensor_add x hd ht]
        calc
          z.1.val (e + f - (fractionTensor x d b + fractionTensor x t c)) =
              z.1.val ((e - fractionTensor x d b) + (f - fractionTensor x t c)) := by congr 1; abel
          _ ≤ max (z.1.val (e - fractionTensor x d b)) (z.1.val (f - fractionTensor x t c)) :=
            z.1.val.map_add _ _
          _ < ε := max_lt (hb z hz) (hc z hz)


/-- A genuine original algebra element peaks at a chosen whole finite fibre point, with one nonvanishing original common denominator. -/
theorem exists_finite_fibre_peak [Module.Finite A B] (x : Spectrum A) (y : Fibre (B := B) x) :
    ∃ d : A, ∃ b : B, x.val d ≠ 0 ∧ y.1.val b = x.val d ∧
      ∀ z : Fibre (B := B) x, z ≠ y → z.1.val b < (1 / 2 : ℝ≥0) * x.val d := by
  classical
  let E := H x ⊗[A] B
  let : IsArtinianRing E := IsArtinianRing.of_finite (H x) E
  let : Finite (Fibre (B := B) x) := finite_fibre x
  let : Fintype (Fibre (B := B) x) := Fintype.ofFinite _
  let m : MaximalSpectrum E := fibreToMaximalSpectrum x y
  let e : E := ArtinianFactors.localIdempotent E m
  have heval (z : Fibre (B := B) x) :
      fibreHom z.2 e = if z = y then 1 else 0 := by
    have hh := ArtinianFactors.localIdempotent_map m (fibreToMaximalSpectrum x z)
      (fibreHom z.2) rfl
    change fibreHom z.2 e = _ at hh
    have hiff : fibreToMaximalSpectrum x z = m ↔ z = y :=
      (fibreToMaximalSpectrum_bijective x).injective.eq_iff
    simpa only [hiff] using hh
  let s := Finset.univ.image (fun z : Fibre (B := B) x => fibrePoint z.2)
  obtain ⟨d, b, hd, happ⟩ := exists_fractionTensor_approx x s e (1 / 2 : ℝ≥0) (by norm_num)
  have herr (z : Fibre (B := B) x) :
      (fibrePoint z.2).1.val (e - fractionTensor x d b) < (1 / 2 : ℝ≥0) :=
    happ _ (Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩)
  have hve (z : Fibre (B := B) x) :
      (fibrePoint z.2).1.val e = if z = y then 1 else 0 := by
    change ‖fibreHom z.2 e‖₊ = _
    rw [heval]
    split_ifs <;> simp
  have hfrac (z : Fibre (B := B) x) :
      (fibrePoint z.2).1.val (fractionTensor x d b) = (x.val d)⁻¹ * z.1.val b := by
    rw [fractionTensor, tensorPoint_val_tmul, nnnorm_inv, nnnorm_toH]
    rw [fibrePoint_val_tmul, nnnorm_one, one_mul]
  have hyfrac : (x.val d)⁻¹ * y.1.val b = 1 := by
    rw [← hfrac]
    have heq := (fibrePoint y.2).1.val.map_eq_of_sub_lt
      (x := e) (y := fractionTensor x d b) (by
        rw [Valuation.map_sub_swap]
        exact (herr y).trans (by rw [hve]; norm_num))
    simpa [hve] using heq
  refine ⟨d, b, hd, ?_, ?_⟩
  · calc
      y.1.val b = x.val d * ((x.val d)⁻¹ * y.1.val b) := by simp [hd]
      _ = x.val d := by rw [hyfrac, mul_one]
  · intro z hz
    have hez : (fibrePoint z.2).1.val e = 0 := by rw [hve, if_neg hz]
    have hratio : (x.val d)⁻¹ * z.1.val b < (1 / 2 : ℝ≥0) := by
      rw [← hfrac]
      calc
        (fibrePoint z.2).1.val (fractionTensor x d b) =
            (fibrePoint z.2).1.val (e - (e - fractionTensor x d b)) := by congr 1; abel
        _ ≤ max ((fibrePoint z.2).1.val e)
            ((fibrePoint z.2).1.val (e - fractionTensor x d b)) :=
          (fibrePoint z.2).1.val.map_sub _ _
        _ < (1 / 2 : ℝ≥0) := max_lt (by rw [hez]; norm_num) (herr z)
    have hh := mul_lt_mul_of_pos_left hratio (show 0 < x.val d from pos_iff_ne_zero.mpr hd)
    calc
      z.1.val b = x.val d * ((x.val d)⁻¹ * z.1.val b) := by simp [hd]
      _ < x.val d * (1 / 2 : ℝ≥0) := hh
      _ = (1 / 2 : ℝ≥0) * x.val d := mul_comm _ _

end EnvelopeProperty.Berkovich.Spectrum
