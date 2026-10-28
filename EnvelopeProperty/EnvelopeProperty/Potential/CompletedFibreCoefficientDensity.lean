import EnvelopeProperty.Potential.FiniteFreeCoefficientNorm
import EnvelopeProperty.Berkovich.SpectrumFibrePeak
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Actual original-fraction density in the whole finite completed-fibre coefficient norm -/

open scoped NNReal TensorProduct
noncomputable section

namespace EnvelopeProperty.Berkovich.Spectrum

variable {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B] [Fintype ι]

/-- Original common-denominator fractions approximate the ENTIRE completed tensor in its actual
finite coefficient norm, retaining nilpotents and every residue-field direction. -/
theorem exists_fractionTensor_coefficientNorm_approx (x : Spectrum A)
    (basis : Module.Basis ι A B) (e : H x ⊗[A] B) (ε : ℝ) (hε : 0 < ε) :
    ∃ d : A, ∃ c : B, x.val d ≠ 0 ∧
      (basis.baseChange (H x)).fcCoefficientNorm (e-fractionTensor x d c) < ε := by
  classical
  let f := (basis.baseChange (H x)).fcCoefficientNorm
  have hzero : f 0 = 0 := by simp only [f,Module.Basis.fcCoefficientNorm,map_zero,norm_zero]
  have hnonneg (u : H x ⊗[A] B) : 0 ≤ f u :=
    (basis.baseChange (H x)).fcCoefficientNorm_nonneg u
  have hadd (u v : H x ⊗[A] B) : f (u+v) ≤ max (f u) (f v) :=
    (basis.baseChange (H x)).fcCoefficientNorm_isNonarchimedean u v
  induction e using TensorProduct.induction_on with
  | zero =>
      refine ⟨1,0,by simp,?_⟩
      change f (0-fractionTensor x 1 0) < ε
      simpa only [fractionTensor_zero,sub_zero,hzero] using hε
  | tmul h c =>
      let M := f ((1 : H x) ⊗ₜ[A] c)
      let δ := ε/(M+1)
      have hM : 0 ≤ M := hnonneg _
      have hδ : 0 < δ := div_pos hε (by positivity)
      obtain ⟨q,hq⟩ := (denseRange_residueToH x).exists_dist_lt h hδ
      have herr : ‖h-x.residueToH q‖ < δ := by
        simpa only [dist_eq_norm] using hq
      obtain ⟨a,d,hd,hfrac⟩ := residueToH_eq_original_fraction x q
      refine ⟨d,algebraMap A B a*c,hd,?_⟩
      rw [← fractionTensor_coefficient,← hfrac,← TensorProduct.sub_tmul]
      have hsmul (z : H x) : f (z ⊗ₜ[A] c) = ‖z‖*M := by
        have ht : z ⊗ₜ[A] c = z • ((1 : H x) ⊗ₜ[A] c) := by
          rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
        rw [ht]
        simp only [f,Module.Basis.fcCoefficientNorm,map_smul,norm_smul,M]
      change f ((h-x.residueToH q) ⊗ₜ[A] c) < ε
      rw [hsmul]
      calc
        ‖h-x.residueToH q‖*M ≤ δ*M := mul_le_mul_of_nonneg_right herr.le hM
        _ < δ*(M+1) := mul_lt_mul_of_pos_left (lt_add_one M) hδ
        _ = ε := by dsimp [δ]; field_simp
  | add e g he hg =>
      obtain ⟨d,c,hd,hc⟩ := he
      obtain ⟨t,b,ht,hb⟩ := hg
      refine ⟨d*t,algebraMap A B t*c+algebraMap A B d*b,?_,?_⟩
      · rw [x.val.map_mul]
        exact mul_ne_zero hd ht
      · rw [← fractionTensor_add x hd ht]
        have heq : e+g-(fractionTensor x d c+fractionTensor x t b) =
            (e-fractionTensor x d c)+(g-fractionTensor x t b) := by abel
        rw [heq]
        exact (hadd _ _).trans_lt (max_lt hc hb)

end EnvelopeProperty.Berkovich.Spectrum
