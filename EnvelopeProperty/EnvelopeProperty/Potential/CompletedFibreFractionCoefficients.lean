import EnvelopeProperty.Potential.CompletedFibreCoefficientDensity

/-! # Exact original ratios of all completed-fibre fraction coefficients -/

open scoped NNReal TensorProduct
noncomputable section

namespace EnvelopeProperty.Berkovich.Spectrum

variable {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B] [Fintype ι]

theorem fractionTensor_basis_coefficient (x : Spectrum A) (basis : Module.Basis ι A B)
    (d : A) (c : B) (i : ι) :
    (basis.baseChange (H x)).equivFun (fractionTensor x d c) i =
      x.toH (basis.equivFun c i)*(x.toH d)⁻¹ := by
  simpa only [fractionTensor,Module.Basis.equivFun_apply,Algebra.smul_def,algebraMap_H] using
    basis.baseChange_repr_tmul (H x) ((x.toH d)⁻¹) c i

theorem fractionTensor_coefficient_nnnorm (x : Spectrum A) (basis : Module.Basis ι A B)
    (d : A) (c : B) (i : ι) :
    ‖(basis.baseChange (H x)).equivFun (fractionTensor x d c) i‖₊ =
      x.val (basis.equivFun c i)/x.val d := by
  rw [fractionTensor_basis_coefficient,nnnorm_mul,nnnorm_inv,nnnorm_toH,nnnorm_toH,div_eq_mul_inv]

theorem fractionTensor_defect_tensor (x : Spectrum A) (d : A) (c : B) (hd : x.val d ≠ 0) :
    (fractionTensor x d c)^2-fractionTensor x d c =
      (x.toH (d^2))⁻¹ ⊗ₜ[A] (c^2-algebraMap A B d*c) := by
  have hdH : x.toH d ≠ 0 := fun h => hd ((toH_eq_zero_iff x).mp h)
  let a := (x.toH d)⁻¹
  have had : x.toH d*a^2 = a := by
    calc
      _ = (x.toH d*a)*a := by ring
      _ = a := by rw [mul_inv_cancel₀ hdH,one_mul]
  rw [map_pow,← inv_pow]
  simp only [fractionTensor,pow_two,Algebra.TensorProduct.tmul_mul_tmul,
    TensorProduct.tmul_sub]
  congr 1
  change a ⊗ₜ[A] c = (a*a) ⊗ₜ[A] (algebraMap A B d*c)
  rw [← Algebra.smul_def d c,TensorProduct.tmul_smul,TensorProduct.smul_tmul',Algebra.smul_def,
    algebraMap_H]
  congr 1
  simpa only [pow_two] using had.symm

theorem fractionTensor_defect_coefficient_nnnorm (x : Spectrum A)
    (basis : Module.Basis ι A B) (d : A) (c : B) (hd : x.val d ≠ 0) (i : ι) :
    ‖(basis.baseChange (H x)).equivFun ((fractionTensor x d c)^2-fractionTensor x d c) i‖₊ =
      x.val (basis.equivFun (c^2-algebraMap A B d*c) i)/x.val (d^2) := by
  rw [fractionTensor_defect_tensor x d c hd]
  change ‖(basis.baseChange (H x)).equivFun
    (fractionTensor x (d^2) (c^2-algebraMap A B d*c)) i‖₊ = _
  exact fractionTensor_coefficient_nnnorm x basis _ _ i

end EnvelopeProperty.Berkovich.Spectrum
