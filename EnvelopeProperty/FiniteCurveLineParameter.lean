/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AffineDimension
import Mathlib.Algebra.Module.PID

open scoped Polynomial

noncomputable section
namespace EnvelopeProperty

/-- A genuine nonfield finite-type integral curve admits an actual finite free polynomial parameter over any field. -/
theorem exists_finiteFree_injective_polynomial_of_dimension_le_one
    (F C : Type*) [Field F] [CommRing C] [IsDomain C] [Algebra F C]
    [Algebra.FiniteType F C] [Ring.KrullDimLE 1 C] (hC : ¬ IsField C) :
    ∃ φ : F[X] →ₐ[F] C, Function.Injective φ ∧ φ.toRingHom.Finite ∧
      (letI := φ.toRingHom.toAlgebra; Module.Free F[X] C) := by
  obtain ⟨n, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg F C
  let A := MvPolynomial (Fin n) F
  let : Algebra A C := g.toRingHom.toAlgebra
  have : Module.Finite A C := hfin
  have : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  have : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr hg
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing F C
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (α := C)
  have : M.IsMaximal := hM
  have hM0 : M ≠ ⊥ := by
    intro h
    exact hC (Ring.isField_iff_maximal_bot.mpr (h ▸ hM))
  have : (M.under A).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) M
  have hheight : M.height = (n : ℕ) := by
    rw [height_eq_under_of_normal_integral (R := A) M]
    exact maximalHeight_mvPolynomialFin F n (M.under A)
  have hn0 : n ≠ 0 := by
    intro h
    have hz : M.height = 0 := by simpa only [h, Nat.cast_zero] using hheight
    exact hM0 (Ideal.height_eq_zero_iff_eq_bot.mp hz)
  have hnle : n ≤ 1 := by
    have hd := Ideal.height_le_ringKrullDim_of_isPrime (I := M)
    have hb := Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 C)
    rw [hheight] at hd
    have hle : (n : ℕ∞) ≤ 1 := WithBot.coe_le_coe.mp (hd.trans hb)
    exact_mod_cast hle
  have hn : n = 1 := by omega
  subst n
  let e : MvPolynomial (Fin 1) F ≃ₐ[F] F[X] := MvPolynomial.uniqueAlgEquiv F (Fin 1)
  let φ : F[X] →ₐ[F] C := g.comp e.symm.toAlgHom
  have hi : Function.Injective φ := hg.comp e.symm.injective
  have hf : φ.toRingHom.Finite := hfin.comp
    (RingHom.Finite.of_surjective e.symm.toRingHom e.symm.surjective)
  refine ⟨φ, hi, hf, ?_⟩
  let : Algebra F[X] C := φ.toRingHom.toAlgebra
  have : Module.Finite F[X] C := hf
  have : Module.IsTorsionFree F[X] C :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hi
  infer_instance

end EnvelopeProperty
