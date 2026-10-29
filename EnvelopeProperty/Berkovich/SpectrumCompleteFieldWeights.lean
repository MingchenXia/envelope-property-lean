import EnvelopeProperty.Berkovich.CompleteFieldResidue
import EnvelopeProperty.Berkovich.SpectrumFibreScalarExtension

/-! # Actual finite fibre weights over already complete coefficient fields -/

open scoped TensorProduct NNReal Classical
noncomputable section
namespace EnvelopeProperty.Berkovich.Spectrum

section CompleteField
variable {K C : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [CommRing C] [Algebra K C]

omit [CompleteSpace K] in
/-- A point with the actual coefficient norm restricts to the genuine norm point. -/
theorem comap_normPoint (y : RelativeSpectrum (NormedField.valuation (K := K)) C) :
    comap (algebraMap K C) y.1 = normPoint K := ext_val y.2

/-- The whole completed tensor algebra over an already complete field is the original algebra. -/
def completeFieldTensorEquiv : H (normPoint K) ⊗[K] C ≃ₐ[K] C :=
  (Algebra.TensorProduct.congr (normPointEquiv K).symm (AlgEquiv.refl : C ≃ₐ[K] C)).trans
    (Algebra.TensorProduct.lid K C)

/-- The genuine tensor comparison preserves every completed coefficient and original function. -/
theorem completeFieldTensorEquiv_tmul (c : K) (a : C) :
    completeFieldTensorEquiv ((toH (normPoint K) c) ⊗ₜ[K] a) = c • a := by
  change ((normPointEquiv K).symm (normPointEquiv K c)) • a = _
  rw [AlgEquiv.symm_apply_apply]

/-- The actual whole fibre evaluator is the original evaluator through the genuine tensor isomorphism. -/
theorem fibreHom_completeField (y : RelativeSpectrum (NormedField.valuation (K := K)) C)
    (q : H (normPoint K) ⊗[K] C) :
    fibreHom (comap_normPoint y) q = toH y.1 (completeFieldTensorEquiv q) := by
  induction q using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul c a =>
    obtain ⟨c, rfl⟩ := (normPoint_toH_bijective K).2 c
    rw [fibreHom_tmul, H.map_toH, completeFieldTensorEquiv_tmul, Algebra.smul_def, map_mul]

/-- The generic completed-fibre weight equals the actual original local-ring dimension. -/
theorem fibreNormMult_eq_completeLocalFinrank [Module.Finite K C]
    (y : RelativeSpectrum (NormedField.valuation (K := K)) C) :
    fibreNormMult K y.1 = Module.finrank K (Localization.AtPrime y.1.val.supp) := by
  let x := normPoint K
  let T := H x ⊗[K] C
  let g : T ≃ₐ[K] C := completeFieldTensorEquiv
  let p : MaximalSpectrum C := ⟨y.1.val.supp,
    RelativeSpectrum.isMaximal_supp_of_isIntegral y⟩
  have hker : (maximalSpectrumAlgEquiv g p).asIdeal =
      RingHom.ker (fibreHom (comap_normPoint y)) := by
    ext q
    change y.1.val (g q) = 0 ↔ fibreHom (comap_normPoint y) q = 0
    rw [fibreHom_completeField, toH_eq_zero_iff]
  let : (RingHom.ker (fibreHom (comap_normPoint y))).IsPrime := RingHom.ker_isPrime _
  let : Module.Finite K (H x) := Module.Finite.equiv (normPointEquiv K).toLinearEquiv
  have hdim : Module.finrank K (H x) = 1 := by
    rw [← (normPointEquiv K).toLinearEquiv.finrank_eq, Module.finrank_self]
  rw [fibreNormMult_eq_localFinrank_of_comap (comap_normPoint y)]
  rw [show Module.finrank (H x)
      (Localization.AtPrime (RingHom.ker (fibreHom (comap_normPoint y)))) =
      Module.finrank K (Localization.AtPrime (RingHom.ker (fibreHom (comap_normPoint y)))) from by
    rw [← Module.finrank_mul_finrank K (H x), hdim, one_mul]]
  exact (localFinrank_congr (K := K) hker.symm).trans
    (finrank_maximalLocalizationAlgEquiv g p).symm

end CompleteField

/-- Passing from an original finite fibre point to its actual completed tensor point retains its full original weight. -/
theorem fibreNormMult_fibrePoint {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] {x : Spectrum A} {y : Spectrum B}
    (hy : comap (algebraMap A B) y = x) :
    fibreNormMult (H x) (fibrePoint hy).1 = fibreNormMult A y := by
  let : (RingHom.ker (fibreHom hy)).IsPrime := RingHom.ker_isPrime _
  rw [fibreNormMult_eq_completeLocalFinrank, fibreNormMult_eq_localFinrank_of_comap hy]
  have hker : (fibrePoint hy).1.val.supp = RingHom.ker (fibreHom hy) := by
    ext q
    change ‖fibreHom hy q‖₊ = 0 ↔ fibreHom hy q = 0
    exact nnnorm_eq_zero
  exact localFinrank_congr hker

end EnvelopeProperty.Berkovich.Spectrum
