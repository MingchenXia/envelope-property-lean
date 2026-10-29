/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumIntegralImage
import EnvelopeProperty.Berkovich.SpectrumQuotient
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Actual rational points above integral algebra maps

An algebraically closed coefficient field with any real valuation has genuine
rational residue quotients at every point above a rational base evaluator through
an integral algebra map. The entire original element values and evaluator are
preserved. Pure rational evaluators extend precisely at the actual kernel
obstruction; injective integral maps are unobstructed.

No norm, completeness, finite module, separability or characteristic assumption
is needed. The coefficient quotient factor itself works over arbitrary rings.
These constructions preserve rationality after an actual integral morphism has
been supplied; constructing a reduced normalized curve remains separate.
-/

open scoped NNReal
noncomputable section
namespace EnvelopeProperty.Berkovich.Spectrum
section Base
variable {F A B : Type*} [CommRing F]
  [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
  [Algebra A B] [IsScalarTower F A B]
  (v : Valuation F ℝ≥0) (e : A →ₐ[F] F) {y : Spectrum B}
  (h : comap (algebraMap A B) y = ⟨v.comap e.toRingHom⟩)

include h in
theorem rationalQuotient_base (a : A) :
    algebraMap A (B ⧸ y.val.supp) a = algebraMap F (B ⧸ y.val.supp) (e a) := by
  have hz := congrArg (fun z : Spectrum A => z.val (a - algebraMap F A (e a))) h
  have hzero : y.val (algebraMap A B (a - algebraMap F A (e a))) = 0 := by
    refine hz.trans ?_
    change v (e (a - algebraMap F A (e a))) = 0
    simp
  apply Ideal.Quotient.eq.mpr
  change y.val (algebraMap A B a - algebraMap F B (e a)) = 0
  rw [IsScalarTower.algebraMap_apply F A B, ← map_sub]
  exact hzero

include h in
theorem rationalFibre_val_algebraMap (c : F) : y.val (algebraMap F B c) = v c := by
  have ht := congrArg (fun z : Spectrum A => z.val (algebraMap F A c)) h
  change y.val (algebraMap A B (algebraMap F A c)) = v (e (algebraMap F A c)) at ht
  simpa only [← IsScalarTower.algebraMap_apply F A B, e.commutes,
    Algebra.algebraMap_self, RingHom.id_apply] using ht

end Base
section Integral
variable {F A B : Type*} [Field F] [IsAlgClosed F]
  [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
  [Algebra A B] [IsScalarTower F A B] [Algebra.IsIntegral A B]
  (v : Valuation F ℝ≥0) (e : A →ₐ[F] F) {y : Spectrum B}
  (h : comap (algebraMap A B) y = ⟨v.comap e.toRingHom⟩)

/-- A point above an actual rational base point has its genuine residue quotient F. -/
def integralRationalQuotientEquiv : (B ⧸ y.val.supp) ≃ₐ[F] F := by
  let : Algebra A F := e.toRingHom.toAlgebra
  let : IsScalarTower A F (B ⧸ y.val.supp) :=
    IsScalarTower.of_algebraMap_eq fun a => rationalQuotient_base v e h a
  have : Algebra.IsIntegral F (B ⧸ y.val.supp) :=
    ⟨fun q => (Algebra.IsIntegral.isIntegral (R := A) q).tower_top⟩
  exact (AlgEquiv.ofBijective (Algebra.ofId F (B ⧸ y.val.supp))
    IsAlgClosed.algebraMap_bijective_of_isIntegral).symm

theorem integralRationalQuotientEquiv_algebraMap (a : A) :
    integralRationalQuotientEquiv v e h (algebraMap A (B ⧸ y.val.supp) a) = e a := by
  rw [rationalQuotient_base v e h a]
  simp only [(integralRationalQuotientEquiv v e h).commutes,
    Algebra.algebraMap_self, RingHom.id_apply]

theorem integralRationalQuotientEquiv_val (q : B ⧸ y.val.supp) :
    y.val.onQuot le_rfl q = v (integralRationalQuotientEquiv v e h q) := by
  have hq : algebraMap F (B ⧸ y.val.supp) (integralRationalQuotientEquiv v e h q) = q := by
    simpa only [← (integralRationalQuotientEquiv v e h).symm.commutes,
      Algebra.algebraMap_self, RingHom.id_apply] using
      (integralRationalQuotientEquiv v e h).symm_apply_apply q
  calc
    y.val.onQuot le_rfl q = y.val.onQuot le_rfl
      (algebraMap F (B ⧸ y.val.supp) (integralRationalQuotientEquiv v e h q)) :=
        congrArg (y.val.onQuot le_rfl) hq.symm
    _ = v (integralRationalQuotientEquiv v e h q) := rationalFibre_val_algebraMap v e h _

/-- The true residue quotient constructs an actual evaluator of the whole original algebra. -/
def integralRationalEval : B →ₐ[F] F :=
  (integralRationalQuotientEquiv v e h).toAlgHom.comp (Ideal.Quotient.mkₐ F y.val.supp)

theorem integralRationalEval_algebraMap (a : A) :
    integralRationalEval v e h (algebraMap A B a) = e a :=
  integralRationalQuotientEquiv_algebraMap v e h a

theorem integralRationalEval_val (b : B) : v (integralRationalEval v e h b) = y.val b :=
  (integralRationalQuotientEquiv_val v e h (Ideal.Quotient.mk _ b)).symm

theorem integralRationalEval_surjective : Function.Surjective (integralRationalEval v e h) := by
  intro c
  refine ⟨algebraMap F B c, ?_⟩
  simp only [(integralRationalEval v e h).commutes, Algebra.algebraMap_self, RingHom.id_apply]

theorem integralRationalEval_kernel :
    RingHom.ker (integralRationalEval v e h).toRingHom = y.val.supp := by
  ext b
  rw [RingHom.mem_ker, Valuation.mem_supp_iff, ← integralRationalEval_val v e h b]
  exact v.map_eq_zero_iff.symm

include h in
theorem rationalFibre_support_isMaximal : y.val.supp.IsMaximal := by
  rw [← integralRationalEval_kernel v e h]
  exact RingHom.ker_isMaximal_of_surjective _ (integralRationalEval_surjective v e h)

end Integral

section Existence
open Classical
variable {F A B : Type*} [Field F] [IsAlgClosed F]
  [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
  [Algebra A B] [IsScalarTower F A B] [Algebra.IsIntegral A B]

/-- An actual rational evaluator extends across an integral map precisely when its kernel is unobstructed. -/
theorem exists_rationalEval_of_isIntegral (e : A →ₐ[F] F)
    (he : RingHom.ker (algebraMap A B) ≤ RingHom.ker e.toRingHom) :
    ∃ d : B →ₐ[F] F, d.comp (IsScalarTower.toAlgHom F A B) = e := by
  let v : Valuation F ℝ≥0 := 1
  let x : Spectrum A := ⟨v.comap e.toRingHom⟩
  have hx : RingHom.ker (algebraMap A B) ≤ x.val.supp := by
    intro a ha
    change v (e a) = 0
    have he0 : e a = 0 := RingHom.mem_ker.mp (he ha)
    rw [he0, map_zero]
  obtain ⟨y, hy⟩ := exists_comap_eq (B := B) x hx
  refine ⟨integralRationalEval v e hy, ?_⟩
  apply AlgHom.ext
  intro a
  exact integralRationalEval_algebraMap v e hy a

theorem exists_rationalEval_iff_of_isIntegral (e : A →ₐ[F] F) :
    (∃ d : B →ₐ[F] F, d.comp (IsScalarTower.toAlgHom F A B) = e) ↔
      RingHom.ker (algebraMap A B) ≤ RingHom.ker e.toRingHom := by
  refine ⟨?_, exists_rationalEval_of_isIntegral e⟩
  rintro ⟨d, hd⟩ a ha
  change e a = 0
  have ht := congrArg (fun g : A →ₐ[F] F => g a) hd
  change d (algebraMap A B a) = e a at ht
  rw [RingHom.mem_ker.mp ha, map_zero] at ht
  exact ht.symm

/-- Injective integral maps genuinely lift every rational evaluator, with no finiteness or norm hypothesis. -/
theorem exists_rationalEval_of_injective_isIntegral (e : A →ₐ[F] F)
    (hinj : Function.Injective (algebraMap A B)) :
    ∃ d : B →ₐ[F] F, d.comp (IsScalarTower.toAlgHom F A B) = e :=
  exists_rationalEval_of_isIntegral e (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le)

end Existence
end EnvelopeProperty.Berkovich.Spectrum
