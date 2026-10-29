/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumEtaleNorm
import EnvelopeProperty.Berkovich.NormFormGeneral

/-!
# Weighted etale norm forms at arbitrary seminorm points

The actual determinant norm form commutes with completed residue-field base
change. A split-algebra polynomial identity over an algebraic closure gives the
weighted fibre formula without any Infinite H(x) hypothesis. The exponents are
the actual residue degrees of finite etale fibre fields; nonetale local lengths
are outside the present theorem.
-/

open scoped NNReal TensorProduct
open MvPolynomial
noncomputable section
namespace EnvelopeProperty

namespace Berkovich.Spectrum

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

/-- The weighted norm-form identity on the actual completed tensor fibre.
There is no infinitude hypothesis on H(x): the producer uses whole-polynomial
base change and splitting over an algebraic closure. -/
theorem wgaussValuation_map_normForm_of_etale [Module.Free B A] [Module.Finite B A]
    [Algebra.Etale B A] {σ : Type*} [Fintype σ] (b : σ → A) (r : σ → ℝ≥0) (x : Spectrum B) :
    wgaussValuation NormedField.valuation r (map (toH x) (normForm B b)) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ fibreMult B y := by
  classical
  have : Fintype (MaximalSpectrum (H x ⊗[B] A)) := Fintype.ofFinite _
  let _ : ∀ m : MaximalSpectrum (H x ⊗[B] A), Field ((H x ⊗[B] A) ⧸ m.asIdeal) :=
    fun m => Ideal.Quotient.field m.asIdeal
  have : ∀ m : MaximalSpectrum (H x ⊗[B] A),
      Algebra.IsSeparable (H x) ((H x ⊗[B] A) ⧸ m.asIdeal) :=
    fun m => Algebra.FormallyUnramified.isSeparable _ _
  -- the point over `x` attached to a maximal ideal `m`, and the absolute value on `E/m`
  let yOf : MaximalSpectrum (H x ⊗[B] A) → Spectrum A :=
    fun m => ((pointFibreEquivMaximalSpectrum x).symm m : Spectrum A)
  have hyOf : ∀ m, comap (algebraMap B A) (yOf m) = x :=
    fun m => ((pointFibreEquivMaximalSpectrum x).symm m).2
  have hker : ∀ m, RingHom.ker (fibreHom (hyOf m)) = m.asIdeal := fun m => by
    rw [← pointFibreEquivMaximalSpectrum_asIdeal, Equiv.apply_symm_apply]
  let g : ∀ m : MaximalSpectrum (H x ⊗[B] A), ((H x ⊗[B] A) ⧸ m.asIdeal) →+* H (yOf m) :=
    fun m => Ideal.Quotient.lift m.asIdeal (fibreHom (hyOf m))
      (fun a ha => by rwa [← hker m, RingHom.mem_ker] at ha)
  let w : ∀ m : MaximalSpectrum (H x ⊗[B] A), Valuation ((H x ⊗[B] A) ⧸ m.asIdeal) ℝ≥0 :=
    fun m => (NormedField.valuation (K := H (yOf m))).comap (g m)
  have hw : ∀ m (c : H x), w m (algebraMap (H x) _ c) = ‖c‖₊ := by
    intro m c
    simp only [w, g]
    rw [Valuation.comap_apply, NormedField.valuation_apply, ← Ideal.Quotient.mk_algebraMap,
      Ideal.Quotient.lift_mk, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, fibreHom_tmul_one]
    exact NNReal.eq (H.norm_map _ (hyOf m) c)
  have hwb : ∀ m (a : A), w m (Ideal.Quotient.mk _ ((1 : H x) ⊗ₜ a)) = (yOf m).val a := by
    intro m a
    simp only [w, g]
    rw [Valuation.comap_apply, NormedField.valuation_apply, Ideal.Quotient.lift_mk,
      fibreHom_one_tmul, nnnorm_toH]
  rw [← algebraMap_H, map_normForm_baseChange,
    wgaussValuation_normForm_of_algEquiv (fibreEquivPi x) w hw]
  symm
  refine Finset.prod_bij (fun y hy => pointFibreEquivMaximalSpectrum x
      ⟨y, (Set.Finite.mem_toFinset _).1 hy⟩) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro y₁ h₁ y₂ h₂ h
    exact congrArg Subtype.val ((pointFibreEquivMaximalSpectrum x).injective h)
  · intro m _
    obtain ⟨⟨y, hy⟩, hym⟩ := (pointFibreEquivMaximalSpectrum x).surjective m
    exact ⟨y, (Set.Finite.mem_toFinset _).2 hy, hym⟩
  · intro y hy
    have hy' : y ∈ comap (algebraMap B A) ⁻¹' {x} :=
      (Set.Finite.mem_toFinset _).1 hy
    have hyy : yOf (pointFibreEquivMaximalSpectrum x ⟨y, hy'⟩) = y := by simp [yOf]
    rw [fibreMult_eq hy', ← pointFibreEquivMaximalSpectrum_asIdeal x ⟨y, hy'⟩]
    congr 1
    refine Finset.sup_congr rfl fun j _ => ?_
    rw [fibreEquivPi_apply, hwb, hyy]

/-- The weighted norm-form identity at an arbitrary point, on its original
coefficient seminorm. Finite free and etale hypotheses give the actual
residue-degree multiplicities, including when H(x) is finite. -/
theorem wgaussValuation_normForm_of_etale [Module.Free B A] [Module.Finite B A] [Algebra.Etale B A]
    {σ : Type*} [Fintype σ] (b : σ → A) (r : σ → ℝ≥0) (x : Spectrum B) :
    wgaussValuation x.val r (normForm B b) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ fibreMult B y := by
  rw [← wgaussValuation_map x.val r (toH x) NormedField.valuation
    (fun a => nnnorm_toH x a)]
  exact wgaussValuation_map_normForm_of_etale b r x

end Berkovich.Spectrum

end EnvelopeProperty
