/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.ProjectiveNormForm
import EnvelopeProperty.Berkovich.SpectrumFiniteNorm

/-!
# Original finite projective norms at arbitrary seminorm points

Actual maximal completed-fibre residues carry valuations obtained from their
entire corresponding analytic points. For every module-finite algebra, the
completed-fibre scalar and whole weighted norm formulas retain genuine local
length times residue degree, and their sum equals the actual fibre dimension.

For a finite projective original algebra, actual intrinsic norm base change
then proves the original scalar and polynomial coefficient identities. No
global freeness, constant rank, etaleness, reducedness, separability, field base
or infinitude is required. Rank-zero fibres give empty sums and products.
Global constant-degree homogeneity and decreasing-limit transport are separate
from these algebraic pointwise producers.
-/

open scoped NNReal TensorProduct Classical
open MvPolynomial
noncomputable section
namespace EnvelopeProperty.Berkovich.Spectrum
variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

/-- Actual valuation on a maximal completed-fibre residue field, constructed
from the corresponding entire analytic point and its genuine residue lift. -/
def completedFibreResidualValuation [Algebra.IsIntegral B A] (x : Spectrum B)
    (m : MaximalSpectrum (H x ⊗[B] A)) : Valuation m.asIdeal.ResidueField ℝ≥0 := by
  let y := (pointFibreEquivMaximalSpectrum x).symm m
  have hker : RingHom.ker (fibreHom y.2) = m.asIdeal := by
    rw [← pointFibreEquivMaximalSpectrum_asIdeal, Equiv.apply_symm_apply]
  let g := Ideal.ResidueField.lift m.asIdeal (fibreHom y.2) (by rw [hker])
    (fun a ha => isUnit_iff_ne_zero.mpr (fun hz => ha (by rw [← hker]; exact hz)))
  exact (NormedField.valuation (K := H y.1)).comap g

set_option backward.isDefEq.respectTransparency false in
/-- Every completed coefficient has its prescribed norm in the actual residue valuation. -/
theorem completedFibreResidualValuation_algebraMap [Algebra.IsIntegral B A]
    (x : Spectrum B) (m : MaximalSpectrum (H x ⊗[B] A)) (c : H x) :
    completedFibreResidualValuation x m (algebraMap (H x) m.asIdeal.ResidueField c) = ‖c‖₊ := by
  simp only [completedFibreResidualValuation, Valuation.comap_apply, NormedField.valuation_apply]
  rw [IsScalarTower.algebraMap_apply (H x) (H x ⊗[B] A),
    Ideal.ResidueField.lift_algebraMap, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, fibreHom_tmul_one]
  exact NNReal.eq (H.norm_map _ ((pointFibreEquivMaximalSpectrum x).symm m).2 c)

set_option backward.isDefEq.respectTransparency false in
/-- Every original algebra element has exactly its corresponding analytic value. -/
theorem completedFibreResidualValuation_one_tmul [Algebra.IsIntegral B A]
    (x : Spectrum B) (m : MaximalSpectrum (H x ⊗[B] A)) (a : A) :
    completedFibreResidualValuation x m
      (algebraMap (H x ⊗[B] A) m.asIdeal.ResidueField ((1 : H x) ⊗ₜ[B] a)) =
        ((pointFibreEquivMaximalSpectrum x).symm m).1.val a := by
  simp only [completedFibreResidualValuation, Valuation.comap_apply, NormedField.valuation_apply]
  rw [Ideal.ResidueField.lift_algebraMap, fibreHom_one_tmul, nnnorm_toH]

/-- True fibre multiplicities sum to its actual completed-tensor dimension, without original freeness. -/
theorem sum_fibreNormMult_eq_completedFinrank [Module.Finite B A] (x : Spectrum B) :
    ∑ y ∈ (finite_preimage_singleton (A := A) x).toFinset, fibreNormMult B y =
      Module.finrank (H x) (H x ⊗[B] A) := by
  classical
  have : IsArtinianRing (H x ⊗[B] A) := IsArtinianRing.of_finite (H x) _
  let : Fintype (MaximalSpectrum (H x ⊗[B] A)) := Fintype.ofFinite _
  have h1 : Module.finrank (H x) (H x ⊗[B] A) = ∑ m : MaximalSpectrum (H x ⊗[B] A),
      (Module.length (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal)).toNat *
        Module.finrank (H x) m.asIdeal.ResidueField := by
    rw [(finiteAlgebraLocalizationEquiv (H x) (H x ⊗[B] A)).toLinearEquiv.finrank_eq,
      Module.finrank_pi_fintype]
    exact Finset.sum_congr rfl fun m _ => finrank_eq_length_mul_residue_finrank
  rw [h1]
  refine Finset.sum_bij (fun y hy => pointFibreEquivMaximalSpectrum x
      ⟨y, (Set.Finite.mem_toFinset _).1 hy⟩) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro y₁ h₁ y₂ h₂ h
    exact congrArg Subtype.val ((pointFibreEquivMaximalSpectrum x).injective h)
  · intro m _
    obtain ⟨⟨y, hy⟩, hym⟩ := (pointFibreEquivMaximalSpectrum x).surjective m
    exact ⟨y, (Set.Finite.mem_toFinset _).2 hy, hym⟩
  · intro y hy
    have hy' : y ∈ comap (algebraMap B A) ⁻¹' {x} :=
      (Set.Finite.mem_toFinset _).1 hy
    rw [fibreNormMult_eq hy']
    rfl

/-- Actual completed-fibre scalar norm for every finite algebra, including nonreduced and inseparable factors. -/
theorem valuation_algebraNorm_completedFibre [Module.Finite B A]
    (b : A) (x : Spectrum B) :
    (NormedField.valuation (K := H x)) (Algebra.norm (H x) ((1 : H x) ⊗ₜ[B] b)) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset, y.val b ^ fibreNormMult B y := by
  classical
  have : IsArtinianRing (H x ⊗[B] A) := IsArtinianRing.of_finite (H x) _
  let : Fintype (MaximalSpectrum (H x ⊗[B] A)) := Fintype.ofFinite _
  let yOf : MaximalSpectrum (H x ⊗[B] A) → Spectrum A :=
    fun m => ((pointFibreEquivMaximalSpectrum x).symm m : Spectrum A)
  let w := completedFibreResidualValuation (A := A) x
  have hw := completedFibreResidualValuation_algebraMap (A := A) x
  have hwb := completedFibreResidualValuation_one_tmul (A := A) x
  rw [valuation_algebraNorm_eq_prod_of_localAlgEquiv
    (finiteAlgebraLocalizationEquiv (H x) (H x ⊗[B] A)) w hw]
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
    have hm : fibreNormMult B y =
        (Module.length (Localization.AtPrime (pointFibreEquivMaximalSpectrum x ⟨y, hy'⟩).asIdeal)
          (Localization.AtPrime (pointFibreEquivMaximalSpectrum x ⟨y, hy'⟩).asIdeal)).toNat *
          Module.finrank (H x) (pointFibreEquivMaximalSpectrum x ⟨y, hy'⟩).asIdeal.ResidueField := by
      rw [fibreNormMult_eq hy']
      rfl
    rw [hm]
    congr 1
    rw [finiteAlgebraLocalizationEquiv_apply]
    change y.val b = w (pointFibreEquivMaximalSpectrum x ⟨y, hy'⟩)
      (algebraMap (H x ⊗[B] A) _ ((1 : H x) ⊗ₜ[B] b))
    rw [hwb]
    simpa only [yOf] using (congrArg (fun z : Spectrum A => z.val b) hyy).symm

/-- Whole completed-fibre weighted norm polynomial for every finite algebra, without original projectivity. -/
theorem wgaussValuation_normForm_completedFibre [Module.Finite B A]
    {σ : Type*} [Fintype σ] (b : σ → A) (r : σ → ℝ≥0) (x : Spectrum B) :
    wgaussValuation NormedField.valuation r
      (normForm (H x) (fun j => (1 : H x) ⊗ₜ[B] b j)) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ fibreNormMult B y := by
  classical
  have : IsArtinianRing (H x ⊗[B] A) := IsArtinianRing.of_finite (H x) _
  let : Fintype (MaximalSpectrum (H x ⊗[B] A)) := Fintype.ofFinite _
  let yOf : MaximalSpectrum (H x ⊗[B] A) → Spectrum A :=
    fun m => ((pointFibreEquivMaximalSpectrum x).symm m : Spectrum A)
  let w := completedFibreResidualValuation (A := A) x
  have hw := completedFibreResidualValuation_algebraMap (A := A) x
  have hwb := completedFibreResidualValuation_one_tmul (A := A) x
  have hf : (finiteAlgebraMaximalSpectrumFinite (H x) (H x ⊗[B] A)).toFinset =
      Finset.univ := by
    ext m
    simp
  rw [wgaussValuation_normForm_of_finite w hw, hf]
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
    have hm : fibreNormMult B y =
        (Module.length (Localization.AtPrime (pointFibreEquivMaximalSpectrum x ⟨y, hy'⟩).asIdeal)
          (Localization.AtPrime (pointFibreEquivMaximalSpectrum x ⟨y, hy'⟩).asIdeal)).toNat *
          Module.finrank (H x) (pointFibreEquivMaximalSpectrum x ⟨y, hy'⟩).asIdeal.ResidueField := by
      rw [fibreNormMult_eq hy']
      rfl
    rw [hm]
    congr 1
    refine Finset.sup_congr rfl fun j _ => ?_
    rw [hwb]
    simpa only [yOf] using (congrArg (fun z : Spectrum A => z.val (b j) * r j) hyy).symm

/-- The original intrinsic finite-projective scalar norm has the actual nonetale fibre product. -/
theorem val_projectiveNorm [Module.Finite B A] [Module.Projective B A]
    (b : A) (x : Spectrum B) :
    x.val (projectiveNorm B A b) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset, y.val b ^ fibreNormMult B y := by
  rw [← valuation_algebraNorm_completedFibre b x,
    ← projectiveNorm_eq_norm_of_free, projectiveNorm_baseChange,
    algebraMap_H, NormedField.valuation_apply, nnnorm_toH]

/-- The mapped WHOLE intrinsic projective norm polynomial satisfies the actual fibre formula. -/
theorem wgaussValuation_map_projectiveNormForm [Module.Finite B A] [Module.Projective B A]
    {σ : Type*} [Fintype σ] (b : σ → A) (r : σ → ℝ≥0) (x : Spectrum B) :
    wgaussValuation NormedField.valuation r (map (toH x) (projectiveNormForm B b)) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ fibreNormMult B y := by
  rw [← algebraMap_H, map_projectiveNormForm_baseChange, projectiveNormForm_eq_normForm_of_free]
  exact wgaussValuation_normForm_completedFibre b r x

/-- The actual ORIGINAL coefficient identity needs projectivity, without global freeness or constant rank. -/
theorem wgaussValuation_projectiveNormForm [Module.Finite B A] [Module.Projective B A]
    {σ : Type*} [Fintype σ] (b : σ → A) (r : σ → ℝ≥0) (x : Spectrum B) :
    wgaussValuation x.val r (projectiveNormForm B b) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ fibreNormMult B y := by
  rw [← wgaussValuation_map x.val r (toH x) NormedField.valuation
    (fun a => nnnorm_toH x a)]
  exact wgaussValuation_map_projectiveNormForm b r x

end EnvelopeProperty.Berkovich.Spectrum
