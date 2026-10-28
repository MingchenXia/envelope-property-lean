/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.GeneralFiniteNormForm
import EnvelopeProperty.Berkovich.SpectrumEtaleNorm
import EnvelopeProperty.Berkovich.SpectrumBaseChange
import EnvelopeProperty.Berkovich.AlgebraScalarExtension

/-!
# Scalar and weighted norm formulas for finite free affine morphisms

For an arbitrary commutative-ring algebra finite free over its base, each
completed tensor fibre has genuine localization length times residue-degree
multiplicity. Its scalar determinant norm and entire weighted norm polynomial
are products over the actual analytic fibre with those exponents, including
nonreduced and inseparable factors. Actual coefficient base change and tensor
cancellation compare the products, each with its own fibre multiplicities.

The extended local length is intrinsic for every map. Its natural version uses
ENat.toNat; finite-module hypotheses prove it is the genuine finite length.
These are finite free algebra statements; a finite projective determinant or
transport of decreasing limits is outside their scope.
-/

open scoped NNReal TensorProduct
open MvPolynomial
noncomputable section
namespace EnvelopeProperty.Berkovich.Spectrum

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

local instance ker_fibreHom_isPrime {x : Spectrum B} {y : Spectrum A}
    (h : comap (algebraMap B A) y = x) : (RingHom.ker (fibreHom h)).IsPrime :=
  RingHom.ker_isPrime _

/-- Intrinsic extended local module length of the actual completed tensor support.
No finiteness or geometric norm multiplicity is asserted for an arbitrary map. -/
def fibreLocalLengthENat (B : Type*) [CommRing B] [Algebra B A] (y : Spectrum A) : ℕ∞ := by
  let p := RingHom.ker (fibreHom (rfl : comap (algebraMap B A) y = _))
  let : p.IsPrime := RingHom.ker_isPrime _
  exact Module.length (Localization.AtPrime p) (Localization.AtPrime p)

/-- Natural-valued local module length. This raw definition uses ENat.toNat;
finite-fibre theorems prove finiteness and hence recover the genuine integer length. -/
def fibreLocalLength (B : Type*) [CommRing B] [Algebra B A] (y : Spectrum A) : ℕ :=
  (fibreLocalLengthENat B y).toNat

/-- Nonetale fibre norm multiplicity retains local length and residue degree. -/
def fibreNormMult (B : Type*) [CommRing B] [Algebra B A] (y : Spectrum A) : ℕ :=
  fibreLocalLength B y * fibreMult B y

/-- The local length computed at an arbitrary named base point. -/
theorem fibreLocalLength_eq {x : Spectrum B} {y : Spectrum A}
    (h : comap (algebraMap B A) y = x) :
    fibreLocalLength B y =
      (Module.length (Localization.AtPrime (RingHom.ker (fibreHom h)))
        (Localization.AtPrime (RingHom.ker (fibreHom h)))).toNat := by
  subst h
  rfl

/-- The actual residual-field homomorphism at the completed tensor support. -/
def fibreResidualHom {x : Spectrum B} {y : Spectrum A}
    (h : comap (algebraMap B A) y = x) :
    (RingHom.ker (fibreHom h)).ResidueField →+* H y :=
  Ideal.ResidueField.lift _ (fibreHom h) le_rfl (fun a ha =>
    isUnit_iff_ne_zero.mpr (fun hz => ha (show a ∈ RingHom.ker (fibreHom h) from hz)))

theorem fibreResidualHom_algebraMap {x : Spectrum B} {y : Spectrum A}
    (h : comap (algebraMap B A) y = x) (a : H x ⊗[B] A) :
    fibreResidualHom h (algebraMap _ _ a) = fibreHom h a :=
  Ideal.ResidueField.lift_algebraMap _ _ _ _ a

/-- The actual local residue valuation, obtained from the completed-field tensor map. -/
def fibreResidualValuation {x : Spectrum B} {y : Spectrum A}
    (h : comap (algebraMap B A) y = x) :
    Valuation (RingHom.ker (fibreHom h)).ResidueField ℝ≥0 :=
  (NormedField.valuation (K := H y)).comap (fibreResidualHom h)

theorem fibreResidualValuation_algebraMap {x : Spectrum B} {y : Spectrum A}
    (h : comap (algebraMap B A) y = x) (c : H x) :
    fibreResidualValuation h (algebraMap (H x) _ c) = ‖c‖₊ := by
  change ‖fibreResidualHom h (algebraMap (H x) _ c)‖₊ = _
  rw [IsScalarTower.algebraMap_apply (H x) (H x ⊗[B] A),
    fibreResidualHom_algebraMap, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, fibreHom_tmul_one]
  exact NNReal.eq (H.norm_map _ h c)

theorem fibreResidualValuation_one_tmul {x : Spectrum B} {y : Spectrum A}
    (h : comap (algebraMap B A) y = x) (a : A) :
    fibreResidualValuation h (algebraMap _ _ ((1 : H x) ⊗ₜ[B] a)) = y.val a := by
  change ‖fibreResidualHom h (algebraMap _ _ ((1 : H x) ⊗ₜ[B] a))‖₊ = _
  rw [fibreResidualHom_algebraMap, fibreHom_one_tmul, nnnorm_toH]

/-- Actual residue-degree times genuine local length, evaluated at a named
completed tensor point. The residue-field comparison is a real quotient algebra isomorphism. -/
theorem fibreNormMult_eq [Algebra.IsIntegral B A] {x : Spectrum B} {y : Spectrum A}
    (h : comap (algebraMap B A) y = x) :
    fibreNormMult B y =
      (Module.length (Localization.AtPrime (RingHom.ker (fibreHom h)))
        (Localization.AtPrime (RingHom.ker (fibreHom h)))).toNat *
        Module.finrank (H x) (RingHom.ker (fibreHom h)).ResidueField := by
  have := isMaximal_ker_fibreHom h
  let e := AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom (H x) ((H x ⊗[B] A) ⧸ RingHom.ker (fibreHom h))
      (RingHom.ker (fibreHom h)).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField _)
  rw [fibreNormMult, fibreLocalLength_eq h, fibreMult_eq h, e.toLinearEquiv.finrank_eq]

/-- The genuine local length times residue degree is the actual local-factor dimension. -/
theorem fibreNormMult_eq_localFinrank [Module.Finite B A] (y : Spectrum A) :
    fibreNormMult B y =
      Module.finrank (H (comap (algebraMap B A) y))
        (Localization.AtPrime (RingHom.ker (fibreHom (rfl : comap (algebraMap B A) y = _)))) := by
  let x := comap (algebraMap B A) y
  have hm := isMaximal_ker_fibreHom (rfl : comap (algebraMap B A) y = x)
  let m : MaximalSpectrum (H x ⊗[B] A) := ⟨_, hm⟩
  have : Module.Finite (H x) (H x ⊗[B] A) := inferInstance
  have : Module.Finite (H x) (Localization.AtPrime m.asIdeal) :=
    finiteAlgebraLocalization_moduleFinite (H x) (H x ⊗[B] A) m
  rw [fibreNormMult_eq (rfl : comap (algebraMap B A) y = x)]
  exact (finrank_eq_length_mul_residue_finrank (K := H x) (E := Localization.AtPrime m.asIdeal)).symm

/-- The intrinsic support-localization length is finite for an actual finite morphism. -/
theorem fibreLocalLengthENat_ne_top [Module.Finite B A] (y : Spectrum A) :
    fibreLocalLengthENat B y ≠ ⊤ := by
  let x := comap (algebraMap B A) y
  have hm := isMaximal_ker_fibreHom (rfl : comap (algebraMap B A) y = x)
  let m : MaximalSpectrum (H x ⊗[B] A) := ⟨_, hm⟩
  have : Module.Finite (H x) (H x ⊗[B] A) := inferInstance
  have : Module.Finite (H x) (Localization.AtPrime m.asIdeal) :=
    finiteAlgebraLocalization_moduleFinite (H x) (H x ⊗[B] A) m
  let : IsNoetherian (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal) :=
    isNoetherian_of_tower (H x) inferInstance
  let : IsArtinian (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal) :=
    isArtinian_of_tower (H x) inferInstance
  exact Module.length_ne_top

/-- Every actual nonetale finite-fibre norm multiplicity is positive. -/
theorem one_le_fibreNormMult [Module.Finite B A] (y : Spectrum A) : 1 ≤ fibreNormMult B y := by
  let x := comap (algebraMap B A) y
  have hm := isMaximal_ker_fibreHom (rfl : comap (algebraMap B A) y = x)
  let m : MaximalSpectrum (H x ⊗[B] A) := ⟨_, hm⟩
  have : Module.Finite (H x) (H x ⊗[B] A) := inferInstance
  have : Module.Finite (H x) (Localization.AtPrime m.asIdeal) :=
    finiteAlgebraLocalization_moduleFinite (H x) (H x ⊗[B] A) m
  rw [fibreNormMult_eq_localFinrank (B := B) y]
  exact Module.finrank_pos (R := H x) (M := Localization.AtPrime m.asIdeal)

/-- Genuine nonetale local-length multiplicities add up to the original finite-free rank. -/
theorem sum_fibreNormMult [Module.Free B A] [Module.Finite B A] (x : Spectrum B) :
    ∑ y ∈ (finite_preimage_singleton (A := A) x).toFinset, fibreNormMult B y =
      Module.finrank B A := by
  classical
  have := nontrivial_of_spectrum x
  have : IsArtinianRing (H x ⊗[B] A) := IsArtinianRing.of_finite (H x) _
  let : Fintype (MaximalSpectrum (H x ⊗[B] A)) := Fintype.ofFinite _
  have h1 : Module.finrank B A = ∑ m : MaximalSpectrum (H x ⊗[B] A),
      (Module.length (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal)).toNat *
        Module.finrank (H x) m.asIdeal.ResidueField := by
    rw [← Module.finrank_baseChange (R := H x),
      (finiteAlgebraLocalizationEquiv (H x) (H x ⊗[B] A)).toLinearEquiv.finrank_eq,
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

/-- Scalar norm at an arbitrary seminorm point, with genuine nonetale local
length times residue-degree multiplicities. -/
theorem val_algebraNorm_of_finiteFree [Module.Free B A] [Module.Finite B A]
    (b : A) (x : Spectrum B) :
    x.val (Algebra.norm B b) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset, y.val b ^ fibreNormMult B y := by
  classical
  have : IsArtinianRing (H x ⊗[B] A) := IsArtinianRing.of_finite (H x) _
  let : Fintype (MaximalSpectrum (H x ⊗[B] A)) := Fintype.ofFinite _
  let yOf : MaximalSpectrum (H x ⊗[B] A) → Spectrum A :=
    fun m => ((pointFibreEquivMaximalSpectrum x).symm m : Spectrum A)
  have hyOf : ∀ m, comap (algebraMap B A) (yOf m) = x :=
    fun m => ((pointFibreEquivMaximalSpectrum x).symm m).2
  have hker : ∀ m, RingHom.ker (fibreHom (hyOf m)) = m.asIdeal := fun m => by
    rw [← pointFibreEquivMaximalSpectrum_asIdeal, Equiv.apply_symm_apply]
  let g : ∀ m : MaximalSpectrum (H x ⊗[B] A), m.asIdeal.ResidueField →+* H (yOf m) := fun m =>
    Ideal.ResidueField.lift m.asIdeal (fibreHom (hyOf m)) (by rw [hker m])
      (fun a ha => isUnit_iff_ne_zero.mpr (fun hz => ha (by rw [← hker m]; exact hz)))
  have hg : ∀ m (a : H x ⊗[B] A), g m (algebraMap _ _ a) = fibreHom (hyOf m) a :=
    fun m a => Ideal.ResidueField.lift_algebraMap _ _ _ _ a
  let w : ∀ m : MaximalSpectrum (H x ⊗[B] A), Valuation m.asIdeal.ResidueField ℝ≥0 :=
    fun m => (NormedField.valuation (K := H (yOf m))).comap (g m)
  have hw : ∀ m (c : H x), w m (algebraMap (H x) m.asIdeal.ResidueField c) = ‖c‖₊ := by
    intro m c
    change ‖g m (algebraMap (H x) m.asIdeal.ResidueField c)‖₊ = _
    rw [IsScalarTower.algebraMap_apply (H x) (H x ⊗[B] A),
      hg, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, fibreHom_tmul_one]
    exact NNReal.eq (H.norm_map _ (hyOf m) c)
  have hwb : ∀ m (a : A), w m (algebraMap (H x ⊗[B] A) m.asIdeal.ResidueField ((1 : H x) ⊗ₜ a)) =
      (yOf m).val a := by
    intro m a
    change ‖g m (algebraMap (H x ⊗[B] A) m.asIdeal.ResidueField ((1 : H x) ⊗ₜ a))‖₊ = _
    rw [hg, fibreHom_one_tmul, nnnorm_toH]
  have hbase : x.val (Algebra.norm B b) =
      (NormedField.valuation (K := H x)) (Algebra.norm (H x) ((1 : H x) ⊗ₜ[B] b)) := by
    rw [← algebraNorm_baseChange_tmul (K := H x) b, algebraMap_H,
      NormedField.valuation_apply, nnnorm_toH]
  rw [hbase, valuation_algebraNorm_eq_prod_of_localAlgEquiv
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
    rw [hwb, hyy]

/-- Whole weighted determinant norm at any seminorm point, with actual nonetale
local lengths and full inseparable residue degrees. -/
theorem wgaussValuation_map_normForm_of_finiteFree [Module.Free B A] [Module.Finite B A]
    {σ : Type*} [Fintype σ] (b : σ → A) (r : σ → ℝ≥0) (x : Spectrum B) :
    wgaussValuation NormedField.valuation r (map (toH x) (normForm B b)) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ fibreNormMult B y := by
  classical
  have : IsArtinianRing (H x ⊗[B] A) := IsArtinianRing.of_finite (H x) _
  let : Fintype (MaximalSpectrum (H x ⊗[B] A)) := Fintype.ofFinite _
  let yOf : MaximalSpectrum (H x ⊗[B] A) → Spectrum A :=
    fun m => ((pointFibreEquivMaximalSpectrum x).symm m : Spectrum A)
  have hyOf : ∀ m, comap (algebraMap B A) (yOf m) = x :=
    fun m => ((pointFibreEquivMaximalSpectrum x).symm m).2
  have hker : ∀ m, RingHom.ker (fibreHom (hyOf m)) = m.asIdeal := fun m => by
    rw [← pointFibreEquivMaximalSpectrum_asIdeal, Equiv.apply_symm_apply]
  let g : ∀ m : MaximalSpectrum (H x ⊗[B] A), m.asIdeal.ResidueField →+* H (yOf m) := fun m =>
    Ideal.ResidueField.lift m.asIdeal (fibreHom (hyOf m)) (by rw [hker m])
      (fun a ha => isUnit_iff_ne_zero.mpr (fun hz => ha (by rw [← hker m]; exact hz)))
  have hg : ∀ m (a : H x ⊗[B] A), g m (algebraMap _ _ a) = fibreHom (hyOf m) a :=
    fun m a => Ideal.ResidueField.lift_algebraMap _ _ _ _ a
  let w : ∀ m : MaximalSpectrum (H x ⊗[B] A), Valuation m.asIdeal.ResidueField ℝ≥0 :=
    fun m => (NormedField.valuation (K := H (yOf m))).comap (g m)
  have hw : ∀ m (c : H x), w m (algebraMap (H x) m.asIdeal.ResidueField c) = ‖c‖₊ := by
    intro m c
    change ‖g m (algebraMap (H x) m.asIdeal.ResidueField c)‖₊ = _
    rw [IsScalarTower.algebraMap_apply (H x) (H x ⊗[B] A),
      hg, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, fibreHom_tmul_one]
    exact NNReal.eq (H.norm_map _ (hyOf m) c)
  have hwb : ∀ m (a : A), w m (algebraMap (H x ⊗[B] A) m.asIdeal.ResidueField ((1 : H x) ⊗ₜ a)) =
      (yOf m).val a := by
    intro m a
    change ‖g m (algebraMap (H x ⊗[B] A) m.asIdeal.ResidueField ((1 : H x) ⊗ₜ a))‖₊ = _
    rw [hg, fibreHom_one_tmul, nnnorm_toH]
  have hf : (finiteAlgebraMaximalSpectrumFinite (H x) (H x ⊗[B] A)).toFinset =
      Finset.univ := by
    ext m
    simp
  rw [← algebraMap_H, map_normForm_baseChange, wgaussValuation_normForm_of_finite w hw, hf]
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
    rw [hwb, hyy]

/-- The original coefficient weighted norm formula for every finite FREE algebra;
no reducedness, separability or infinitude is required. -/
theorem wgaussValuation_normForm_of_finiteFree [Module.Free B A] [Module.Finite B A]
    {σ : Type*} [Fintype σ] (b : σ → A) (r : σ → ℝ≥0) (x : Spectrum B) :
    wgaussValuation x.val r (normForm B b) =
      ∏ y ∈ (finite_preimage_singleton (A := A) x).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ fibreNormMult B y := by
  rw [← wgaussValuation_map x.val r (toH x) NormedField.valuation
    (fun a => nnnorm_toH x a)]
  exact wgaussValuation_map_normForm_of_finiteFree b r x

end EnvelopeProperty.Berkovich.Spectrum
namespace EnvelopeProperty.Berkovich.Spectrum

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]

/-- Genuine finite free weighted norm products commute with arbitrary
coefficient base change. The fibres need not be in bijection. -/
theorem weightedFibreNormProduct_baseChange [Module.Free A B] [Module.Finite A B]
 {σ : Type*} [Fintype σ]
    (b : σ → B) (r : σ → ℝ≥0) (x' : Spectrum C) :
    (∏ y' ∈ (finite_preimage_singleton (A := C ⊗[A] B) x').toFinset,
      (Finset.univ.sup fun j => y'.val ((1 : C) ⊗ₜ[A] b j) * r j) ^
        fibreNormMult C y') =
    ∏ y ∈ (finite_preimage_singleton (A := B) (comap (algebraMap A C) x')).toFinset,
      (Finset.univ.sup fun j => y.val (b j) * r j) ^ fibreNormMult A y := by
  rw [← wgaussValuation_normForm_of_finiteFree, ← wgaussValuation_normForm_of_finiteFree,
    ← EnvelopeProperty.map_normForm_baseChange]
  exact (EnvelopeProperty.wgaussValuation_map
    (comap (algebraMap A C) x').val r (algebraMap A C) x'.val
    (fun a => rfl) _)

/-- The scalar specialization of the genuine coefficient base-change formula. -/
theorem scalarFibreNormProduct_baseChange [Module.Free A B] [Module.Finite A B]
 (b : B) (x' : Spectrum C) :
    (∏ y' ∈ (finite_preimage_singleton (A := C ⊗[A] B) x').toFinset,
      y'.val ((1 : C) ⊗ₜ[A] b) ^ fibreNormMult C y') =
    ∏ y ∈ (finite_preimage_singleton (A := B) (comap (algebraMap A C) x')).toFinset,
      y.val b ^ fibreNormMult A y := by
  rw [← val_algebraNorm_of_finiteFree, ← val_algebraNorm_of_finiteFree,
    ← EnvelopeProperty.algebraNorm_baseChange_tmul]
  rfl

end EnvelopeProperty.Berkovich.Spectrum

namespace EnvelopeProperty.Berkovich.Spectrum

section ScalarExtension
variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
private local instance finiteNorm_rightAlgebra : Algebra A (S ⊗[R] A) :=
  Algebra.TensorProduct.rightAlgebra
private local instance (priority := low) finiteNorm_scalarExtensionAlgebra :
    Algebra (S ⊗[R] A) (S ⊗[R] B) :=
  ScalarExtension.algebra R S A B
private local instance (priority := low) finiteNorm_scalarExtensionFree [Module.Free A B] :
    Module.Free (S ⊗[R] A) (S ⊗[R] B) :=
  ScalarExtension.moduleFree R S A B
private local instance (priority := low) finiteNorm_scalarExtensionFinite [Module.Finite A B] :
    Module.Finite (S ⊗[R] A) (S ⊗[R] B) :=
  ScalarExtension.moduleFinite R S A B

/-- Weighted fibre norm products for the actual scalar-extended affine morphism. -/
theorem weightedFibreNormProduct_scalarExtension [Module.Free A B] [Module.Finite A B]
 {σ : Type*} [Fintype σ]
    (b : σ → B) (r : σ → ℝ≥0) (x' : Spectrum (S ⊗[R] A)) :
    (∏ y' ∈ (finite_preimage_singleton (A := S ⊗[R] B) x').toFinset,
      (Finset.univ.sup fun j => y'.val ((1 : S) ⊗ₜ[R] b j) * r j) ^
        fibreNormMult (S ⊗[R] A) y') =
    ∏ y ∈ (finite_preimage_singleton (A := B) (comap (algebraMap A (S ⊗[R] A)) x')).toFinset,
      (Finset.univ.sup fun j => y.val (b j) * r j) ^ fibreNormMult A y := by
  rw [← wgaussValuation_normForm_of_finiteFree, ← wgaussValuation_normForm_of_finiteFree,
    ← ScalarExtension.map_normForm R S A B]
  exact EnvelopeProperty.wgaussValuation_map
    (comap (algebraMap A (S ⊗[R] A)) x').val r (algebraMap A (S ⊗[R] A)) x'.val
    (fun a => rfl) _

/-- Scalar fibre norm products for the actual scalar-extended affine morphism. -/
theorem scalarFibreNormProduct_scalarExtension [Module.Free A B] [Module.Finite A B]
 (b : B) (x' : Spectrum (S ⊗[R] A)) :
    (∏ y' ∈ (finite_preimage_singleton (A := S ⊗[R] B) x').toFinset,
      y'.val ((1 : S) ⊗ₜ[R] b) ^ fibreNormMult (S ⊗[R] A) y') =
    ∏ y ∈ (finite_preimage_singleton (A := B) (comap (algebraMap A (S ⊗[R] A)) x')).toFinset,
      y.val b ^ fibreNormMult A y := by
  rw [← val_algebraNorm_of_finiteFree, ← val_algebraNorm_of_finiteFree, ← ScalarExtension.map_algebraNorm R S A B]
  rfl

/-- On prescribed-base point spaces, genuine weighted fibre products commute
with the actual compatible restriction map. -/
theorem weightedFibreNormProduct_relativeScalarExtension [Module.Free A B] [Module.Finite A B]
 {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}
    (hwv : ∀ r, w (algebraMap R S r) = v r)
    {σ : Type*} [Fintype σ] (b : σ → B) (r : σ → ℝ≥0)
    (x' : RelativeSpectrum w (S ⊗[R] A)) :
    (∏ y' ∈ (finite_preimage_singleton (A := S ⊗[R] B) x'.1).toFinset,
      (Finset.univ.sup fun j => y'.val ((1 : S) ⊗ₜ[R] b j) * r j) ^
        fibreNormMult (S ⊗[R] A) y') =
    ∏ y ∈ (finite_preimage_singleton (A := B)
      (RelativeSpectrum.baseChangeRestriction hwv x').1).toFinset,
      (Finset.univ.sup fun j => y.val (b j) * r j) ^ fibreNormMult A y :=
  weightedFibreNormProduct_scalarExtension b r x'.1


/-- The scalar companion on compatible prescribed-base point spaces. -/
theorem scalarFibreNormProduct_relativeScalarExtension [Module.Free A B] [Module.Finite A B]
 {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}
    (hwv : ∀ r, w (algebraMap R S r) = v r)
    (b : B) (x' : RelativeSpectrum w (S ⊗[R] A)) :
    (∏ y' ∈ (finite_preimage_singleton (A := S ⊗[R] B) x'.1).toFinset,
      y'.val ((1 : S) ⊗ₜ[R] b) ^ fibreNormMult (S ⊗[R] A) y') =
    ∏ y ∈ (finite_preimage_singleton (A := B)
      (RelativeSpectrum.baseChangeRestriction hwv x').1).toFinset,
      y.val b ^ fibreNormMult A y :=
  scalarFibreNormProduct_scalarExtension b x'.1

end ScalarExtension
end EnvelopeProperty.Berkovich.Spectrum
