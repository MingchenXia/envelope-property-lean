/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumFibre
import EnvelopeProperty.Berkovich.ValuationExtension

/-!
# Integral and finite fibres of arbitrary real seminorm spectra

An integral algebra over a complete ultrametric normed field has exactly one
prescribed-norm seminorm point over each maximal ideal. This is proved from
actual quotient-field norm existence and uniqueness. The genuine completed
tensor fibre equivalence then classifies integral fibres over arbitrary rings.
Module finiteness makes the tensor algebra Artinian and the fibre finite.
Prescribed-base fibres inherit the classification without triviality assumptions.
-/

open scoped NNReal Topology TensorProduct
open Classical

noncomputable section

namespace EnvelopeProperty.Berkovich

namespace RelativeSpectrum

section CompleteField

variable {K C : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [CommRing C] [Algebra K C] [Algebra.IsIntegral K C]

omit [CompleteSpace K] in
/-- Integral prescribed-norm points over a field have actual maximal valuation kernels. -/
theorem isMaximal_supp_of_isIntegral (x : RelativeSpectrum (NormedField.valuation (K := K)) C) :
    x.1.val.supp.IsMaximal := by
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := K) _ ?_
  have : (x.1.val.supp.comap (algebraMap K C)).IsPrime := Ideal.comap_isPrime _ _
  infer_instance

/-- Over a complete field, an integral prescribed-norm point is determined by its entire support. -/
theorem eq_of_supp_eq_of_isIntegral
    (x y : RelativeSpectrum (NormedField.valuation (K := K)) C)
    (hxy : x.1.val.supp = y.1.val.supp) : x = y := by
  let P := x.1.val.supp
  have : P.IsMaximal := isMaximal_supp_of_isIntegral x
  let : Field (C ⧸ P) := Ideal.Quotient.field P
  let vx : Valuation (C ⧸ P) ℝ≥0 := x.1.val.onQuot le_rfl
  let vy : Valuation (C ⧸ P) ℝ≥0 := y.1.val.onQuot hxy.le
  have hvx : ∀ c : K, vx (algebraMap K (C ⧸ P) c) = ‖c‖₊ := by
    intro c
    change x.1.val (algebraMap K C c) = ‖c‖₊
    exact x.2 c
  have hvy : ∀ c : K, vy (algebraMap K (C ⧸ P) c) = ‖c‖₊ := by
    intro c
    change y.1.val (algebraMap K C c) = ‖c‖₊
    exact y.2 c
  have hv := EnvelopeProperty.Valuation.eq_of_extends_norm hvx hvy
  apply Subtype.ext
  refine Spectrum.ext_val fun a => ?_
  exact congrArg (fun w : Valuation (C ⧸ P) ℝ≥0 => w (Ideal.Quotient.mk P a)) hv

/-- The actual maximal ideal associated with an integral prescribed-norm point. -/
def integralSupport (x : RelativeSpectrum (NormedField.valuation (K := K)) C) : MaximalSpectrum C :=
  ⟨x.1.val.supp, isMaximal_supp_of_isIntegral x⟩

omit [CompleteSpace K] in
@[simp]
theorem integralSupport_asIdeal (x : RelativeSpectrum (NormedField.valuation (K := K)) C) :
    (integralSupport x).asIdeal = x.1.val.supp := rfl

/-- Each maximal quotient field carries an actual extension of the complete coefficient norm. -/
theorem integralSupport_surjective : Function.Surjective
    (integralSupport : RelativeSpectrum (NormedField.valuation (K := K)) C → MaximalSpectrum C) := by
  intro m
  have : m.asIdeal.IsMaximal := m.isMaximal
  let : Field (C ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  obtain ⟨w, hw⟩ := EnvelopeProperty.Valuation.exists_extends_norm (K := K) (L := C ⧸ m.asIdeal)
  let x : RelativeSpectrum (NormedField.valuation (K := K)) C :=
    ⟨Spectrum.ofValuation (w.comap (Ideal.Quotient.mk m.asIdeal)), fun c => by
      change w (Ideal.Quotient.mk m.asIdeal (algebraMap K C c)) = ‖c‖₊
      rw [Ideal.Quotient.mk_algebraMap]
      exact hw c⟩
  refine ⟨x, MaximalSpectrum.ext (Ideal.ext fun a => ?_)⟩
  change w (Ideal.Quotient.mk m.asIdeal a) = 0 ↔ a ∈ m.asIdeal
  rw [Valuation.zero_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- The integral prescribed-norm spectrum is genuinely classified by maximal ideals. -/
theorem integralSupport_bijective : Function.Bijective
    (integralSupport : RelativeSpectrum (NormedField.valuation (K := K)) C → MaximalSpectrum C) :=
  ⟨fun x y h => eq_of_supp_eq_of_isIntegral x y (congrArg MaximalSpectrum.asIdeal h),
    integralSupport_surjective⟩

/-- The proved maximal-support classification as a point equivalence. -/
def integralMaximalSpectrumEquiv :
    RelativeSpectrum (NormedField.valuation (K := K)) C ≃ MaximalSpectrum C :=
  Equiv.ofBijective integralSupport integralSupport_bijective

/-- A finite algebra over a complete ultrametric field has finitely many prescribed-norm points. -/
theorem finite_normSpectrum [Module.Finite K C] :
    Finite (RelativeSpectrum (NormedField.valuation (K := K)) C) := by
  have : IsArtinianRing C := IsArtinianRing.of_finite K C
  exact Finite.of_injective integralSupport integralSupport_bijective.1

end CompleteField

end RelativeSpectrum

namespace Spectrum

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The tensor point's valuation support is precisely the kernel of its actual completed-field map. -/
theorem fibrePoint_supp {x : Spectrum A} {y : Spectrum B}
    (h : comap (algebraMap A B) y = x) :
    (fibrePoint h).1.val.supp = RingHom.ker (fibreHom h) := by
  ext q
  change ‖fibreHom h q‖₊ = 0 ↔ fibreHom h q = 0
  exact nnnorm_eq_zero

/-- Integral base change makes the genuine completed tensor support maximal. -/
theorem isMaximal_ker_fibreHom [Algebra.IsIntegral A B] {x : Spectrum A} {y : Spectrum B}
    (h : comap (algebraMap A B) y = x) : (RingHom.ker (fibreHom h)).IsMaximal := by
  rw [← fibrePoint_supp]
  exact RelativeSpectrum.isMaximal_supp_of_isIntegral (fibrePoint h)

/-- Send a fibre point to the actual maximal kernel of its completed-field tensor map. -/
def fibreToMaximalSpectrum [Algebra.IsIntegral A B] (x : Spectrum A) :
    Fibre (B := B) x → MaximalSpectrum (H x ⊗[A] B) :=
  fun y => ⟨RingHom.ker (fibreHom y.2), isMaximal_ker_fibreHom y.2⟩

/-- The completed tensor fibre equivalence and norm-extension theorem prove kernel classification. -/
theorem fibreToMaximalSpectrum_bijective [Algebra.IsIntegral A B] (x : Spectrum A) :
    Function.Bijective (fibreToMaximalSpectrum (B := B) x) := by
  have heq : fibreToMaximalSpectrum (B := B) x =
      RelativeSpectrum.integralSupport ∘ (fibreEquiv (B := B) x).symm := by
    funext y
    exact MaximalSpectrum.ext (fibrePoint_supp y.2).symm
  rw [heq]
  exact RelativeSpectrum.integralSupport_bijective.comp (fibreEquiv x).symm.bijective

/-- The actual seminorm fibre of an integral ring map is classified by maximal tensor ideals. -/
def fibreEquivMaximalSpectrum [Algebra.IsIntegral A B] (x : Spectrum A) :
    Fibre (B := B) x ≃ MaximalSpectrum (H x ⊗[A] B) :=
  Equiv.ofBijective (fibreToMaximalSpectrum x) (fibreToMaximalSpectrum_bijective x)

/-- The completed tensor kernel determines every integral fibre point. -/
theorem eq_of_ker_fibreHom_eq [Algebra.IsIntegral A B] {x : Spectrum A} {y₁ y₂ : Spectrum B}
    (h₁ : comap (algebraMap A B) y₁ = x) (h₂ : comap (algebraMap A B) y₂ = x)
    (hker : RingHom.ker (fibreHom h₁) = RingHom.ker (fibreHom h₂)) : y₁ = y₂ := by
  have he : (⟨y₁, h₁⟩ : Fibre x) = ⟨y₂, h₂⟩ :=
    (fibreToMaximalSpectrum_bijective x).1 (MaximalSpectrum.ext hker)
  exact congrArg Subtype.val he

/-- The fibres of a module-finite algebra homomorphism are finite, without coefficient restrictions. -/
theorem finite_fibre [Module.Finite A B] (x : Spectrum A) : Finite (Fibre (B := B) x) := by
  have : IsArtinianRing (H x ⊗[A] B) := IsArtinianRing.of_finite (H x) _
  exact Finite.of_injective _ (fibreToMaximalSpectrum_bijective (B := B) x).1

omit [Algebra A B] in
/-- An arbitrary module-finite ring homomorphism has finite inverse images of singletons. -/
theorem finite_preimage_comap_singleton (φ : A →+* B) (hφ : φ.Finite) (x : Spectrum A) :
    (comap φ ⁻¹' {x}).Finite := by
  let : Algebra A B := φ.toAlgebra
  let : Module.Finite A B := hφ
  have : Finite (Fibre (B := B) x) := finite_fibre x
  apply Set.finite_coe_iff.mp
  exact Finite.of_injective
    (fun y : comap φ ⁻¹' {x} =>
      (⟨y.1, Set.mem_singleton_iff.mp y.2⟩ : Fibre (B := B) x))
    (fun _ _ h => Subtype.ext (congrArg Subtype.val h))

end Spectrum

namespace RelativeSpectrum

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  {v : Valuation R ℝ≥0}

/-- The actual fibre of a scalar-tower algebra pullback between prescribed-base spectra. -/
abbrev Fibre (x : RelativeSpectrum v A) :=
  {y : RelativeSpectrum v B // comap (IsScalarTower.toAlgHom R A B) y = x}

/-- Every absolute point over a prescribed-base point automatically has the same base values. -/
def fibreForgetEquiv (x : RelativeSpectrum v A) : Fibre (B := B) x ≃ Spectrum.Fibre (B := B) x.1 where
  toFun y := ⟨y.1.1, congrArg Subtype.val y.2⟩
  invFun z := ⟨⟨z.1, fun r => by
    have h := congrArg (fun t : Spectrum A => t.val (algebraMap R A r)) z.2
    change z.1.val (algebraMap A B (algebraMap R A r)) = x.1.val (algebraMap R A r) at h
    rw [← IsScalarTower.algebraMap_apply R A B] at h
    exact h.trans (x.2 r)⟩, Subtype.ext z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Arbitrary prescribed-base integral fibres have the same genuine completed tensor classification. -/
def fibreEquivMaximalSpectrum [Algebra.IsIntegral A B] (x : RelativeSpectrum v A) :
    Fibre (B := B) x ≃ MaximalSpectrum (Spectrum.H x.1 ⊗[A] B) :=
  (fibreForgetEquiv x).trans (Spectrum.fibreEquivMaximalSpectrum x.1)

/-- Module-finite relative algebra morphisms have finite fibres for every prescribed base valuation. -/
theorem finite_fibre [Module.Finite A B] (x : RelativeSpectrum v A) : Finite (Fibre (B := B) x) := by
  have := Spectrum.finite_fibre (B := B) x.1
  exact Finite.of_injective _ (fibreForgetEquiv x).injective

omit [Algebra A B] [IsScalarTower R A B] in
/-- Every finite algebra homomorphism has finite prescribed-base point fibres. -/
theorem finite_preimage_comap_singleton (φ : A →ₐ[R] B) (hφ : φ.toRingHom.Finite)
    (x : RelativeSpectrum v A) : (comap φ ⁻¹' {x}).Finite := by
  let : Algebra A B := φ.toRingHom.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  let : Module.Finite A B := hφ
  have : Finite (Fibre (B := B) x) := finite_fibre x
  apply Set.finite_coe_iff.mp
  exact Finite.of_injective
    (fun y : comap φ ⁻¹' {x} =>
      (⟨y.1, Set.mem_singleton_iff.mp y.2⟩ : Fibre (B := B) x))
    (fun _ _ h => Subtype.ext (congrArg Subtype.val h))

end RelativeSpectrum

end EnvelopeProperty.Berkovich
