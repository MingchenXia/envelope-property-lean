/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.GenericMinimalComponents
import EnvelopeProperty.TensorFractionComparison
import EnvelopeProperty.EtaleGenericFibre
import EnvelopeProperty.ComponentNormalizationProduct
import Mathlib.RingTheory.TensorProduct.Pi

open scoped nonZeroDivisors TensorProduct
noncomputable section
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace EnvelopeProperty.ReducedComponents
variable {A R : Type*} [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
  [Module.Finite A R]

/-- The actual generic algebra of each original component agrees with that of its literal normalization. -/
def componentNormalizationGenericEquiv (p : Index (⊥ : Ideal R))
    (hp : Function.Injective (algebraMap A (Component (⊥ : Ideal R) p))) :
    FractionRing A ⊗[A] Component (⊥ : Ideal R) p ≃ₐ[FractionRing A]
      FractionRing A ⊗[A] CurveNormalization.Ring (Component (⊥ : Ideal R) p) := by
  let C := Component (⊥ : Ideal R) p
  let N := CurveNormalization.Ring C
  let L := FractionRing C
  have : Module.Finite A C := inferInstance
  have : Algebra.IsIntegral A N := Algebra.IsIntegral.trans C
  have : IsFractionRing N L := CurveNormalization.isFractionRing_ring C
  have hi : Function.Injective (algebraMap A N) := CurveNormalization.coefficientMap_injective A C hp
  exact ((AlgebraicFraction.tensorFractionEquivOverBase (K := FractionRing A) (L := L) hp).trans
    (AlgebraicFraction.tensorFractionEquivOverBase (K := FractionRing A) (L := L) hi).symm).extendScalarsOfIsLocalization
      (FractionRing A) A⁰

/-- The genuine component generic comparison retains every original entire component element. -/
theorem componentNormalizationGenericEquiv_one_tmul (p : Index (⊥ : Ideal R))
    (hp : Function.Injective (algebraMap A (Component (⊥ : Ideal R) p)))
    (c : Component (⊥ : Ideal R) p) :
    componentNormalizationGenericEquiv p hp (1 ⊗ₜ[A] c) =
      1 ⊗ₜ[A] CurveNormalization.inclusion _ c := by
  let C := Component (⊥ : Ideal R) p
  let N := CurveNormalization.Ring C
  let L := FractionRing C
  have : Module.Finite A C := inferInstance
  have : Algebra.IsIntegral A N := Algebra.IsIntegral.trans C
  have : IsFractionRing N L := CurveNormalization.isFractionRing_ring C
  have hi : Function.Injective (algebraMap A N) := CurveNormalization.coefficientMap_injective A C hp
  change (AlgebraicFraction.tensorFractionEquivOverBase (K := FractionRing A) (L := L) hi).symm
    ((AlgebraicFraction.tensorFractionEquivOverBase (K := FractionRing A) (L := L) hp) _) = _
  apply (AlgebraicFraction.tensorFractionEquivOverBase (K := FractionRing A) (L := L) hi).injective
  rw [AlgEquiv.apply_symm_apply, AlgebraicFraction.tensorFractionEquivOverBase_one_tmul,
    AlgebraicFraction.tensorFractionEquivOverBase_one_tmul]
  rfl

omit [Module.Finite A R] in
/-- Actual domination means no original minimal component meets a nonzero coefficient denominator. -/
theorem coefficientDenominators_disjoint
    (p : Index (⊥ : Ideal R))
    (hp : Function.Injective (algebraMap A (Component (⊥ : Ideal R) p))) :
    Disjoint (Algebra.algebraMapSubmonoid R A⁰ : Set R) (p.1 : Set R) := by
  refine Set.disjoint_left.mpr ?_
  intro r hr hrp
  obtain ⟨a, ha, rfl⟩ := hr
  have hz : algebraMap A (Component (⊥ : Ideal R) p) a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hrp
  exact (mem_nonZeroDivisors_iff_ne_zero.mp ha)
    ((injective_iff_map_eq_zero _).mp hp a hz)

/-- Actual finite generic algebra and genuine surviving components derive finiteness of the original minimal index. -/
theorem genericIndex_finite
    (hd : ∀ p : Index (⊥ : Ideal R), Function.Injective (algebraMap A (Component (⊥ : Ideal R) p))) :
    Finite (Index (⊥ : Ideal R)) := by
  let E := FractionRing A ⊗[A] R
  have : IsArtinianRing E := IsArtinianRing.of_finite (FractionRing A) E
  exact localizationIndex_finite (Algebra.algebraMapSubmonoid R A⁰) E
    (fun p => coefficientDenominators_disjoint p (hd p))

/-- The actual reduced finite generic algebra is the whole tensor product of its original component quotients. -/
def genericReducedEquivPiComponents [IsReduced (FractionRing A ⊗[A] R)]
    (hd : ∀ p : Index (⊥ : Ideal R), Function.Injective (algebraMap A (Component (⊥ : Ideal R) p))) :
    FractionRing A ⊗[A] R ≃ₐ[FractionRing A]
      ∀ p : Index (⊥ : Ideal R), FractionRing A ⊗[A] Component (⊥ : Ideal R) p := by
  let E := FractionRing A ⊗[A] R
  let M := Algebra.algebraMapSubmonoid R A⁰
  have : IsArtinianRing E := IsArtinianRing.of_finite (FractionRing A) E
  have hM : ∀ p : Index (⊥ : Ideal R), Disjoint (M : Set R) (p.1 : Set R) :=
    fun p => coefficientDenominators_disjoint p (hd p)
  exact ((localizationReducedEquivPi M E hM).restrictScalars (FractionRing A)).trans
    (AlgEquiv.piCongrRight fun p : Index (⊥ : Ideal R) =>
      (Algebra.TensorProduct.tensorQuotientEquiv (R := A) (FractionRing A) R (FractionRing A) p.1).symm)

/-- The entire original generic function lands in its actual original component quotient. -/
theorem genericReducedEquivPiComponents_one_tmul [IsReduced (FractionRing A ⊗[A] R)]
    (hd : ∀ p : Index (⊥ : Ideal R), Function.Injective (algebraMap A (Component (⊥ : Ideal R) p)))
    (r : R) (p : Index (⊥ : Ideal R)) :
    genericReducedEquivPiComponents hd (1 ⊗ₜ[A] r) p =
      1 ⊗ₜ[A] Ideal.Quotient.mk p.1 r := by
  change (Algebra.TensorProduct.tensorQuotientEquiv (R := A) (FractionRing A) R (FractionRing A) p.1).symm
    (Ideal.Quotient.mk (p.1.map (algebraMap R (FractionRing A ⊗[A] R))) (1 ⊗ₜ[A] r)) = _
  exact Algebra.TensorProduct.tensorQuotientEquiv_symm_apply_tmul _ _ _ _ _ _

/-- Genuine generic reduction and actual component domination construct the entire normalization-product generic comparison. -/
def genericNormalizationProductEquiv [IsReduced (FractionRing A ⊗[A] R)]
    (hd : ∀ p : Index (⊥ : Ideal R), Function.Injective (algebraMap A (Component (⊥ : Ideal R) p))) :
    FractionRing A ⊗[A] R ≃ₐ[FractionRing A]
      FractionRing A ⊗[A] NormalizationProduct (⊥ : Ideal R) := by
  classical
  let E := FractionRing A ⊗[A] R
  let M := Algebra.algebraMapSubmonoid R A⁰
  have : IsArtinianRing E := IsArtinianRing.of_finite (FractionRing A) E
  have hM : ∀ p : Index (⊥ : Ideal R), Disjoint (M : Set R) (p.1 : Set R) :=
    fun p => coefficientDenominators_disjoint p (hd p)
  have : Finite (Index (⊥ : Ideal R)) := localizationIndex_finite M E hM
  let : Fintype (Index (⊥ : Ideal R)) := Fintype.ofFinite _
  exact (genericReducedEquivPiComponents hd).trans
    ((AlgEquiv.piCongrRight fun p : Index (⊥ : Ideal R) => componentNormalizationGenericEquiv p (hd p)).trans
      (Algebra.TensorProduct.piRight A (FractionRing A) (FractionRing A)
        (fun p : Index (⊥ : Ideal R) => CurveNormalization.Ring (Component (⊥ : Ideal R) p))).symm)

/-- Every whole original function is retained under the actual generic normalization-product isomorphism. -/
theorem genericNormalizationProductEquiv_one_tmul [IsReduced (FractionRing A ⊗[A] R)]
    (hd : ∀ p : Index (⊥ : Ideal R), Function.Injective (algebraMap A (Component (⊥ : Ideal R) p)))
    (r : R) :
    genericNormalizationProductEquiv hd (1 ⊗ₜ[A] r) =
      1 ⊗ₜ[A] normalizationMap (⊥ : Ideal R) r := by
  classical
  have : Finite (Index (⊥ : Ideal R)) := genericIndex_finite hd
  let : Fintype (Index (⊥ : Ideal R)) := Fintype.ofFinite _
  let e := Algebra.TensorProduct.piRight A (FractionRing A) (FractionRing A)
    (fun p : Index (⊥ : Ideal R) => CurveNormalization.Ring (Component (⊥ : Ideal R) p))
  apply e.injective
  change e (e.symm (fun p : Index (⊥ : Ideal R) =>
    componentNormalizationGenericEquiv p (hd p) (genericReducedEquivPiComponents hd (1 ⊗ₜ[A] r) p))) = _
  rw [AlgEquiv.apply_symm_apply]
  change (fun p : Index (⊥ : Ideal R) =>
    componentNormalizationGenericEquiv p (hd p) (genericReducedEquivPiComponents hd (1 ⊗ₜ[A] r) p)) =
      fun p => 1 ⊗ₜ[A] normalizationMap (⊥ : Ideal R) r p
  funext p
  rw [genericReducedEquivPiComponents_one_tmul, componentNormalizationGenericEquiv_one_tmul]
  rfl

/-- The whole canonical base-changed original normalization map is the constructed genuine generic isomorphism. -/
theorem genericNormalizationProductEquiv_toAlgHom [IsReduced (FractionRing A ⊗[A] R)]
    (hd : ∀ p : Index (⊥ : Ideal R), Function.Injective (algebraMap A (Component (⊥ : Ideal R) p))) :
    (genericNormalizationProductEquiv hd).toAlgHom =
      Algebra.TensorProduct.map (AlgHom.id (FractionRing A) (FractionRing A))
        (normalizationMapAlg A (⊥ : Ideal R)) := by
  apply Algebra.TensorProduct.ext
  · ext
  · ext r
    exact genericNormalizationProductEquiv_one_tmul hd r

/-- Genuine generic reducedness and actual domination prove the original normalization map is a generic isomorphism. -/
theorem genericNormalizationMap_bijective [IsReduced (FractionRing A ⊗[A] R)]
    (hd : ∀ p : Index (⊥ : Ideal R), Function.Injective (algebraMap A (Component (⊥ : Ideal R) p))) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (FractionRing A) (FractionRing A))
      (normalizationMapAlg A (⊥ : Ideal R))) := by
  rw [← genericNormalizationProductEquiv_toAlgHom hd]
  exact (genericNormalizationProductEquiv hd).bijective

/-- Actual finite free normalization-product rank is the degree of the ORIGINAL unreduced generic algebra, when its genuine generic fibre is reduced. -/
theorem finrank_normalizationProduct_eq_original_generic
    [Module.Free A (NormalizationProduct (⊥ : Ideal R))]
    [Module.Finite A (NormalizationProduct (⊥ : Ideal R))]
    [IsReduced (FractionRing A ⊗[A] R)]
    (hd : ∀ p : Index (⊥ : Ideal R), Function.Injective (algebraMap A (Component (⊥ : Ideal R) p))) :
    Module.finrank A (NormalizationProduct (⊥ : Ideal R)) =
      Module.finrank (FractionRing A) (FractionRing A ⊗[A] R) := by
  rw [← Module.finrank_baseChange (R := FractionRing A),
    (genericNormalizationProductEquiv hd).toLinearEquiv.finrank_eq]

/-- An actual nonzero etale principal open derives the entire normalization map's genuine generic bijectivity. -/
theorem genericNormalizationMap_bijective_of_principal_etale (a : A) (ha : a ≠ 0)
    [Algebra.Etale (Localization.Away a) (Localization.Away a ⊗[A] R)]
    (hd : ∀ p : Index (⊥ : Ideal R), Function.Injective (algebraMap A (Component (⊥ : Ideal R) p))) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (FractionRing A) (FractionRing A))
      (normalizationMapAlg A (⊥ : Ideal R))) := by
  have : IsReduced (FractionRing A ⊗[A] R) := generic_isReduced_of_principal_etale a ha
  exact genericNormalizationMap_bijective hd

/-- Actual finite free normalization rank equals the original generic degree from genuine etaleness on a nonzero principal open. -/
theorem finrank_normalizationProduct_eq_original_generic_of_principal_etale
    [Module.Free A (NormalizationProduct (⊥ : Ideal R))]
    [Module.Finite A (NormalizationProduct (⊥ : Ideal R))]
    (a : A) (ha : a ≠ 0)
    [Algebra.Etale (Localization.Away a) (Localization.Away a ⊗[A] R)]
    (hd : ∀ p : Index (⊥ : Ideal R), Function.Injective (algebraMap A (Component (⊥ : Ideal R) p))) :
    Module.finrank A (NormalizationProduct (⊥ : Ideal R)) =
      Module.finrank (FractionRing A) (FractionRing A ⊗[A] R) := by
  have : IsReduced (FractionRing A ⊗[A] R) := generic_isReduced_of_principal_etale a ha
  exact finrank_normalizationProduct_eq_original_generic hd

end EnvelopeProperty.ReducedComponents
