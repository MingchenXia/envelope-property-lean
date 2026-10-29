import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingBaseChange
import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingRatioEquiv
import Mathlib.RingTheory.Localization.FractionRing

/-! # The WHOLE generic algebra over the SAME original fraction field

Literal tensor products are identified by their native whole pushout property.
The ratio comparison keeps every original coefficient and root.
-/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching
namespace BaseChange
open NadelMixedKummer
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {q : ℕ}
  (N : Fin q → ℕ) (c : Fin q → R)

/-- The genuine WHOLE tensor product equals the actual mapped-coefficient
quotient, from the two proved native pushout universal properties. -/
def tensorRingEquiv : S ⊗[R] NadelMixedKummer.Ring N c ≃+*
    NadelMixedKummer.Ring N (fun i => algebraMap R S (c i)) :=
  ((CommRingCat.isPushout_tensorProduct R S (NadelMixedKummer.Ring N c)).isoIsPushout
    _ _ (isPushout N c (algebraMap R S))).commRingCatIsoToRingEquiv

/-- The tensor comparison preserves the WHOLE new coefficient inclusion. -/
theorem tensorRingEquiv_left : (tensorRingEquiv (S := S) N c).toRingHom.comp
    Algebra.TensorProduct.includeLeftRingHom =
      algebraMap S (NadelMixedKummer.Ring N (fun i => algebraMap R S (c i))) := by
  exact congrArg CommRingCat.Hom.hom
    (IsPushout.inl_isoIsPushout_hom _ _
      (CommRingCat.isPushout_tensorProduct R S (NadelMixedKummer.Ring N c))
      (isPushout N c (algebraMap R S)))

/-- The WHOLE original algebra inclusion remains its actual coefficient
extension, without passing to a component or reduced quotient. -/
theorem tensorRingEquiv_right : (tensorRingEquiv (S := S) N c).toRingHom.comp
    Algebra.TensorProduct.includeRight.toRingHom = map N c (algebraMap R S) := by
  exact congrArg CommRingCat.Hom.hom
    (IsPushout.inr_isoIsPushout_hom _ _
      (CommRingCat.isPushout_tensorProduct R S (NadelMixedKummer.Ring N c))
      (isPushout N c (algebraMap R S)))

/-- The actual tensor comparison is an algebra isomorphism over the SAME
new coefficient ring. -/
def tensorAlgEquiv : S ⊗[R] NadelMixedKummer.Ring N c ≃ₐ[S]
    NadelMixedKummer.Ring N (fun i => algebraMap R S (c i)) :=
  { toRingEquiv := tensorRingEquiv N c
    commutes' := fun s => congrArg (fun f : S →+* _ => f s) (tensorRingEquiv_left N c) }

/-- Every SAME original root has its corresponding whole generic root. -/
theorem tensorAlgEquiv_root (i : Fin q) :
    tensorAlgEquiv (S := S) N c (Algebra.TensorProduct.includeRight (root N c i)) =
      root N (fun i => algebraMap R S (c i)) i := by
  exact (congrArg (fun f : NadelMixedKummer.Ring N c →+* _ => f (root N c i))
    (tensorRingEquiv_right (S := S) N c)).trans (map_root N c (algebraMap R S) i)

end BaseChange
namespace MultiRatio
open NadelMixedKummer
variable {R : Type u} [CommRing R] [IsDomain R] {q : ℕ}
  (N : Fin q → ℕ) (c b : Fin q → R) (H : Fin q → Fin q)
  (hH : ∀ i, H (H i) = H i) (hN : ∀ i, N (H i) = N i)
  (hb : ∀ i, b (H i) = c (H i))
  (hc : ∀ i, i ≠ H i → c i = c (H i) * b i)
  (hpositive : ∀ i, 0 < N i) (hne : ∀ i, c (H i) ≠ 0)

include hne in
/-- The SAME original fraction field inverts every actual original
nonzero distinguished branch coefficient. -/
theorem generic_common_isUnit (i : Fin q) :
    IsUnit (algebraMap R (FractionRing R) (c (H i))) := by
  apply isUnit_iff_ne_zero.mpr
  simpa only [map_zero] using (IsFractionRing.injective R (FractionRing R)).ne (hne i)

/-- The WHOLE generic quotient comparison over the SAME original function
field, retaining the actual original indices and every original root. -/
def genericQuotientAlgEquiv :
    Ring N (fun i => algebraMap R (FractionRing R) (c i)) ≃ₐ[FractionRing R]
      Ring N (fun i => algebraMap R (FractionRing R) (b i)) :=
  wholeAlgEquiv N (fun i => algebraMap R (FractionRing R) (c i))
    (fun i => algebraMap R (FractionRing R) (b i)) H hH hN
    (fun i => congrArg (algebraMap R (FractionRing R)) (hb i))
    (fun i hi => by rw [hc i hi, map_mul]) hpositive (generic_common_isUnit c H hne)

/-- The SAME literal WHOLE generic tensor algebra of the original raw
quotient is the WHOLE generic tensor algebra of the adapted ratio quotient.
No field factor, connected component or unit-root factor is discarded. -/
def genericTensorAlgEquiv :
    FractionRing R ⊗[R] Ring N c ≃ₐ[FractionRing R] FractionRing R ⊗[R] Ring N b :=
  (BaseChange.tensorAlgEquiv N c).trans
    ((genericQuotientAlgEquiv N c b H hH hN hb hc hpositive hne).trans
      (BaseChange.tensorAlgEquiv N b).symm)

/-- The actual generic quotient map retains EVERY original raw root's
whole monomial value, with all original root labels unchanged. -/
theorem genericQuotientAlgEquiv_root (i : Fin q) :
    genericQuotientAlgEquiv N c b H hH hN hb hc hpositive hne
      (root N (fun i => algebraMap R (FractionRing R) (c i)) i) =
        forwardRoots N (fun i => algebraMap R (FractionRing R) (b i)) H i :=
  rawToRatio_root N (fun i => algebraMap R (FractionRing R) (c i))
    (fun i => algebraMap R (FractionRing R) (b i)) H hN
    (fun i => congrArg (algebraMap R (FractionRing R)) (hb i))
    (fun i hi => by rw [hc i hi, map_mul]) i

/-- Every SAME original raw root has its actual whole generic monomial
image in the literal SAME original fraction-field tensor algebra. -/
theorem genericTensorAlgEquiv_root (i : Fin q) :
    genericTensorAlgEquiv N c b H hH hN hb hc hpositive hne
      (Algebra.TensorProduct.includeRight (root N c i)) =
        Algebra.TensorProduct.includeRight (forwardRoots N b H i) := by
  apply (BaseChange.tensorAlgEquiv (S := FractionRing R) N b).injective
  change BaseChange.tensorAlgEquiv N b
      ((BaseChange.tensorAlgEquiv N b).symm
        (genericQuotientAlgEquiv N c b H hH hN hb hc hpositive hne
          (BaseChange.tensorAlgEquiv N c (Algebra.TensorProduct.includeRight (root N c i))))) = _
  rw [AlgEquiv.apply_symm_apply, BaseChange.tensorAlgEquiv_root, genericQuotientAlgEquiv_root]
  by_cases hi : i = H i
  · simp only [forwardRoots, if_pos hi, BaseChange.tensorAlgEquiv_root]
  · simp only [forwardRoots, if_neg hi, map_mul, BaseChange.tensorAlgEquiv_root]

/-- The actual WHOLE generic isomorphism commutes with the original raw
algebra inclusion on EVERY element, not only on a selected component. -/
theorem genericTensorAlgEquiv_includeRight (z : Ring N c) :
    genericTensorAlgEquiv N c b H hH hN hb hc hpositive hne
      (Algebra.TensorProduct.includeRight z) =
        Algebra.TensorProduct.includeRight (rawToRatio N c b H hN hb hc z) := by
  have heq : (genericTensorAlgEquiv N c b H hH hN hb hc hpositive hne).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (rawToRatio N c b H hN hb hc) := by
    refine NadelMixedKummer.hom_ext (S := FractionRing R ⊗[R] Ring N b) N c _ _ ?_ ?_
    · ext r
      change genericTensorAlgEquiv N c b H hH hN hb hc hpositive hne
          (Algebra.TensorProduct.includeRight (algebraMap R (Ring N c) r)) =
          Algebra.TensorProduct.includeRight (rawToRatio N c b H hN hb hc (algebraMap R (Ring N c) r))
      have hr : rawToRatio N c b H hN hb hc (algebraMap R (Ring N c) r) =
          algebraMap R (Ring N b) r := (rawAlgHom N c b H hN hb hc).commutes r
      rw [hr, Algebra.TensorProduct.includeRight.commutes, Algebra.TensorProduct.includeRight.commutes,
        IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing R ⊗[R] Ring N c),
        IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing R ⊗[R] Ring N b)]
      exact (genericTensorAlgEquiv N c b H hH hN hb hc hpositive hne).commutes _
    · intro i
      change genericTensorAlgEquiv N c b H hH hN hb hc hpositive hne
          (Algebra.TensorProduct.includeRight (root N c i)) =
          Algebra.TensorProduct.includeRight (rawToRatio N c b H hN hb hc (root N c i))
      rw [genericTensorAlgEquiv_root, rawToRatio_root]
  exact congrArg (fun f : Ring N c →+* FractionRing R ⊗[R] Ring N b => f z) heq

end MultiRatio
end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching
