import EnvelopeProperty.DeligneIllusie.WittTwoEtaleLiftRestriction

/-! # Actual chosen etale restrictions of original Witt lifts preserve identity and composition -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoEtaleRestrictionCoherence
open scoped TensorProduct
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoSourceResidue.twistSMul WittTwoRelativeLift.residueCopyAlgebra
  WittTwoLiftDifference.frobeniusAlgebra
  WittTwoOriginalCotangentMaps.originalResidueRing WittTwoOriginalCotangentMaps.residueAlgebra
private abbrev T (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A] :=
  WittTwoRelativeLift.TwistAlgebra p k A
private abbrev B (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A] :=
  WittTwoSmoothDifferentials.ResidueAlgebra p k A
variable {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
  [Algebra (WittTwo.Ring p k) A] [Algebra (WittTwo.Ring p k) A'] [Algebra (WittTwo.Ring p k) A'']
  (β : A →ₐ[WittTwo.Ring p k] A') (γ : A' →ₐ[WittTwo.Ring p k] A'')

omit [PerfectRing k p] in
/-- EVERY actual twisted element retains the original composite algebra image. -/
theorem twistMap_comp (t : T p k A) :
    WittTwoLiftDifferenceNaturality.twistMap p k (γ.comp β) t =
      WittTwoLiftDifferenceNaturality.twistMap p k γ
        (WittTwoLiftDifferenceNaturality.twistMap p k β t) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add t s ht hs => rw [map_add, map_add, map_add, ht, hs]
  | tmul c a =>
    rw [WittTwoLiftDifferenceNaturality.twistMap_tmul,
      WittTwoLiftDifferenceNaturality.twistMap_tmul,
      WittTwoLiftDifferenceNaturality.twistMap_tmul]
    rfl

variable [Algebra.Smooth (WittTwo.Ring p k) A']
variable (f : WittTwoLiftDifference.Lift p k A)
  (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)
  (hβ : β.toRingHom.Etale)

/-- The genuine unique original restricted lift, produced rather than supplied. -/
def restrictedLift : WittTwoLiftDifference.Lift p k A' :=
  (WittTwoEtaleLiftRestriction.exists_restrictedLift p k β f hf hβ).choose

/-- The produced whole original restriction has exactly the genuine target residue Frobenius. -/
theorem restrictedLift_reduction (t : T p k A') :
    algebraMap A' (B p k A') (restrictedLift p k β f hf hβ t) =
      WittTwoRelativeLift.residueFrobenius p k A' t :=
  (WittTwoEtaleLiftRestriction.exists_restrictedLift p k β f hf hβ).choose_spec.1 t

/-- The literal lifted restriction square is internally derived on EVERY actual element. -/
theorem restrictedLift_commutes (t : T p k A) :
    β (f t) = restrictedLift p k β f hf hβ (WittTwoLiftDifferenceNaturality.twistMap p k β t) :=
  (WittTwoEtaleLiftRestriction.exists_restrictedLift p k β f hf hβ).choose_spec.2 t

omit [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A'] in
private theorem twistMap_id (t : T p k A) :
    WittTwoLiftDifferenceNaturality.twistMap p k (AlgHom.id (WittTwo.Ring p k) A) t = t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | add t s ht hs => rw [map_add, ht, hs]
  | tmul c a => rw [WittTwoLiftDifferenceNaturality.twistMap_tmul]; rfl

omit [Algebra.Smooth (WittTwo.Ring p k) A'] in
/-- Actual identity restriction returns the SAME original whole lift. -/
theorem restrictedLift_id [Algebra.Smooth (WittTwo.Ring p k) A] :
    restrictedLift p k (AlgHom.id (WittTwo.Ring p k) A) f hf
      (RingHom.Etale.of_bijective Function.bijective_id) = f := by
  apply WittTwoEtaleLiftRestriction.restrictedLift_unique p k (AlgHom.id (WittTwo.Ring p k) A) f
    (RingHom.Etale.of_bijective Function.bijective_id)
  · exact restrictedLift_reduction p k _ f hf _
  · exact hf
  · exact restrictedLift_commutes p k _ f hf _
  · intro t
    rw [twistMap_id]
    rfl

/-- Actual composite restriction equals the two successive whole original restrictions. -/
theorem restrictedLift_comp [Algebra.Smooth (WittTwo.Ring p k) A''] (hγ : γ.toRingHom.Etale) :
    restrictedLift p k (γ.comp β) f hf
      (RingHom.Etale.stableUnderComposition β.toRingHom γ.toRingHom hβ hγ) =
    restrictedLift p k γ (restrictedLift p k β f hf hβ)
      (restrictedLift_reduction p k β f hf hβ) hγ := by
  apply WittTwoEtaleLiftRestriction.restrictedLift_unique p k (γ.comp β) f
    (RingHom.Etale.stableUnderComposition β.toRingHom γ.toRingHom hβ hγ)
  · exact restrictedLift_reduction p k _ f hf _
  · exact restrictedLift_reduction p k _ _ _ _
  · exact restrictedLift_commutes p k _ f hf _
  · intro t
    change γ (β (f t)) = _
    rw [restrictedLift_commutes p k β f hf hβ,
      restrictedLift_commutes p k γ (restrictedLift p k β f hf hβ)
        (restrictedLift_reduction p k β f hf hβ) hγ, twistMap_comp]

end EnvelopeProperty.DeligneIllusie.WittTwoEtaleRestrictionCoherence
