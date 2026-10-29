import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistTargetLocalization
import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationReductionPushout

/-! # Genuine geometric-Frobenius cotangent divisors and their actual localized lifts -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistDivisorLocalization
open CategoryTheory FrobeniusLiftDifference
open DeligneIllusieLocalContinuationRelativeLiftLocalization
universe u v w z

section ActualLocalization
variable {C : Type*} {S : Type*} [CommRing C] [CommRing S] [Algebra C S]

/-- Honest smoothness of the ACTUAL original lifting model passes to its principal localization. -/
theorem localizedModel_formallySmooth [Algebra.FormallySmooth C S] (s : S) :
    Algebra.FormallySmooth C (Localization.Away s) := by
  let : Algebra.FormallySmooth S (Localization.Away s) :=
    Algebra.FormallySmooth.of_isLocalization (Submonoid.powers s)
  exact Algebra.FormallySmooth.comp C S (Localization.Away s)

private theorem localize_divisor (p : ℕ) (s x : S) (η : KaehlerDifferential C S)
    (hη : (p : S) • η = KaehlerDifferential.D C S x) :
    (p : Localization.Away s) •
        KaehlerDifferential.map C C S (Localization.Away s) η =
      KaehlerDifferential.D C (Localization.Away s) (algebraMap S (Localization.Away s) x) := by
  have h := congrArg (KaehlerDifferential.map C C S (Localization.Away s)) hη
  rw [map_smul, KaehlerDifferential.map_D] at h
  calc
    _ = (algebraMap S (Localization.Away s) (p : S)) •
        KaehlerDifferential.map C C S (Localization.Away s) η := by rw [map_natCast]
    _ = (p : S) • KaehlerDifferential.map C C S (Localization.Away s) η :=
      IsScalarTower.algebraMap_smul (Localization.Away s) (p : S) _
    _ = _ := h
end ActualLocalization

variable {K B : Type u} [Field K] [CommRing B] [Algebra K B]
  {C : Type v} {R : Type w} {S : Type z}
  [CommRing C] [CommRing R] [CommRing S] [Algebra C K] [Algebra C R] [Algebra C S]
  (p : ℕ) [Fact p.Prime] [CharP K p]
attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra
private abbrev coefficientCAlgebra : Algebra C (RelativeFrobenius.twist (algebraMap K B) p) :=
  ((RelativeFrobenius.coefficientMap (algebraMap K B) p).hom.comp (algebraMap C K)).toAlgebra
attribute [local instance] coefficientCAlgebra
private instance coefficientTower : IsScalarTower C K (RelativeFrobenius.twist (algebraMap K B) p) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
private abbrev residueCAlgebra : Algebra C B :=
  ((algebraMap K B).comp (algebraMap C K)).toAlgebra
private theorem residueCoefficientTower :
    letI : Algebra C B := residueCAlgebra (C := C) (K := K) (B := B)
    IsScalarTower C K B := by
  let : Algebra C B := residueCAlgebra (C := C) (K := K) (B := B)
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

variable [Algebra R (RelativeFrobenius.twist (algebraMap K B) p)]
  [IsScalarTower C R (RelativeFrobenius.twist (algebraMap K B) p)]
  (c : Reduction p C K) (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p))
  (b : FlatReduction p S B) (F : R →ₐ[C] S)
  (hF : b.map.comp F.toRingHom =
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)
  (ha : algebraMap R (RelativeFrobenius.twist (algebraMap K B) p) = a.map)
  (hc : algebraMap C K = c.map)

include hF ha in
private theorem target_base (x : C) :
    b.map (algebraMap C S x) = algebraMap K B (algebraMap C K x) := by
  rw [← F.commutes x]
  have h := RingHom.congr_fun hF (algebraMap C R x)
  change b.map (F (algebraMap C R x)) =
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom
      (a.map (algebraMap C R x)) at h
  rw [h, ← ha, ← IsScalarTower.algebraMap_apply C R (RelativeFrobenius.twist (algebraMap K B) p)]
  exact congrArg (fun h : CommRingCat.of K ⟶ CommRingCat.of B => h.hom (algebraMap C K x))
    (SchemeRelativeFrobeniusAffineMap.coefficient_ringMap (algebraMap K B) p)

include c a b hF ha hc

/-- Actual individual divisors for geometric beta, INCLUDING zero B, with NO incoming divisor. -/
theorem exists_native_divisor (x : R) :
    ∃ η : KaehlerDifferential C S, (p : S) • η = KaehlerDifferential.D C S (F x) := by
  let : Algebra C B := residueCAlgebra (C := C) (K := K) (B := B)
  let : IsScalarTower C K B := residueCoefficientTower (C := C) (K := K) (B := B)
  let : Algebra S B := b.map.toAlgebra
  let : IsScalarTower C S B := IsScalarTower.of_algebraMap_eq
    (fun y => (target_base p (a := a) (b := b) (F := F) hF ha y).symm)
  apply (DeligneIllusieLocalContinuationReductionPushout.cotangent_reduction_eq_zero_iff
    c b.toReduction hc rfl (KaehlerDifferential.D C S (F x))).mp
  change KaehlerDifferential.map C K S B (KaehlerDifferential.D C S (F x)) = 0
  rw [KaehlerDifferential.map_D]
  change KaehlerDifferential.D K B (b.map (F x)) = 0
  have hx := RingHom.congr_fun hF x
  change b.map (F x) =
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom (a.map x) at hx
  rw [hx]
  exact SchemeRelativeFrobeniusAffineMap.D_ringMap_eq_zero p (a.map x)

/-- A genuine ORIGINAL divisor and its ACTUAL cotangent image divide the same localized lift. -/
theorem exists_compatible_localized_divisor (r x : R) :
    ∃ η : KaehlerDifferential C S,
      (p : S) • η = KaehlerDifferential.D C S (F x) ∧
      (p : Localization.Away (F r)) •
          KaehlerDifferential.map C C S (Localization.Away (F r)) η =
        KaehlerDifferential.D C (Localization.Away (F r))
          (localizedLift F r (algebraMap R (Localization.Away r) x)) := by
  obtain ⟨η, hη⟩ := exists_native_divisor p c a b F hF ha hc x
  refine ⟨η, hη, ?_⟩
  have hn := RingHom.congr_fun (localizedLift_triangle F r) x
  change localizedLift F r (algebraMap R (Localization.Away r) x) =
    algebraMap S (Localization.Away (F r)) (F x) at hn
  exact (localize_divisor p (F r) (F x) η hη).trans
    (congrArg (KaehlerDifferential.D C (Localization.Away (F r))) hn.symm)
end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistDivisorLocalization
