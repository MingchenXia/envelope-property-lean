import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationFlatReductionLocalization
import EnvelopeProperty.Cartier.RelativeCartierContinuationTwistPrincipalLocalization

/-! # Actual localized source models reducing to the SAME native localized twist -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistSourceLocalization
open CategoryTheory FrobeniusLiftDifference
open DeligneIllusieLocalContinuationFlatReductionLocalization
universe u v w
/-- Genuine transport of a proved p-kernel reduction through an actual ring equivalence. -/
private def transportReduction {D : Type*} {A : Type*} {A' : Type*}
    [CommRing D] [CommRing A] [CommRing A'] {p : ℕ}
    (a : Reduction p D A) (e : A ≃+* A') : Reduction p D A' where
  map := e.toRingHom.comp a.map
  surjective := e.surjective.comp a.surjective
  kernel_iff x := by
    constructor
    · intro hx
      apply (a.kernel_iff x).mp
      apply e.injective
      exact hx.trans e.map_zero.symm
    · intro hx
      change e (a.map x) = 0
      rw [(a.kernel_iff x).mpr hx, map_zero]

variable {K B : Type u} [Field K] [CommRing B] [Algebra K B]
  (p : ℕ) [Fact p.Prime] [CharP K p]
local notation "T" => RelativeFrobenius.twist (algebraMap K B) p
local notation "β" => CommRingCat.Hom.hom (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p)
local notation "Bₗ" t => Localization.Away (β t)
local notation "αₗ" t => RingHom.comp (algebraMap B (Bₗ t)) (algebraMap K B)
local notation "Tₗ" t => RelativeFrobenius.twist (αₗ t) p
local notation "τ" t => CommRingCat.Hom.hom
  (RelativeEtaleBaseChange.twistMap (algebraMap K B) (algebraMap B (Bₗ t)) p)

private def principalEquiv (t : T) : (Tₗ t) ≃+* Localization.Away t :=
  (RelativeTwistPrincipalLocalization.principalIso (algebraMap K B) p t).commRingCatIsoToRingEquiv

#check @transportReduction
#check @principalEquiv

variable {R : Type v} [CommRing R]
  (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p))

/-- GENUINE actual source reduction into native T_(B[1/beta(a r)]), with exact p-kernel. -/
def sourceReduction (r : R) : Reduction p (Localization.Away r) (Tₗ (a.map r)) :=
  transportReduction (D := Localization.Away r) (A := Localization.Away (a.map r))
    (A' := (Tₗ (a.map r))) (awayReduction a r)
    (principalEquiv (K := K) (B := B) p (a.map r)).symm

/-- ENTIRE source numerator triangle uses exactly ORIGINAL native twist map τ. -/
theorem sourceReduction_numerator (r : R) :
    (sourceReduction p a r).map.comp (algebraMap R (Localization.Away r)) =
      (τ (a.map r)).comp a.map := by
  ext x
  apply (principalEquiv (K := K) (B := B) p (a.map r)).injective
  change (principalEquiv (K := K) (B := B) p (a.map r))
      ((principalEquiv (K := K) (B := B) p (a.map r)).symm
        ((awayReduction a r).map (algebraMap R (Localization.Away r) x))) =
    (principalEquiv (K := K) (B := B) p (a.map r)) ((τ (a.map r)) (a.map x))
  rw [RingEquiv.apply_symm_apply]
  have hL := RingHom.congr_fun (awayReduction_triangle a r) x
  have hτ := congrArg (fun h : T ⟶ CommRingCat.of (Localization.Away (a.map r)) => h.hom (a.map x))
    (RelativeTwistPrincipalLocalization.principalIso_twistMap (algebraMap K B) p (a.map r))
  exact hL.trans hτ.symm

variable {C : Type w} [CommRing C] [Algebra C K] [Algebra C R]
private abbrev coefficientCAlgebra : Algebra C T :=
  ((RelativeFrobenius.coefficientMap (algebraMap K B) p).hom.comp (algebraMap C K)).toAlgebra
attribute [local instance] coefficientCAlgebra
variable [Algebra R (RelativeFrobenius.twist (algebraMap K B) p)]
  [hCRT : IsScalarTower C R (RelativeFrobenius.twist (algebraMap K B) p)]
  (ha : algebraMap R (RelativeFrobenius.twist (algebraMap K B) p) = a.map)
include ha hCRT

/-- ENTIRE actual coefficient triangle is DERIVED from original source and twist triangles. -/
theorem sourceReduction_coefficient (r : R) :
    (sourceReduction p a r).map.comp (algebraMap C (Localization.Away r)) =
      (RelativeFrobenius.coefficientMap (αₗ (a.map r)) p).hom.comp (algebraMap C K) := by
  ext x
  change (sourceReduction p a r).map
      (algebraMap R (Localization.Away r) (algebraMap C R x)) = _
  have h := RingHom.congr_fun (sourceReduction_numerator p a r) (algebraMap C R x)
  change (sourceReduction p a r).map
      (algebraMap R (Localization.Away r) (algebraMap C R x)) =
    (τ (a.map r)) (a.map (algebraMap C R x)) at h
  have hbase : a.map (algebraMap C R x) =
      (RelativeFrobenius.coefficientMap (algebraMap K B) p).hom (algebraMap C K x) := by
    rw [← ha, ← IsScalarTower.algebraMap_apply C R T]
    rfl
  have hcoeff := congrArg (fun h : CommRingCat.of K ⟶ (Tₗ (a.map r)) => h.hom (algebraMap C K x))
    (RelativeEtaleBaseChange.coefficientMap_twistMap (algebraMap K B)
      (algebraMap B (Bₗ (a.map r))) p)
  exact h.trans ((congrArg (τ (a.map r)) hbase).trans hcoeff)

/-- Original C coefficients and ACTUAL localized reduction give a genuine native scalar tower. -/
theorem sourceTower (r : R) :
    letI : Algebra C (Tₗ (a.map r)) :=
      ((RelativeFrobenius.coefficientMap (αₗ (a.map r)) p).hom.comp (algebraMap C K)).toAlgebra
    letI : Algebra (Localization.Away r) (Tₗ (a.map r)) := (sourceReduction p a r).map.toAlgebra
    IsScalarTower C (Localization.Away r) (Tₗ (a.map r)) := by
  let : Algebra C (Tₗ (a.map r)) :=
    ((RelativeFrobenius.coefficientMap (αₗ (a.map r)) p).hom.comp (algebraMap C K)).toAlgebra
  let : Algebra (Localization.Away r) (Tₗ (a.map r)) := (sourceReduction p a r).map.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun x =>
    (RingHom.congr_fun (sourceReduction_coefficient p a ha r) x).symm)
end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistSourceLocalization
