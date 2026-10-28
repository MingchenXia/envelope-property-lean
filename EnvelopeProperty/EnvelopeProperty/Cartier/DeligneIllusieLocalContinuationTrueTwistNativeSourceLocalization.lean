import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistSourceLocalization
import EnvelopeProperty.Cartier.RelativeCartierContinuationGeometricTwistBaseChange

/-! # The actual native localized-twist source reduction and its original actions -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistNativeSourceLocalization
open CategoryTheory FrobeniusLiftDifference
universe u v w

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
local notation "Tₗ" t => RelativeFrobenius.twist (algebraMap K (Bₗ t)) p
local notation "Tcₗ" t => RelativeFrobenius.twist (RingHom.comp (algebraMap B (Bₗ t)) (algebraMap K B)) p
local notation "τ" t => CommRingCat.Hom.hom
  (RelativeEtaleCartierNaturality.twistMap (k := K) (A := B) (B := Bₗ t) p)

private def nativeBaseEquiv (t : T) : (Tₗ t) ≃+* (Tcₗ t) :=
  (RelativeGeometricTwistBaseChange.targetBaseIso (k := K) (A := B) (B := Bₗ t) p).commRingCatIsoToRingEquiv

variable {R : Type v} [CommRing R]
  (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p))

/-- Actual native localized source reduction, with derived surjectivity and exact p-kernel. -/
def sourceReduction (r : R) : Reduction p (Localization.Away r) (Tₗ (a.map r)) :=
  transportReduction (D := Localization.Away r) (A := Tcₗ (a.map r))
    (A' := Tₗ (a.map r))
    (DeligneIllusieLocalContinuationTrueTwistSourceLocalization.sourceReduction p a r)
    (nativeBaseEquiv (K := K) (B := B) p (a.map r)).symm

/-- Entire numerator triangle into the ORIGINAL native localization K-algebra twist. -/
theorem sourceReduction_numerator (r : R) :
    (sourceReduction p a r).map.comp (algebraMap R (Localization.Away r)) =
      (τ (a.map r)).comp a.map := by
  ext x
  apply (nativeBaseEquiv (K := K) (B := B) p (a.map r)).injective
  change (nativeBaseEquiv (K := K) (B := B) p (a.map r))
      ((nativeBaseEquiv (K := K) (B := B) p (a.map r)).symm
        ((DeligneIllusieLocalContinuationTrueTwistSourceLocalization.sourceReduction p a r).map
          (algebraMap R (Localization.Away r) x))) =
    (nativeBaseEquiv (K := K) (B := B) p (a.map r)) ((τ (a.map r)) (a.map x))
  rw [RingEquiv.apply_symm_apply]
  have hL := RingHom.congr_fun
    (DeligneIllusieLocalContinuationTrueTwistSourceLocalization.sourceReduction_numerator p a r) x
  have hτ := congrArg (fun h : T ⟶ (Tcₗ (a.map r)) => h.hom (a.map x))
    (RelativeGeometricTwistBaseChange.twistMap_targetBaseIso
      (k := K) (A := B) (B := Bₗ (a.map r)) p)
  exact hL.trans hτ.symm

variable {C : Type w} [CommRing C] [Algebra C K] [Algebra C R]
private abbrev coefficientCAlgebra : Algebra C T :=
  ((RelativeFrobenius.coefficientMap (algebraMap K B) p).hom.comp (algebraMap C K)).toAlgebra
attribute [local instance] coefficientCAlgebra
variable [Algebra R (RelativeFrobenius.twist (algebraMap K B) p)]
  [hCRT : IsScalarTower C R (RelativeFrobenius.twist (algebraMap K B) p)]
  (ha : algebraMap R (RelativeFrobenius.twist (algebraMap K B) p) = a.map)
include ha hCRT

/-- Original C coefficients agree with the ACTUAL native coefficient inclusion. -/
theorem sourceReduction_coefficient (r : R) :
    (sourceReduction p a r).map.comp (algebraMap C (Localization.Away r)) =
      (RelativeFrobenius.coefficientMap (algebraMap K (Bₗ (a.map r))) p).hom.comp
        (algebraMap C K) := by
  ext x
  apply (nativeBaseEquiv (K := K) (B := B) p (a.map r)).injective
  change (nativeBaseEquiv (K := K) (B := B) p (a.map r))
      ((nativeBaseEquiv (K := K) (B := B) p (a.map r)).symm
        ((DeligneIllusieLocalContinuationTrueTwistSourceLocalization.sourceReduction p a r).map
          (algebraMap C (Localization.Away r) x))) =
    (nativeBaseEquiv (K := K) (B := B) p (a.map r))
      ((RelativeFrobenius.coefficientMap (algebraMap K (Bₗ (a.map r))) p).hom (algebraMap C K x))
  rw [RingEquiv.apply_symm_apply]
  have hL := RingHom.congr_fun
    (DeligneIllusieLocalContinuationTrueTwistSourceLocalization.sourceReduction_coefficient p a ha r) x
  have hc := congrArg (fun h : CommRingCat.of K ⟶ (Tcₗ (a.map r)) => h.hom (algebraMap C K x))
    (RelativeGeometricTwistBaseChange.targetBaseIso_coefficient
      (k := K) (A := B) (B := Bₗ (a.map r)) p)
  exact hL.trans hc.symm

/-- Derived scalar tower uses the ACTUAL native coefficient action and ACTUAL reduction map. -/
theorem sourceTower (r : R) :
    letI : Algebra C (Tₗ (a.map r)) :=
      ((RelativeFrobenius.coefficientMap (algebraMap K (Bₗ (a.map r))) p).hom.comp
        (algebraMap C K)).toAlgebra
    letI : Algebra (Localization.Away r) (Tₗ (a.map r)) := (sourceReduction p a r).map.toAlgebra
    IsScalarTower C (Localization.Away r) (Tₗ (a.map r)) := by
  let : Algebra C (Tₗ (a.map r)) :=
    ((RelativeFrobenius.coefficientMap (algebraMap K (Bₗ (a.map r))) p).hom.comp
      (algebraMap C K)).toAlgebra
  let : Algebra (Localization.Away r) (Tₗ (a.map r)) := (sourceReduction p a r).map.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun x =>
    (RingHom.congr_fun (sourceReduction_coefficient p a ha r) x).symm)
end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistNativeSourceLocalization
