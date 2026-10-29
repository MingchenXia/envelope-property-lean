import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistNativeSourceLocalization
import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationRelativeLiftLocalization

/-! # Genuine target flat models and the actual native localized Frobenius lift square -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistTargetLocalization
open CategoryTheory FrobeniusLiftDifference
open DeligneIllusieLocalContinuationFlatReductionLocalization
open DeligneIllusieLocalContinuationRelativeLiftLocalization
universe u v w z

private def transportFlatReduction {D : Type*} {A : Type*} {A' : Type*}
    [CommRing D] [CommRing A] [CommRing A'] {p : ℕ}
    (b : FlatReduction p D A) (e : A ≃+* A') : FlatReduction p D A' where
  map := e.toRingHom.comp b.map
  surjective := e.surjective.comp b.surjective
  kernel_iff x := by
    constructor
    · intro hx
      apply (b.kernel_iff x).mp
      apply e.injective
      exact hx.trans e.map_zero.symm
    · intro hx
      change e (b.map x) = 0
      rw [(b.kernel_iff x).mpr hx, map_zero]
  p_sq_zero := b.p_sq_zero
  flat x hx := by
    change e (b.map x) = 0
    rw [b.flat x hx, map_zero]

private def awayCast {A : Type*} [CommRing A] {s t : A} (h : s = t) :
    Localization.Away s ≃+* Localization.Away t :=
  RingEquiv.cast (R := fun x : A => Localization.Away x) h

private theorem awayCast_numerator {A : Type*} [CommRing A] {s t : A}
    (h : s = t) (x : A) :
    awayCast h (algebraMap A (Localization.Away s) x) =
      algebraMap A (Localization.Away t) x := by
  subst t
  rfl

variable {K B : Type u} [Field K] [CommRing B] [Algebra K B]
  (p : ℕ) [Fact p.Prime] [CharP K p]
local notation "T" => RelativeFrobenius.twist (algebraMap K B) p
local notation "β" => CommRingCat.Hom.hom (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p)
local notation "Bₗ" t => Localization.Away (β t)
local notation "Tₗ" t => RelativeFrobenius.twist (algebraMap K (Bₗ t)) p
local notation "βₗ" t => CommRingCat.Hom.hom
  (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K (Bₗ t)) p)
local notation "τ" t => CommRingCat.Hom.hom
  (RelativeEtaleCartierNaturality.twistMap (k := K) (A := B) (B := Bₗ t) p)

variable {R : Type v} {S : Type w} [CommRing R] [CommRing S]
  (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p))
  (b : FlatReduction p S B) (f : R →+* S)
  (hf : b.map.comp f =
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)

/-- Genuine flat reduction to the ORIGINAL native B localization; all fields are derived. -/
def targetReduction (r : R) : FlatReduction p (Localization.Away (f r)) (Bₗ (a.map r)) :=
  transportFlatReduction (D := Localization.Away (f r))
    (A := Localization.Away (b.map (f r))) (A' := Bₗ (a.map r))
    (awayFlatReduction b (f r)) (awayCast (RingHom.congr_fun hf r))

/-- ENTIRE original target numerator triangle, with no supplied localized comparison. -/
theorem targetReduction_numerator (r : R) :
    (targetReduction p a b f hf r).map.comp (algebraMap S (Localization.Away (f r))) =
      (algebraMap B (Bₗ (a.map r))).comp b.map := by
  ext x
  change awayCast (RingHom.congr_fun hf r)
      ((awayFlatReduction b (f r)).map (algebraMap S (Localization.Away (f r)) x)) = _
  have h := RingHom.congr_fun (awayReduction_triangle b.toReduction (f r)) x
  change (awayFlatReduction b (f r)).map (algebraMap S (Localization.Away (f r)) x) =
    algebraMap B (Localization.Away (b.map (f r))) (b.map x) at h
  rw [h]
  exact awayCast_numerator (RingHom.congr_fun hf r) (b.map x)

private theorem nativeGeometricSquare (t : T) :
    (βₗ t).comp (τ t) = (algebraMap B (Bₗ t)).comp β := by
  have he := congrArg CommRingCat.Hom.hom
    (RelativeGeometricTwistBaseChange.targetBaseIso_ringMap
      (k := K) (A := B) (B := Bₗ t) p)
  have hτ := congrArg CommRingCat.Hom.hom
    (RelativeGeometricTwistBaseChange.twistMap_targetBaseIso
      (k := K) (A := B) (B := Bₗ t) p)
  change (SchemeRelativeFrobeniusAffineMap.ringMap
      ((algebraMap B (Bₗ t)).comp (algebraMap K B)) p).hom.comp
      (RelativeGeometricTwistBaseChange.targetBaseIso
        (k := K) (A := B) (B := Bₗ t) p).hom.hom = βₗ t at he
  change (RelativeGeometricTwistBaseChange.targetBaseIso
      (k := K) (A := B) (B := Bₗ t) p).hom.hom.comp (τ t) =
    (RelativeEtaleBaseChange.twistMap (algebraMap K B) (algebraMap B (Bₗ t)) p).hom at hτ
  calc
    (βₗ t).comp (τ t) =
        ((SchemeRelativeFrobeniusAffineMap.ringMap
          ((algebraMap B (Bₗ t)).comp (algebraMap K B)) p).hom.comp
          (RelativeGeometricTwistBaseChange.targetBaseIso
            (k := K) (A := B) (B := Bₗ t) p).hom.hom).comp (τ t) := by rw [he]
    _ = (SchemeRelativeFrobeniusAffineMap.ringMap
          ((algebraMap B (Bₗ t)).comp (algebraMap K B)) p).hom.comp
        (RelativeEtaleBaseChange.twistMap (algebraMap K B) (algebraMap B (Bₗ t)) p).hom := by
      rw [RingHom.comp_assoc, hτ]
    _ = (algebraMap B (Bₗ t)).comp β :=
      RelativeGeometricTwistBaseChange.geometricCoefficientSquare p
        (algebraMap K B) (algebraMap B (Bₗ t))

section AlgebraLift
variable {C : Type z} [CommRing C] [Algebra C R] [Algebra C S]
  (F : R →ₐ[C] S)
  (hF : b.map.comp F.toRingHom =
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)

/-- The ACTUAL localized C-algebra lift reduces through the SAME actual native geometric beta. -/
theorem localizedLift_reduction (r : R) :
    (targetReduction p a b F.toRingHom hF r).map.comp (localizedLift F r).toRingHom =
      (βₗ (a.map r)).comp
        (DeligneIllusieLocalContinuationTrueTwistNativeSourceLocalization.sourceReduction p a r).map := by
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext x
  change (targetReduction p a b F.toRingHom hF r).map
      (localizedLift F r (algebraMap R (Localization.Away r) x)) =
    (βₗ (a.map r))
      ((DeligneIllusieLocalContinuationTrueTwistNativeSourceLocalization.sourceReduction p a r).map
        (algebraMap R (Localization.Away r) x))
  have hL := RingHom.congr_fun (localizedLift_triangle F r) x
  change localizedLift F r (algebraMap R (Localization.Away r) x) =
    algebraMap S (Localization.Away (F r)) (F x) at hL
  have hB := RingHom.congr_fun (targetReduction_numerator p a b F.toRingHom hF r) (F x)
  change (targetReduction p a b F.toRingHom hF r).map
      (algebraMap S (Localization.Away (F r)) (F x)) =
    algebraMap B (Bₗ (a.map r)) (b.map (F x)) at hB
  have hA := RingHom.congr_fun
    (DeligneIllusieLocalContinuationTrueTwistNativeSourceLocalization.sourceReduction_numerator p a r) x
  change (DeligneIllusieLocalContinuationTrueTwistNativeSourceLocalization.sourceReduction p a r).map
      (algebraMap R (Localization.Away r) x) = (τ (a.map r)) (a.map x) at hA
  rw [hL, hB, hA]
  exact (congrArg (algebraMap B (Bₗ (a.map r))) (RingHom.congr_fun hF x)).trans
    (RingHom.congr_fun (nativeGeometricSquare (K := K) (B := B) p (a.map r)) (a.map x)).symm

variable [Algebra C B] [Algebra S B] [hCSB : IsScalarTower C S B]
  (hb : algebraMap S B = b.map)
include hb hCSB

/-- ENTIRE original target C-coefficient triangle is derived from the actual original tower. -/
theorem targetReduction_coefficient (r : R) :
    (targetReduction p a b F.toRingHom hF r).map.comp (algebraMap C (Localization.Away (F r))) =
      (algebraMap B (Bₗ (a.map r))).comp (algebraMap C B) := by
  ext x
  change (targetReduction p a b F.toRingHom hF r).map
      (algebraMap S (Localization.Away (F r)) (algebraMap C S x)) = _
  have h := RingHom.congr_fun (targetReduction_numerator p a b F.toRingHom hF r)
    (algebraMap C S x)
  change (targetReduction p a b F.toRingHom hF r).map
      (algebraMap S (Localization.Away (F r)) (algebraMap C S x)) =
    algebraMap B (Bₗ (a.map r)) (b.map (algebraMap C S x)) at h
  exact h.trans (congrArg (algebraMap B (Bₗ (a.map r))) (by
    rw [← hb, ← IsScalarTower.algebraMap_apply C S B]
    rfl))
end AlgebraLift
end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistTargetLocalization
