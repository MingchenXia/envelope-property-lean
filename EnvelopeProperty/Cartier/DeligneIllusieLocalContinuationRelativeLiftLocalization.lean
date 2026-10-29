import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationFlatReductionLocalization
import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationRelativeFrobeniusExistence

/-! # Actual principal localizations of the genuinely constructed relative Frobenius lift -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationRelativeLiftLocalization
open CategoryTheory FrobeniusLiftDifference
open DeligneIllusieLocalContinuationFlatReductionLocalization
universe u v w z t

section Localization
variable {C : Type t} {R : Type u} {S : Type v} {A : Type w} {B : Type z}
  [CommRing C] [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra C R] [Algebra C S] {p : ℕ}

/-- The ACTUAL native C-algebra map on the original principal localizations. -/
def localizedLift (f : R →ₐ[C] S) (r : R) :
    Localization.Away r →ₐ[C] Localization.Away (f r) :=
  IsLocalization.Away.mapₐ (Localization.Away r) (Localization.Away (f r)) f r

/-- The ENTIRE original numerator triangle, with the original algebra maps. -/
theorem localizedLift_triangle (f : R →ₐ[C] S) (r : R) :
    (localizedLift f r).toRingHom.comp (algebraMap R (Localization.Away r)) =
      (algebraMap S (Localization.Away (f r))).comp f.toRingHom := by
  ext x
  change IsLocalization.Away.map (Localization.Away r) (Localization.Away (f r))
    f.toRingHom r (algebraMap R (Localization.Away r) x) =
      algebraMap S (Localization.Away (f r)) (f x)
  dsimp only [IsLocalization.Away.map]
  apply IsLocalization.map_eq

private theorem residue_powers (a : Reduction p R A) (b : FlatReduction p S B)
    (f : R →+* S) (β : A →+* B) (hf : b.map.comp f = β.comp a.map) (r : R) :
    Submonoid.powers (a.map r) ≤ (Submonoid.powers (b.map (f r))).comap β := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  have hr : b.map (f r) = β (a.map r) := RingHom.congr_fun hf r
  rw [hr]
  exact (map_pow β (a.map r) n).symm.trans (congrArg β hn)

/-- Matched residue denominators are DERIVED from the ORIGINAL whole square. -/
def localizedResidue (a : Reduction p R A) (b : FlatReduction p S B)
    (f : R →+* S) (β : A →+* B) (hf : b.map.comp f = β.comp a.map) (r : R) :
    Localization.Away (a.map r) →+* Localization.Away (b.map (f r)) :=
  IsLocalization.map (Localization.Away (b.map (f r))) β (residue_powers a b f β hf r)

/-- The ENTIRE localized square, using the genuinely derived actual localized flat reduction. -/
theorem localizedReduction_square (a : Reduction p R A) (b : FlatReduction p S B)
    (f : R →ₐ[C] S) (β : A →+* B) (hf : b.map.comp f.toRingHom = β.comp a.map) (r : R) :
    (awayFlatReduction b (f r)).map.comp (localizedLift f r).toRingHom =
      (localizedResidue a b f.toRingHom β hf r).comp (awayReduction a r).map := by
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext x
  change (awayFlatReduction b (f r)).map
      (localizedLift f r (algebraMap R (Localization.Away r) x)) =
    localizedResidue a b f.toRingHom β hf r
      ((awayReduction a r).map (algebraMap R (Localization.Away r) x))
  have hL := RingHom.congr_fun (localizedLift_triangle f r) x
  change localizedLift f r (algebraMap R (Localization.Away r) x) =
    algebraMap S (Localization.Away (f r)) (f x) at hL
  have hB := RingHom.congr_fun (awayReduction_triangle b.toReduction (f r)) (f x)
  change (awayFlatReduction b (f r)).map (algebraMap S (Localization.Away (f r)) (f x)) =
    algebraMap B (Localization.Away (b.map (f r))) (b.map (f x)) at hB
  have hA := RingHom.congr_fun (awayReduction_triangle a r) x
  change (awayReduction a r).map (algebraMap R (Localization.Away r) x) =
    algebraMap A (Localization.Away (a.map r)) (a.map x) at hA
  rw [hL, hB, hA]
  change algebraMap B (Localization.Away (b.map (f r))) (b.map (f x)) =
    IsLocalization.map (Localization.Away (b.map (f r))) β (residue_powers a b f.toRingHom β hf r)
      (algebraMap A (Localization.Away (a.map r)) (a.map x))
  rw [IsLocalization.map_eq]
  exact congrArg (algebraMap B (Localization.Away (b.map (f r)))) (RingHom.congr_fun hf x)
end Localization

section Constructed
variable {C : Type v} {K B : Type u} {R : Type w} {S : Type z}
  [CommRing C] [Field K] [CommRing B] [CommRing R] [CommRing S]
  [Algebra C K] [Algebra K B] [Algebra C R] [Algebra C S] [Algebra S B] [Algebra C B]
  [IsScalarTower C K B] [IsScalarTower C S B]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
private abbrev twistCAlgebra : Algebra C (RelativeFrobenius.twist (algebraMap K B) p) :=
  ((RelativeFrobenius.coefficientMap (algebraMap K B) p).hom.comp (algebraMap C K)).toAlgebra
attribute [local instance] twistCAlgebra
variable [Algebra R (RelativeFrobenius.twist (algebraMap K B) p)]
  [IsScalarTower C R (RelativeFrobenius.twist (algebraMap K B) p)]
  (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p)) (b : FlatReduction p S B)
  (ha : algebraMap R (RelativeFrobenius.twist (algebraMap K B) p) = a.map) (hb : algebraMap S B = b.map)
  [Algebra.FormallySmooth C R]
open DeligneIllusieLocalContinuationRelativeFrobeniusExistence

/-- The ACTUAL constructed relative lift localized at r and its ACTUAL image; no incoming lift. -/
def relativeLiftAway (r : R) : Localization.Away r →ₐ[C]
    Localization.Away (relativeLift (C := C) (K := K) p a b ha hb r) :=
  localizedLift (relativeLift (C := C) (K := K) p a b ha hb) r

/-- Both original and localized reduction squares are DERIVED for this constructed lift. -/
theorem relativeLiftAway_reduction (r : R) :
    (awayFlatReduction b (relativeLift (C := C) (K := K) p a b ha hb r)).map.comp
        (relativeLiftAway (C := C) (K := K) p a b ha hb r).toRingHom =
      (localizedResidue a b (relativeLift (C := C) (K := K) p a b ha hb).toRingHom
        (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom
        (relativeLift_reduction (C := C) (K := K) p a b ha hb) r).comp (awayReduction a r).map := by
  exact localizedReduction_square a b (relativeLift (C := C) (K := K) p a b ha hb)
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom
    (relativeLift_reduction (C := C) (K := K) p a b ha hb) r
end Constructed
end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationRelativeLiftLocalization
