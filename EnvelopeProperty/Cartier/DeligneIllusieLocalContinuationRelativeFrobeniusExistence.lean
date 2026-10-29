import EnvelopeProperty.Cartier.FrobeniusLiftDifference
import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineCoefficient
import Mathlib.RingTheory.Smooth.Basic

/-! # Constructing a genuine relative Frobenius lift from the actual smooth source model -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationRelativeFrobeniusExistence
open CategoryTheory FrobeniusLiftDifference
universe u v w z
variable {C : Type v} {K B : Type u} {R : Type w} {S : Type z}
  [CommRing C] [Field K] [CommRing B] [CommRing R] [CommRing S]
  [Algebra C K] [Algebra K B] [Algebra C R] [Algebra C S] [Algebra S B] [Algebra C B]
  [IsScalarTower C K B] [IsScalarTower C S B]
variable (p : ℕ) [Fact p.Prime] [CharP K p]

private abbrev twistCAlgebra : Algebra C (RelativeFrobenius.twist (algebraMap K B) p) :=
  ((RelativeFrobenius.coefficientMap (algebraMap K B) p).hom.comp (algebraMap C K)).toAlgebra
attribute [local instance] twistCAlgebra

omit [Algebra S B] [Fact p.Prime] in
private theorem reduction_kernel_nilpotent (b : FlatReduction p S B) :
    IsNilpotent (RingHom.ker b.map) := by
  refine ⟨2, ?_⟩
  change (RingHom.ker b.map)^2 = ⊥
  rw [pow_two]
  apply le_antisymm ?_ bot_le
  apply Ideal.mul_le.mpr
  intro x hx y hy
  change b.map x = 0 at hx
  change b.map y = 0 at hy
  change x*y = 0
  obtain ⟨r, hr⟩ := (b.kernel_iff x).mp hx
  obtain ⟨s, hs⟩ := (b.kernel_iff y).mp hy
  rw [← hr, ← hs]
  calc
    (p : S)*r*((p : S)*s) = ((p : S)*(p : S))*(r*s) := by ring
    _ = 0 := by rw [b.p_sq_zero, zero_mul]

variable [Algebra R (RelativeFrobenius.twist (algebraMap K B) p)]
  [IsScalarTower C R (RelativeFrobenius.twist (algebraMap K B) p)]
  (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p)) (b : FlatReduction p S B)
  (ha : algebraMap R (RelativeFrobenius.twist (algebraMap K B) p) = a.map) (hb : algebraMap S B = b.map)

private def residueAlgHom : R →ₐ[C] B where
  __ := (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map
  commutes' c := by
    change (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom (a.map (algebraMap C R c)) = algebraMap C B c
    rw [← ha, ← IsScalarTower.algebraMap_apply C R (RelativeFrobenius.twist (algebraMap K B) p)]
    change (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom ((RelativeFrobenius.coefficientMap (algebraMap K B) p).hom
      (algebraMap C K c)) = algebraMap C B c
    exact (congrArg (fun h : CommRingCat.of K ⟶ CommRingCat.of B => h.hom (algebraMap C K c))
      (SchemeRelativeFrobeniusAffineMap.coefficient_ringMap (algebraMap K B) p)).trans
        (IsScalarTower.algebraMap_apply C K B c).symm

omit [Fact p.Prime] in
private theorem reduction_surjective (b : FlatReduction p S B) (hb : algebraMap S B = b.map) : Function.Surjective (IsScalarTower.toAlgHom C S B) := by
  change Function.Surjective (algebraMap S B)
  rw [hb]
  exact b.surjective

omit [Fact p.Prime] in
private theorem reduction_nilpotent (b : FlatReduction p S B) (hb : algebraMap S B = b.map) :
    IsNilpotent (RingHom.ker (IsScalarTower.toAlgHom C S B).toRingHom) := by
  change IsNilpotent (RingHom.ker (algebraMap S B))
  rw [hb]
  exact reduction_kernel_nilpotent p b

variable [Algebra.FormallySmooth C R]

/-- An ACTUAL C-algebra lift of the SAME geometric relative Frobenius; no supplied lift witness. -/
def relativeLift : R →ₐ[C] S :=
  Algebra.FormallySmooth.liftOfSurjective (residueAlgHom (C := C) (K := K) p a ha)
    (IsScalarTower.toAlgHom C S B) (reduction_surjective (C := C) p b hb)
    (reduction_nilpotent (C := C) p b hb)

/-- The ENTIRE original reduction triangle is derived from genuine infinitesimal lifting. -/
theorem relativeLift_reduction :
    b.map.comp (relativeLift (C := C) (K := K) p a b ha hb).toRingHom = (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map := by
  ext r
  have h := Algebra.FormallySmooth.liftOfSurjective_apply
    (residueAlgHom (C := C) (K := K) p a ha) (IsScalarTower.toAlgHom C S B)
    (reduction_surjective (C := C) p b hb) (reduction_nilpotent (C := C) p b hb) r
  change algebraMap S B (relativeLift (C := C) (K := K) p a b ha hb r) = (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom (a.map r) at h
  change b.map (relativeLift (C := C) (K := K) p a b ha hb r) =
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom (a.map r)
  rw [← hb]
  exact h

/-- Every original base coefficient is preserved by the constructed actual algebra map. -/
theorem relativeLift_base (c : C) :
    relativeLift (C := C) (K := K) p a b ha hb (algebraMap C R c) = algebraMap C S c :=
  (relativeLift (C := C) (K := K) p a b ha hb).commutes c

/-- In the native characteristic branch this is EXACTLY the old individual xi input, now constructed. -/
theorem relativeLift_reduction_native [CharP B p] (r : R) :
    b.map (relativeLift (C := C) (K := K) p a b ha hb r) =
      (RelativeFrobenius.map (algebraMap K B) p).hom (a.map r) := by
  have h := RingHom.congr_fun (relativeLift_reduction (C := C) (K := K) p a b ha hb) r
  change b.map (relativeLift (C := C) (K := K) p a b ha hb r) = (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom (a.map r) at h
  rw [SchemeRelativeFrobeniusAffineMap.ringMap_eq_native] at h
  exact h

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationRelativeFrobeniusExistence
