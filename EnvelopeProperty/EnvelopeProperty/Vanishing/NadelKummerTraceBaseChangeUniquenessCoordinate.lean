import EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniquenessCanonical

/-! # Invariance under actual coefficient-preserving coordinate automorphisms

The top-form map is the exterior map of the original Kähler algebra
morphism.  Its compatibility with the actual finite counit is proved
from intrinsic trace, not assumed as a canonical comparison certificate.
-/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniqueness

open CategoryTheory ModuleCat CanonicalGeometry NadelKummerCanonicalTrace
open NadelKummerCanonicalBaseChange

section NativeMaps
variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]

/-- The actual native Kähler morphism of an original algebra homomorphism. -/
def algebraDifferentialMap (f : A →ₐ[K] B) :
    KaehlerDifferential K A →ₛₗ[f.toRingHom] KaehlerDifferential K B := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  exact kaehlerSemilinear

/-- The native algebra Kähler morphism retains every actual differential. -/
theorem algebraDifferentialMap_D (f : A →ₐ[K] B) (b : A) :
    algebraDifferentialMap f (KaehlerDifferential.D K A b) = KaehlerDifferential.D K B (f b) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  exact kaehlerSemilinear_D b

/-- The genuine exterior map of the actual original algebra Kähler morphism. -/
def algebraExteriorMap (f : A →ₐ[K] B) (n : ℕ) :
    (⋀[A]^n (KaehlerDifferential K A)) →ₛₗ[f.toRingHom]
      (⋀[B]^n (KaehlerDifferential K B)) :=
  exteriorSemilinearMap f.toRingHom (algebraDifferentialMap f) n

/-- The genuine exterior algebra map preserves the whole actual differential wedge. -/
theorem algebraExteriorMap_differential_wedge (f : A →ₐ[K] B) (n : ℕ) (x : Fin n → A) :
    algebraExteriorMap f n (exteriorPower.ιMulti A n (fun j => KaehlerDifferential.D K A (x j))) =
      exteriorPower.ιMulti B n (fun j => KaehlerDifferential.D K B (f (x j))) := by
  rw [algebraExteriorMap, exteriorSemilinearMap_ιMulti]
  congr 1
  funext j
  exact algebraDifferentialMap_D f (x j)

end NativeMaps

section Coefficient
variable (R : Type u) [CommRing R] [Nontrivial R] {n : ℕ} (d : Fin n → ℕ)
    (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)

/-- The genuine native top-form map of an actual automorphism fixing the coefficient ring. -/
def coordinateExteriorMap
    (e : letI : Algebra S (powerBaseChangeRing R d S a) := (powerBaseChangeLeft R d S a).toAlgebra
      powerBaseChangeRing R d S a ≃ₐ[S] powerBaseChangeRing R d S a) :
    letI : Algebra S (powerBaseChangeRing R d S a) := (powerBaseChangeLeft R d S a).toAlgebra
    targetCanonicalModule R d S a →ₛₗ[e.toRingEquiv.toRingHom] targetCanonicalModule R d S a := by
  let := baseRAlgebra R S a
  let := targetRAlgebra R d S a
  let : Algebra S (powerBaseChangeRing R d S a) := (powerBaseChangeLeft R d S a).toAlgebra
  let : IsScalarTower R S (powerBaseChangeRing R d S a) :=
    IsScalarTower.of_algebraMap_eq' (smallCoefficient_square R d S a).symm
  exact algebraExteriorMap (e.toAlgHom.restrictScalars R) n

/-- The same genuine coordinate exterior map is linear over the actual fixed coefficient ring. -/
def coordinateExteriorMorphism
    (e : letI : Algebra S (powerBaseChangeRing R d S a) := (powerBaseChangeLeft R d S a).toAlgebra
      powerBaseChangeRing R d S a ≃ₐ[S] powerBaseChangeRing R d S a) :
    (restrictScalars (powerBaseChangeLeft R d S a)).obj
        (ModuleCat.of (powerBaseChangeRing R d S a) (targetCanonicalModule R d S a)) ⟶
      (restrictScalars (powerBaseChangeLeft R d S a)).obj
        (ModuleCat.of (powerBaseChangeRing R d S a) (targetCanonicalModule R d S a)) := by
  let : Algebra S (powerBaseChangeRing R d S a) := (powerBaseChangeLeft R d S a).toAlgebra
  exact ModuleCat.ofHom
    (X := (restrictScalars (powerBaseChangeLeft R d S a)).obj
      (ModuleCat.of (powerBaseChangeRing R d S a) (targetCanonicalModule R d S a)))
    (Y := (restrictScalars (powerBaseChangeLeft R d S a)).obj
      (ModuleCat.of (powerBaseChangeRing R d S a) (targetCanonicalModule R d S a)))
    { toFun := fun w => coordinateExteriorMap R d S a e w
      map_add' := map_add (coordinateExteriorMap R d S a e)
      map_smul' s w := by
        change coordinateExteriorMap R d S a e (powerBaseChangeLeft R d S a s •
          (show targetCanonicalModule R d S a from w)) =
            powerBaseChangeLeft R d S a s • coordinateExteriorMap R d S a e w
        rw [(coordinateExteriorMap R d S a e).map_smulₛₗ]
        exact congrArg (fun z => z • coordinateExteriorMap R d S a e w) (e.commutes s) }

omit [Nontrivial R] in
/-- The whole intrinsic native trace is unchanged by an actual coefficient-preserving automorphism. -/
theorem baseChangeTrace_coordinate
    (e : letI : Algebra S (powerBaseChangeRing R d S a) := (powerBaseChangeLeft R d S a).toAlgebra
      powerBaseChangeRing R d S a ≃ₐ[S] powerBaseChangeRing R d S a)
    (c : powerBaseChangeRing R d S a) :
    baseChangeTrace R d S a (e c) = baseChangeTrace R d S a c := by
  let : Algebra S (powerBaseChangeRing R d S a) := (powerBaseChangeLeft R d S a).toAlgebra
  exact Algebra.trace_eq_of_algEquiv e c

omit [Nontrivial R] in
/-- Every actual coefficient-preserving coordinate automorphism fixes the genuine pulled base wedge. -/
theorem coordinateExteriorMap_pulled_generator (ha : a.FormallyEtale)
    (e : letI : Algebra S (powerBaseChangeRing R d S a) := (powerBaseChangeLeft R d S a).toAlgebra
      powerBaseChangeRing R d S a ≃ₐ[S] powerBaseChangeRing R d S a) :
    coordinateExteriorMap R d S a e
        (canonicalPullback R d S a (baseCanonicalGenerator R S a ha)) =
      canonicalPullback R d S a (baseCanonicalGenerator R S a ha) := by
  let := baseRAlgebra R S a
  let := targetRAlgebra R d S a
  let : Algebra S (powerBaseChangeRing R d S a) := (powerBaseChangeLeft R d S a).toAlgebra
  let : IsScalarTower R S (powerBaseChangeRing R d S a) :=
    IsScalarTower.of_algebraMap_eq' (smallCoefficient_square R d S a).symm
  have hg : canonicalPullback R d S a (baseCanonicalGenerator R S a ha) =
      exteriorPower.ιMulti (powerBaseChangeRing R d S a) n
        (fun j => KaehlerDifferential.D R (powerBaseChangeRing R d S a)
          (powerBaseChangeLeft R d S a (a (MvPolynomial.X j)))) := by
    rw [baseCanonicalGenerator_eq_wedge, canonicalPullback, exteriorSemilinearMap_ιMulti]
    congr 1
    funext j
    exact canonicalDifferentialPullback_D R d S a (a (MvPolynomial.X j))
  rw [hg]
  calc
    _ = exteriorPower.ιMulti (powerBaseChangeRing R d S a) n
        (fun j => KaehlerDifferential.D R (powerBaseChangeRing R d S a)
          (e (powerBaseChangeLeft R d S a (a (MvPolynomial.X j))))) :=
      algebraExteriorMap_differential_wedge (e.toAlgHom.restrictScalars R) n
        (fun j => powerBaseChangeLeft R d S a (a (MvPolynomial.X j)))
    _ = _ := by
      congr 1
      funext j
      exact congrArg (KaehlerDifferential.D R (powerBaseChangeRing R d S a))
        (e.commutes (a (MvPolynomial.X j)))

omit [Nontrivial R] in
/-- The genuine coordinate map fixes the actual pullback of every actual base top form. -/
theorem coordinateExteriorMap_pulled_topform (ha : a.FormallyEtale)
    (e : letI : Algebra S (powerBaseChangeRing R d S a) := (powerBaseChangeLeft R d S a).toAlgebra
      powerBaseChangeRing R d S a ≃ₐ[S] powerBaseChangeRing R d S a)
    (w : baseCanonicalModule R S a) :
    coordinateExteriorMap R d S a e (canonicalPullback R d S a w) = canonicalPullback R d S a w := by
  let : Algebra S (powerBaseChangeRing R d S a) := (powerBaseChangeLeft R d S a).toAlgebra
  let s := baseCanonicalTrivialization R S a ha w
  have hw : w = s • baseCanonicalGenerator R S a ha := by
    rw [← baseCanonicalTrivialization_symm]
    exact ((baseCanonicalTrivialization R S a ha).symm_apply_apply w).symm
  rw [hw, (canonicalPullback R d S a).map_smulₛₗ,
    (coordinateExteriorMap R d S a e).map_smulₛₗ, coordinateExteriorMap_pulled_generator]
  exact congrArg (fun z => z • canonicalPullback R d S a (baseCanonicalGenerator R S a ha))
    (e.commutes s)

end Coefficient

section Domain
variable (R : Type u) [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (d : Fin n → ℕ)
    (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)

/-- Intrinsic normalization proves whole counit invariance under every actual coefficient-preserving automorphism. -/
theorem canonicalCounit_coordinate (hflat : a.Flat) (ha : a.FormallyEtale)
    (e : letI : Algebra S (powerBaseChangeRing R d S a) := (powerBaseChangeLeft R d S a).toAlgebra
      powerBaseChangeRing R d S a ≃ₐ[S] powerBaseChangeRing R d S a) :
    coordinateExteriorMorphism R d S a e ≫ etaleCanonicalCounit R d S a ha =
      etaleCanonicalCounit R d S a ha := by
  let : Algebra S (powerBaseChangeRing R d S a) := (powerBaseChangeLeft R d S a).toAlgebra
  apply canonicalCounit_eq_of_topforms R d S a hflat ha
  intro c w
  change etaleCanonicalCounit R d S a ha
    (coordinateExteriorMap R d S a e (c • canonicalPullback R d S a w)) = _
  have he : coordinateExteriorMap R d S a e (c • canonicalPullback R d S a w) =
      e c • canonicalPullback R d S a w := by
    rw [(coordinateExteriorMap R d S a e).map_smulₛₗ,
      coordinateExteriorMap_pulled_topform R d S a ha e w]
    rfl
  exact (congrArg (fun v : targetCanonicalModule R d S a => etaleCanonicalCounit R d S a ha v) he).trans
    ((canonicalCounit_pulled_topform R d S a ha (e c) w).trans
      (congrArg (fun z => z • w) (baseChangeTrace_coordinate R d S a e c)))

end Domain
end EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniqueness
