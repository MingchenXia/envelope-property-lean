import EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniqueness

/-! # Actual differential pullback and intrinsic normalization on all top forms

The pullback is built from the original Kähler map.  Normalization on all
actual base forms is proved from the actual counit; it is not an input
comparison between two coordinate constructions.
-/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniqueness

open CategoryTheory ModuleCat CanonicalGeometry NadelKummerCanonicalTrace
open NadelKummerCanonicalBaseChange NadelKummerTraceJacobian

section Coefficient
variable (R : Type u) [CommRing R] [Nontrivial R] {n : ℕ} (d : Fin n → ℕ)
    (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)

/-- The actual Kähler pullback through the original left tensor inclusion. -/
def canonicalDifferentialPullback :
    let _ := baseRAlgebra R S a
    let _ := targetRAlgebra R d S a
    KaehlerDifferential R S →ₛₗ[powerBaseChangeLeft R d S a]
      KaehlerDifferential R (powerBaseChangeRing R d S a) := by
  let := baseRAlgebra R S a
  let := targetRAlgebra R d S a
  let : Algebra S (powerBaseChangeRing R d S a) := (powerBaseChangeLeft R d S a).toAlgebra
  let : IsScalarTower R S (powerBaseChangeRing R d S a) :=
    IsScalarTower.of_algebraMap_eq' (smallCoefficient_square R d S a).symm
  exact kaehlerSemilinear

omit [Nontrivial R] in
/-- The actual differential pullback sends each original differential to its true image. -/
theorem canonicalDifferentialPullback_D (s : S) :
    let _ := baseRAlgebra R S a
    let _ := targetRAlgebra R d S a
    canonicalDifferentialPullback R d S a (KaehlerDifferential.D R S s) =
      KaehlerDifferential.D R (powerBaseChangeRing R d S a) (powerBaseChangeLeft R d S a s) := by
  let := baseRAlgebra R S a
  let := targetRAlgebra R d S a
  let : Algebra S (powerBaseChangeRing R d S a) := (powerBaseChangeLeft R d S a).toAlgebra
  let : IsScalarTower R S (powerBaseChangeRing R d S a) :=
    IsScalarTower.of_algebraMap_eq' (smallCoefficient_square R d S a).symm
  exact kaehlerSemilinear_D s

/-- The genuine native exterior pullback for the same actual tensor morphism. -/
def canonicalPullback :
    baseCanonicalModule R S a →ₛₗ[powerBaseChangeLeft R d S a] targetCanonicalModule R d S a := by
  let := baseRAlgebra R S a
  let := targetRAlgebra R d S a
  exact exteriorSemilinearMap (powerBaseChangeLeft R d S a)
    (canonicalDifferentialPullback R d S a) n

omit [Nontrivial R] in
/-- The actual differential pullback of the base generator is the original Jacobian wedge. -/
theorem canonicalPullback_generator (ha : a.FormallyEtale) :
    canonicalPullback R d S a (baseCanonicalGenerator R S a ha) =
      powerBaseChangeRight R d S a (jacobian R d) • targetCanonicalGenerator R d S a ha := by
  let := baseRAlgebra R S a
  let := targetRAlgebra R d S a
  have hD (b : PolynomialRing R n) :
      targetDifferentialMap R d S a (KaehlerDifferential.D R (PolynomialRing R n) b) =
        KaehlerDifferential.D R (powerBaseChangeRing R d S a) (powerBaseChangeRight R d S a b) := by
    let : Algebra (PolynomialRing R n) (powerBaseChangeRing R d S a) :=
      (powerBaseChangeRight R d S a).toAlgebra
    let : IsScalarTower R (PolynomialRing R n) (powerBaseChangeRing R d S a) :=
      IsScalarTower.of_algebraMap_eq' rfl
    exact kaehlerSemilinear_D b
  have he : canonicalPullback R d S a (baseCanonicalGenerator R S a ha) =
      targetExteriorMap R d S a
        (exteriorPower.ιMulti (PolynomialRing R n) n
          (fun j => KaehlerDifferential.D R (PolynomialRing R n) (powerMap R d (MvPolynomial.X j)))) := by
    rw [baseCanonicalGenerator_eq_wedge, canonicalPullback, exteriorSemilinearMap_ιMulti,
      targetExteriorMap, exteriorSemilinearMap_ιMulti]
    congr 1
    funext j
    rw [Function.comp_apply, Function.comp_apply, canonicalDifferentialPullback_D, hD]
    exact congrArg (KaehlerDifferential.D R (powerBaseChangeRing R d S a))
      (RingHom.congr_fun (powerBaseChange_square R d S a) (MvPolynomial.X j))
  rw [he]
  change targetExteriorMap R d S a
    (exteriorPower.ιMulti (PolynomialRing R n) n
      (fun j => KaehlerDifferential.D R (PolynomialRing R n)
        (NadelKummerCover.coordinatePowerHom R (fun i => d i + 1) (MvPolynomial.X j)))) = _
  rw [differential_power_wedge, map_smulₛₗ, targetExteriorMap_generator]

/-- The actual canonical counit is intrinsically normalized on its genuine pulled base generator. -/
theorem canonicalCounit_pulled_generator (ha : a.FormallyEtale)
    (c : powerBaseChangeRing R d S a) :
    etaleCanonicalCounit R d S a ha
        (c • canonicalPullback R d S a (baseCanonicalGenerator R S a ha)) =
      baseChangeTrace R d S a c • baseCanonicalGenerator R S a ha := by
  rw [canonicalPullback_generator, smul_smul, etaleCanonicalCounit_apply, map_smul,
    targetCanonicalTrivialization_generator, smul_eq_mul, mul_one]
  rw [baseChangeTrace_eq_coefficient_jacobian, coefficientFunctional_apply, mul_comm c]

/-- The actual trace normalization holds for every actual base top form. -/
theorem canonicalCounit_pulled_topform (ha : a.FormallyEtale)
    (c : powerBaseChangeRing R d S a) (w : baseCanonicalModule R S a) :
    etaleCanonicalCounit R d S a ha (c • canonicalPullback R d S a w) =
      baseChangeTrace R d S a c • w := by
  let s := baseCanonicalTrivialization R S a ha w
  have hw : w = s • baseCanonicalGenerator R S a ha := by
    rw [← baseCanonicalTrivialization_symm]
    exact ((baseCanonicalTrivialization R S a ha).symm_apply_apply w).symm
  rw [hw, map_smulₛₗ]
  have he : c • (powerBaseChangeLeft R d S a s •
      canonicalPullback R d S a (baseCanonicalGenerator R S a ha)) =
      powerBaseChangeLeft R d S a s •
        (c • canonicalPullback R d S a (baseCanonicalGenerator R S a ha)) := by
    exact smul_comm _ _ _
  have hτ := (etaleCanonicalCounit R d S a ha).hom.map_smul s
    (c • canonicalPullback R d S a (baseCanonicalGenerator R S a ha))
  change etaleCanonicalCounit R d S a ha
    (powerBaseChangeLeft R d S a s •
      (c • canonicalPullback R d S a (baseCanonicalGenerator R S a ha))) = _ at hτ
  rw [he, hτ, canonicalCounit_pulled_generator, smul_comm s]

/-- A candidate's actual coefficient functional in the two genuine top-form bases. -/
def canonicalCandidateCoefficient (ha : a.FormallyEtale)
    (σ : (restrictScalars (powerBaseChangeLeft R d S a)).obj
      (ModuleCat.of (powerBaseChangeRing R d S a) (targetCanonicalModule R d S a)) ⟶
        ModuleCat.of S (baseCanonicalModule R S a)) :
    (restrictScalars (powerBaseChangeLeft R d S a)).obj
      (ModuleCat.of (powerBaseChangeRing R d S a) (powerBaseChangeRing R d S a)) →ₗ[S] S :=
  ((restrictScalars (powerBaseChangeLeft R d S a)).map
      (ModuleCat.ofHom (LinearMap.toSpanSingleton (powerBaseChangeRing R d S a)
        (targetCanonicalModule R d S a) (targetCanonicalGenerator R d S a ha))) ≫
    σ ≫ ModuleCat.ofHom (baseCanonicalTrivialization R S a ha).toLinearMap).hom

omit [Nontrivial R] in
/-- The actual candidate coefficient retains the whole original top-form evaluation. -/
theorem canonicalCandidateCoefficient_apply (ha : a.FormallyEtale)
    (σ : (restrictScalars (powerBaseChangeLeft R d S a)).obj
      (ModuleCat.of (powerBaseChangeRing R d S a) (targetCanonicalModule R d S a)) ⟶
        ModuleCat.of S (baseCanonicalModule R S a)) (c : powerBaseChangeRing R d S a) :
    canonicalCandidateCoefficient R d S a ha σ c =
      baseCanonicalTrivialization R S a ha (σ (c • targetCanonicalGenerator R d S a ha)) := rfl

end Coefficient

section Domain
variable (R : Type u) [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (d : Fin n → ℕ)
    (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)

/-- Intrinsic normalization on the genuine generator determines the whole actual canonical counit. -/
theorem canonicalCounit_eq_of_generator (hflat : a.Flat) (ha : a.FormallyEtale)
    (σ : (restrictScalars (powerBaseChangeLeft R d S a)).obj
      (ModuleCat.of (powerBaseChangeRing R d S a) (targetCanonicalModule R d S a)) ⟶
        ModuleCat.of S (baseCanonicalModule R S a))
    (hσ : ∀ c, σ (c • canonicalPullback R d S a (baseCanonicalGenerator R S a ha)) =
      baseChangeTrace R d S a c • baseCanonicalGenerator R S a ha) :
    σ = etaleCanonicalCounit R d S a ha := by
  have hcoeff := eq_coefficientFunctional_of_trace R d S a hflat
    (canonicalCandidateCoefficient R d S a ha σ) (fun c => by
      change baseCanonicalTrivialization R S a ha
        (σ ((powerBaseChangeRight R d S a (jacobian R d) * c) •
          targetCanonicalGenerator R d S a ha)) = _
      have hm : c • canonicalPullback R d S a (baseCanonicalGenerator R S a ha) =
          (powerBaseChangeRight R d S a (jacobian R d) * c) • targetCanonicalGenerator R d S a ha := by
        rw [canonicalPullback_generator, smul_smul, mul_comm c]
      have h := (congrArg (fun w : targetCanonicalModule R d S a => σ w) hm).symm.trans (hσ c)
      rw [h, map_smul, baseCanonicalTrivialization_generator, smul_eq_mul, mul_one])
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  let c := targetCanonicalTrivialization R d S a ha w
  have hw : w = c • targetCanonicalGenerator R d S a ha := by
    apply (targetCanonicalTrivialization R d S a ha).injective
    rw [map_smul, targetCanonicalTrivialization_generator, smul_eq_mul, mul_one]
  apply (baseCanonicalTrivialization R S a ha).injective
  rw [hw, etaleCanonicalCounit_apply, map_smul, baseCanonicalTrivialization_generator,
    map_smul, targetCanonicalTrivialization_generator, smul_eq_mul, mul_one]
  have he := (canonicalCandidateCoefficient_apply R d S a ha σ c).symm.trans
    ((congrArg (fun f => f c) hcoeff).trans (coefficientFunctional_apply R d S a c))
  simpa only [smul_eq_mul, mul_one] using he

/-- The intrinsic condition on all genuine base top forms determines the whole canonical counit. -/
theorem canonicalCounit_eq_of_topforms (hflat : a.Flat) (ha : a.FormallyEtale)
    (σ : (restrictScalars (powerBaseChangeLeft R d S a)).obj
      (ModuleCat.of (powerBaseChangeRing R d S a) (targetCanonicalModule R d S a)) ⟶
        ModuleCat.of S (baseCanonicalModule R S a))
    (hσ : ∀ c w, σ (c • canonicalPullback R d S a w) = baseChangeTrace R d S a c • w) :
    σ = etaleCanonicalCounit R d S a ha :=
  canonicalCounit_eq_of_generator R d S a hflat ha σ
    (fun c => hσ c (baseCanonicalGenerator R S a ha))

end Domain
end EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniqueness
