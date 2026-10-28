import EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChange
import EnvelopeProperty.Vanishing.NadelKummerCanonicalTrace
import EnvelopeProperty.AlgGeom.Canonical.AffineCanonicalModule
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Genuine étale top differential frames on the actual Kummer base-change square

All coefficient algebras and Kähler bases are derived from the original maps.
The actual native counit retains the original coefficient formula after base
change.  Arbitrary coordinate-change/global gluing is a separate obligation.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChange

open CategoryTheory ModuleCat TensorProduct CanonicalGeometry
open scoped TensorProduct
open NadelKummerCanonicalTrace NadelKummerCover

universe u

private theorem tensorRight_formallyEtale {A B S : Type u}
    [CommRing A] [CommRing B] [CommRing S] [Algebra A B] [Algebra A S]
    [Algebra.FormallyEtale A S] :
    let _ : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    Algebra.FormallyEtale B (S ⊗[A] B) := by
  let : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  exact Algebra.FormallyEtale.of_equiv (Algebra.TensorProduct.commRight A B S)

variable (R : Type u) [CommRing R] [Nontrivial R] {n : ℕ} (d : Fin n → ℕ)

omit [Nontrivial R] in
/-- The actual original tensor base-change projection is formally étale, internally from the original map. -/
theorem powerBaseChangeRight_formallyEtale (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) :
    (powerBaseChangeRight R d S a).FormallyEtale := by
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
  let : Module (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra.toModule
  let : Algebra.FormallyEtale (PolynomialRing R n) S := ha
  let : Algebra (PolynomialRing R n) (S ⊗[PolynomialRing R n] PolynomialRing R n) :=
    Algebra.TensorProduct.rightAlgebra
  change Algebra.FormallyEtale (PolynomialRing R n) (S ⊗[PolynomialRing R n] PolynomialRing R n)
  exact tensorRight_formallyEtale (A := PolynomialRing R n) (B := PolynomialRing R n) (S := S)

/-- The actual original small coefficient algebra on the étale base chart. -/
@[instance_reducible]
def baseRAlgebra (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S) : Algebra R S :=
  (a.comp MvPolynomial.C).toAlgebra

/-- The actual original small coefficient algebra on the same literal new source. -/
@[instance_reducible]
def targetRAlgebra (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S) :
    Algebra R (powerBaseChangeRing R d S a) :=
  ((powerBaseChangeRight R d S a).comp MvPolynomial.C).toAlgebra

omit [Nontrivial R] in
/-- Both actual small-coefficient paths agree on the entire original coefficient ring. -/
theorem smallCoefficient_square (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S) :
    (powerBaseChangeLeft R d S a).comp (a.comp MvPolynomial.C) =
      (powerBaseChangeRight R d S a).comp MvPolynomial.C := by
  apply RingHom.ext
  intro r
  have h := congrArg (fun q : PolynomialRing R n →+* powerBaseChangeRing R d S a =>
    q (MvPolynomial.C r)) (powerBaseChange_square R d S a)
  change powerBaseChangeLeft R d S a (a (MvPolynomial.C r)) =
    powerBaseChangeRight R d S a (coordinatePowerHom R (fun j => d j + 1) (MvPolynomial.C r)) at h
  rw [coordinatePowerHom_C] at h
  exact h

/-- The native original top Kähler module on the actual étale base chart. -/
abbrev baseCanonicalModule (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S) :=
  let _ := baseRAlgebra R S a
  affineCanonicalModule R S n

/-- The native original top Kähler module on the literal actual new source. -/
abbrev targetCanonicalModule (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S) :=
  let _ := targetRAlgebra R d S a
  affineCanonicalModule R (powerBaseChangeRing R d S a) n

/-- The actual étale base differential basis, internally from the original polynomial basis. -/
def baseDifferentialBasis (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)
    (ha : a.FormallyEtale) :
    let _ := baseRAlgebra R S a
    Module.Basis (Fin n) S (KaehlerDifferential R S) := by
  let := baseRAlgebra R S a
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : IsScalarTower R (PolynomialRing R n) S := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FormallyEtale (PolynomialRing R n) S := ha
  exact polynomialEtaleDifferentialBasis R S n

/-- The actual new-source differential basis, internally from the original target polynomial coordinates. -/
def targetDifferentialBasis (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)
    (ha : a.FormallyEtale) :
    let _ := targetRAlgebra R d S a
    Module.Basis (Fin n) (powerBaseChangeRing R d S a)
      (KaehlerDifferential R (powerBaseChangeRing R d S a)) := by
  let := targetRAlgebra R d S a
  let : Algebra (PolynomialRing R n) (powerBaseChangeRing R d S a) :=
    (powerBaseChangeRight R d S a).toAlgebra
  let : IsScalarTower R (PolynomialRing R n) (powerBaseChangeRing R d S a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FormallyEtale (PolynomialRing R n) (powerBaseChangeRing R d S a) :=
    powerBaseChangeRight_formallyEtale R d S a ha
  exact polynomialEtaleDifferentialBasis R (powerBaseChangeRing R d S a) n

omit [Nontrivial R] in
/-- Every actual base differential basis vector is the native differential of the original coordinate image. -/
theorem baseDifferentialBasis_apply (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) (j : Fin n) :
    let _ := baseRAlgebra R S a
    baseDifferentialBasis R S a ha j = KaehlerDifferential.D R S (a (MvPolynomial.X j)) := by
  let := baseRAlgebra R S a
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : IsScalarTower R (PolynomialRing R n) S := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FormallyEtale (PolynomialRing R n) S := ha
  exact polynomialEtaleDifferentialBasis_apply R S n j

omit [Nontrivial R] in
/-- Every actual new-source basis vector is the native differential of the original target-coordinate image. -/
theorem targetDifferentialBasis_apply (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) (j : Fin n) :
    let _ := targetRAlgebra R d S a
    targetDifferentialBasis R d S a ha j =
      KaehlerDifferential.D R (powerBaseChangeRing R d S a)
        (powerBaseChangeRight R d S a (MvPolynomial.X j)) := by
  let := targetRAlgebra R d S a
  let : Algebra (PolynomialRing R n) (powerBaseChangeRing R d S a) :=
    (powerBaseChangeRight R d S a).toAlgebra
  let : IsScalarTower R (PolynomialRing R n) (powerBaseChangeRing R d S a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FormallyEtale (PolynomialRing R n) (powerBaseChangeRing R d S a) :=
    powerBaseChangeRight_formallyEtale R d S a ha
  exact polynomialEtaleDifferentialBasis_apply R (powerBaseChangeRing R d S a) n j

/-- The genuine ordered base top wedge, with no supplied canonical trivialization. -/
def baseCanonicalGenerator (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)
    (ha : a.FormallyEtale) : baseCanonicalModule R S a := by
  let := baseRAlgebra R S a
  exact affineCanonicalGenerator (baseDifferentialBasis R S a ha)

/-- The genuine ordered new-source top wedge, with no supplied canonical trivialization. -/
def targetCanonicalGenerator (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)
    (ha : a.FormallyEtale) : targetCanonicalModule R d S a := by
  let := targetRAlgebra R d S a
  exact affineCanonicalGenerator (targetDifferentialBasis R d S a ha)

omit [Nontrivial R] in
/-- The actual base canonical generator is the original ordered wedge of native coordinate-image differentials. -/
theorem baseCanonicalGenerator_eq_wedge (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) :
    let _ := baseRAlgebra R S a
    baseCanonicalGenerator R S a ha = exteriorPower.ιMulti S n
      (fun j => KaehlerDifferential.D R S (a (MvPolynomial.X j))) := by
  let := baseRAlgebra R S a
  rw [baseCanonicalGenerator, affineCanonicalGenerator_eq_wedge]
  congr 1
  funext j
  exact baseDifferentialBasis_apply R S a ha j

omit [Nontrivial R] in
/-- The actual new-source canonical generator is the original ordered wedge of native coordinate-image differentials. -/
theorem targetCanonicalGenerator_eq_wedge (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) :
    let _ := targetRAlgebra R d S a
    targetCanonicalGenerator R d S a ha = exteriorPower.ιMulti (powerBaseChangeRing R d S a) n
      (fun j => KaehlerDifferential.D R (powerBaseChangeRing R d S a)
        (powerBaseChangeRight R d S a (MvPolynomial.X j))) := by
  let := targetRAlgebra R d S a
  rw [targetCanonicalGenerator, affineCanonicalGenerator_eq_wedge]
  congr 1
  funext j
  exact targetDifferentialBasis_apply R d S a ha j

/-- The actual étale base top-form coefficient trivialization. -/
def baseCanonicalTrivialization (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)
    (ha : a.FormallyEtale) : baseCanonicalModule R S a ≃ₗ[S] S := by
  let := baseRAlgebra R S a
  exact affineCanonicalTrivialization (baseDifferentialBasis R S a ha)

/-- The actual literal new-source top-form coefficient trivialization. -/
def targetCanonicalTrivialization (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)
    (ha : a.FormallyEtale) :
    targetCanonicalModule R d S a ≃ₗ[powerBaseChangeRing R d S a] powerBaseChangeRing R d S a := by
  let := targetRAlgebra R d S a
  exact affineCanonicalTrivialization (targetDifferentialBasis R d S a ha)

omit [Nontrivial R] in
/-- The original actual base wedge is the unit vector for its actual differential trivialization. -/
theorem baseCanonicalTrivialization_generator (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) :
    baseCanonicalTrivialization R S a ha (baseCanonicalGenerator R S a ha) = 1 := by
  let := baseRAlgebra R S a
  exact affineCanonicalTrivialization_generator (baseDifferentialBasis R S a ha)

omit [Nontrivial R] in
/-- The original actual new-source wedge is the unit vector for its actual differential trivialization. -/
theorem targetCanonicalTrivialization_generator (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) :
    targetCanonicalTrivialization R d S a ha (targetCanonicalGenerator R d S a ha) = 1 := by
  let := targetRAlgebra R d S a
  exact affineCanonicalTrivialization_generator (targetDifferentialBasis R d S a ha)

omit [Nontrivial R] in
/-- The actual base canonical inverse frame uses its same original top differential generator. -/
theorem baseCanonicalTrivialization_symm (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) (s : S) :
    (baseCanonicalTrivialization R S a ha).symm s = s • baseCanonicalGenerator R S a ha := by
  apply (baseCanonicalTrivialization R S a ha).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, baseCanonicalTrivialization_generator,
    smul_eq_mul, mul_one]

/-- The actual new-source top differential module is the native coextension of the actual base top module. -/
def etaleCanonicalIso (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)
    (ha : a.FormallyEtale) :
    ModuleCat.of (powerBaseChangeRing R d S a) (targetCanonicalModule R d S a) ≅
      (coextendScalars (powerBaseChangeLeft R d S a)).obj
        (ModuleCat.of S (baseCanonicalModule R S a)) :=
  (targetCanonicalTrivialization R d S a ha).toModuleIso ≪≫ powerBaseChangeIso R d S a ≪≫
    (coextendScalars (powerBaseChangeLeft R d S a)).mapIso
      (baseCanonicalTrivialization R S a ha).symm.toModuleIso

/-- The whole actual canonical duality on the étale coefficient base change retains its coefficient formula. -/
theorem etaleCanonicalIso_apply (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale)
    (w : targetCanonicalModule R d S a) (y : powerBaseChangeRing R d S a) :
    (etaleCanonicalIso R d S a ha).hom w y =
      powerBaseChangeCoefficient R d S a (y * targetCanonicalTrivialization R d S a ha w) •
        baseCanonicalGenerator R S a ha := by
  change (baseCanonicalTrivialization R S a ha).symm
    ((powerBaseChangeIso R d S a).hom (targetCanonicalTrivialization R d S a ha w) y) = _
  rw [powerBaseChangeIso_apply, baseCanonicalTrivialization_symm]

/-- The true canonical counit on the same actual formally étale coefficient base change. -/
def etaleCanonicalCounit (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)
    (ha : a.FormallyEtale) :
    (restrictScalars (powerBaseChangeLeft R d S a)).obj
        (ModuleCat.of (powerBaseChangeRing R d S a) (targetCanonicalModule R d S a)) ⟶
      ModuleCat.of S (baseCanonicalModule R S a) :=
  (restrictScalars (powerBaseChangeLeft R d S a)).map (etaleCanonicalIso R d S a ha).hom ≫
    (restrictCoextendScalarsAdj (powerBaseChangeLeft R d S a)).counit.app
      (ModuleCat.of S (baseCanonicalModule R S a))

/-- The entire native canonical counit on actual original top forms has the original extended coefficient. -/
theorem etaleCanonicalCounit_apply (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) (w : targetCanonicalModule R d S a) :
    etaleCanonicalCounit R d S a ha w =
      powerBaseChangeCoefficient R d S a (targetCanonicalTrivialization R d S a ha w) •
        baseCanonicalGenerator R S a ha := by
  change (etaleCanonicalIso R d S a ha).hom w (1 : powerBaseChangeRing R d S a) = _
  rw [etaleCanonicalIso_apply, one_mul]

/-- The native canonical counit commutes with original coefficient extension on every actual pure tensor. -/
theorem etaleCanonicalCounit_tensor (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) (s : S) (b : PolynomialRing R n) :
    etaleCanonicalCounit R d S a ha
        (powerBaseChangeTensor R d S a s b • targetCanonicalGenerator R d S a ha) =
      (s * a (coefficientMap R d b)) • baseCanonicalGenerator R S a ha := by
  rw [etaleCanonicalCounit_apply, map_smul, targetCanonicalTrivialization_generator,
    smul_eq_mul, mul_one, powerBaseChangeCoefficient_tensor]

/-- In particular the same actual original target-polynomial coefficient retains its canonical trace after base change. -/
theorem etaleCanonicalCounit_right (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) (b : PolynomialRing R n) :
    etaleCanonicalCounit R d S a ha
        (powerBaseChangeRight R d S a b • targetCanonicalGenerator R d S a ha) =
      a (coefficientMap R d b) • baseCanonicalGenerator R S a ha := by
  rw [powerBaseChangeRight_tensor, etaleCanonicalCounit_tensor, one_mul]

/-- The actual base top-frame map uses the original coefficient map and actual native differential wedge. -/
def baseTopFrameMap (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)
    (ha : a.FormallyEtale) :
    canonicalModule R n →ₛₗ[a] baseCanonicalModule R S a where
  toFun w := a (canonicalTrivialization R n w) • baseCanonicalGenerator R S a ha
  map_add' w v := by rw [map_add, map_add, add_smul]
  map_smul' r w := by rw [map_smul, smul_eq_mul, map_mul, mul_smul]

/-- The actual target top-frame map uses the original right inclusion and actual native differential wedge. -/
def targetTopFrameMap (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)
    (ha : a.FormallyEtale) :
    canonicalModule R n →ₛₗ[powerBaseChangeRight R d S a] targetCanonicalModule R d S a where
  toFun w := powerBaseChangeRight R d S a (canonicalTrivialization R n w) •
    targetCanonicalGenerator R d S a ha
  map_add' w v := by rw [map_add, map_add, add_smul]
  map_smul' r w := by rw [map_smul, smul_eq_mul, map_mul, mul_smul]

omit [Nontrivial R] in
/-- The actual original base wedge is carried to its actual étale differential wedge, with original coefficients. -/
theorem baseTopFrameMap_generator (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) (b : PolynomialRing R n) :
    baseTopFrameMap R S a ha (b • canonicalGenerator R n) =
      a b • baseCanonicalGenerator R S a ha := by
  change a (canonicalTrivialization R n (b • canonicalGenerator R n)) •
    baseCanonicalGenerator R S a ha = _
  rw [map_smul, canonicalTrivialization_generator, smul_eq_mul, mul_one]

omit [Nontrivial R] in
/-- The actual original target wedge is carried to its actual étale differential wedge, with original coefficients. -/
theorem targetTopFrameMap_generator (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) (b : PolynomialRing R n) :
    targetTopFrameMap R d S a ha (b • canonicalGenerator R n) =
      powerBaseChangeRight R d S a b • targetCanonicalGenerator R d S a ha := by
  change powerBaseChangeRight R d S a
    (canonicalTrivialization R n (b • canonicalGenerator R n)) •
      targetCanonicalGenerator R d S a ha = _
  rw [map_smul, canonicalTrivialization_generator, smul_eq_mul, mul_one]

/-- The whole actual top-frame counit diagram commutes, proved from original maps rather than assumed. -/
theorem etaleCanonicalCounit_frame_naturality (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (ha : a.FormallyEtale) (w : canonicalModule R n) :
    etaleCanonicalCounit R d S a ha (targetTopFrameMap R d S a ha w) =
      baseTopFrameMap R S a ha (canonicalCounit R d w) := by
  change etaleCanonicalCounit R d S a ha
      (powerBaseChangeRight R d S a (canonicalTrivialization R n w) •
        targetCanonicalGenerator R d S a ha) =
    a (canonicalTrivialization R n (canonicalCounit R d w)) • baseCanonicalGenerator R S a ha
  rw [etaleCanonicalCounit_right, canonicalCounit_apply, map_smul,
    canonicalTrivialization_generator, smul_eq_mul, mul_one]

end EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChange
