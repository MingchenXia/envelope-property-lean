import EnvelopeProperty.Vanishing.NadelKummerCanonicalTraceDual
import EnvelopeProperty.AlgGeom.Canonical.AffineCanonicalModule

/-! # Actual top differential modules and the coordinate-power duality counit

Both canonical modules are the native top exterior powers of the original
polynomial Kähler differentials.  Their actual ordered differential bases
are composed with the proved native power-map dual frame.  Coordinate-change
and global gluing compatibility are separate obligations.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelKummerCanonicalTrace

open CategoryTheory ModuleCat CanonicalGeometry NadelKummerCover NadelFiniteDualityTower

universe u
variable (R : Type u) [CommRing R] [Nontrivial R]

/-- The actual native top exterior Kähler module on original polynomial affine space. -/
abbrev canonicalModule (n : ℕ) := affineCanonicalModule R (PolynomialRing R n) n

/-- The actual original ordered wedge of all polynomial coordinate differentials. -/
def canonicalGenerator (n : ℕ) : canonicalModule R n := polynomialCanonicalGenerator R n

/-- The native one-vector differential-wedge trivialization of the actual canonical module. -/
def canonicalTrivialization (n : ℕ) : canonicalModule R n ≃ₗ[PolynomialRing R n] PolynomialRing R n :=
  affineCanonicalTrivialization (KaehlerDifferential.mvPolynomialBasis R (Fin n))

omit [Nontrivial R] in
/-- The retained generator is literally the original ordered wedge of native differentials. -/
theorem canonicalGenerator_eq_wedge (n : ℕ) :
    canonicalGenerator R n = exteriorPower.ιMulti (PolynomialRing R n) n
      (fun j => KaehlerDifferential.D R (PolynomialRing R n) (MvPolynomial.X j)) :=
  polynomialCanonicalGenerator_eq_wedge R n

omit [Nontrivial R] in
/-- The actual ordered top wedge has its original unit coefficient. -/
theorem canonicalTrivialization_generator (n : ℕ) :
    canonicalTrivialization R n (canonicalGenerator R n) = 1 :=
  affineCanonicalTrivialization_generator (KaehlerDifferential.mvPolynomialBasis R (Fin n))

omit [Nontrivial R] in
/-- Every actual native top form is the scalar multiple of its original ordered top wedge. -/
theorem canonicalTrivialization_symm (n : ℕ) (g : PolynomialRing R n) :
    (canonicalTrivialization R n).symm g = g • canonicalGenerator R n := by
  apply (canonicalTrivialization R n).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, canonicalTrivialization_generator,
    smul_eq_mul, mul_one]

variable {n : ℕ} (d : Fin n → ℕ)

/-- The actual top differential module is the native power-map coextension of the actual base top module. -/
def canonicalIso : ModuleCat.of (PolynomialRing R n) (canonicalModule R n) ≅
    (coextendScalars (powerMap R d)).obj
      (ModuleCat.of (PolynomialRing R n) (canonicalModule R n)) :=
  (canonicalTrivialization R n).toModuleIso ≪≫ powerDualizingIso R d ≪≫
    (coextendScalars (powerMap R d)).mapIso (canonicalTrivialization R n).symm.toModuleIso

/-- Every original actual top form has the proved whole native dual-functional formula. -/
theorem canonicalIso_apply (w : canonicalModule R n) (b : PolynomialRing R n) :
    (canonicalIso R d).hom w b =
      coefficientMap R d (b * canonicalTrivialization R n w) • canonicalGenerator R n := by
  change (canonicalTrivialization R n).symm
    (powerDualizingMap R d (canonicalTrivialization R n w) b) = _
  rw [powerDualizingMap_apply, canonicalTrivialization_symm, coefficientMap_apply]

/-- The whole actual ordered-wedge generator formula, with the literal original coefficient action. -/
theorem canonicalIso_generator (g b : PolynomialRing R n) :
    (canonicalIso R d).hom (g • canonicalGenerator R n) b =
      coefficientMap R d (b * g) • canonicalGenerator R n := by
  rw [canonicalIso_apply, map_smul, canonicalTrivialization_generator, smul_eq_mul, mul_one]

/-- The canonical chart counit is the original native restriction/coextension counit on actual top forms. -/
def canonicalCounit :
    (restrictScalars (powerMap R d)).obj
        (ModuleCat.of (PolynomialRing R n) (canonicalModule R n)) ⟶
      ModuleCat.of (PolynomialRing R n) (canonicalModule R n) :=
  (restrictScalars (powerMap R d)).map (canonicalIso R d).hom ≫
    (restrictCoextendScalarsAdj (powerMap R d)).counit.app
      (ModuleCat.of (PolynomialRing R n) (canonicalModule R n))

/-- The actual native canonical counit retains the original top-form coefficient formula everywhere. -/
theorem canonicalCounit_apply (w : canonicalModule R n) :
    canonicalCounit R d w =
      coefficientMap R d (canonicalTrivialization R n w) • canonicalGenerator R n := by
  change (canonicalIso R d).hom w (1 : PolynomialRing R n) = _
  rw [canonicalIso_apply, one_mul]

/-- The canonical counit sends every original coefficient times the actual top wedge to its proved coefficient. -/
theorem canonicalCounit_generator (g : PolynomialRing R n) :
    canonicalCounit R d (g • canonicalGenerator R n) =
      coefficientMap R d g • canonicalGenerator R n := by
  rw [canonicalCounit_apply, map_smul, canonicalTrivialization_generator, smul_eq_mul, mul_one]

/-- The whole original canonical counit is exactly the original composed tower top coefficient. -/
theorem canonicalCounit_composite_topCoefficient (g : PolynomialRing R n) :
    canonicalCounit R d (g • canonicalGenerator R n) =
      independentTopCoefficient (coordinateTowerDegree d)
        (coordinateTowerCoefficient R (n := n)) n ((coordinateTowerEquiv R d).symm g) •
          canonicalGenerator R n := by
  rw [canonicalCounit_generator, coefficientMap_apply]

end EnvelopeProperty.Vanishing.NadelKummerCanonicalTrace
