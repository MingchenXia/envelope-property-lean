import EnvelopeProperty.Vanishing.NadelKummerCoverTowerPolynomial
import EnvelopeProperty.Vanishing.NadelFiniteDualityTowerFinite

/-! # The native dual frame of the actual polynomial coordinate-power algebra

The proved original tower/polynomial equivalence supplies the coefficient
triangle.  The native coextension action is retained on the literal power
homomorphism, including when the two polynomial rings share a carrier.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelKummerCanonicalTrace

open CategoryTheory ModuleCat NadelKummerCover NadelFiniteDualityTower

universe u

section NativeFrame
variable {A B : Type u} [CommRing A] [CommRing B]

/-- Native adjunction applied once to an actual coefficient functional on a restricted regular module. -/
def coextensionFrame (f : A →+* B)
    (ℓ : (restrictScalars f).obj (ModuleCat.of B B) →ₗ[A] A) :
    B →ₗ[B] (coextendScalars f).obj (ModuleCat.of A A) :=
  (RestrictionCoextensionAdj.HomEquiv.fromRestriction f
    (X := ModuleCat.of A A) (Y := ModuleCat.of B B)
    (ModuleCat.ofHom (X := (restrictScalars f).obj (ModuleCat.of B B))
      (Y := ModuleCat.of A A) ℓ)).hom

/-- The native adjunction frame has its whole original multiplication formula. -/
theorem coextensionFrame_apply (f : A →+* B)
    (ℓ : (restrictScalars f).obj (ModuleCat.of B B) →ₗ[A] A) (x y : B) :
    coextensionFrame f ℓ x y = ℓ (y * x) := rfl

end NativeFrame

variable (R : Type u) [CommRing R] [Nontrivial R] {n : ℕ} (d : Fin n → ℕ)

/-- The actual original coefficient ring of the coordinate-power chart. -/
abbrev PolynomialRing (n : ℕ) := MvPolynomial (Fin n) R

/-- The literal original power coefficient homomorphism, retaining positive original degrees. -/
def powerMap : PolynomialRing R n →+* PolynomialRing R n :=
  (coordinatePowerHom R (fun j => d j + 1)).toRingHom

/-- The original coordinate algebra iso identifies the actual restricted coefficient modules. -/
def towerRestrictionEquiv :
    (restrictScalars (coordinateTowerStructure R d)).obj
        (ModuleCat.of (coordinateTowerRing R d) (coordinateTowerRing R d)) ≃ₗ[PolynomialRing R n]
      (restrictScalars (powerMap R d)).obj
        (ModuleCat.of (PolynomialRing R n) (PolynomialRing R n)) where
  toFun x := coordinateTowerEquiv R d x
  invFun x := (coordinateTowerEquiv R d).symm x
  left_inv x := (coordinateTowerEquiv R d).left_inv x
  right_inv x := (coordinateTowerEquiv R d).right_inv x
  map_add' x y := (coordinateTowerEquiv R d).map_add x y
  map_smul' r x := by
    change coordinateTowerEquiv R d
      (coordinateTowerStructure R d r * (show coordinateTowerRing R d from x)) =
      powerMap R d r * coordinateTowerEquiv R d x
    rw [map_mul]
    exact congrArg (fun z => z * coordinateTowerEquiv R d x)
      (congrArg (fun h => h r) (coordinateTowerToPolynomial_structure R d))

/-- The actual native dual module over the literal original coordinate-power map. -/
abbrev powerDualizingModule : ModuleCat (PolynomialRing R n) :=
  (coextendScalars (powerMap R d)).obj (ModuleCat.of (PolynomialRing R n) (PolynomialRing R n))

/-- Transport of the actual original top-coefficient counit to the original polynomial algebra. -/
def coefficientMap :
    (restrictScalars (powerMap R d)).obj
        (ModuleCat.of (PolynomialRing R n) (PolynomialRing R n)) →ₗ[PolynomialRing R n]
      PolynomialRing R n :=
  ((restrictCoextendScalarsAdj (coordinateTowerStructure R d)).counit.app
      (ModuleCat.of (PolynomialRing R n) (PolynomialRing R n))).hom.comp
    (((restrictScalars (coordinateTowerStructure R d)).map
      (independentRootIso (coordinateTowerDegree d)
        (coordinateTowerCoefficient R (n := n)) n).hom).hom.comp
      (towerRestrictionEquiv R d).symm.toLinearMap)

/-- Every original polynomial coefficient is exactly the composite of the actual tower coefficients. -/
theorem coefficientMap_apply (x : PolynomialRing R n) :
    coefficientMap R d x = independentTopCoefficient (coordinateTowerDegree d)
      (coordinateTowerCoefficient R (n := n)) n ((coordinateTowerEquiv R d).symm x) :=
  independentRootIso_counit (coordinateTowerDegree d) (coordinateTowerCoefficient R (n := n)) n _

/-- The original native adjunction produces the polynomial-root-algebra-linear dual frame map. -/
def powerDualizingMap : PolynomialRing R n →ₗ[PolynomialRing R n] powerDualizingModule R d :=
  coextensionFrame (powerMap R d) (coefficientMap R d)

/-- The whole native dual frame keeps the actual multiplication and composite coefficient. -/
theorem powerDualizingMap_apply (x y : PolynomialRing R n) :
    powerDualizingMap R d x y = independentTopCoefficient (coordinateTowerDegree d)
      (coordinateTowerCoefficient R (n := n)) n ((coordinateTowerEquiv R d).symm (y * x)) := by
  rw [powerDualizingMap, coextensionFrame_apply]
  exact coefficientMap_apply R d (y * x)

/-- Actual precomposition with the whole coefficient-preserving algebra iso on native dual carriers. -/
def functionalTransport : powerDualizingModule R d ≃
    (coextendScalars (coordinateTowerStructure R d)).obj
      (ModuleCat.of (PolynomialRing R n) (PolynomialRing R n)) :=
  (CoextendScalars.equiv (powerMap R d)
    (ModuleCat.of (PolynomialRing R n) (PolynomialRing R n))).toEquiv |>.trans
      (((towerRestrictionEquiv R d).symm.arrowCongr
        (LinearEquiv.refl (PolynomialRing R n) (PolynomialRing R n))).toEquiv.trans
          (CoextendScalars.equiv (coordinateTowerStructure R d)
            (ModuleCat.of (PolynomialRing R n) (PolynomialRing R n))).symm.toEquiv)

omit [Nontrivial R] in
/-- The native carrier comparison is literal precomposition with the original whole ring iso. -/
theorem functionalTransport_apply (φ : powerDualizingModule R d) (x : coordinateTowerRing R d) :
    functionalTransport R d φ x = φ (coordinateTowerEquiv R d x) := rfl

/-- The whole frame comparison commutes with the original tower equivalence, without an input diagram. -/
theorem functionalTransport_powerDualizingMap (x : PolynomialRing R n) :
    functionalTransport R d (powerDualizingMap R d x) =
      (independentRootIso (coordinateTowerDegree d)
        (coordinateTowerCoefficient R (n := n)) n).hom ((coordinateTowerEquiv R d).symm x) := by
  apply CoextendScalars.ext
  ext (y : coordinateTowerRing R d)
  rw [functionalTransport_apply, powerDualizingMap_apply, independentRootIso_hom_apply,
    map_mul, RingEquiv.symm_apply_apply]

/-- Bijectivity is derived from the actual whole tower frame and original algebra iso. -/
theorem powerDualizingMap_bijective : Function.Bijective (powerDualizingMap R d) := by
  let e := (coordinateTowerEquiv R d).symm.toEquiv.trans
    ((independentRootIso (coordinateTowerDegree d)
      (coordinateTowerCoefficient R (n := n)) n).toLinearEquiv.toEquiv.trans
        (functionalTransport R d).symm)
  have he : (powerDualizingMap R d : PolynomialRing R n → powerDualizingModule R d) = e := by
    funext x
    apply (functionalTransport R d).injective
    rw [functionalTransport_powerDualizingMap]
    exact ((functionalTransport R d).apply_symm_apply _).symm
  rw [he]
  exact e.bijective

/-- The actual whole coordinate-power algebra is its native power-map coextension dual. -/
def powerDualizingEquiv : PolynomialRing R n ≃ₗ[PolynomialRing R n] powerDualizingModule R d :=
  LinearEquiv.ofBijective (powerDualizingMap R d) (powerDualizingMap_bijective R d)

/-- The same whole native power-map duality as an actual module-category isomorphism. -/
def powerDualizingIso :
    ModuleCat.of (PolynomialRing R n) (PolynomialRing R n) ≅ powerDualizingModule R d :=
  LinearEquiv.toModuleIso (X₁ := ModuleCat.of (PolynomialRing R n) (PolynomialRing R n))
    (X₂ := powerDualizingModule R d) (powerDualizingEquiv R d)

end EnvelopeProperty.Vanishing.NadelKummerCanonicalTrace
