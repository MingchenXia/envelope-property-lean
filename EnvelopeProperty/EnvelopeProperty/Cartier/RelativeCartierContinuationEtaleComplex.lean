import EnvelopeProperty.Cartier.RelativeFrobeniusCoefficient
import EnvelopeProperty.Cartier.EtaleDifferentialLeibniz

/-!
# The actual affine etale de Rham complex over the relative Frobenius twist

All original exterior cotangent modules and whole differentials are retained. Native
restriction along the actual relative Frobenius gives the correct coefficient ring,
including over imperfect fields: original base coefficients act by themselves.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeEtaleDeRham
open CategoryTheory
open scoped Classical
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP R p] [CharP B p]
local notation "T" => RelativeFrobenius.twist (algebraMap R B) p

/-- The SAME whole original exterior cotangent differential has genuine relative
Frobenius scalar linearity on every original form in every degree. -/
theorem originalDifferential_map_smul (q : ℕ) (a : T)
    (w : ⋀[B]^q (KaehlerDifferential R B)) :
    EtaleDeRham.differential v hv q
        ((RelativeFrobenius.map (algebraMap R B) p).hom a • w) =
      (RelativeFrobenius.map (algebraMap R B) p).hom a • EtaleDeRham.differential v hv q w := by
  rw [EtaleDifferentialLeibniz.differential_smul, RelativeFrobeniusCoefficient.D_map_eq_zero]
  change (EtaleDifferentialLeibniz.leftWedgeLinear q 0) w + _ = _
  simp only [map_zero, LinearMap.zero_apply, zero_add]

/-- The actual original exterior cotangent module with native restriction along the
SAME genuine relative Frobenius, over its actual coefficient pushout ring. -/
def formModule (q : ℕ) : ModuleCat T :=
  (ModuleCat.restrictScalars (RelativeFrobenius.map (algebraMap R B) p).hom).obj
    (ModuleCat.of B (⋀[B]^q (KaehlerDifferential R B)))

/-- The actual whole original differential, genuinely linear over the SAME native
relative Frobenius twist ring, with linearity derived from the original universal D. -/
def differential (q : ℕ) :
    formModule (R := R) (B := B) p q ⟶ formModule (R := R) (B := B) p (q+1) :=
  ModuleCat.ofHom (X := formModule (R := R) (B := B) p q)
    (Y := formModule (R := R) (B := B) p (q+1))
    { toFun := EtaleDeRham.differential v hv q
      map_add' := (EtaleDeRham.differential v hv q).map_add
      map_smul' := fun a w => originalDifferential_map_smul v hv p q a w }

/-- Every original form has exactly its SAME original whole etale differential. -/
theorem differential_apply (q : ℕ) (w : ⋀[B]^q (KaehlerDifferential R B)) :
    (differential v hv p q).hom (show formModule (R := R) (B := B) p q from w) =
      (show formModule (R := R) (B := B) p (q+1) from EtaleDeRham.differential v hv q w) := rfl

/-- The actual entire affine etale de Rham cochain complex over the genuine relative
Frobenius coefficient ring, with its original exterior modules and original maps. -/
def complex : CochainComplex (ModuleCat T) ℕ :=
  CochainComplex.of (formModule (R := R) (B := B) p) (differential v hv p)
    (fun q => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      exact EtaleDeRham.differential_square v hv q w)

/-- EVERY original base coefficient acts by its SAME original image on EVERY form
in the genuine relative module, including over imperfect characteristic-p fields. -/
theorem coefficient_smul (q : ℕ) (c : R) (w : ⋀[B]^q (KaehlerDifferential R B)) :
    (RelativeFrobenius.coefficientMap (algebraMap R B) p).hom c •
        (show formModule (R := R) (B := B) p q from w) =
      (show formModule (R := R) (B := B) p q from (algebraMap R B c) • w) := by
  change (RelativeFrobenius.map (algebraMap R B) p).hom
    ((RelativeFrobenius.coefficientMap (algebraMap R B) p).hom c) • w = (algebraMap R B c) • w
  have h := congrArg (fun h : CommRingCat.of R ⟶ CommRingCat.of B => h.hom c)
    (RelativeFrobenius.coefficientMap_map (algebraMap R B) p)
  change (RelativeFrobenius.map (algebraMap R B) p).hom
    ((RelativeFrobenius.coefficientMap (algebraMap R B) p).hom c) = algebraMap R B c at h
  rw [h]

/-- The SAME original source inclusion recovers the actual absolute Frobenius scalar
action on EVERY original form, in every degree. -/
theorem source_smul (q : ℕ) (b : B) (w : ⋀[B]^q (KaehlerDifferential R B)) :
    (RelativeFrobenius.sourceMap (algebraMap R B) p).hom b •
        (show formModule (R := R) (B := B) p q from w) =
      (show formModule (R := R) (B := B) p q from b^p • w) := by
  change (RelativeFrobenius.map (algebraMap R B) p).hom
    ((RelativeFrobenius.sourceMap (algebraMap R B) p).hom b) • w = b^p • w
  have h := congrArg (fun h : CommRingCat.of B ⟶ CommRingCat.of B => h.hom b)
    (RelativeFrobenius.sourceMap_map (algebraMap R B) p)
  change (RelativeFrobenius.map (algebraMap R B) p).hom
    ((RelativeFrobenius.sourceMap (algebraMap R B) p).hom b) = b^p at h
  rw [h]

end EnvelopeProperty.Cartier.RelativeEtaleDeRham
