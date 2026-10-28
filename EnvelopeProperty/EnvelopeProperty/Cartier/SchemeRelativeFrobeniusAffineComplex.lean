import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineCoefficient
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleComplex

/-! # The affine exterior complex with its genuine geometric relative action

The original exterior modules and differential are restricted along the actual
geometric relative Frobenius section map. Zero endpoints need no `CharP B p`.
Route: `blueprint/src/smooth-scheme-relative-frobenius-complex.tex`.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineDeRham
open CategoryTheory
universe u
variable {k B : Type u} [Field k] [CommRing B] [Algebra k B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "T" => RelativeFrobenius.twist (algebraMap k B) p
local notation "β" => CommRingCat.Hom.hom
  (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k B) p)

/-- The whole original exterior differential is linear for the genuine geometric
relative Frobenius action, in every degree and at zero endpoints. -/
theorem originalDifferential_map_smul (q : ℕ) (a : T)
    (w : ⋀[B]^q (KaehlerDifferential k B)) :
    EtaleDeRham.differential v hv q (β a • w) =
      β a • EtaleDeRham.differential v hv q w := by
  rw [EtaleDifferentialLeibniz.differential_smul,
    SchemeRelativeFrobeniusAffineMap.D_ringMap_eq_zero]
  change (EtaleDifferentialLeibniz.leftWedgeLinear q 0) w + _ = _
  simp only [map_zero, LinearMap.zero_apply, zero_add]

/-- The original exterior module with its actual geometric relative action. -/
def formModule (q : ℕ) : ModuleCat T :=
  (ModuleCat.restrictScalars β).obj (ModuleCat.of B (⋀[B]^q (KaehlerDifferential k B)))

/-- The unchanged original exterior differential as a genuine native T-linear map. -/
def differential (q : ℕ) :
    formModule (k := k) (B := B) p q ⟶ formModule (k := k) (B := B) p (q+1) :=
  ModuleCat.ofHom (X := formModule (k := k) (B := B) p q)
    (Y := formModule (k := k) (B := B) p (q+1))
    { toFun := EtaleDeRham.differential v hv q
      map_add' := (EtaleDeRham.differential v hv q).map_add
      map_smul' := fun a w => originalDifferential_map_smul v hv p q a w }

/-- Every original form has its same original exterior differential. -/
theorem differential_apply (q : ℕ) (w : ⋀[B]^q (KaehlerDifferential k B)) :
    (differential v hv p q).hom (show formModule (k := k) (B := B) p q from w) =
      (show formModule (k := k) (B := B) p (q+1) from EtaleDeRham.differential v hv q w) := rfl

/-- The actual zero-safe affine target complex over the genuine twist ring. -/
def complex : CochainComplex (ModuleCat T) ℕ :=
  CochainComplex.of (formModule (k := k) (B := B) p) (differential v hv p)
    (fun q => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      exact EtaleDeRham.differential_square v hv q w)

/-- Every original coefficient has its unchanged original action on every form. -/
theorem coefficient_smul (q : ℕ) (a : k) (w : ⋀[B]^q (KaehlerDifferential k B)) :
    (RelativeFrobenius.coefficientMap (algebraMap k B) p).hom a •
        (show formModule (k := k) (B := B) p q from w) =
      (show formModule (k := k) (B := B) p q from (algebraMap k B a) • w) := by
  change β ((RelativeFrobenius.coefficientMap (algebraMap k B) p).hom a) • w = _
  have h := congrArg (fun g : CommRingCat.of k ⟶ CommRingCat.of B => g.hom a)
    (SchemeRelativeFrobeniusAffineMap.coefficient_ringMap (algebraMap k B) p)
  change β ((RelativeFrobenius.coefficientMap (algebraMap k B) p).hom a) = algebraMap k B a at h
  rw [h]

/-- Every original source element acts by its actual original pth power. -/
theorem source_smul (q : ℕ) (b : B) (w : ⋀[B]^q (KaehlerDifferential k B)) :
    (RelativeFrobenius.sourceMap (algebraMap k B) p).hom b •
        (show formModule (k := k) (B := B) p q from w) =
      (show formModule (k := k) (B := B) p q from b^p • w) := by
  change β ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom b) • w = _
  rw [SchemeRelativeFrobeniusAffineMap.source_ringMap_apply]

set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
#check @originalDifferential_map_smul
#print axioms originalDifferential_map_smul
#check @formModule
#print axioms formModule
#check @differential
#print axioms differential
#check @differential_apply
#print axioms differential_apply
#check @complex
#print axioms complex
#check @coefficient_smul
#print axioms coefficient_smul
#check @source_smul
#print axioms source_smul
end EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineDeRham
