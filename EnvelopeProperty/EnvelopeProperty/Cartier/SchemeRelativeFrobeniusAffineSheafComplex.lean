import Mathlib.Algebra.Homology.Additive
import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineSpec
import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineComplex
import EnvelopeProperty.AlgGeom.SpecPushforwardTilde
import EnvelopeProperty.AlgGeom.Canonical.ExteriorSheaf

/-! # Actual relative affine pushed exterior sheaves and their native complex

The target is the genuine twist spectrum, and the source sheaves are the
original exterior cotangent sheaves. No characteristic instance on B is used.
Route: `blueprint/src/smooth-scheme-relative-frobenius-complex.tex`.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineSheafDeRham
open AlgebraicGeometry CategoryTheory Limits
universe u

private theorem conjugate_comm {C : Type*} [Category* C]
    {P Q R S : C} (e : P ≅ Q) (f : R ≅ S) (a : Q ⟶ S) :
    (e.hom ≫ a ≫ f.inv) ≫ f.hom = e.hom ≫ a := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem conjugate_square {C : Type*} [Category* C] [HasZeroMorphisms C]
    {P Q R S T U : C} (e : P ≅ Q) (f : R ≅ S) (g : T ≅ U)
    (a : Q ⟶ S) (b : S ⟶ U) (h : a ≫ b = 0) :
    (e.hom ≫ a ≫ f.inv) ≫ (f.hom ≫ b ≫ g.inv) = 0 := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc a b, h, zero_comp, comp_zero]

variable {k B : Type u} [Field k] [CommRing B] [Algebra k B]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "T" => RelativeFrobenius.twist (algebraMap k B) p
local notation "f" => CanonicalGeometry.affineStructuralMap k (CommRingCat.of B)
local notation "g" => SchemeRelativeFrobeniusAffineMap.affineMap (algebraMap k B) p
local notation "β" => SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k B) p
variable {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)

/-- The same genuinely pushed exterior sheaf has its original native twist-module model. -/
def formIso (q : ℕ) :
    (Scheme.Modules.pushforward g).obj (CanonicalGeometry.exteriorCotangentSheaf f q) ≅
      AlgebraicGeometry.tilde (SchemeRelativeFrobeniusAffineDeRham.formModule
        (k := k) (B := B) p q) :=
  eqToIso (congrArg (fun h : Spec (CommRingCat.of B) ⟶ Spec T =>
    (Scheme.Modules.pushforward h).obj (CanonicalGeometry.exteriorCotangentSheaf f q))
      (SchemeRelativeFrobeniusAffineMap.affineMap_eq_spec_ringMap (algebraMap k B) p)) ≪≫
    (Scheme.Modules.pushforward (Spec.map β)).mapIso
      (CanonicalGeometry.affineExteriorCotangentSheafIso k (CommRingCat.of B)
        (Char0.etaleDifferentialBasis v hv) q) ≪≫
      SpecPushforwardTilde.pushforwardTildeIso β
        (CanonicalGeometry.affineExteriorCotangentModule k (CommRingCat.of B) q)

/-- The actual original pushed sheaf differential, genuinely linear over the twist. -/
def differential (q : ℕ) :
    (Scheme.Modules.pushforward g).obj (CanonicalGeometry.exteriorCotangentSheaf f q) ⟶
      (Scheme.Modules.pushforward g).obj (CanonicalGeometry.exteriorCotangentSheaf f (q+1)) :=
  (formIso p v hv q).hom ≫
    (tilde.functor T).map (SchemeRelativeFrobeniusAffineDeRham.differential v hv p q) ≫
      (formIso p v hv (q+1)).inv

/-- The entire original affine differential square commutes in the actual native category. -/
theorem differential_comm (q : ℕ) :
    differential p v hv q ≫ (formIso p v hv (q+1)).hom =
      (formIso p v hv q).hom ≫
        (tilde.functor T).map (SchemeRelativeFrobeniusAffineDeRham.differential v hv p q) := by
  exact conjugate_comm (formIso p v hv q) (formIso p v hv (q+1))
    ((tilde.functor T).map (SchemeRelativeFrobeniusAffineDeRham.differential v hv p q))

/-- Square zero holds on the actual whole original pushed sheaves. -/
theorem differential_square (q : ℕ) :
    differential p v hv q ≫ differential p v hv (q+1) = 0 := by
  have h : SchemeRelativeFrobeniusAffineDeRham.differential v hv p q ≫
      SchemeRelativeFrobeniusAffineDeRham.differential v hv p (q+1) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    exact EtaleDeRham.differential_square v hv q w
  have hm := ((tilde.functor T).map_comp
    (SchemeRelativeFrobeniusAffineDeRham.differential v hv p q)
    (SchemeRelativeFrobeniusAffineDeRham.differential v hv p (q+1))).symm.trans
      ((congrArg (tilde.functor T).map h).trans AlgebraicGeometry.tilde.map_zero)
  exact conjugate_square (formIso p v hv q) (formIso p v hv (q+1))
    (formIso p v hv (q+1+1))
    ((tilde.functor T).map (SchemeRelativeFrobeniusAffineDeRham.differential v hv p q))
    ((tilde.functor T).map (SchemeRelativeFrobeniusAffineDeRham.differential v hv p (q+1)))
    hm

/-- The genuine complex of original relative-Frobenius-pushed exterior sheaves. -/
def complex : CochainComplex (Spec T).Modules ℕ :=
  CochainComplex.of
    (fun q => (Scheme.Modules.pushforward g).obj (CanonicalGeometry.exteriorCotangentSheaf f q))
    (differential p v hv) (differential_square p v hv)

/-- The actual associated-sheaf image of the same original native relative complex. -/
def associatedComplex : CochainComplex (Spec T).Modules ℕ := by
  let J := tilde.functor T
  letI : J.PreservesZeroMorphisms := ⟨fun _ _ => AlgebraicGeometry.tilde.map_zero⟩
  exact (J.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (SchemeRelativeFrobeniusAffineDeRham.complex v hv p)

/-- The actual entire affine complex comparison keeps every original differential. -/
def complexIso : complex p v hv ≅ associatedComplex p v hv := by
  let J := tilde.functor T
  letI : J.PreservesZeroMorphisms := ⟨fun _ _ => AlgebraicGeometry.tilde.map_zero⟩
  refine HomologicalComplex.Hom.isoOfComponents (fun q => formIso p v hv q) ?_
  intro q r h
  have hr : q+1 = r := h
  subst r
  simp only [complex, associatedComplex, SchemeRelativeFrobeniusAffineDeRham.complex,
    Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d]
  exact (differential_comm p v hv q).symm

set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
#check @conjugate_comm
#print axioms conjugate_comm
#check @conjugate_square
#print axioms conjugate_square
#check @formIso
#print axioms formIso
#check @differential
#print axioms differential
#check @differential_comm
#print axioms differential_comm
#check @differential_square
#print axioms differential_square
#check @complex
#print axioms complex
#check @associatedComplex
#print axioms associatedComplex
#check @complexIso
#print axioms complexIso
end EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineSheafDeRham
