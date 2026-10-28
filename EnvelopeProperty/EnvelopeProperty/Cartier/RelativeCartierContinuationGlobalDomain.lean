import EnvelopeProperty.Cartier.RelativeFrobenius
import EnvelopeProperty.AlgGeom.Canonical.ExteriorSheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-! # The genuine global source-restricted native Cartier domain

The twist is an actual pushout of ring presheaves. Its cotangent exterior
presheaf is restricted along the original source inclusion, then sheafified.
No section-ring characteristic, chart, perfection or global comparison is assumed.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeGlobalCartierDomain
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The actual original coefficient Frobenius as a whole constant-presheaf map. -/
def constantFrobenius : CanonicalGeometry.constantRingPresheaf k X ⟶
    CanonicalGeometry.constantRingPresheaf k X :=
  (Functor.const X.Opensᵒᵖ).map (CommRingCat.ofHom (frobenius k p))

/-- The actual native Frobenius pushout in the category of ring presheaves. -/
def twistPresheaf : X.Opensᵒᵖ ⥤ CommRingCat.{u} :=
  pushout (constantFrobenius (k := k) (X := X) p)
    (CanonicalGeometry.schemeConstantPresheafMap f)

/-- The original coefficient inclusion as an actual natural transformation. -/
def coefficientMap : CanonicalGeometry.constantRingPresheaf k X ⟶ twistPresheaf f p :=
  pushout.inl _ _

/-- The original source inclusion as an actual natural transformation. -/
def sourceMap : X.presheaf ⟶ twistPresheaf f p :=
  pushout.inr _ _

/-- The entire original native pushout relation, with no square supplied. -/
theorem pushout_condition : constantFrobenius (k := k) (X := X) p ≫ coefficientMap f p =
    CanonicalGeometry.schemeConstantPresheafMap f ≫ sourceMap f p :=
  pushout.condition

/-- Evaluation gives the SAME native affine twist from the actual structural map,
including on zero section rings. -/
def evaluationIso (U : X.Opensᵒᵖ) : (twistPresheaf f p).obj U ≅
    RelativeFrobenius.twist (A := k) ((CanonicalGeometry.schemeConstantPresheafMap f).app U).hom p :=
  pushoutObjIso (constantFrobenius (k := k) (X := X) p)
    (CanonicalGeometry.schemeConstantPresheafMap f) U

/-- The genuine evaluation isomorphism preserves the entire original coefficient map. -/
theorem coefficientMap_evaluationIso (U : X.Opensᵒᵖ) :
    (coefficientMap f p).app U ≫ (evaluationIso f p U).hom =
      RelativeFrobenius.coefficientMap (A := k) ((CanonicalGeometry.schemeConstantPresheafMap f).app U).hom p :=
  inl_comp_pushoutObjIso_hom _ _ U

/-- The genuine evaluation isomorphism preserves the entire original source map. -/
theorem sourceMap_evaluationIso (U : X.Opensᵒᵖ) :
    (sourceMap f p).app U ≫ (evaluationIso f p U).hom =
      RelativeFrobenius.sourceMap (A := k) ((CanonicalGeometry.schemeConstantPresheafMap f).app U).hom p :=
  inr_comp_pushoutObjIso_hom _ _ U

/-- The actual relative cotangent presheaf of the original coefficient inclusion. -/
def cotangentPresheaf : PresheafOfModules.{u} (twistPresheaf f p ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials' (coefficientMap f p)

/-- The genuine universal derivation of the actual twist ring presheaf over k. -/
def cotangentDerivation : (cotangentPresheaf f p).Derivation' (coefficientMap f p) :=
  PresheafOfModules.DifferentialsConstruction.derivation' (coefficientMap f p)

/-- Actual universal factorization and uniqueness, derived objectwise. -/
def cotangentUniversal : (cotangentDerivation f p).Universal :=
  PresheafOfModules.DifferentialsConstruction.isUniversal' (coefficientMap f p)

/-- The coefficient algebra is the actual original inclusion on each open. -/
@[instance_reducible]
def coefficientAlgebra (U : X.Opensᵒᵖ) : Algebra k ((twistPresheaf f p).obj U) :=
  ((coefficientMap f p).app U).hom.toAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The actual cotangent presheaf has the ordinary coefficient-relative Kaehler module
on each open, with its genuine original coefficient algebra. -/
def cotangentSectionsEquiv (U : X.Opensᵒᵖ) :
    letI := coefficientAlgebra f p U
    (cotangentPresheaf f p).obj U ≃ₗ[(twistPresheaf f p).obj U]
      KaehlerDifferential k ((twistPresheaf f p).obj U) := by
  letI := coefficientAlgebra f p U
  exact LinearEquiv.refl _ _

/-- All actual exterior degrees of the genuine twist cotangent presheaf. -/
def exteriorPresheaf (q : ℕ) :
    PresheafOfModules.{u} (twistPresheaf f p ⋙ forget₂ CommRingCat RingCat) :=
  CanonicalGeometry.exteriorPresheaf (cotangentPresheaf f p) q

/-- The original source inclusion as a morphism of native ring presheaves. -/
def sourceRingMap : X.presheaf ⋙ forget₂ CommRingCat RingCat ⟶
    twistPresheaf f p ⋙ forget₂ CommRingCat RingCat :=
  Functor.whiskerRight (sourceMap f p) (forget₂ CommRingCat RingCat)

/-- The CORRECT source-restricted exterior presheaf as a genuine O_X-module presheaf. -/
def domainPresheaf (q : ℕ) : X.PresheafOfModules :=
  (PresheafOfModules.restrictScalars (sourceRingMap f p)).obj (exteriorPresheaf f p q)

/-- Actual restrictions retain the full original exterior wedge, including degree zero. -/
theorem exterior_restriction_wedge (q : ℕ) {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (m : Fin q → (cotangentPresheaf f p).obj U) :
    (domainPresheaf f p q).map i (exteriorPower.ιMulti ((twistPresheaf f p).obj U) q m) =
      exteriorPower.ιMulti ((twistPresheaf f p).obj V) q
        (fun j => (cotangentPresheaf f p).map i (m j)) :=
  CanonicalGeometry.exteriorPresheaf_map_mk (cotangentPresheaf f p) q i m

/-- Actual module sheafification of the corrected source in every degree. -/
def domainSheaf (q : ℕ) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (domainPresheaf f p q)

/-- The genuine adjunction unit is a whole presheaf map into the corrected source sheaf. -/
def sheafificationMap (q : ℕ) : domainPresheaf f p q ⟶
    (Scheme.Modules.toPresheafOfModules X).obj (domainSheaf f p q) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (domainPresheaf f p q)

end EnvelopeProperty.Cartier.RelativeGlobalCartierDomain
