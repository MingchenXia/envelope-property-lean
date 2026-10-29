import EnvelopeProperty.Cartier.RelativeCartierContinuationAffineGeometricTwist

/-! # The actual affine relative Frobenius and its zero-safe section-ring map

The source is the genuine geometric relative Frobenius. Both actual projection
and section-ring triangles are derived, with no CharP instance on a zero ring.
Route: `blueprint/src/smooth-scheme-relative-frobenius-complex.tex`.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineMap
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
variable {k B : Type u} [Field k] [CommRing B]
variable (α : k →+* B) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "T" => RelativeFrobenius.twist α p
local notation "f" => Spec.map (CommRingCat.ofHom α)
local notation "F" => SchemeRelativeFrobenius.baseMap (k := k) p

/-- The genuine relative Frobenius in the actual native affine twist chart. -/
def affineMap : Spec (CommRingCat.of B) ⟶ Spec T :=
  SchemeRelativeFrobenius.map p f ≫ (RelativeAffineGeometricTwist.affineTwistIso α p).inv

/-- Its entire original source projection is the actual absolute Frobenius. -/
theorem affineMap_source :
    affineMap α p ≫ Spec.map (RelativeFrobenius.sourceMap α p) =
      SchemeFrobenius.map f p := by
  rw [affineMap, Category.assoc, RelativeAffineGeometricTwist.affineTwistIso_inv_source,
    SchemeRelativeFrobenius.map_fst]

/-- Its entire original coefficient projection is the actual structural morphism. -/
theorem affineMap_coefficient :
    affineMap α p ≫ Spec.map (RelativeFrobenius.coefficientMap α p) = f := by
  rw [affineMap, Category.assoc, RelativeAffineGeometricTwist.affineTwistIso_inv_coefficient,
    SchemeRelativeFrobenius.map_snd]

/-- The actual relative scheme section map in the SAME native ring coordinates. -/
def ringMap : T ⟶ CommRingCat.of B :=
  (RelativeAffineGeometricTwist.sectionsIso α p).inv ≫
    (SchemeRelativeFrobenius.map p f).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom

/-- The actual absolute scheme section map in the original affine ring coordinates. -/
def absoluteRingMap : CommRingCat.of B ⟶ CommRingCat.of B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
    (SchemeFrobenius.map f p).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom

/-- The entire relative coefficient ring-map triangle includes zero endpoints. -/
theorem coefficient_ringMap :
    RelativeFrobenius.coefficientMap α p ≫ ringMap α p = CommRingCat.ofHom α := by
  rw [← RelativeAffineGeometricTwist.sectionsIso_coefficient α p]
  dsimp only [ringMap]
  simp only [Category.assoc]
  erw [Category.assoc (pullback.snd f F).appTop
      (RelativeAffineGeometricTwist.sectionsIso α p).hom
      ((RelativeAffineGeometricTwist.sectionsIso α p).inv ≫
        (SchemeRelativeFrobenius.map p f).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom),
    Iso.hom_inv_id_assoc]
  erw [← Category.assoc (pullback.snd f F).appTop (SchemeRelativeFrobenius.map p f).appTop
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom,
    ← Scheme.Hom.comp_appTop, SchemeRelativeFrobenius.map_snd,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- The entire source composite is the SAME actual absolute section map. -/
theorem source_ringMap :
    RelativeFrobenius.sourceMap α p ≫ ringMap α p = absoluteRingMap α p := by
  rw [← RelativeAffineGeometricTwist.sectionsIso_source α p]
  dsimp only [ringMap, absoluteRingMap]
  simp only [Category.assoc]
  erw [Category.assoc (pullback.fst f F).appTop
      (RelativeAffineGeometricTwist.sectionsIso α p).hom
      ((RelativeAffineGeometricTwist.sectionsIso α p).inv ≫
        (SchemeRelativeFrobenius.map p f).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom),
    Iso.hom_inv_id_assoc]
  erw [← Category.assoc (pullback.fst f F).appTop (SchemeRelativeFrobenius.map p f).appTop
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom,
    ← Scheme.Hom.comp_appTop, SchemeRelativeFrobenius.map_fst]

/-- Every original affine element has its actual pth power, including on a zero ring. -/
theorem absoluteRingMap_apply (b : B) : (absoluteRingMap α p).hom b = b ^ p := by
  have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
    (SchemeFrobenius.map_app f p ⊤ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b))
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
      ((SchemeFrobenius.map f p).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) =
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
      (((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) ^ p) at h
  simpa only [absoluteRingMap, CommRingCat.hom_comp, RingHom.comp_apply,
    map_pow, Iso.inv_hom_id_apply] using h

/-- Every actual source element retains its original pth-power value. -/
theorem source_ringMap_apply (b : B) :
    (ringMap α p).hom ((RelativeFrobenius.sourceMap α p).hom b) = b ^ p := by
  have h := congrArg (fun g : CommRingCat.of B ⟶ CommRingCat.of B => g.hom b)
    (source_ringMap α p)
  exact h.trans (absoluteRingMap_apply α p b)

set_option pp.universes true
set_option pp.deepTerms true
#check @affineMap
#print axioms affineMap
#check @affineMap_source
#print axioms affineMap_source
#check @affineMap_coefficient
#print axioms affineMap_coefficient
#check @ringMap
#print axioms ringMap
#check @absoluteRingMap
#print axioms absoluteRingMap
#check @coefficient_ringMap
#print axioms coefficient_ringMap
#check @source_ringMap
#print axioms source_ringMap
#check @absoluteRingMap_apply
#print axioms absoluteRingMap_apply
#check @source_ringMap_apply
#print axioms source_ringMap_apply
end EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineMap
