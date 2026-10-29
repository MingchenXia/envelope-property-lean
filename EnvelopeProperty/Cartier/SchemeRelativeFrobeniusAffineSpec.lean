import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineMap

/-! # The genuine relative Frobenius is the spectrum of its actual ring map

Whole scheme-map identities retain zero endpoints and precede all native module
pushforward comparisons. Route: smooth-scheme-relative-frobenius-complex.tex.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineMap
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
variable {k B : Type u} [Field k] [CommRing B]
variable (α : k →+* B) (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The actual ring map is the spectrum-section conjugate of the same whole
affine scheme morphism, without any nonzero or chart premise. -/
theorem ringMap_eq_conjugate_affineMap :
    ringMap α p = (Scheme.ΓSpecIso (RelativeFrobenius.twist α p)).inv ≫
      (affineMap α p).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom := by
  change ((Scheme.ΓSpecIso (RelativeFrobenius.twist α p)).inv ≫
      (RelativeAffineGeometricTwist.affineTwistIso α p).inv.appTop) ≫
        (SchemeRelativeFrobenius.map p (Spec.map (CommRingCat.ofHom α))).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
    (Scheme.ΓSpecIso (RelativeFrobenius.twist α p)).inv ≫
      (SchemeRelativeFrobenius.map p (Spec.map (CommRingCat.ofHom α)) ≫
        (RelativeAffineGeometricTwist.affineTwistIso α p).inv).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of B)).hom
  simp only [Scheme.Hom.comp_appTop, Category.assoc]

/-- The entire actual affine relative Frobenius is the native spectrum map of
its own genuine zero-safe section-ring map. -/
theorem affineMap_eq_spec_ringMap : affineMap α p = Spec.map (ringMap α p) := by
  obtain ⟨g, hg⟩ := Spec.map_surjective (affineMap α p)
  have hβ : ringMap α p = g := by
    rw [ringMap_eq_conjugate_affineMap, ← hg,
      Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [hβ]
  exact hg.symm

/-- The original geometric relative Frobenius is the same entire spectrum map
followed by its internally constructed genuine affine twist chart. -/
theorem map_eq_spec_ringMap_chart :
    SchemeRelativeFrobenius.map p (Spec.map (CommRingCat.ofHom α)) =
      Spec.map (ringMap α p) ≫ (RelativeAffineGeometricTwist.affineTwistIso α p).hom := by
  rw [← affineMap_eq_spec_ringMap, affineMap, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
#check @ringMap_eq_conjugate_affineMap
#print axioms ringMap_eq_conjugate_affineMap
#check @affineMap_eq_spec_ringMap
#print axioms affineMap_eq_spec_ringMap
#check @map_eq_spec_ringMap_chart
#print axioms map_eq_spec_ringMap_chart
end EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineMap
