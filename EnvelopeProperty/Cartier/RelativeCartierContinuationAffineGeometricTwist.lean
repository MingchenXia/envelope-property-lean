import EnvelopeProperty.Cartier.SchemeRelativeFrobenius
import EnvelopeProperty.Cartier.RelativeFrobenius

/-! # The actual affine geometric Frobenius twist is the SAME native pushout

Both original projections and their actual global-section maps are retained.
The endpoint ring may be zero; no characteristic instance on it is required.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeAffineGeometricTwist
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
variable {k B : Type u} [Field k] [CommRing B]
variable (α : k →+* B) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "T" => RelativeFrobenius.twist α p
local notation "s" => RelativeFrobenius.sourceMap α p
local notation "c" => RelativeFrobenius.coefficientMap α p
local notation "f" => Spec.map (CommRingCat.ofHom α)
local notation "F" => SchemeRelativeFrobenius.baseMap (k := k) p
local notation "Y" => SchemeRelativeFrobenius.twist p f

/-- The native spectrum of the ORIGINAL ring pushout is a true geometric pullback,
with the actual original source and coefficient projections, including zero endpoints. -/
theorem nativeIsPullback : IsPullback (Spec.map s) (Spec.map c) f F := by
  rw [SchemeRelativeFrobenius.baseMap_eq_spec]
  exact (isPullback_SpecMap_pushout (CommRingCat.ofHom (frobenius k p))
    (CommRingCat.ofHom α)).flip

/-- The SAME actual geometric scheme twist is genuinely the spectrum of the native twist. -/
def affineTwistIso : Spec T ≅ Y := (nativeIsPullback α p).isoPullback

/-- The ENTIRE first projection is the original source-inclusion spectrum map. -/
theorem affineTwistIso_hom_fst :
    (affineTwistIso α p).hom ≫ pullback.fst f F = Spec.map s :=
  (nativeIsPullback α p).isoPullback_hom_fst

/-- The ENTIRE structural coefficient projection is the original coefficient-inclusion map. -/
theorem affineTwistIso_hom_snd :
    (affineTwistIso α p).hom ≫ pullback.snd f F = Spec.map c :=
  (nativeIsPullback α p).isoPullback_hom_snd

/-- The actual inverse preserves the SAME entire source projection. -/
theorem affineTwistIso_inv_source :
    (affineTwistIso α p).inv ≫ Spec.map s = pullback.fst f F :=
  (nativeIsPullback α p).isoPullback_inv_fst

/-- The actual inverse preserves the SAME entire structural coefficient projection. -/
theorem affineTwistIso_inv_coefficient :
    (affineTwistIso α p).inv ≫ Spec.map c = pullback.snd f F :=
  (nativeIsPullback α p).isoPullback_inv_snd

/-- Genuine global sections of the ACTUAL geometric twist have the SAME native ring. -/
def sectionsIso : Γ(Y, ⊤) ≅ T :=
  Scheme.Γ.mapIso (affineTwistIso α p).op ≪≫ Scheme.ΓSpecIso T

/-- The actual entire first-projection section map retains the ORIGINAL source inclusion. -/
theorem sectionsIso_source :
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (pullback.fst f F).appTop ≫
      (sectionsIso α p).hom = s := by
  change (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (pullback.fst f F).appTop ≫
    (affineTwistIso α p).hom.appTop ≫ (Scheme.ΓSpecIso T).hom = s
  erw [← Category.assoc (pullback.fst f F).appTop (affineTwistIso α p).hom.appTop
    (Scheme.ΓSpecIso T).hom,
    ← Scheme.Hom.comp_appTop (affineTwistIso α p).hom (pullback.fst f F),
    affineTwistIso_hom_fst α p, Scheme.ΓSpecIso_naturality s, Iso.inv_hom_id_assoc]

/-- The ACTUAL structural coefficient map on the true geometric twist retains EVERY
original coefficient under the SAME native section-ring isomorphism. -/
theorem sectionsIso_coefficient :
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (pullback.snd f F).appTop ≫
      (sectionsIso α p).hom = c := by
  change (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (pullback.snd f F).appTop ≫
    (affineTwistIso α p).hom.appTop ≫ (Scheme.ΓSpecIso T).hom = c
  erw [← Category.assoc (pullback.snd f F).appTop (affineTwistIso α p).hom.appTop
    (Scheme.ΓSpecIso T).hom,
    ← Scheme.Hom.comp_appTop (affineTwistIso α p).hom (pullback.snd f F),
    affineTwistIso_hom_snd α p, Scheme.ΓSpecIso_naturality c, Iso.inv_hom_id_assoc]

end EnvelopeProperty.Cartier.RelativeAffineGeometricTwist
