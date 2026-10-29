/-
Mathlib-only proof port. Original source: EnvelopeProperty/ComplexGeometry/Schemes/BundleTensorLocalization.lean
Upstream SHA256: f65dd9bd69b3102a495e61e48129b1272d5e37c5ea2e67c4432812741ccf69bc
Upstream canonical-source commit: feaaab87c3197e6e4f18c6176d50b5c739c81b50
Compatibility changes: module imports and enclosing namespace only.
Original mathematical statements and proofs below are preserved.
-/
import EnvelopeProperty.AlgGeom.Canonical.LineBundleSections
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.Algebra.Category.Grp.FilteredColimits

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace EnvelopeProperty.CanonicalGeometry

noncomputable section

variable {X : Scheme.{u}}

/-- Actual presheaf restriction to the site of opens contained in `U`. -/
abbrev bundlePresheafOver (P : X.PresheafOfModules) (U : X.Opens) :
    PresheafOfModules.{u} (X.ringCatSheaf.over U).obj :=
  (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).obj P

/-- Restrict the actual sheafification unit to the open site. -/
def bundleSheafificationOverMap (P : X.PresheafOfModules) (U : X.Opens) :
    bundlePresheafOver P U ⟶
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U |>.val :=
  (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)

/-- Its underlying abelian-presheaf map is the literal restricted unit. -/
theorem bundleSheafificationOverMap_underlying (P : X.PresheafOfModules) (U : X.Opens) :
    (PresheafOfModules.toPresheaf _).map (bundleSheafificationOverMap P U) =
      Functor.whiskerLeft (Over.forget U).op
        ((PresheafOfModules.toPresheaf _).map
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)) := rfl

/-- Local bijectivity of sheafification survives genuine open restriction. -/
theorem bundleSheafificationOverMap_locally_bijective (P : X.PresheafOfModules) (U : X.Opens) :
    Presheaf.IsLocallyInjective ((_root_.Opens.grothendieckTopology X).over U)
      ((PresheafOfModules.toPresheaf _).map (bundleSheafificationOverMap P U)) ∧
    Presheaf.IsLocallySurjective ((_root_.Opens.grothendieckTopology X).over U)
      ((PresheafOfModules.toPresheaf _).map (bundleSheafificationOverMap P U)) := by
  rw [bundleSheafificationOverMap_underlying,
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  have hinj : Presheaf.IsLocallyInjective (_root_.Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X) P.presheaf) :=
    ((_root_.Opens.grothendieckTopology X).W_toSheafify P.presheaf).isLocallyInjective
  have hsurj : Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X) P.presheaf) :=
    ((_root_.Opens.grothendieckTopology X).W_toSheafify P.presheaf).isLocallySurjective
  constructor
  · exact ⟨fun x y h => (Over.forget U).cover_lift _ _
      (hinj.equalizerSieve_mem x y h)⟩
  · exact ⟨fun s => (Over.forget U).cover_lift _ _ (hsurj.imageSieve_mem s)⟩

/-- Sheafification on the open site inverts the restricted unit. -/
theorem bundleSheafificationOverMap_becomes_iso (P : X.PresheafOfModules) (U : X.Opens) :
    IsIso ((PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).map
      (bundleSheafificationOverMap P U)) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (X.ringCatSheaf.over U))]
  change IsIso ((presheafToSheaf ((_root_.Opens.grothendieckTopology X).over U)
    AddCommGrpCat).map ((PresheafOfModules.toPresheaf _).map
      (bundleSheafificationOverMap P U)))
  rw [← GrothendieckTopology.W_iff]
  exact (GrothendieckTopology.W_iff_isLocallyBijective _ _).2
    (bundleSheafificationOverMap_locally_bijective P U)

/-- The actual sheafification counit on an open site is an isomorphism. -/
def bundleOverCounitIso (U : X.Opens)
    (S : SheafOfModules.{u} (X.ringCatSheaf.over U)) :
    (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).obj S.val ≅ S := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf.over U) (𝟙 (X.ringCatSheaf.over U).obj)
  have : IsIso adj.counit := by dsimp [adj]; infer_instance
  exact (asIso adj.counit).app S

/-- Sheafification of a module presheaf commutes with restriction to any open. -/
def bundleOverSheafificationIso (P : X.PresheafOfModules) (U : X.Opens) :
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U ≅
      (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).obj
        (bundlePresheafOver P U) := by
  have := bundleSheafificationOverMap_becomes_iso P U
  exact (asIso ((PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).map
    (bundleSheafificationOverMap P U)) ≪≫
    bundleOverCounitIso U
      (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U)).symm

local instance (U : X.Opens) :
    MonoidalCategory (PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
  PresheafOfModules.monoidalCategory (R := (Over.forget U).op ⋙ X.sheaf.obj)

local instance (U : X.Opens) (V : (Over U)ᵒᵖ) :
    CommRing (((Over.forget U).op ⋙ X.ringCatSheaf.obj).obj V) :=
  inferInstanceAs (CommRing (X.sheaf.obj.obj ((Over.forget U).op.obj V)))

/-- Objectwise tensor of the actual restricted module sheaves. -/
def bundleOverTensorPresheaf (L N : X.Modules) (U : X.Opens) :
    PresheafOfModules.{u} (X.ringCatSheaf.over U).obj :=
  PresheafOfModules.Monoidal.tensorObj (R := (Over.forget U).op ⋙ X.sheaf.obj)
    (L.over U).val (N.over U).val

set_option backward.isDefEq.respectTransparency false in
/-- Restriction commutes with the objectwise module tensor presheaf. -/
def bundleOverTensorPresheafIso (L N : X.Modules) (U : X.Opens) :
    bundlePresheafOver (bundleTensorPresheaf L N) U ≅ bundleOverTensorPresheaf L N U :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun V _ _ => by
    apply ModuleCat.MonoidalCategory.tensor_ext
      (R := X.sheaf.obj.obj ((Over.forget U).op.obj V))
    intro s t
    rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Tensor two genuine frames on the same open, using restriction and
sheafification rather than a global trivialization. -/
def LocalBundleFrame.tensor {L N : X.Modules} {U : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame N U) :
    LocalBundleFrame (bundleTensor L N) U :=
  bundleOverSheafificationIso (bundleTensorPresheaf L N) U ≪≫
    (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).mapIso
      (bundleOverTensorPresheafIso L N U ≪≫
        MonoidalCategory.tensorIso ((SheafOfModules.forget _).mapIso e)
          ((SheafOfModules.forget _).mapIso f) ≪≫
        MonoidalCategory.leftUnitor (SheafOfModules.unit (X.ringCatSheaf.over U)).val) ≪≫
    bundleOverCounitIso U (SheafOfModules.unit (X.ringCatSheaf.over U))

/-- A frame on an open constructs frames of every actual tensor power there. -/
def LocalBundleFrame.tensorPower {L : X.Modules} {U : X.Opens}
    (e : LocalBundleFrame L U) : ∀ n, LocalBundleFrame (bundleTensorPower L n) U
  | 0 => Iso.refl _
  | n + 1 => (e.tensorPower n).tensor e

/-- Every tensor power of a line-bundle atlas uses its original genuine open
cover; no global trivialization is assumed. -/
def LineBundleAtlas.tensorPower {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ) :
    LineBundleAtlas (bundleTensorPower L n) where
  I := a.I
  opens := a.opens
  covers := a.covers
  frame i := (a.frame i).tensorPower n

/-- Intrinsic tensor powers of an arbitrary locally trivial line bundle. -/
def IntrinsicLineBundle.tensorPower (L : IntrinsicLineBundle X) (n : ℕ) :
    IntrinsicLineBundle X where
  sheaf := bundleTensorPower L.sheaf n
  atlas := L.atlas.tensorPower n

end

end EnvelopeProperty.CanonicalGeometry
