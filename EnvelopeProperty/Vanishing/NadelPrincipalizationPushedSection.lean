import EnvelopeProperty.Vanishing.NadelPrincipalizationOpenPushforwardMates
import EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeRoundedSection
import EnvelopeProperty.Char0.RoundedCanonicalKernelModuleMap

/-! # Whole original rounded pushforwards with the actual differential section -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationPushedSection
open Char0.RoundedCanonicalModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y X Y' X' : Scheme.{u}} (p : Y ⟶ X) (p' : Y' ⟶ X')
    (v : Y' ⟶ Y) (g : X' ⟶ X) [IsOpenImmersion v] [IsOpenImmersion g]
    (H : IsPullback p' v g p)

/-- Actual open Cartesian base change followed by a proved original source comparison. -/
def transportIso (M : Y.Modules) (M' : Y'.Modules) (e : (pullback v).obj M ≅ M') :
    (pullback g).obj ((pushforward p).obj M) ≅ (pushforward p').obj M' :=
  NadelPrincipalizationOpenPushforward.openIso p p' v g H M ≪≫ (pushforward p').mapIso e

/-- Whole inclusion functoriality of that actual original Cartesian comparison. -/
theorem transportIso_inclusion (M N : Y.Modules) (M' N' : Y'.Modules)
    (eM : (pullback v).obj M ≅ M') (eN : (pullback v).obj N ≅ N')
    (φ : M ⟶ N) (φ' : M' ⟶ N')
    (he : eM.hom ≫ φ' = (pullback v).map φ ≫ eN.hom) :
    (transportIso p p' v g H M M' eM).hom ≫ (pushforward p').map φ' =
      (pullback g).map ((pushforward p).map φ) ≫ (transportIso p p' v g H N N' eN).hom := by
  change (NadelPrincipalizationOpenPushforward.openIso p p' v g H M).hom ≫
      (pushforward p').map eM.hom ≫ (pushforward p').map φ' = _
  rw [← (pushforward p').map_comp, he, (pushforward p').map_comp]
  simpa only [transportIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using
    congrArg (fun z => z ≫ (pushforward p').map eN.hom)
      (NadelPrincipalizationOpenPushforward.openIso_naturality p p' v g H φ).symm

/-- A PROVED entire original section triangle is carried through the SAME
native adjunction and actual Cartesian comparison. -/
theorem transportIso_section (M : Y.Modules) (M' : Y'.Modules)
    (e : (pullback v).obj M ≅ M') (δ : unitObj Y ⟶ M) (ε : unitObj Y' ⟶ M')
    (hδ : (pullbackUnitIso v).inv ≫ (pullback v).map δ ≫ e.hom = ε) :
    (pullbackUnitIso g).inv ≫
      (pullback g).map ((pullbackPushforwardAdjunction p).homEquiv _ _
        ((pullbackUnitIso p).hom ≫ δ)) ≫ (transportIso p p' v g H M M' e).hom =
      (pullbackPushforwardAdjunction p').homEquiv _ _ ((pullbackUnitIso p').hom ≫ ε) := by
  change ((pullbackUnitIso g).inv ≫ (pullback g).map _ ≫
      (NadelPrincipalizationOpenPushforward.openIso p p' v g H M).hom) ≫
      (pushforward p').map e.hom = _
  rw [NadelPrincipalizationOpenPushforward.adjointSection_triangle]
  rw [show (pullbackUnitIso p').hom ≫ (pullbackUnitIso v).inv ≫ (pullback v).map δ =
      (pullbackUnitIso p').hom ≫ ((pullbackUnitIso v).inv ≫ (pullback v).map δ) from rfl,
    pushforwardUnitSection_homEquiv, pushforwardUnitSection_homEquiv]
  rw [Category.assoc, ← Functor.map_comp, Category.assoc, hδ]

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f]

private theorem base_smooth : SmoothOfRelativeDimension n (g ≫ f) :=
  (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp (f := g) (n := 0) (m := n) f)

/-- Whole original relative-canonical pushforward compared by the actual
internally proved differential-compatible line comparison. -/
def relativeIso :
    (pullback g).obj ((pushforward p).obj (relative f p n)) ≅
      (pushforward p').obj (relative (g ≫ f) p' n) :=
  transportIso p p' v g H _ _
    (NadelPrincipalizationRelativeSection.relativeIso f g p p' v H.w n)

/-- The SAME original whole pushed differential section is preserved. -/
theorem relativeIso_section :
    letI := base_smooth g f n
    (pullbackUnitIso g).inv ≫ (pullback g).map (pushedDifferentialSection f p n) ≫
      (relativeIso p p' v g H f n).hom = pushedDifferentialSection (g ≫ f) p' n := by
  let := base_smooth g f n
  exact transportIso_section p p' v g H _ _
    (NadelPrincipalizationRelativeSection.relativeIso f g p p' v H.w n)
    (differentialSection f p n) (differentialSection (g ≫ f) p' n)
    (NadelPrincipalizationRelativeSection.relativeIso_section f g p p' v H.w n)

variable [CharZero k] [Smooth (p ≫ f)] (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)

/-- SAME whole original rounded pushforward, with all original ideal data. -/
def roundedIso :
    (pullback g).obj ((pushforward p).obj (relativeRounded f p n J hJ q)) ≅
      (pushforward p').obj (relativeRounded (g ≫ f) p' n (J.comap v)
        (hJ.comap_of_smooth (p ≫ f) v) q) :=
  transportIso p p' v g H _ _
    (NadelPrincipalizationRelativeRoundedSection.roundedIso f g p p' v H.w n J hJ q)

/-- Both the whole original rounded inclusion and its whole original
relative-canonical target are retained by the same comparisons. -/
theorem roundedIso_inclusion :
    (roundedIso p p' v g H f n J hJ q).hom ≫ (pushforward p').map
      (relativeRoundedInclusion (g ≫ f) p' n (J.comap v)
        (hJ.comap_of_smooth (p ≫ f) v) q) =
    (pullback g).map ((pushforward p).map (relativeRoundedInclusion f p n J hJ q)) ≫
      (relativeIso p p' v g H f n).hom :=
  transportIso_inclusion p p' v g H _ _ _ _
    (NadelPrincipalizationRelativeRoundedSection.roundedIso f g p p' v H.w n J hJ q)
    (NadelPrincipalizationRelativeSection.relativeIso f g p p' v H.w n) _ _
    (NadelPrincipalizationRelativeRoundedSection.roundedIso_inclusion f g p p' v H.w n J hJ q)

end EnvelopeProperty.Vanishing.NadelPrincipalizationPushedSection
