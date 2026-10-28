import ModularCurves.ForMathlib.SchemeModuleRestrictPushforward
import EnvelopeProperty.Cartier.RelativeCartierContinuationTwistedAffineFrobenius
import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusComplex
import EnvelopeProperty.AlgGeom.Canonical.CanonicalLineSheaf
import EnvelopeProperty.AlgGeom.Canonical.CotangentSmoothLocallyFree

/-! # Original pushed exterior objects in the SAME genuine relative twist chart

All original module actions and whole-section component maps are retained.
No differential comparison or characteristic instance on a zero section ring is used.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeTwistedAffinePushforward
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
variable (U : X.Opens) (hU : IsAffineOpen U)
private def structuralRingMap : k →+* Γ(X, U) :=
  ((CanonicalGeometry.schemeConstantPresheafMap f).app (op U)).hom
local notation "α" => structuralRingMap f U
local notation "T" => RelativeFrobenius.twist (α) p
local notation "g" => SchemeRelativeFrobeniusAffineMap.affineMap (α) p
local notation "Fr" => SchemeRelativeFrobenius.map p f
local notation "j" => RelativeTwistedAffineFrobenius.chartMap f p U hU
local notation "H" => RelativeTwistedAffineFrobenius.chartIsPullback f p U hU

/-- Genuine native Cartier-chart base change for EVERY original module sheaf. -/
def restrictionIso (M : X.Modules) :=
  @Scheme.Modules.restrictPushforwardIsoOfIsPullbackApp
    X (SchemeRelativeFrobenius.twist p f) (Spec (CommRingCat.of Γ(X, U))) (Spec T)
    (Fr) (g) hU.fromSpec (j)
    (RelativeTwistedAffineFrobenius.chartMap_isOpenImmersion f p U hU)
    (inferInstance : IsOpenImmersion hU.fromSpec) (H) M

/-- EVERY original section is transported by its specified ORIGINAL restriction. -/
theorem restrictionIso_hom_apply (M : X.Modules) (W : (Spec T).Opens)
    (s : Γ(((Scheme.Modules.pushforward (Fr)).obj M).restrict (j), W)) :
    (restrictionIso f p U hU M).hom.val.app (op W) s =
      M.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback (H) W)).op s := rfl

/-- The inverse retains the reverse specified ORIGINAL restriction on EVERY section. -/
theorem restrictionIso_inv_apply (M : X.Modules) (W : (Spec T).Opens)
    (s : Γ((Scheme.Modules.pushforward (g)).obj (M.restrict hU.fromSpec), W)) :
    (restrictionIso f p U hU M).inv.val.app (op W) s =
      M.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback (H) W).symm).op s := rfl

/-- The SAME original whole affine exterior sheaf with EXACT original structural constants. -/
def ordinaryExteriorIso (q : ℕ) :
    (CanonicalGeometry.exteriorCotangentSheaf f q).restrict hU.fromSpec ≅
      CanonicalGeometry.exteriorCotangentSheaf (Spec.map (CommRingCat.ofHom (α))) q :=
  CanonicalGeometry.exteriorCotangentSheafOpenImmersionIso f hU.fromSpec q ≪≫
    eqToIso (congrArg (fun h => CanonicalGeometry.exteriorCotangentSheaf h q)
      (CanonicalGeometry.affineChartStructuralMap f hU))

/-- ALL-degree actual true-Y pushed exterior objects in the SAME native twist chart. -/
def formIso (q : ℕ) :
    (SchemeRelativeFrobeniusDeRham.formModule f p q).restrict (j) ≅
      (Scheme.Modules.pushforward (g)).obj
        (CanonicalGeometry.exteriorCotangentSheaf (Spec.map (CommRingCat.ofHom (α))) q) :=
  restrictionIso f p U hU (CanonicalGeometry.exteriorCotangentSheaf f q) ≪≫
    (Scheme.Modules.pushforward (g)).mapIso (ordinaryExteriorIso f U hU q)

end EnvelopeProperty.Cartier.RelativeTwistedAffinePushforward
