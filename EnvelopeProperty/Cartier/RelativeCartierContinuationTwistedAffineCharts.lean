import EnvelopeProperty.Cartier.RelativeCartierContinuationTwistedAffineBasis
import EnvelopeProperty.Cartier.RelativeCartierContinuationAffineGeometricTwist
import EnvelopeProperty.AlgGeom.Canonical.CotangentSmoothLocallyFree
import Mathlib.AlgebraicGeometry.Restrict

/-! # The SAME actual twisted open is the original native affine pushout chart

Actual open-restriction pullbacks and native pullback pasting derive the chart.
Original source/coefficient projections and the actual section ring are retained.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeTwistedAffineCharts
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "Fk" => SchemeRelativeFrobenius.baseMap (k := k) p
local notation "π" => (pullback.fst f Fk : Y ⟶ X)
variable (U : X.Opens)
local notation "V" => RelativeTwistedAffineBasis.twistedOpen f p U

/-- The SAME original twisted open is a genuine pullback over the original open U. -/
theorem twistedOpenIsPullback : IsPullback ((π) ∣_ U)
    ((V).ι ≫ pullback.snd f Fk) (U.ι ≫ f) Fk :=
  (((isPullback_morphismRestrict (π) U).flip).paste_horiz
    (IsPullback.of_hasPullback f Fk).flip).flip

private def structuralRingMap : k →+* Γ(X, U) :=
  ((CanonicalGeometry.schemeConstantPresheafMap f).app (op U)).hom

local notation "α" => structuralRingMap f U
local notation "T" => RelativeFrobenius.twist (α) p
local notation "s" => RelativeFrobenius.sourceMap (α) p
local notation "c" => RelativeFrobenius.coefficientMap (α) p
variable (hU : IsAffineOpen U)

/-- The original native twist spectrum is a genuine cartesian chart over the SAME U. -/
theorem nativeChartIsPullback : IsPullback
    (Spec.map s ≫ hU.isoSpec.inv) (Spec.map c) (U.ι ≫ f) Fk := by
  have he : hU.isoSpec.inv ≫ (U.ι ≫ f) =
      Spec.map (CommRingCat.ofHom (α)) ≫ 𝟙 (Spec (CommRingCat.of k)) := by
    have hc : hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (α)) :=
      CanonicalGeometry.affineChartStructuralMap f hU
    calc
      _ = hU.fromSpec ≫ f := (Category.assoc _ _ _).symm
      _ = Spec.map (CommRingCat.ofHom (α)) := hc
      _ = _ := (Category.comp_id _).symm
  have hi : IsPullback hU.isoSpec.inv (Spec.map (CommRingCat.ofHom (α)))
      (U.ι ≫ f) (𝟙 (Spec (CommRingCat.of k))) :=
    IsPullback.of_horiz_isIso ⟨he⟩
  simpa only [Category.comp_id] using
    (RelativeAffineGeometricTwist.nativeIsPullback (α) p).paste_horiz hi

/-- Genuine native affine chart of the SAME actual twisted open, including empty U. -/
def chartIso : Spec T ≅ (V).toScheme :=
  (nativeChartIsPullback f p U hU).isoPullback ≪≫
    (twistedOpenIsPullback f p U).isoPullback.symm

/-- The ENTIRE first chart projection preserves the original source inclusion. -/
theorem chartIso_hom_source :
    (chartIso f p U hU).hom ≫ ((π) ∣_ U) = Spec.map s ≫ hU.isoSpec.inv := by
  change ((nativeChartIsPullback f p U hU).isoPullback.hom ≫
    (twistedOpenIsPullback f p U).isoPullback.inv) ≫ ((π) ∣_ U) = _
  erw [Category.assoc (nativeChartIsPullback f p U hU).isoPullback.hom
    (twistedOpenIsPullback f p U).isoPullback.inv ((π) ∣_ U),
    (twistedOpenIsPullback f p U).isoPullback_inv_fst,
    (nativeChartIsPullback f p U hU).isoPullback_hom_fst]

/-- The ENTIRE second chart projection preserves the original coefficient inclusion. -/
theorem chartIso_hom_coefficient :
    (chartIso f p U hU).hom ≫ (V).ι ≫ pullback.snd f Fk = Spec.map c := by
  change ((nativeChartIsPullback f p U hU).isoPullback.hom ≫
    (twistedOpenIsPullback f p U).isoPullback.inv) ≫ ((V).ι ≫ pullback.snd f Fk) = _
  erw [Category.assoc (nativeChartIsPullback f p U hU).isoPullback.hom
    (twistedOpenIsPullback f p U).isoPullback.inv ((V).ι ≫ pullback.snd f Fk),
    (twistedOpenIsPullback f p U).isoPullback_inv_snd,
    (nativeChartIsPullback f p U hU).isoPullback_hom_snd]

/-- The SAME entire original chart into X retains its original affine source map. -/
theorem chartIso_hom_source_into_X :
    (chartIso f p U hU).hom ≫ (V).ι ≫ (π) = Spec.map s ≫ hU.fromSpec := by
  calc
    _ = (chartIso f p U hU).hom ≫ (((π) ∣_ U) ≫ U.ι) :=
      congrArg (fun z => (chartIso f p U hU).hom ≫ z) (morphismRestrict_ι (π) U).symm
    _ = ((chartIso f p U hU).hom ≫ ((π) ∣_ U)) ≫ U.ι := (Category.assoc _ _ _).symm
    _ = (Spec.map s ≫ hU.isoSpec.inv) ≫ U.ι :=
      congrArg (fun z => z ≫ U.ι) (chartIso_hom_source f p U hU)
    _ = _ := Category.assoc _ _ _

/-- Actual sections of the SAME twisted affine open have the original native twist ring. -/
def sectionsIso : Γ(Y, V) ≅ T :=
  (Scheme.ΓSpecIso Γ(Y, V)).symm ≪≫
    Scheme.Γ.mapIso (chartIso f p U hU ≪≫
      (RelativeTwistedAffineBasis.twistedOpen_isAffine f p U hU).isoSpec).op ≪≫
    Scheme.ΓSpecIso T

end EnvelopeProperty.Cartier.RelativeTwistedAffineCharts
