import EnvelopeProperty.Cartier.RelativeCartierContinuationTwistedAffineCharts
import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineMap

/-! # The original relative Frobenius in its actual twisted affine chart

Both whole scheme maps are constructed; their equality follows from the actual
pullback projections and original absolute-Frobenius naturality, including zero.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeTwistedAffineFrobenius
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
variable (U : X.Opens) (hU : IsAffineOpen U)
private def structuralRingMap : k →+* Γ(X, U) :=
  ((CanonicalGeometry.schemeConstantPresheafMap f).app (op U)).hom
local notation "α" => structuralRingMap f U
local notation "T" => RelativeFrobenius.twist (α) p
local notation "s" => RelativeFrobenius.sourceMap (α) p
local notation "c" => RelativeFrobenius.coefficientMap (α) p
local notation "Fk" => SchemeRelativeFrobenius.baseMap (k := k) p
local notation "π₁" => pullback.fst f Fk
local notation "π₂" => pullback.snd f Fk
local notation "V" => RelativeTwistedAffineBasis.twistedOpen f p U
local notation "e" => RelativeTwistedAffineCharts.chartIso f p U hU
local notation "g" => SchemeRelativeFrobeniusAffineMap.affineMap (α) p
local notation "Fr" => SchemeRelativeFrobenius.map p f

/-- The actual native spectrum chart into the SAME entire geometric twist. -/
def chartMap : Spec T ⟶ SchemeRelativeFrobenius.twist p f := (e).hom ≫ (V).ι

/-- The actual native twisted chart is genuinely an open immersion. -/
instance chartMap_isOpenImmersion : IsOpenImmersion (chartMap f p U hU) := by
  dsimp only [chartMap]
  exact IsOpenImmersion.comp (e).hom (V).ι

/-- The actual whole chart retains its original source projection. -/
theorem chartMap_source :
    chartMap f p U hU ≫ π₁ = Spec.map s ≫ hU.fromSpec :=
  (Category.assoc _ _ _).trans
    (RelativeTwistedAffineCharts.chartIso_hom_source_into_X f p U hU)

/-- The actual whole chart retains its original coefficient projection. -/
theorem chartMap_coefficient : chartMap f p U hU ≫ π₂ = Spec.map c :=
  (Category.assoc _ _ _).trans
    (RelativeTwistedAffineCharts.chartIso_hom_coefficient f p U hU)

/-- The SAME whole global relative Frobenius is the actual affine relative map
in the SAME original native twisted chart, including empty affine opens. -/
theorem chart_relativeFrobenius :
    hU.fromSpec ≫ Fr = g ≫ (e).hom ≫ (V).ι := by
  apply pullback.hom_ext
  · calc
      (hU.fromSpec ≫ Fr) ≫ π₁ = hU.fromSpec ≫ SchemeFrobenius.map f p := by
        exact (Category.assoc hU.fromSpec (Fr) (π₁)).trans
          (congrArg (fun z => hU.fromSpec ≫ z) (SchemeRelativeFrobenius.map_fst p f))
      _ = SchemeFrobenius.map (Spec.map (CommRingCat.ofHom (α))) p ≫ hU.fromSpec :=
        (SchemeFrobenius.naturality (Spec.map (CommRingCat.ofHom (α))) p f hU.fromSpec).symm
      _ = (g ≫ Spec.map s) ≫ hU.fromSpec :=
        congrArg (fun z => z ≫ hU.fromSpec)
          (SchemeRelativeFrobeniusAffineMap.affineMap_source (α) p).symm
      _ = g ≫ (Spec.map s ≫ hU.fromSpec) := Category.assoc _ _ _
      _ = g ≫ (chartMap f p U hU ≫ π₁) :=
        congrArg (fun z => g ≫ z) (chartMap_source f p U hU).symm
      _ = (g ≫ chartMap f p U hU) ≫ π₁ := (Category.assoc _ _ _).symm
  · calc
      (hU.fromSpec ≫ Fr) ≫ π₂ = hU.fromSpec ≫ f := by
        exact (Category.assoc hU.fromSpec (Fr) (π₂)).trans
          (congrArg (fun z => hU.fromSpec ≫ z) (SchemeRelativeFrobenius.map_snd p f))
      _ = Spec.map (CommRingCat.ofHom (α)) :=
        CanonicalGeometry.affineChartStructuralMap f hU
      _ = g ≫ Spec.map c :=
        (SchemeRelativeFrobeniusAffineMap.affineMap_coefficient (α) p).symm
      _ = g ≫ (chartMap f p U hU ≫ π₂) :=
        congrArg (fun z => g ≫ z) (chartMap_coefficient f p U hU).symm
      _ = (g ≫ chartMap f p U hU) ≫ π₂ := (Category.assoc _ _ _).symm

/-- The actual image is the SAME original twisted open, with no image input. -/
theorem chartMap_opensRange : (chartMap f p U hU).opensRange = V :=
  (Scheme.Hom.opensRange_comp_of_isIso (e).hom (V).ι).trans
    (Scheme.Opens.opensRange_ι (V))

/-- The original relative-Frobenius chart square is genuinely cartesian,
derived from the actual whole-map and original inverse-image identities. -/
theorem chartIsPullback : IsPullback (g) hU.fromSpec (chartMap f p U hU) (Fr) := by
  apply IsOpenImmersion.isPullback
  · exact chart_relativeFrobenius f p U hU
  · exact (congrArg (fun W => (Fr) ⁻¹ᵁ W) (chartMap_opensRange f p U hU)).trans
      ((RelativeTwistedAffineBasis.relative_preimage f p U).trans hU.opensRange_fromSpec.symm)

end EnvelopeProperty.Cartier.RelativeTwistedAffineFrobenius
