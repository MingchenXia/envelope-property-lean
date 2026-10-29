import EnvelopeProperty.Cartier.RelativeCartierContinuationTwistedAffineFrobenius
import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineSpec

/-! # The actual relative section map on the same native twisted affine open

Both original section triangles and the whole actual pullback = conjugate beta
are derived from genuine scheme maps, retaining the original coefficient algebra.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeTwistedAffineSections
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
variable (U : X.Opens)
local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "Fk" => SchemeRelativeFrobenius.baseMap (k := k) p
local notation "π₁" => (pullback.fst f Fk : Y ⟶ X)
local notation "π₂" => (pullback.snd f Fk : Y ⟶ Spec (CommRingCat.of k))
local notation "Fr" => SchemeRelativeFrobenius.map p f
local notation "V" => RelativeTwistedAffineBasis.twistedOpen f p U

/-- The ORIGINAL structural coefficient map on the SAME actual twisted open. -/
def coefficientSectionMap : CommRingCat.of k ⟶ Γ(Y, V) :=
  (CanonicalGeometry.schemeConstantPresheafMap (π₂)).app (op (V))

/-- The ORIGINAL relative pullback with target literally Γ(X,U), by the proved preimage. -/
def relativeSectionMap : Γ(Y, V) ⟶ Γ(X, U) :=
  (Fr).appLE (V) U (RelativeTwistedAffineBasis.relative_preimage f p U).symm.le

private def structuralRingMap : k →+* Γ(X, U) :=
  ((CanonicalGeometry.schemeConstantPresheafMap f).app (op U)).hom
local notation "α" => structuralRingMap f U
local notation "T" => RelativeFrobenius.twist (α) p
local notation "s" => RelativeFrobenius.sourceMap (α) p
local notation "c" => RelativeFrobenius.coefficientMap (α) p
local notation "β" => SchemeRelativeFrobeniusAffineMap.ringMap (α) p
local notation "ρ" => Scheme.Hom.appLE (π₁) U (V) le_rfl
local notation "μ" => relativeSectionMap f p U
local notation "δ" => coefficientSectionMap f p U
variable (hU : IsAffineOpen U)
local notation "hV" => RelativeTwistedAffineBasis.twistedOpen_isAffine f p U hU
local notation "e" => RelativeTwistedAffineCharts.chartIso f p U hU
local notation "σ" => RelativeTwistedAffineCharts.sectionsIso f p U hU
local notation "j" => RelativeTwistedAffineFrobenius.chartMap f p U hU

/-- The SAME actual section isomorphism has the entire original spectrum chart. -/
theorem sectionsIso_spec : Spec.map (σ).hom = (e).hom ≫ (hV).isoSpec.hom := by
  obtain ⟨a, ha⟩ := Spec.map_surjective ((e).hom ≫ (hV).isoSpec.hom)
  have hs : (σ).hom = a := by
    change (Scheme.ΓSpecIso Γ(Y, V)).inv ≫ ((e).hom ≫ (hV).isoSpec.hom).appTop ≫
      (Scheme.ΓSpecIso T).hom = a
    erw [← ha, Scheme.ΓSpecIso_naturality a, Iso.inv_hom_id_assoc]
  rw [hs]
  exact ha

/-- The SAME original native chart is exactly Spec of its section isomorphism
followed by the original affine source map of V. -/
theorem chartMap_eq_spec_sectionsIso : j = Spec.map (σ).hom ≫ (hV).fromSpec := by
  have hv : (hV).isoSpec.hom ≫ (hV).fromSpec = (V).ι :=
    (hV).isoSpec.hom_inv_id_assoc (V).ι
  symm
  exact (congrArg (fun z => z ≫ (hV).fromSpec) (sectionsIso_spec f p U hU)).trans
    ((Category.assoc (e).hom (hV).isoSpec.hom (hV).fromSpec).trans
      (congrArg (fun z => (e).hom ≫ z) hv))

/-- The ENTIRE original first-projection section map is the original source inclusion. -/
theorem sectionsIso_source : ρ ≫ (σ).hom = s := by
  have hr : Spec.map (ρ) ≫ hU.fromSpec = (hV).fromSpec ≫ (π₁) :=
    IsAffineOpen.SpecMap_appLE_fromSpec (π₁) hU (hV) le_rfl
  have hj : (Spec.map (σ).hom ≫ (hV).fromSpec) ≫ (π₁) = Spec.map s ≫ hU.fromSpec :=
    (congrArg (fun z => z ≫ (π₁)) (chartMap_eq_spec_sectionsIso f p U hU).symm).trans
      (RelativeTwistedAffineFrobenius.chartMap_source f p U hU)
  apply Spec.map_injective
  apply (cancel_mono hU.fromSpec).mp
  have he : Spec.map ((ρ) ≫ (σ).hom) ≫ hU.fromSpec =
      (Spec.map (σ).hom ≫ (hV).fromSpec) ≫ (π₁) := by
    calc
      Spec.map ((ρ) ≫ (σ).hom) ≫ hU.fromSpec =
          (Spec.map (σ).hom ≫ Spec.map (ρ)) ≫ hU.fromSpec :=
        congrArg (fun z => z ≫ hU.fromSpec) (Spec.map_comp (ρ) (σ).hom)
      _ = Spec.map (σ).hom ≫ (Spec.map (ρ) ≫ hU.fromSpec) := Category.assoc _ _ _
      _ = Spec.map (σ).hom ≫ ((hV).fromSpec ≫ (π₁)) :=
        congrArg (fun z => Spec.map (σ).hom ≫ z) hr
      _ = (Spec.map (σ).hom ≫ (hV).fromSpec) ≫ (π₁) := (Category.assoc _ _ _).symm
  exact he.trans hj

/-- The ENTIRE original structural coefficient map is the original coefficient inclusion. -/
theorem sectionsIso_coefficient : (δ) ≫ (σ).hom = c := by
  have hc : (hV).fromSpec ≫ (π₂) = Spec.map (δ) :=
    CanonicalGeometry.affineChartStructuralMap (π₂) (hV)
  have hj : (Spec.map (σ).hom ≫ (hV).fromSpec) ≫ (π₂) = Spec.map c :=
    (congrArg (fun z => z ≫ (π₂)) (chartMap_eq_spec_sectionsIso f p U hU).symm).trans
      (RelativeTwistedAffineFrobenius.chartMap_coefficient f p U hU)
  apply Spec.map_injective
  have he : Spec.map ((δ) ≫ (σ).hom) =
      (Spec.map (σ).hom ≫ (hV).fromSpec) ≫ (π₂) := by
    calc
      Spec.map ((δ) ≫ (σ).hom) = Spec.map (σ).hom ≫ Spec.map (δ) :=
        Spec.map_comp (δ) (σ).hom
      _ = Spec.map (σ).hom ≫ ((hV).fromSpec ≫ (π₂)) :=
        congrArg (fun z => Spec.map (σ).hom ≫ z) hc.symm
      _ = (Spec.map (σ).hom ≫ (hV).fromSpec) ≫ (π₂) := (Category.assoc _ _ _).symm
  exact he.trans hj

/-- The WHOLE actual relative pullback is the SAME original geometric beta
through the SAME actual twisted-open section isomorphism, including zero. -/
theorem relativeSectionMap_eq : (μ) = (σ).hom ≫ β := by
  have hm : Spec.map (μ) ≫ (hV).fromSpec = hU.fromSpec ≫ (Fr) :=
    IsAffineOpen.SpecMap_appLE_fromSpec (Fr) (hV) hU
      (RelativeTwistedAffineBasis.relative_preimage f p U).symm.le
  apply Spec.map_injective
  apply (cancel_mono (hV).fromSpec).mp
  calc
    Spec.map (μ) ≫ (hV).fromSpec = hU.fromSpec ≫ (Fr) := hm
    _ = SchemeRelativeFrobeniusAffineMap.affineMap (α) p ≫ (j) :=
      RelativeTwistedAffineFrobenius.chart_relativeFrobenius f p U hU
    _ = Spec.map (β) ≫ (j) :=
      congrArg (fun z => z ≫ (j))
        (SchemeRelativeFrobeniusAffineMap.affineMap_eq_spec_ringMap (α) p)
    _ = Spec.map (β) ≫ (Spec.map (σ).hom ≫ (hV).fromSpec) :=
      congrArg (fun z => Spec.map (β) ≫ z) (chartMap_eq_spec_sectionsIso f p U hU)
    _ = (Spec.map (β) ≫ Spec.map (σ).hom) ≫ (hV).fromSpec := (Category.assoc _ _ _).symm
    _ = Spec.map ((σ).hom ≫ β) ≫ (hV).fromSpec :=
      congrArg (fun z => z ≫ (hV).fromSpec) (Spec.map_comp (σ).hom (β)).symm

/-- The ENTIRE actual inverse-isomorphism/pullback square is literally the original beta. -/
theorem sectionsIso_inv_relativeSectionMap : (σ).inv ≫ (μ) = β := by
  exact (congrArg (fun z => (σ).inv ≫ z) (relativeSectionMap_eq f p U hU)).trans
    ((σ).inv_hom_id_assoc (β))

/-- EVERY original native twist element has its actual original beta value. -/
theorem relativeSectionMap_sectionsIso_inv_apply (t : T) :
    (μ).hom ((σ).inv.hom t) = (β).hom t := by
  change ((σ).inv ≫ (μ)).hom t = (β).hom t
  exact congrArg (fun z : T ⟶ Γ(X, U) => z.hom t)
    (sectionsIso_inv_relativeSectionMap f p U hU)

include hU

/-- The original cotangentOpenAlgebra f U coefficient action is unchanged. -/
theorem relativeSectionMap_coefficient :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U
    (δ) ≫ (μ) = CommRingCat.ofHom (algebraMap k Γ(X, U)) := by
  change (δ) ≫ (μ) = CommRingCat.ofHom (α)
  calc
    _ = (δ) ≫ ((σ).hom ≫ β) :=
      congrArg (fun z => (δ) ≫ z) (relativeSectionMap_eq f p U hU)
    _ = ((δ) ≫ (σ).hom) ≫ β := (Category.assoc _ _ _).symm
    _ = c ≫ β := congrArg (fun z => z ≫ β) (sectionsIso_coefficient f p U hU)
    _ = _ := SchemeRelativeFrobeniusAffineMap.coefficient_ringMap (α) p

/-- EVERY original source section retains its original pth-power pullback. -/
theorem relativeSectionMap_source_apply (b : Γ(X, U)) : (μ).hom ((ρ).hom b) = b^p := by
  have ht : (ρ) ≫ (μ) = s ≫ β := by
    calc
      _ = (ρ) ≫ ((σ).hom ≫ β) :=
        congrArg (fun z => (ρ) ≫ z) (relativeSectionMap_eq f p U hU)
      _ = ((ρ) ≫ (σ).hom) ≫ β := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun z => z ≫ β) (sectionsIso_source f p U hU)
  exact (congrArg (fun z : Γ(X, U) ⟶ Γ(X, U) => z.hom b) ht).trans
    (SchemeRelativeFrobeniusAffineMap.source_ringMap_apply (α) p b)

end EnvelopeProperty.Cartier.RelativeTwistedAffineSections
