import EnvelopeProperty.Berkovich.SchemeGenericLinePullback
import EnvelopeProperty.Berkovich.SchemeCenterBaseChange
import EnvelopeProperty.AlgGeom.SchemeLineFramePullbackCoherence

/-! # The actual original generic local frame under the true residue-field map -/
open scoped NNReal
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R S : Type u} [CommRing R] [CommRing S]
variable {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}
variable (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r)
variable {X Y : Scheme.{u}}
variable {fX : X ⟶ Spec (CommRingCat.of S)} {fY : Y ⟶ Spec (CommRingCat.of R)}
variable [IsProper fX] [IsProper fY]
variable (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
variable (hbR : ∀ r, v r ≤ 1) (hbS : ∀ s, w s ≤ 1) (y : RelativeSchemeValuedPoint w fX)

private theorem sourceCenterMem (U : Y.Opens) (hc : center hbR (mapOverBase φ hφ g hg y) ∈ U) :
    center hbS y ∈ g ⁻¹ᵁ U := by
  change g (center hbS y) ∈ U
  rw [center_map_overBase φ hφ g hg hbR hbS y]
  exact hc

/-- The SAME actual original local generic factor commutes with the actual
original residue-field map, as a WHOLE map into the original frame open. -/
theorem localGenericFactor_map_overBase
    (U : Y.Opens) (hc : center hbR (mapOverBase φ hφ g hg y) ∈ U) :
    localGenericFactor hbS y (g ⁻¹ᵁ U) (sourceCenterMem φ hφ g hg hbR hbS y U hc) ≫ (g ∣_ U) =
      Spec.map (g.residueFieldMap y.1.point) ≫
        localGenericFactor hbR (mapOverBase φ hφ g hg y) U hc := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc,morphismRestrict_ι,← Category.assoc,localGenericFactor_comp,
    Category.assoc,localGenericFactor_comp]
  exact (g.SpecMap_residueFieldMap_fromSpecResidueField y.1.point).symm

private def mappedGenericFrame {M : Y.Modules}
    (U : Y.Opens) (hc : center hbR (mapOverBase φ hφ g hg y) ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme) :
    genericLineModule y ((Scheme.Modules.pullback g).obj M) ≅
      Scheme.Modules.unitObj (Spec (CommRingCat.of (X.residueField y.1.point))) :=
  (Scheme.Modules.pullbackComp (X.fromSpecResidueField y.1.point) g).app M ≪≫
    Scheme.Modules.frameViaFactor (Spec.map (g.residueFieldMap y.1.point))
      (Y.fromSpecResidueField (g y.1.point)) (X.fromSpecResidueField y.1.point ≫ g)
      (g.SpecMap_residueFieldMap_fromSpecResidueField y.1.point)
      (localFrameGenericIso hbR (mapOverBase φ hφ g hg y) U hc e)

private theorem localFrameGenericIso_pullback {M : Y.Modules}
    (U : Y.Opens) (hc : center hbR (mapOverBase φ hφ g hg y) ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme) :
    localFrameGenericIso hbS y (g ⁻¹ᵁ U) (sourceCenterMem φ hφ g hg hbR hbS y U hc)
      (SchemeLineSectionEvaluation.localPullbackFrame g U e) =
        mappedGenericFrame φ hφ g hg hbR y U hc e := by
  let z := mapOverBase φ hφ g hg y
  let hx := sourceCenterMem φ hφ g hg hbR hbS y U hc
  let lX := localGenericFactor hbS y (g ⁻¹ᵁ U) hx
  let lY := localGenericFactor hbR z U hc
  let ρ := Spec.map (g.residueFieldMap y.1.point)
  let pX := X.fromSpecResidueField y.1.point
  let pY := Y.fromSpecResidueField z.1.point
  have hX : lX ≫ (g ⁻¹ᵁ U).ι = pX := localGenericFactor_comp hbS y _ hx
  have hY : lY ≫ U.ι = pY := localGenericFactor_comp hbR z _ hc
  have hρ : ρ ≫ pY = pX ≫ g := g.SpecMap_residueFieldMap_fromSpecResidueField y.1.point
  have hfactor : lX ≫ (g ∣_ U) = ρ ≫ lY := localGenericFactor_map_overBase φ hφ g hg hbR hbS y U hc
  have hs := Scheme.Modules.frameViaFactor_pullbackComp lX (g ⁻¹ᵁ U).ι pX hX g
    (Scheme.Modules.frameViaFactor (g ∣_ U) U.ι ((g ⁻¹ᵁ U).ι ≫ g) (morphismRestrict_ι g U) e)
  have hs' := Scheme.Modules.frameViaFactor_comp lX (g ∣_ U) U.ι
    ((g ⁻¹ᵁ U).ι ≫ g) (morphismRestrict_ι g U) (pX ≫ g)
    (by rw [← Category.assoc,hX]) e
  have ht := Scheme.Modules.frameViaFactor_comp ρ lY U.ι pY hY (pX ≫ g) hρ e
  have he : localFrameGenericIso hbS y (g ⁻¹ᵁ U) hx
      (SchemeLineSectionEvaluation.localPullbackFrame g U e) =
      (Scheme.Modules.pullbackComp pX g).app M ≪≫
        Scheme.Modules.frameViaFactor ρ pY (pX ≫ g) hρ (localFrameGenericIso hbR z U hc e) := by
    change Scheme.Modules.frameViaFactor lX (g ⁻¹ᵁ U).ι pX hX
      ((Scheme.Modules.pullbackComp (g ⁻¹ᵁ U).ι g).app M ≪≫
        Scheme.Modules.frameViaFactor (g ∣_ U) U.ι ((g ⁻¹ᵁ U).ι ≫ g) (morphismRestrict_ι g U) e) = _
    rw [hs,hs']
    change (Scheme.Modules.pullbackComp pX g).app M ≪≫
      Scheme.Modules.frameViaFactor (lX ≫ (g ∣_ U)) U.ι (pX ≫ g) _ e =
      (Scheme.Modules.pullbackComp pX g).app M ≪≫
        Scheme.Modules.frameViaFactor ρ pY (pX ≫ g) hρ
          (Scheme.Modules.frameViaFactor lY U.ι pY hY e)
    rw [ht]
    simp only [hfactor]
  exact he

/-- The actual original generic-residue pullback comparison preserves the
whole TRUE pulled local frame. All native composition and open-factor
comparisons are DERIVED, without a frame-preservation premise. -/
theorem residueModulePullbackIso_localFrame
    {M : Y.Modules} (U : Y.Opens) (hc : center hbR (mapOverBase φ hφ g hg y) ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme) :
    SchemeValuedPoint.residueModulePullbackIso g y.1.point M ≪≫
      localFrameGenericIso hbS y (g ⁻¹ᵁ U) (sourceCenterMem φ hφ g hg hbR hbS y U hc)
        (SchemeLineSectionEvaluation.localPullbackFrame g U e) =
      (Scheme.Modules.pullback (Spec.map (g.residueFieldMap y.1.point))).mapIso
        (localFrameGenericIso hbR (mapOverBase φ hφ g hg y) U hc e) ≪≫
          Scheme.Modules.pullbackUnitIso (Spec.map (g.residueFieldMap y.1.point)) := by
  rw [localFrameGenericIso_pullback φ hφ g hg hbR hbS y U hc e]
  exact SchemeValuedPoint.residueModulePullbackIso_frame g y.1.point M
    (localFrameGenericIso hbR (mapOverBase φ hφ g hg y) U hc e)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
