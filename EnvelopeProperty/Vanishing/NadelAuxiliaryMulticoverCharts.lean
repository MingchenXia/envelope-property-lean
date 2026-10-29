import EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverChartsSingle

/-! # Actual whole affine charts of the original auxiliary multicover

The map and its cartesian square are constructed, not assumed. The original
finite list, every original line frame and section coefficient, the original
degrees and the whole native scheme fibre products are retained literally.
-/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverCharts
open NadelAuxiliaryMulticover
variable {X : Scheme.{u}} (U : X.Opens) [IsAffine U.toScheme]

/-- The actual whole affine spectrum with its SAME original coefficient map. -/
def baseMap (D : List (AuxiliarySection X)) (e : Frames U D) :
    Spec (ring U D e) ⟶ U.toScheme :=
  Spec.map (structureMap U D e) ≫ U.toScheme.isoSpec.inv

/-- The actual head/tail spectrum square over the original affine open. -/
theorem stage_overOpen_isPullback (E : AuxiliarySection X) (D : List (AuxiliarySection X))
    (e : Frames U (E :: D)) :
    IsPullback (Spec.map (tailMap U E D e)) (Spec.map (headMap U E D e))
      (baseMap U D (fun i => e i.succ)) (singleBase U E (e 0)) := by
  exact (stage_isPullback U E D e).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    U.toScheme.isoSpec.symm (by simp) (by simp) (by simp [baseMap])
    (by simp [singleBase])

/-- The actual affine projection through the original tail stage. -/
theorem tailSpec_baseMap (E : AuxiliarySection X) (D : List (AuxiliarySection X))
    (e : Frames U (E :: D)) :
    Spec.map (tailMap U E D e) ≫ baseMap U D (fun i => e i.succ) =
      baseMap U (E :: D) e := by
  simp only [baseMap, ← Category.assoc, ← Spec.map_comp, structureMap_cons]

private def chartMapData : (D : List (AuxiliarySection X)) → (e : Frames U D) →
    { f : Spec (ring U D e) ⟶ rawScheme D //
      IsPullback f (baseMap U D e) (projection D) U.ι }
  | [], e => ⟨baseMap U [] e ≫ U.ι, by
      change IsPullback _ _ (𝟙 X) U.ι
      have : IsIso (baseMap U [] e) := by
        change IsIso (Spec.map (𝟙 (baseRing U)) ≫ U.toScheme.isoSpec.inv)
        infer_instance
      exact IsPullback.of_vert_isIso ⟨Category.comp_id _⟩⟩
  | E :: D, e => by
      let t := chartMapData D (fun i => e i.succ)
      let p := Spec.map (tailMap U E D e)
      let q := Spec.map (headMap U E D e) ≫ singleMap U E (e 0)
      have ho : IsPullback q p (factorProjection E)
          (baseMap U D (fun i => e i.succ) ≫ U.ι) :=
        (stage_overOpen_isPullback U E D e).flip.paste_horiz
          (single_isPullback U E (e 0))
      have hc : (p ≫ t.val) ≫ projection D = q ≫ factorProjection E := by
        rw [Category.assoc, t.property.w]
        exact ho.w.symm
      let f : Spec (ring U (E :: D) e) ⟶ rawScheme (E :: D) :=
        Limits.pullback.lift (p ≫ t.val) q hc
      have hfhead : f ≫ headProjection E D = q := Limits.pullback.lift_snd _ _ _
      have hftail : f ≫ tailProjection E D = p ≫ t.val := Limits.pullback.lift_fst _ _ _
      have ho' : IsPullback (f ≫ headProjection E D) p (factorProjection E)
          (t.val ≫ projection D) := by
        rw [hfhead, t.property.w]
        exact ho
      have hi : IsPullback f p (tailProjection E D) t.val :=
        ho'.of_right hftail (NadelAuxiliaryMulticover.stage_isPullback E D).flip
      refine ⟨f, ?_⟩
      have hh := hi.paste_vert t.property
      rw [tailSpec_baseMap U E D e, tailProjection_over] at hh
      exact hh

/-- The actual constructed WHOLE affine chart map to the original raw multicover. -/
def chartMap (D : List (AuxiliarySection X)) (e : Frames U D) :
    Spec (ring U D e) ⟶ rawScheme D := (chartMapData U D e).val

/-- The WHOLE original multicover has this actual affine-open root-algebra chart.
No desired affine identification is supplied as an input. -/
theorem chart_isPullback (D : List (AuxiliarySection X)) (e : Frames U D) :
    IsPullback (chartMap U D e) (baseMap U D e) (projection D) U.ι :=
  (chartMapData U D e).property

/-- The constructed WHOLE chart is an actual open immersion into the SAME
original raw multicover, over the actual original affine-open inclusion. -/
theorem chartMap_isOpenImmersion (D : List (AuxiliarySection X)) (e : Frames U D) :
    IsOpenImmersion (chartMap U D e) :=
  MorphismProperty.of_isPullback (chart_isPullback U D e).flip inferInstance

/-- The actual original whole projection triangle. -/
theorem chartMap_over (D : List (AuxiliarySection X)) (e : Frames U D) :
    chartMap U D e ≫ projection D = baseMap U D e ≫ U.ι :=
  (chart_isPullback U D e).w

/-- A genuine scheme isomorphism to the literal WHOLE affine-open base change
of the SAME original multicover, retaining every component and nilpotent. -/
def wholeChartIso (D : List (AuxiliarySection X)) (e : Frames U D) :
    Spec (ring U D e) ≅ Limits.pullback (projection D) U.ι :=
  (chart_isPullback U D e).isoPullback

/-- The SAME original whole multicover restriction is genuinely affine. -/
theorem whole_isAffine (D : List (AuxiliarySection X)) (e : Frames U D) :
    IsAffine (Limits.pullback (projection D) U.ι) :=
  IsAffine.of_isIso (wholeChartIso U D e).inv

/-- The genuine whole chart identifies the original raw-cover projection. -/
theorem wholeChartIso_fst (D : List (AuxiliarySection X)) (e : Frames U D) :
    (wholeChartIso U D e).hom ≫ Limits.pullback.fst (projection D) U.ι = chartMap U D e :=
  (chart_isPullback U D e).isoPullback_hom_fst

/-- The genuine whole chart identifies the SAME original affine-open projection. -/
theorem wholeChartIso_snd (D : List (AuxiliarySection X)) (e : Frames U D) :
    (wholeChartIso U D e).hom ≫ Limits.pullback.snd (projection D) U.ι = baseMap U D e :=
  (chart_isPullback U D e).isoPullback_hom_snd

/-- The actual global-section ring of the WHOLE original affine-open base
change is the constructed original simultaneous-root algebra. -/
def wholeGammaIso (D : List (AuxiliarySection X)) (e : Frames U D) :
    Γ(Limits.pullback (projection D) U.ι, ⊤) ≅ ring U D e :=
  Scheme.Γ.mapIso (wholeChartIso U D e).op ≪≫ (Scheme.ΓSpecIso (ring U D e))

/-- The actual global-section identification preserves the ORIGINAL affine
coefficient map, rather than only identifying the underlying abstract rings. -/
theorem wholeGammaIso_structure (D : List (AuxiliarySection X)) (e : Frames U D) :
    (Limits.pullback.snd (projection D) U.ι).appTop ≫ (wholeGammaIso U D e).hom =
      structureMap U D e := by
  have hu : U.toScheme.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso (baseRing U)).hom = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop]
    change U.toScheme.isoSpec.inv.appTop ≫ U.toScheme.isoSpec.hom.appTop = 𝟙 _
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  change (Limits.pullback.snd (projection D) U.ι).appTop ≫
    (wholeChartIso U D e).hom.appTop ≫ (Scheme.ΓSpecIso (ring U D e)).hom = _
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop, wholeChartIso_snd]
  rw [baseMap, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    ← Category.assoc, hu, Category.id_comp]

end EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverCharts
