/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeScalarBaseChange
import EnvelopeProperty.ProperMapLocality

/-!
# Whole-scheme proper scalar restriction on actual native points

True pullback charts identify each original support-open inverse image with
the native space of its literal scalar-changed chart. Genuine proper-map
locality on the original affine cover glues the actual affine tensor result.
-/

open scoped Classical NNReal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeScalarBaseChange
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}
    (hw : ∀ r, w (algebraMap R S r) = v r)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual scalar-changed source chart maps into the whole actual pullback. -/
def openChartMap {U : Scheme.{u}} (g : U ⟶ X) :
    model (S := S) (g ≫ f) ⟶ model (S := S) f :=
  (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom (algebraMap R S))) g).inv ≫
    pullback.snd g (projection (S := S) f)

/-- Genuine original open charts stay open immersions under actual scalar change. -/
instance openChartMap_isOpenImmersion {U : Scheme.{u}} (g : U ⟶ X) [IsOpenImmersion g] :
    IsOpenImmersion (openChartMap (S := S) f g) := by
  dsimp only [openChartMap]
  infer_instance

/-- The entire actual new coefficient structure is preserved by the chart map. -/
theorem openChartMap_structure {U : Scheme.{u}} (g : U ⟶ X) :
    openChartMap (S := S) f g ≫ structureMap (S := S) f = structureMap (S := S) (g ≫ f) := by
  simpa only [openChartMap, structureMap, Category.assoc] using
    pullbackRightPullbackFstIso_inv_snd_snd f (Spec.map (CommRingCat.ofHom (algebraMap R S))) g

/-- The actual chart projection preserves the entire original scheme morphism. -/
theorem openChartMap_projection {U : Scheme.{u}} (g : U ⟶ X) :
    openChartMap (S := S) f g ≫ projection (S := S) f =
      projection (S := S) (g ≫ f) ≫ g := by
  simpa only [openChartMap, projection, Category.assoc] using
    pullbackRightPullbackFstIso_inv_snd_fst f (Spec.map (CommRingCat.ofHom (algebraMap R S))) g

/-- The whole true chart range is the original projection inverse image. -/
theorem openChartMap_range {U : Scheme.{u}} (g : U ⟶ X) [IsOpenImmersion g] :
    (openChartMap (S := S) f g).opensRange = (projection (S := S) f) ⁻¹ᵁ g.opensRange := by
  change ((pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom (algebraMap R S))) g).inv ≫
    pullback.snd g (projection (S := S) f)).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackSnd]

/-- The actual native chart map and actual scalar restriction commute on whole points. -/
theorem openChartNative_commutes {U : Scheme.{u}} (g : U ⟶ X)
    (y : RelativeSchemeValuedPoint w (structureMap (S := S) (g ≫ f))) :
    nativeMap hw f
      (RelativeSchemeValuedPoint.map (openChartMap f g) (openChartMap_structure f g) y) =
    RelativeSchemeValuedPoint.map (v := v) g rfl (nativeMap hw (g ≫ f) y) := by
  apply Subtype.ext
  change SchemeValuedPoint.map (projection (S := S) f)
    (SchemeValuedPoint.map (openChartMap f g) y.1) =
      SchemeValuedPoint.map g (SchemeValuedPoint.map (projection (S := S) (g ≫ f)) y.1)
  rw [← SchemeValuedPoint.map_comp, openChartMap_projection, SchemeValuedPoint.map_comp]

/-- The literal scalar-changed chart is precisely the whole native inverse
image of its original scheme support-open under true scalar restriction. -/
def openChartNativeHomeomorph {U : Scheme.{u}} (g : U ⟶ X) [IsOpenImmersion g] :
    RelativeSchemeValuedPoint w (structureMap (S := S) (g ≫ f)) ≃ₜ
      {y : RelativeSchemeValuedPoint w (structureMap (S := S) f) //
        (nativeMap hw f y).1.point ∈ g.opensRange} :=
  (RelativeSchemeValuedPoint.openImmersionHomeomorph
    (openChartMap f g) (openChartMap_structure f g)).trans
    (Homeomorph.setCongr (by
      ext y
      change y.1.point ∈ (openChartMap (S := S) f g).opensRange ↔
        (projection (S := S) f) y.1.point ∈ g.opensRange
      rw [openChartMap_range]
      rfl))

/-- On a genuine affine support open, the whole native scalar restriction
is proper through the actual scalar-changed chart comparison. -/
theorem isProperMap_nativeMap_restrict_affine (U : X.Opens) (hU : IsAffineOpen U) :
    IsProperMap ((RelativeSchemeValuedPoint.supportOpens v f U :
      Set (RelativeSchemeValuedPoint v f)).restrictPreimage (nativeMap hw f)) := by
  let : IsAffine U := hU
  let e := (openChartNativeHomeomorph hw f U.ι).trans
    (Homeomorph.setCongr (by rw [Scheme.Opens.opensRange_ι]))
  let t := RelativeSchemeValuedPoint.restrictionHomeomorph (v := v) U f
  have hp := t.isClosedEmbedding.isProperMap.comp
    ((isProperMap_nativeMap_of_isAffine hw (U.ι ≫ f)).comp e.symm.isClosedEmbedding.isProperMap)
  have he : t ∘ nativeMap hw (U.ι ≫ f) ∘ e.symm =
      (RelativeSchemeValuedPoint.supportOpens v f U :
        Set (RelativeSchemeValuedPoint v f)).restrictPreimage (nativeMap hw f) := by
    funext y
    apply Subtype.ext
    have hy := congrArg Subtype.val (e.apply_symm_apply y)
    change RelativeSchemeValuedPoint.map (openChartMap f U.ι)
      (openChartMap_structure f U.ι) (e.symm y) = y.1 at hy
    change RelativeSchemeValuedPoint.map (v := v) U.ι rfl
      (nativeMap hw (U.ι ≫ f) (e.symm y)) = nativeMap hw f y.1
    rw [← openChartNative_commutes, hy]
  exact he ▸ hp

/-- The genuine native scalar restriction on any actual scheme is proper.
No coefficient bound, separation, finite-type or proper-model premise occurs. -/
theorem isProperMap_nativeMap : IsProperMap (nativeMap hw f) := by
  let U : SchemeValuedPoint.AffineAtlasIndex X →
      TopologicalSpace.Opens (RelativeSchemeValuedPoint v f) :=
    fun i => RelativeSchemeValuedPoint.supportOpens v f (SchemeValuedPoint.canonicalAffineOpens X i)
  have hU : TopologicalSpace.IsOpenCover U := TopologicalSpace.IsOpenCover.mk (by
    apply TopologicalSpace.Opens.ext
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    exact RelativeSchemeValuedPoint.iUnion_supportOpens v f
      (SchemeValuedPoint.canonicalAffineOpens X) (SchemeValuedPoint.iUnion_canonicalAffineOpens X))
  exact (EnvelopeProperty.isProperMap_iff_restrictPreimage_of_openCover hU
    (continuous_nativeMap hw f)).mpr (fun i => isProperMap_nativeMap_restrict_affine hw f _
      (SchemeValuedPoint.isAffineOpen_canonicalAffineOpens X i))

/-- Whole-scheme actual scalar restriction is closed for arbitrary compatible coefficients. -/
theorem isClosedMap_nativeMap : IsClosedMap (nativeMap hw f) :=
  (isProperMap_nativeMap hw f).isClosedMap

/-- Compact native sets have compact inverse images under the same actual scalar map. -/
theorem isCompact_preimage_nativeMap {K : Set (RelativeSchemeValuedPoint v f)} (hK : IsCompact K) :
    IsCompact (nativeMap hw f ⁻¹' K) := (isProperMap_nativeMap hw f).isCompact_preimage hK

/-- Actual whole native scalar-restriction fibres are compact. -/
theorem isCompact_fibre_nativeMap (x : RelativeSchemeValuedPoint v f) :
    IsCompact (nativeMap hw f ⁻¹' {x}) := isCompact_preimage_nativeMap hw f isCompact_singleton

/-- Every whole native point of any actual scheme lifts through the
completion of an algebraic normed scalar extension of a complete field.
The actual original affine cover constructs the lift on the literal whole
scheme pullback, rather than assuming a chartwise gluing certificate. -/
theorem nativeMap_surjective_algebraicCompletion
    {K L : Type u} [NormedField K] [NormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [NormedAlgebra K L]
    [CompleteSpace K] [Algebra.IsAlgebraic K L]
    {Y : Scheme.{u}} (fK : Y ⟶ Spec (CommRingCat.of K)) :
    Function.Surjective (nativeMap
      (RelativeSpectrum.fcCompletedExtension_val_algebraMap (K := K) (L := L)) fK) := by
  intro x
  obtain ⟨i, p, hp⟩ := Y.affineCover.exists_eq x.1.point
  have hx : x ∈ Set.range (RelativeSchemeValuedPoint.map
      (v := NormedField.valuation (K := K)) (fY := fK) (Y.affineCover.f i) rfl) := by
    rw [RelativeSchemeValuedPoint.range_map_of_isOpenImmersion]
    exact ⟨p, hp⟩
  obtain ⟨z, hz⟩ := hx
  obtain ⟨z', hz'⟩ := nativeMap_surjective_algebraicCompletion_of_isAffine
    (L := L) (Y.affineCover.f i ≫ fK) z
  refine ⟨RelativeSchemeValuedPoint.map (openChartMap fK (Y.affineCover.f i))
    (openChartMap_structure fK (Y.affineCover.f i)) z', ?_⟩
  rw [openChartNative_commutes, hz', hz]

end EnvelopeProperty.Berkovich.SchemeScalarBaseChange
