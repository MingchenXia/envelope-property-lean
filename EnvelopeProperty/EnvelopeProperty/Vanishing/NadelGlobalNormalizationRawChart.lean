import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingWholeChart

/-! # Actual cartesian whole original raw chart over its SAME SNC affine ring -/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalNormalization.RawChart
open NadelAuxiliaryMulticover NadelAdaptedChartMatching
variable {X : Scheme.{u}} (U : X.affineOpens) (D : List (AuxiliarySection X))
  (e : NadelAuxiliaryMulticoverCharts.Frames U.1 D)

/-- The actual whole original raw affine ring comparison under Spec. -/
def sourceIso : Spec (.of (WholeChart.Ring U D e)) ≅
    Spec (NadelAuxiliaryMulticoverCharts.ring U.1 D e) :=
  Scheme.Spec.mapIso (WholeChart.ringEquiv U D e).toCommRingCatIso.op

/-- The actual entire original raw chart map, preserving every cyclic factor. -/
def map : Spec (.of (WholeChart.Ring U D e)) ⟶ rawScheme D := by
  let : IsAffine U.1.toScheme := U.2
  exact (sourceIso U D e).hom ≫ NadelAuxiliaryMulticoverCharts.chartMap U.1 D e

/-- The SAME original SNC coordinate-ring map on the whole raw quotient. -/
def baseMap : Spec (.of (WholeChart.Ring U D e)) ⟶ Spec Γ(X, U.1) :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (WholeChart.Ring U D e)))

/-- The native actual raw chart ring comparison gives its actual original
open-subscheme coefficient triangle, without a chart-matching hypothesis. -/
theorem sourceIso_baseMap :
    let _ : IsAffine U.1.toScheme := U.2
    (sourceIso U D e).hom ≫ NadelAuxiliaryMulticoverCharts.baseMap U.1 D e =
      baseMap U D e ≫ U.2.isoSpec.inv := by
  let : IsAffine U.1.toScheme := U.2
  change Spec.map (CommRingCat.ofHom (WholeChart.ringEquiv U D e).toRingHom) ≫
    (Spec.map (NadelAuxiliaryMulticoverCharts.structureMap U.1 D e) ≫ U.1.toScheme.isoSpec.inv) = _
  rw [← Spec.map_comp_assoc]
  have hc : NadelAuxiliaryMulticoverCharts.structureMap U.1 D e ≫
      CommRingCat.ofHom (WholeChart.ringEquiv U D e).toRingHom =
      U.1.topIso.hom ≫ CommRingCat.ofHom (algebraMap Γ(X, U.1) (WholeChart.Ring U D e)) := by
    apply CommRingCat.hom_ext
    exact WholeChart.ringEquiv_structure U D e
  rw [hc, Spec.map_comp]
  rfl

/-- The SAME original whole raw affine chart is actually cartesian over
Spec of the SAME original SNC coordinate ring. -/
theorem isPullback : IsPullback (map U D e) (baseMap U D e) (projection D) U.2.fromSpec := by
  let : IsAffine U.1.toScheme := U.2
  exact (NadelAuxiliaryMulticoverCharts.chart_isPullback U.1 D e).of_iso
    (sourceIso U D e).symm (Iso.refl _) U.2.isoSpec (Iso.refl _)
    (by simp [map]) (by
      apply (cancel_epi (sourceIso U D e).hom).mp
      rw [← Category.assoc, sourceIso_baseMap]
      simp [Category.assoc])
    (by simp) (by simp [IsAffineOpen.fromSpec])

/-- The original raw chart is an ACTUAL whole open immersion. -/
theorem isOpenImmersion : IsOpenImmersion (map U D e) := by
  let : IsOpenImmersion U.2.fromSpec := by
    change IsOpenImmersion (U.2.isoSpec.inv ≫ U.1.ι)
    infer_instance
  exact MorphismProperty.of_isPullback (isPullback U D e).flip inferInstance

/-- The exact SAME original projection triangle to X. -/
theorem map_over : map U D e ≫ projection D = baseMap U D e ≫ U.2.fromSpec :=
  (isPullback U D e).w

attribute [local instance] isOpenImmersion

/-- The actual whole original raw chart has EXACTLY the original whole
preimage of U as its open range. -/
theorem opensRange_map : (map U D e).opensRange = projection D ⁻¹ᵁ U.1 := by
  let : IsOpenImmersion U.2.fromSpec := by
    change IsOpenImmersion (U.2.isoSpec.inv ≫ U.1.ι)
    infer_instance
  apply TopologicalSpace.Opens.ext
  change Set.range (map U D e) = projection D ⁻¹' (U.1 : Set X)
  let H := isPullback U D e
  have hsurj : Function.Surjective H.isoPullback.hom := by
    intro z
    obtain ⟨p, hp⟩ := (Scheme.homeoOfIso H.isoPullback).surjective z
    exact ⟨p, by rw [← Scheme.homeoOfIso_apply]; exact hp⟩
  have hcomp : ⇑(H.isoPullback.hom ≫ Limits.pullback.fst (projection D) U.2.fromSpec) =
      ⇑(Limits.pullback.fst (projection D) U.2.fromSpec) ∘ ⇑H.isoPullback.hom :=
    funext fun p => Scheme.Hom.comp_apply _ _ p
  rw [← H.isoPullback_hom_fst, hcomp, Set.range_comp, Set.range_eq_univ.mpr hsurj,
    Set.image_univ, Scheme.Pullback.range_fst, U.2.range_fromSpec]

end EnvelopeProperty.Vanishing.NadelGlobalNormalization.RawChart
