/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeSeparatedSections
import EnvelopeProperty.Berkovich.SpectrumTensorFilters
import EnvelopeProperty.Berkovich.SchemeRelativeAtlas

/-!
# Native Hausdorff topology for separated schemes

The genuine separated intersection section tensor map bounds ultrafilters
in an actual affine intersection. Whole-point affine limit uniqueness
then proves Hausdorffness of the independently defined native topology.
Prescribed-base spaces inherit it for separated structure morphisms to
affine bases, without coefficient bounds or finite type.
-/


open scoped NNReal Topology TensorProduct
open Topology Filter CategoryTheory AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EnvelopeProperty.Berkovich.SchemeValuedPoint
variable {X : Scheme.{u}}

/-- The actual inclusion of one native support open in another. -/
def supportInclusion {U V : X.Opens} (h : U ≤ V) :
    {y : SchemeValuedPoint X // y.point ∈ U} → {y : SchemeValuedPoint X // y.point ∈ V} :=
  fun y => ⟨y.1, h y.2⟩

theorem continuous_supportInclusion {U V : X.Opens} (h : U ≤ V) :
    Continuous (supportInclusion h) := continuous_subtype_val.subtype_mk _

/-- The same original section has identical values in genuine nested affine charts. -/
theorem affineOpenSpectrumHomeomorph_restrict {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V)
    (y : {y : SchemeValuedPoint X // y.point ∈ U}) (s : Γ(X, V)) :
    (affineOpenSpectrumHomeomorph hU y).val (X.presheaf.map (homOfLE h).op s) =
      (affineOpenSpectrumHomeomorph hV (supportInclusion h y)).val s := by
  rw [affineOpenSpectrumHomeomorph_val_apply, affineOpenSpectrumHomeomorph_val_apply]
  exact eval_restrict y.1 V U h y.2 s

private local instance (priority := low) separatedIntegerAlgebra (A : Type u) [CommRing A] :
    Algebra (ULift.{u} ℤ) A := EnvelopeProperty.liftedIntegerAlgebra A
private local instance separatedIntegerModule (A : Type u) [CommRing A] :
    Module (ULift.{u} ℤ) A := Algebra.toModule

/-- Two limits of a native ultrafilter on a separated scheme agree, using the genuine section tensor comparison. -/
theorem eq_of_ultrafilter_le_nhds [X.IsSeparated] {y₁ y₂ : SchemeValuedPoint X}
    (F : Ultrafilter (SchemeValuedPoint X))
    (h₁ : (F : Filter _) ≤ 𝓝 y₁) (h₂ : (F : Filter _) ≤ 𝓝 y₂) : y₁ = y₂ := by
  classical
  obtain ⟨U, hU, hy₁, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := y₁.point) trivial
  obtain ⟨V, hV, hy₂, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := y₂.point) trivial
  let W := U ⊓ V
  have hW : IsAffineOpen W := hU.inf hV
  let D := {y : SchemeValuedPoint X // y.point ∈ W}
  have hlarge : Set.range (Subtype.val : D → SchemeValuedPoint X) ∈ F := by
    have hUm : {y : SchemeValuedPoint X | y.point ∈ U} ∈ F :=
      h₁ (isOpen_point_preimage U |>.mem_nhds hy₁)
    have hVm : {y : SchemeValuedPoint X | y.point ∈ V} ∈ F :=
      h₂ (isOpen_point_preimage V |>.mem_nhds hy₂)
    rw [Subtype.range_coe_subtype]
    exact inter_mem hUm hVm
  let G : Ultrafilter D := F.comap Subtype.val_injective hlarge
  have ht₁ : Tendsto (supportInclusion (show W ≤ U from inf_le_left)) G (𝓝 ⟨y₁, hy₁⟩) := by
    apply IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr
    exact Filter.map_comap_le.trans h₁
  have ht₂ : Tendsto (supportInclusion (show W ≤ V from inf_le_right)) G (𝓝 ⟨y₂, hy₂⟩) := by
    apply IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr
    exact Filter.map_comap_le.trans h₂
  let e := affineOpenSpectrumHomeomorph hW
  let H := Ultrafilter.map e G
  let φ := EnvelopeProperty.SchemeSeparatedSections.tensorSectionMap
    (⟨U, hU⟩ : X.affineOpens) (⟨V, hV⟩ : X.affineOpens)
  have hA : ∀ a : Γ(X, U), ∃ M : ℝ≥0, ∀ᶠ z in (H : Filter (Spectrum Γ(X, W))),
      z.val (φ (a ⊗ₜ[ULift.{u} ℤ] (1 : Γ(X, V)))) ≤ M := by
    intro a
    have ht := (Spectrum.continuous_val_apply a).tendsto (affineOpenSpectrumHomeomorph hU ⟨y₁, hy₁⟩)
    have hg := ht.comp ((affineOpenSpectrumHomeomorph hU).continuous.tendsto _ |>.comp ht₁)
    obtain ⟨M, hM⟩ := hg.isBoundedUnder_le
    change ∀ᶠ z in (G : Filter D), (affineOpenSpectrumHomeomorph hU (supportInclusion inf_le_left z)).val a ≤ M at hM
    refine ⟨M, ?_⟩
    change ∀ᶠ z in (G : Filter D), (e z).val (φ (a ⊗ₜ[ULift.{u} ℤ] (1 : Γ(X, V)))) ≤ M
    have ha := RingHom.congr_fun (EnvelopeProperty.SchemeSeparatedSections.tensorSectionMap_comp_includeLeft
      (⟨U, hU⟩ : X.affineOpens) (⟨V, hV⟩ : X.affineOpens)) a
    change φ (a ⊗ₜ[ULift.{u} ℤ] (1 : Γ(X, V))) = X.presheaf.map (homOfLE (show W ≤ U from inf_le_left)).op a at ha
    exact hM.mono fun z hz => by
      rw [ha, affineOpenSpectrumHomeomorph_restrict hW hU inf_le_left]
      exact hz
  have hB : ∀ b : Γ(X, V), ∃ M : ℝ≥0, ∀ᶠ z in (H : Filter (Spectrum Γ(X, W))),
      z.val (φ ((1 : Γ(X, U)) ⊗ₜ[ULift.{u} ℤ] b)) ≤ M := by
    intro b
    have ht := (Spectrum.continuous_val_apply b).tendsto (affineOpenSpectrumHomeomorph hV ⟨y₂, hy₂⟩)
    have hg := ht.comp ((affineOpenSpectrumHomeomorph hV).continuous.tendsto _ |>.comp ht₂)
    obtain ⟨M, hM⟩ := hg.isBoundedUnder_le
    change ∀ᶠ z in (G : Filter D), (affineOpenSpectrumHomeomorph hV (supportInclusion inf_le_right z)).val b ≤ M at hM
    refine ⟨M, ?_⟩
    change ∀ᶠ z in (G : Filter D), (e z).val (φ ((1 : Γ(X, U)) ⊗ₜ[ULift.{u} ℤ] b)) ≤ M
    have hb := RingHom.congr_fun (EnvelopeProperty.SchemeSeparatedSections.tensorSectionMap_comp_includeRight
      (⟨U, hU⟩ : X.affineOpens) (⟨V, hV⟩ : X.affineOpens)) b
    change φ ((1 : Γ(X, U)) ⊗ₜ[ULift.{u} ℤ] b) = X.presheaf.map (homOfLE (show W ≤ V from inf_le_right)).op b at hb
    exact hM.mono fun z hz => by
      rw [hb, affineOpenSpectrumHomeomorph_restrict hW hV inf_le_right]
      exact hz
  obtain ⟨z, hz⟩ := Spectrum.exists_ultrafilter_limit_of_tensor_bounds φ
    (EnvelopeProperty.SchemeSeparatedSections.tensorSectionMap_surjective
      (⟨U, hU⟩ : X.affineOpens) (⟨V, hV⟩ : X.affineOpens)) H hA hB
  have hg : Tendsto (id : D → D) G (𝓝 (e.symm z)) := by
    apply e.isEmbedding.tendsto_nhds_iff.mpr
    rw [Homeomorph.apply_symm_apply]
    change (H : Filter (Spectrum Γ(X, W))) ≤ 𝓝 z
    exact hz
  have hu := (continuous_supportInclusion (show W ≤ U from inf_le_left)).tendsto (e.symm z) |>.comp hg
  have hv := (continuous_supportInclusion (show W ≤ V from inf_le_right)).tendsto (e.symm z) |>.comp hg
  have hi₁ : supportInclusion (show W ≤ U from inf_le_left) (e.symm z) = ⟨y₁, hy₁⟩ := by
    apply (affineOpenSpectrumHomeomorph hU).injective
    exact tendsto_nhds_unique ((affineOpenSpectrumHomeomorph hU).continuous.tendsto _ |>.comp hu)
      ((affineOpenSpectrumHomeomorph hU).continuous.tendsto _ |>.comp ht₁)
  have hi₂ : supportInclusion (show W ≤ V from inf_le_right) (e.symm z) = ⟨y₂, hy₂⟩ := by
    apply (affineOpenSpectrumHomeomorph hV).injective
    exact tendsto_nhds_unique ((affineOpenSpectrumHomeomorph hV).continuous.tendsto _ |>.comp hv)
      ((affineOpenSpectrumHomeomorph hV).continuous.tendsto _ |>.comp ht₂)
  exact (congrArg Subtype.val hi₁).symm.trans (congrArg Subtype.val hi₂)

/-- The actual native valued-point topology is Hausdorff for every separated scheme. -/
instance t2Space_of_isSeparated [X.IsSeparated] : T2Space (SchemeValuedPoint X) :=
  t2_iff_ultrafilter.mpr fun F h₁ h₂ => eq_of_ultrafilter_le_nhds F h₁ h₂
end EnvelopeProperty.Berkovich.SchemeValuedPoint

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- A separated structure morphism to an affine base gives genuine Hausdorff native prescribed-base points. -/
instance t2Space_of_isSeparated [IsSeparated f] : T2Space (RelativeSchemeValuedPoint v f) := by
  let : X.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from f]
    infer_instance⟩
  exact inferInstanceAs (T2Space {y : SchemeValuedPoint X // y ∈ SchemeValuedPoint.relativeLocus v f})
end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
