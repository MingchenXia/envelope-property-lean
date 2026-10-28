/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeRelativeAtlas
import EnvelopeProperty.Berkovich.SchemeCenter
import EnvelopeProperty.Berkovich.SpectrumTopology

/-!
# Actual compact proper native spaces over bounded prescribed coefficients

Actual inverse affine charts map the genuinely compact all-element radius-one
relative spectra to compact native images. True proper centers put every
point into one such image. Genuine scheme quasi-compactness produces a finite
affine cover, whose actual compact images prove compactness of the whole
native prescribed-base space. No finite-type or Hausdorff hypothesis on any
section spectrum is used; every prescribed coefficient must be at most one.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite

universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- The genuine native image of the bounded relative spectrum of an actual affine section ring. -/
def boundedAffineImage (v : Valuation R ℝ≥0) (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.affineOpens) : Set (RelativeSchemeValuedPoint v f) := by
  letI := SchemeValuedPoint.sectionBaseAlgebra f U.1
  exact (fun x : RelativeSpectrum v Γ(X, U) =>
    ((affineOpenSpectrumHomeomorph U.2).symm x : RelativeSchemeValuedPoint v f)) ''
      {x : RelativeSpectrum v Γ(X, U) | Spectrum.IsBounded x.1}

/-- All-element radius-one bounds give compact actual affine images, without section-ring finite type. -/
theorem isCompact_boundedAffineImage (v : Valuation R ℝ≥0) (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.affineOpens) : IsCompact (boundedAffineImage v f U) := by
  let := SchemeValuedPoint.sectionBaseAlgebra f U.1
  have hc : IsCompact {x : RelativeSpectrum v Γ(X, U) | Spectrum.IsBounded x.1} :=
    RelativeSpectrum.isCompact_setOf_forall_val_le (fun _ => 1)
  exact hc.image (continuous_subtype_val.comp (affineOpenSpectrumHomeomorph U.2).symm.continuous)

/-- Actual center neighborhoods provide genuine bounded affine spectrum representatives. -/
theorem mem_boundedAffineImage_of_center_mem [IsProper f] (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (U : X.affineOpens) (hc : center hb y ∈ U.1) :
    y ∈ boundedAffineImage v f U := by
  let := SchemeValuedPoint.sectionBaseAlgebra f U.1
  let z : {y : RelativeSchemeValuedPoint v f // y.1.point ∈ U.1} :=
    ⟨y, support_mem_of_center_mem hb y U.1 hc⟩
  refine ⟨affineOpenSpectrumHomeomorph U.2 z, ?_, ?_⟩
  · intro s
    rw [affineOpenSpectrumHomeomorph_val_apply]
    exact eval_le_one_of_center_mem hb y U.1 hc s
  · exact congrArg Subtype.val ((affineOpenSpectrumHomeomorph U.2).symm_apply_apply z)

/-- A genuine affine scheme cover covers the entire native proper point space by compact bounded images. -/
theorem iUnion_boundedAffineImage_eq_univ [IsProper f] (hb : ∀ r, v r ≤ 1)
    {ι : Type u} (U : ι → X.affineOpens) (hcover : (⋃ i, (U i).1.carrier) = Set.univ) :
    (⋃ i, boundedAffineImage v f (U i)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  have hc : center hb y ∈ ⋃ i, (U i).1.carrier := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hc
  exact Set.mem_iUnion.mpr ⟨i, mem_boundedAffineImage_of_center_mem hb y (U i) hi⟩

/-- Any actual finite affine cover gives compactness via true compact images, without a Hausdorff assumption. -/
theorem isCompact_univ_of_finite_affine_cover [IsProper f] (hb : ∀ r, v r ≤ 1)
    {ι : Type u} [Finite ι] (U : ι → X.affineOpens) (hcover : (⋃ i, (U i).1.carrier) = Set.univ) :
    IsCompact (Set.univ : Set (RelativeSchemeValuedPoint v f)) := by
  rw [← iUnion_boundedAffineImage_eq_univ hb U hcover]
  exact isCompact_iUnion fun i => isCompact_boundedAffineImage v f (U i)

/-- Genuine scheme quasi-compactness produces the finite affine cover; native proper spectra over bounded prescribed coefficients are compact. -/
theorem compactSpace_of_isProper [IsProper f] (hb : ∀ r, v r ≤ 1) :
    CompactSpace (RelativeSchemeValuedPoint v f) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨s, hs, hcover⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
    (show IsCompact (Set.univ : Set X) ∧ IsOpen (Set.univ : Set X) from ⟨isCompact_univ, isOpen_univ⟩)
  let : Finite s := hs.to_subtype
  apply isCompact_univ_iff.mp
  apply isCompact_univ_of_finite_affine_cover hb (fun i : s => i.1)
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ U ∈ s, (U.1 : Set X) := by rw [← hcover]; trivial
  obtain ⟨U, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hU, hxU⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
