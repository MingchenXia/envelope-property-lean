/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeCenterAffine
import EnvelopeProperty.Berkovich.SchemeHausdorff
import Mathlib.Topology.LocallyFinite

/-!
# Continuous genuine model ideal functions by finite closed pasting

Actual bounded affine images are compact and Hausdorff, hence closed.
Real finite generators give continuous intrinsic model norms on each piece.
True proper quasi-compactness and finite closed pasting yield global norm
and logarithm continuity for explicitly locally finitely generated actual
ideal-sheaf data. Prescribed coefficient boundedness remains explicit.
-/


open scoped NNReal ENNReal Topology
open Topology Filter CategoryTheory AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- Genuine compact bounded affine images are closed in the proven Hausdorff native space. -/
theorem isClosed_boundedAffineImage [IsSeparated f] (U : X.affineOpens) :
    IsClosed (boundedAffineImage v f U) := (isCompact_boundedAffineImage v f U).isClosed

/-- The actual center inverse image of a genuine affine open is closed, by the proved bounded-center criterion. -/
theorem isClosed_center_preimage_affine [IsProper f] (hb : ∀ r, v r ≤ 1) (U : X.affineOpens) :
    IsClosed ((center (v := v) (f := f) hb) ⁻¹' (U.1 : Set X)) := by
  rw [← boundedAffineImage_eq_center_preimage hb U]
  exact isClosed_boundedAffineImage U

/-- Finite affine generators give continuous intrinsic model norms on the genuine closed bounded affine image. -/
theorem continuousOn_modelIdealNorm_boundedAffineImage [IsProper f]
    (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1) (U : X.affineOpens)
    (S : Finset Γ(X, U)) (hS : I.ideal U = Ideal.span (S : Set Γ(X, U))) :
    ContinuousOn (modelIdealNorm (v := v) (f := f) I hb) (boundedAffineImage v f U) := by
  let := SchemeValuedPoint.sectionBaseAlgebra f U.1
  let c : {y : RelativeSchemeValuedPoint v f // y ∈ boundedAffineImage v f U} →
      {y : RelativeSchemeValuedPoint v f // y.1.point ∈ U.1} := fun y =>
    ⟨y.1, support_mem_of_center_mem hb y.1 U.1 (center_mem_of_mem_boundedAffineImage hb y.1 U y.2)⟩
  have hc : Continuous c := continuous_subtype_val.subtype_mk _
  have he : Continuous fun y : {y : RelativeSchemeValuedPoint v f // y ∈ boundedAffineImage v f U} =>
      (affineOpenSpectrumHomeomorph U.2 (c y)).1 :=
    continuous_subtype_val.comp ((affineOpenSpectrumHomeomorph U.2).continuous.comp hc)
  have hn : Continuous fun y : {y : RelativeSchemeValuedPoint v f // y ∈ boundedAffineImage v f U} =>
      ((S.sup fun s => (affineOpenSpectrumHomeomorph U.2 (c y)).1.val s : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.continuous_coe.comp (Continuous.finset_sup_apply fun s _ =>
      (Spectrum.continuous_val_apply s).comp he)
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hn.congr
  intro y
  change ((S.sup fun s => (affineOpenSpectrumHomeomorph U.2 (c y)).1.val s : ℝ≥0) : ℝ≥0∞) = modelIdealNorm I hb y.1
  rw [modelIdealNorm_eq_generators I hb y.1 U (center_mem_of_mem_boundedAffineImage hb y.1 U y.2) S hS]
  congr 1
  exact Finset.sup_congr rfl fun s _ => affineOpenSpectrumHomeomorph_val_apply U.2 (c y) s

/-- The genuine logarithmic model norm is continuous on each finitely generated bounded affine piece. -/
theorem continuousOn_modelIdealLog_boundedAffineImage [IsProper f]
    (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1) (U : X.affineOpens)
    (S : Finset Γ(X, U)) (hS : I.ideal U = Ideal.span (S : Set Γ(X, U))) :
    ContinuousOn (modelIdealLog (v := v) (f := f) I hb) (boundedAffineImage v f U) :=
  ENNReal.continuous_log.comp_continuousOn
    (continuousOn_modelIdealNorm_boundedAffineImage I hb U S hS)

/-- A genuine finite affine cover with actual finite ideal generators gives global continuity by finite closed pasting. -/
theorem continuous_modelIdealNorm_of_finite_affine_cover [IsProper f]
    (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1) {ι : Type u} [Finite ι]
    (U : ι → X.affineOpens) (hcover : (⋃ i, (U i).1.carrier) = Set.univ)
    (S : ∀ i, Finset Γ(X, U i))
    (hS : ∀ i, I.ideal (U i) = Ideal.span (S i : Set Γ(X, U i))) :
    Continuous (modelIdealNorm (v := v) (f := f) I hb) :=
  (locallyFinite_of_finite (fun i => boundedAffineImage v f (U i))).continuous
    (iUnion_boundedAffineImage_eq_univ hb U hcover)
    (fun i => isClosed_boundedAffineImage (U i))
    (fun i => continuousOn_modelIdealNorm_boundedAffineImage I hb (U i) (S i) (hS i))

/-- Actual local finite generation on every affine and true proper quasi-compactness yield continuous intrinsic model norms. -/
theorem continuous_modelIdealNorm_of_fg [IsProper f] (I : X.IdealSheafData)
    (hb : ∀ r, v r ≤ 1) (hfg : ∀ U : X.affineOpens, (I.ideal U).FG) :
    Continuous (modelIdealNorm (v := v) (f := f) I hb) := by
  classical
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let C := X.affineCover.finiteSubcover
  let U : C.I₀ → X.affineOpens := fun i => ⟨(C.f i).opensRange, isAffineOpen_opensRange (C.f i)⟩
  have hcover : (⋃ i, (U i).1.carrier) = Set.univ := by
    exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨C.idx x, C.covers x⟩
  choose S hS using fun i => hfg (U i)
  exact continuous_modelIdealNorm_of_finite_affine_cover I hb U hcover S (fun i => (hS i).symm)

/-- The genuine global logarithm is continuous, including the zero ideal's negative-infinite value. -/
theorem continuous_modelIdealLog_of_fg [IsProper f] (I : X.IdealSheafData)
    (hb : ∀ r, v r ≤ 1) (hfg : ∀ U : X.affineOpens, (I.ideal U).FG) :
    Continuous (modelIdealLog (v := v) (f := f) I hb) :=
  ENNReal.continuous_log.comp (continuous_modelIdealNorm_of_fg I hb hfg)
end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
