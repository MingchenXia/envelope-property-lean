/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeModelIdeals

/-!
# Genuine native and model-center supports of intrinsic model ideal norms

Actual scheme ideal support equals maximal-ideal containment of the genuine
stalk ideal. Original native section-value vanishing detects that support.
The intrinsic model norm zero locus and logarithmic bottom locus therefore
detect the original native support and are genuinely closed. A strict
smaller-than-one norm detects support at the TRUE model center, with the
converse requiring explicitly supplied finite affine generators. No global
continuity or center anti-continuity is supplied by these support results.
-/

open scoped NNReal ENNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite

universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The genuine stalk ideal is contained in the actual maximal ideal precisely on the actual scheme ideal-sheaf support. -/
theorem stalkIdeal_le_maximalIdeal_iff_mem_support (I : X.IdealSheafData) (x : X) :
    I.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔ x ∈ I.support := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  rw [I.stalkIdeal_eq_affine x ⟨U, hU⟩ hx, Ideal.map_le_iff_le_comap,
    I.mem_support_iff_of_mem (U := ⟨U, hU⟩) hx, Scheme.mem_zeroLocus_iff]
  change (∀ s ∈ I.ideal ⟨U, hU⟩, X.presheaf.germ U x hx s ∈
    IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ↔ ∀ s ∈ I.ideal ⟨U, hU⟩, x ∉ X.basicOpen s
  apply forall_congr'
  intro s
  apply forall_congr'
  intro hs
  change ¬ IsUnit (X.presheaf.germ U x hx s) ↔ x ∉ X.basicOpen s
  exact not_congr (Scheme.mem_basicOpen X s x hx).symm

end AlgebraicGeometry.Scheme.IdealSheafData

namespace EnvelopeProperty.Berkovich.SchemeValuedPoint

variable {X : Scheme.{u}}

/-- Actual section-ideal seminorm vanishing detects the genuine ideal-sheaf support at the original native point. -/
theorem sectionIdealNorm_eq_zero_iff_mem_support (I : X.IdealSheafData)
    (y : SchemeValuedPoint X) (U : X.affineOpens) (hy : y.point ∈ U.1) :
    Spectrum.idealNorm (I.ideal U)
      (Spectrum.ofValuation (y.residueVal.comap (X.evaluation U.1 y.point hy).hom)) = 0 ↔
        y.point ∈ I.support := by
  rw [Spectrum.idealNorm_eq_zero_iff, I.mem_support_iff_of_mem hy, Scheme.mem_zeroLocus_iff]
  change (∀ s ∈ I.ideal U, eval y U.1 hy s = 0) ↔ ∀ s ∈ I.ideal U, y.point ∉ X.basicOpen s
  simp only [eval_eq_zero_iff]

end EnvelopeProperty.Berkovich.SchemeValuedPoint

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- Intrinsic model-ideal norm vanishing detects genuine ideal-sheaf support at the NATIVE support, not only at the model center. -/
theorem modelIdealNorm_eq_zero_iff [IsProper f] (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) : modelIdealNorm I hb y = 0 ↔ y.1.point ∈ I.support := by
  obtain ⟨U, hU, hc, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := center hb y) trivial
  rw [modelIdealNorm_eq_affine I hb y ⟨U, hU⟩ hc]
  exact SchemeValuedPoint.sectionIdealNorm_eq_zero_iff_mem_support I y.1 ⟨U, hU⟩
    (support_mem_of_center_mem hb y U hc)

/-- The negative-infinite logarithmic model-ideal locus is exactly the original native scheme support locus. -/
theorem modelIdealLog_eq_bot_iff [IsProper f] (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) : modelIdealLog I hb y = ⊥ ↔ y.1.point ∈ I.support := by
  rw [modelIdealLog, ENNReal.log_eq_bot_iff, modelIdealNorm_eq_zero_iff]

/-- The genuine native zero locus of an intrinsic model ideal norm is closed. -/
theorem isClosed_modelIdealNorm_zeroLocus [IsProper f] (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1) :
    IsClosed {y : RelativeSchemeValuedPoint v f | modelIdealNorm I hb y = 0} := by
  have he : {y : RelativeSchemeValuedPoint v f | modelIdealNorm I hb y = 0} =
      (fun y => y.1.point) ⁻¹' (I.support : Set X) := by
    ext y
    exact modelIdealNorm_eq_zero_iff I hb y
  rw [he]
  exact I.support.isClosed.preimage (SchemeValuedPoint.continuous_point.comp continuous_subtype_val)

/-- A strictly smaller-than-one intrinsic norm implies actual support at the MODEL center, without finite generators. -/
theorem center_mem_support_of_modelIdealNorm_lt_one [IsProper f] (I : X.IdealSheafData)
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) (h : modelIdealNorm I hb y < 1) :
    center hb y ∈ I.support := by
  apply (I.stalkIdeal_le_maximalIdeal_iff_mem_support (center hb y)).mp
  intro a ha
  apply (centerStalkVal_lt_one_iff hb y a).mp
  have hv := Spectrum.val_le_idealNorm (I.stalkIdeal (center hb y)) (centerStalkSpectrum hb y) ha
  exact_mod_cast hv.trans_lt h

/-- Actual finite generators supply the converse: norm smaller than one detects closed-ideal support at the TRUE center. -/
theorem modelIdealNorm_lt_one_iff_of_generators [IsProper f] (I : X.IdealSheafData)
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) (U : X.affineOpens)
    (hc : center hb y ∈ U.1) (S : Finset Γ(X, U))
    (hS : I.ideal U = Ideal.span (S : Set Γ(X, U))) :
    modelIdealNorm I hb y < 1 ↔ center hb y ∈ I.support := by
  rw [modelIdealNorm_eq_generators I hb y U hc S hS,
    ← I.stalkIdeal_le_maximalIdeal_iff_mem_support (center hb y),
    I.stalkIdeal_eq_affine (center hb y) U hc, hS, Ideal.map_span, Ideal.span_le]
  simp only [ENNReal.coe_lt_one_iff, Finset.sup_lt_iff (show (⊥ : ℝ≥0) < 1 from zero_lt_one),
    Set.subset_def, SetLike.mem_coe, ← centerStalkVal_lt_one_iff, Set.forall_mem_image]
  change (∀ s ∈ S, SchemeValuedPoint.eval y.1 U.1 _ s < 1) ↔
    ∀ s ∈ S, centerStalkVal hb y (X.presheaf.germ U.1 (center hb y) hc s) < 1
  simp only [centerStalkVal_germ]

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
