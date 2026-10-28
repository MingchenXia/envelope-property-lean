/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeCenterAnticontinuity
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Genuine locally Noetherian model specialization

Actual affine section rings on a locally Noetherian scheme are Noetherian,
so their genuine ideals are finitely generated. This discharges the general
model norm/logarithm continuity and support-open hypotheses. Actual proper
quasi-compactness supplies global scheme/topological Noetherianity and full
true-center anti-continuity. Prescribed coefficient bounds remain explicit.
-/


open scoped NNReal Topology
open Topology TopologicalSpace CategoryTheory AlgebraicGeometry Opposite
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X : Scheme.{u}}

/-- Actual local Noetherianity makes every genuine affine ideal finitely generated. -/
theorem affineIdeals_fg_of_isLocallyNoetherian [IsLocallyNoetherian X] (I : X.IdealSheafData) :
    ∀ U : X.affineOpens, (I.ideal U).FG := by
  intro U
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  exact Ideal.fg_of_isNoetherianRing _
end AlgebraicGeometry.Scheme.IdealSheafData

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- Genuine local Noetherianity discharges affine finite generation for continuous intrinsic proper-model norms. -/
theorem continuous_modelIdealNorm_of_isLocallyNoetherian [IsProper f] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1) :
    Continuous (modelIdealNorm (v := v) (f := f) I hb) :=
  continuous_modelIdealNorm_of_fg I hb I.affineIdeals_fg_of_isLocallyNoetherian

/-- The genuine logarithmic model ideal is continuous on every locally Noetherian proper model over bounded coefficients. -/
theorem continuous_modelIdealLog_of_isLocallyNoetherian [IsProper f] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1) :
    Continuous (modelIdealLog (v := v) (f := f) I hb) :=
  continuous_modelIdealLog_of_fg I hb I.affineIdeals_fg_of_isLocallyNoetherian

/-- Genuine local Noetherianity makes every actual ideal support have an open true-center inverse image. -/
theorem isOpen_center_preimage_idealSupport_of_isLocallyNoetherian [IsProper f] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hb : ∀ r, v r ≤ 1) :
    IsOpen ((center (v := v) (f := f) hb) ⁻¹' (I.support : Set X)) :=
  isOpen_center_preimage_idealSupport_of_fg I hb I.affineIdeals_fg_of_isLocallyNoetherian

/-- Actual proper quasi-compactness turns local scheme Noetherianity into the topological finiteness needed for full center anti-continuity. -/
theorem isClosed_center_preimage_of_isLocallyNoetherian [IsProper f] [IsLocallyNoetherian X]
    (hb : ∀ r, v r ≤ 1) (U : X.Opens) :
    IsClosed ((center (v := v) (f := f) hb) ⁻¹' (U : Set X)) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  exact isClosed_center_preimage_of_noetherian hb U

/-- All actual closed subsets have open center inverse images on a locally Noetherian proper model. -/
theorem isOpen_center_preimage_of_isClosed_of_isLocallyNoetherian [IsProper f] [IsLocallyNoetherian X]
    (hb : ∀ r, v r ≤ 1) (C : Set X) (hC : IsClosed C) :
    IsOpen ((center (v := v) (f := f) hb) ⁻¹' C) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  exact isOpen_center_preimage_of_isClosed hb C hC
end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
