/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.DVRLogDerivatives

/-!
# The actual divisorial-coordinate logarithmic Jacobian bound

The constructed DVR-coordinate partials preserve the actual valuation ring.
Their restrictions are actual derivations and produce the logarithmic bound
for the original actual field Jacobian and log discrepancy.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open IsDiscreteValuationRing IsLocalRing
open scoped Classical

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [CharZero F]
  (V : Subalgebra F K) [IsDiscreteValuationRing V] [IsFractionRing V K]
  [Algebra.EssFiniteType F V] {ι : Type*} [Fintype ι]
  {π : V} {u : ι → V}

/-- The actual field coordinate partial restricts to an actual DVR derivation, with its
preservation produced by the primitive-coordinate theorem. -/
def dvrCoordinatePartial (hπ : Irreducible π)
    (hu : IsTranscendenceBasis F (residue V ∘ u)) (j : Option ι) : Derivation F V V where
  toFun x := ⟨partialDeriv (isTranscendenceBasis_dvrCoordinates hπ hu) j (x : K),
    partialDeriv_mem hπ hu j x.2⟩
  map_add' x y := Subtype.ext (map_add _ (x : K) (y : K))
  map_smul' c x := Subtype.ext (Derivation.map_smul _ c (x : K))
  map_one_eq_zero' := Subtype.ext (Derivation.map_one_eq_zero _)
  leibniz' x y := Subtype.ext (Derivation.leibniz _ (x : K) (y : K))

/-- The actual restricted residue-coordinate partial annihilates the uniformizer. -/
theorem dvrCoordinatePartial_uniformizer_some (hπ : Irreducible π)
    (hu : IsTranscendenceBasis F (residue V ∘ u)) (i : ι) :
    dvrCoordinatePartial V hπ hu (some i) π = 0 := by
  apply Subtype.ext
  change partialDeriv (isTranscendenceBasis_dvrCoordinates hπ hu) (some i)
    (dvrCoordinates π u none) = 0
  rw [partialDeriv_apply]
  simp

/-- The determinant of the restricted actual derivatives is exactly the original actual
field-coordinate Jacobian under the DVR inclusion. -/
theorem coe_det_dvrCoordinatePartial (hπ : Irreducible π)
    (hu : IsTranscendenceBasis F (residue V ∘ u)) (z : Option ι → V) :
    ((Matrix.of fun i j => dvrCoordinatePartial V hπ hu j (z i)).det : K) =
      jacobian (isTranscendenceBasis_dvrCoordinates hπ hu) (fun i => (z i : K)) := by
  have h := (V.val : V →+* K).map_det (Matrix.of fun i j =>
    dvrCoordinatePartial V hπ hu j (z i))
  exact h

/-- The sum of actual coordinate orders is bounded by the actual log discrepancy in the
produced DVR coordinates, without an assumed Jacobian or derivative bound. -/
theorem sum_addVal_le_logDiscrepancy (hπ : Irreducible π)
    (hu : IsTranscendenceBasis F (residue V ∘ u)) (z : Option ι → V) :
    (∑ i, addVal V (z i)) ≤ logDiscrepancy hπ hu (fun i => (z i).2) := by
  have h := sum_addVal_le_one_add_addVal_jacobian (dvrCoordinatePartial V hπ hu) hπ
    (dvrCoordinatePartial_uniformizer_some V hπ hu) z
  have hdet : (Matrix.of fun i j => dvrCoordinatePartial V hπ hu j (z i)).det =
      (⟨jacobian (isTranscendenceBasis_dvrCoordinates hπ hu) (fun i => (z i : K)),
        jacobian_mem hπ hu (fun i => (z i).2)⟩ : V) := by
    apply Subtype.ext
    exact coe_det_dvrCoordinatePartial V hπ hu z
  rw [hdet] at h
  exact h

end EnvelopeProperty.Char0
