/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.ValuativeBound
import EnvelopeProperty.Char0.AssemblyInputs

/-!
# The valuative input of the characteristic-zero assembly

This file discharges the hypothesis `EnvelopeProperty.Char0.ValuativeUpperBound` of the
characteristic-zero assembly (`EnvelopeProperty.Char0.AssemblyInputs`): the field
`valuative_bound` is `prop:c0-valuative-bound` (`valuativeBound_of_coordinates`, applied to
coordinates `(π, u)` chosen once for each divisorial valuation ring `V`, with constant
`A = A(V) = 1 + ord_V(Jac_V)`), and the field `valuative_upper` (`cor:c0-valuative-upper`) follows
from it by `ValuativeUpperBound.of_valuative_bound`.

## Main results

* `EnvelopeProperty.Char0.valuativeBound_forall_dvr`: the field `valuative_bound`;
* `EnvelopeProperty.Char0.valuativeUpperBound_holds : ValuativeUpperBound`.
-/

noncomputable section

open MvPolynomial IsLocalRing

namespace EnvelopeProperty.Char0

/-- **`prop:c0-valuative-bound` in the form used by the assembly**: for every divisorial valuation
ring `V` over `ℂ` in `n + 2` variables there is `A` (the log discrepancy `A(V)` for coordinates
chosen at `V`) with `ord_V(f) > c ord_V(g) - A` whenever `g` is not identically zero, `c > 0` and
`f` is square integrable against `|g|^{-2c}`. -/
theorem valuativeBound_forall_dvr :
    ∀ (n : ℕ) (V : BirationalDVR ℂ (MvPolynomial (Fin (n + 2)) ℂ)), ∃ A : ℝ,
      ∀ (ι : Type) [Fintype ι] (g : ι → MvPolynomial (Fin (n + 2)) ℂ), (∃ j, g j ≠ 0) →
        ∀ c : ℝ, 0 < c → ∀ f : MvPolynomial (Fin (n + 2)) ℂ, IsSqIntegrableAgainst f g c →
          (c : EReal) * ((⨅ j, V.ord (g j) : ℕ∞) : EReal) - (A : EReal) < (V.ord f : EReal) := by
  intro n V
  obtain ⟨π, u, e, hπ, hu⟩ := BirationalDVR.exists_dvrCoordinates V
  refine ⟨(logDiscrepancy hπ hu (z := fun o => algebraMap (MvPolynomial (Fin (n + 2)) ℂ)
    (FractionRing (MvPolynomial (Fin (n + 2)) ℂ)) (X (e o)))
    (fun o => V.algebraMap_mem (X (e o)))).toNat, ?_⟩
  intro ι _ g hg c hc f hfg
  have hcast : ∀ N : ℕ, ((N : ℕ∞) : EReal) = ((N : ℝ) : EReal) := fun N => by norm_cast
  have ho : (⨅ j, V.ord (g j)) ≠ ⊤ := by
    obtain ⟨j, hj⟩ := hg
    exact ne_top_of_le_ne_top (V.ord_eq_top_iff.not.2 hj) (iInf_le _ j)
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 ho
  rw [← hb, hcast]
  by_cases hf : f = 0
  · rw [hf, V.ord_zero, show (((⊤ : ℕ∞)) : EReal) = ⊤ by simp, ← EReal.coe_mul, ← EReal.coe_sub]
    exact EReal.coe_lt_top _
  have hcore := valuativeBound_of_coordinates V hπ hu e g hg hc hf (fun K hK => hfg K hK)
    (b := b) (fun j => hb ▸ iInf_le _ j)
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (V.ord_eq_top_iff.not.2 hf)
  rw [← ha, ENat.toNat_natCast] at hcore
  rw [← ha, hcast, ← EReal.coe_mul, ← EReal.coe_sub, EReal.coe_lt_coe_iff]
  linarith

/-- **The valuative input of the characteristic-zero assembly holds** (`prop:c0-valuative-bound`
and `cor:c0-valuative-upper`). -/
theorem valuativeUpperBound_holds : ValuativeUpperBound :=
  ValuativeUpperBound.of_valuative_bound valuativeBound_forall_dvr

end EnvelopeProperty.Char0
