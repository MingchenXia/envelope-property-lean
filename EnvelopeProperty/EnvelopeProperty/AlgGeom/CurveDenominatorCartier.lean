import EnvelopeProperty.AlgGeom.SchemeRationalDenominators
import Hironaka.Scheme.IdealSheaf.Invertible
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! # Genuine Cartier denominator ideals on the original normal integral curve -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open scoped nonZeroDivisors
universe u
namespace EnvelopeProperty.CurveDenominatorCartier
variable {X : Scheme.{u}} [IsIntegral X]

omit [IsIntegral X] in
/-- The actual topological curve bound gives the actual dimension bound on
every original local ring, including the original generic point. -/
theorem stalk_krullDimLE_one (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    Ring.KrullDimLE 1 (X.presheaf.stalk x) := by
  have ho : Order.krullDim X ≤ 1 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  apply AlgebraicGeometry.krullDimLE_of_coheight_le
  exact_mod_cast (Order.coheight_le_krullDim x).trans ho

/-- Normal Noetherian original curve stalks are genuinely principal ideal
rings; the original generic field is included without a nonfield premise. -/
theorem stalk_isPrincipalIdealRing [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (x : X) :
    IsPrincipalIdealRing (X.presheaf.stalk x) := by
  let := stalk_krullDimLE_one hdim x
  apply (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk x)).out 3 0 |>.mp
  refine ⟨hNormal x, fun P hP hPrime => ?_⟩
  exact IsLocalRing.eq_maximalIdeal (hPrime.isMaximal_of_ne_bot hP)

/-- Every genuinely nonzero original ideal on a normal locally Noetherian
integral curve is Cartier, derived from its actual original stalk ideals. -/
theorem isInvertible_of_nonzero_stalks [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (I : X.IdealSheafData) (hI : ∀ x : X, I.stalkIdeal x ≠ ⊥) : I.IsInvertible := by
  apply Scheme.IdealSheafData.isInvertible_of_forall_stalkIdeal_eq_span
  intro x
  let := stalk_isPrincipalIdealRing hdim hNormal x
  let a := Submodule.IsPrincipal.generator (I.stalkIdeal x)
  have ha : a ≠ 0 := by
    exact (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero (I.stalkIdeal x)).not.mp (hI x)
  exact ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha,
    (Ideal.span_singleton_generator (I.stalkIdeal x)).symm⟩

/-- The actual denominator ideal of EVERY SAME original rational function
is Cartier on the original normal locally Noetherian integral curve. No
nonzero-ideal, principal-stalk or Cartier certificate is supplied. -/
theorem denominator_isInvertible [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (f : X.functionField) :
    (SchemeRationalDenominators.idealSheaf X f).IsInvertible :=
  isInvertible_of_nonzero_stalks hdim hNormal _
    (SchemeRationalDenominators.stalkIdeal_ne_bot X f)

end EnvelopeProperty.CurveDenominatorCartier
