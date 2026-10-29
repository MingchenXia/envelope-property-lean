import EnvelopeProperty.Vanishing.NadelPrincipalizationAffineChart
import EnvelopeProperty.Char0.SchemeMultiplierIdealSheaf

/-! # The original multiplier ideal uses the actual principalization field chart -/

open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationAffineChart
variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k))
attribute [local instance] algebra_isFractionRing

/-- The original scheme multiplier affine ideal uses exactly this same
literal chart algebra and ideal, through the original coefficient map. -/
theorem multiplierAffineIdeal_eq_comap (I : X.IdealSheafData)
    (hI : I.stalkIdeal (genericPoint X) ≠ ⊥) (q : ℚ)
    (U : X.affineOpens) [Nonempty U.1] :
    letI := f.stalkAlgebra (genericPoint X)
    Char0.schemeMultiplierAffineIdeal f I hI q U =
      (Char0.valuativeMultiplierIdeal (algebra f U) (ideal f I U)
        (ideal_ne_bot f I hI U) q).comap (ringEquiv f U).toRingHom := by
  simp only [Char0.schemeMultiplierAffineIdeal, dif_pos (inferInstance : Nonempty U.1)]
  rfl

end EnvelopeProperty.Vanishing.NadelPrincipalizationAffineChart
