import EnvelopeProperty.Berkovich.SchemeResidueFrameComparison
import EnvelopeProperty.Berkovich.GeneratedLineGenericFrameNorms

/-! # Coherence of the genuine original frame transition units -/
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeResidueFrameTransition
open SchemeResidueFrameComparison SchemeModuleFrameCoefficients

variable {A : Type u} [CommRing A] {P : (Spec (.of A)).Modules}

/-- The derived genuine transition unit is the actual coefficient of the actual inverse-frame unit section. -/
theorem transitionUnit_val (e₀ e₁ : P ≅ Scheme.Modules.unitObj (Spec (.of A))) :
    (transitionUnit e₀ e₁ : A) =
      (Scheme.ΓSpecIso (.of A)).hom (e₁.hom.app ⊤ (unitSection e₀)) := by
  have hu : (Scheme.ΓSpecIso (.of A)).hom (e₀.hom.app ⊤ (unitSection e₀)) = (1 : A) := by
    exact (congrArg (Scheme.ΓSpecIso (.of A)).hom.hom (coefficient_unitSection e₀)).trans
      (map_one (Scheme.ΓSpecIso (.of A)).hom.hom)
  have h := transitionUnit_coefficient e₀ e₁ (unitSection e₀)
  rw [hu, mul_one] at h
  exact h.symm

/-- The actual entire frame has the genuine identity transition unit. -/
theorem transitionUnit_self (e : P ≅ Scheme.Modules.unitObj (Spec (.of A))) :
    transitionUnit e e = 1 := by
  apply Units.ext
  have hu := congrArg (Scheme.ΓSpecIso (.of A)).hom.hom (coefficient_unitSection e)
  exact (transitionUnit_val e e).trans (hu.trans (map_one _))

/-- Three actual entire original frames give genuine unit-valued composition coherence. -/
theorem transitionUnit_trans (e₀ e₁ e₂ : P ≅ Scheme.Modules.unitObj (Spec (.of A))) :
    transitionUnit e₀ e₂ = transitionUnit e₀ e₁ * transitionUnit e₁ e₂ := by
  apply Units.ext
  have h := transitionUnit_coefficient e₁ e₂ (unitSection e₀)
  have hc := congrArg (fun a : A => (transitionUnit e₁ e₂ : A) * a) (transitionUnit_val e₀ e₁).symm
  exact (transitionUnit_val e₀ e₂).trans (h.trans (hc.trans (mul_comm _ _)))

/-- Reversing the two original frames gives the inverse actual transition unit. -/
theorem transitionUnit_symm (e₀ e₁ : P ≅ Scheme.Modules.unitObj (Spec (.of A))) :
    transitionUnit e₁ e₀ = (transitionUnit e₀ e₁)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  exact (transitionUnit_trans e₀ e₁ e₀).symm.trans (transitionUnit_self e₀)

end EnvelopeProperty.Berkovich.SchemeResidueFrameTransition
