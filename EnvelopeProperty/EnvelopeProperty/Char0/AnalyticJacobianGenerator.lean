import EnvelopeProperty.Char0.AnalyticEtaleJacobian
import TranscendentalNakamaye.Pending.HolomorphicGermJacobian

/-!
# A genuine target-coordinate generator of the whole analytic Jacobian ideal

The original target's actual etale coordinates reduce the whole all-functions
ideal to its actual complex-Jacobian germ. Neither determinant nonvanishing
nor a supplied ideal comparison is required.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0.AnalyticJacobianGenerator

open Filter Module Ideal
open TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open AnalyticEtaleJacobian HolomorphicGermJacobian HironakaHolomorphicJetMonomialSpan
open scoped Topology

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra ℂ A]
  [Algebra ℂ R] [Algebra R A] [IsScalarTower ℂ R A] {n : ℕ}

/-- Genuine original target etale coordinates generate the WHOLE actual analytic Jacobian ideal. -/
theorem analyticSourceJacobianIdeal_eq_span (φ : A →ₐ[ℂ] HolGerm (ComplexModel n))
    (u : Fin n → A) (hu : (MvPolynomial.aeval (R := ℂ) u).toRingHom.Etale)
    (c : Fin n → ℂ) (hφ : ∀ i, φ (u i) = coordinateGerm i + HolGerm.constHom (c i))
    (t : Fin n → R) (ht : (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale) :
    analyticSourceJacobianIdeal (R := R) φ = Ideal.span {analyticSourceJacobian φ t} := by
  rw [analyticSourceJacobianIdeal_eq_map φ u hu c hφ u hu,
    affineRelativeJacobianIdeal_eq_span t ht,
    relativeDifferentialDet_eq_etaleJacobian t ht u hu,
    Ideal.map_span, Set.image_singleton,
    analyticSourceJacobian_normalized φ u hu c hφ]
  rfl

omit [Algebra ℂ R] [IsScalarTower ℂ R A] in
/-- Whole coefficient germs give exactly the complex Jacobian of their actual vector map. -/
theorem analyticSourceJacobian_eq_jacobianGerm (φ : A →ₐ[ℂ] HolGerm (ComplexModel n))
    (t : Fin n → R) (F : ComplexModel n → ComplexModel n)
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z)
    (hφ : ∀ i, ((φ (algebraMap R A (t i)) : HolGerm (ComplexModel n)) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) = (fun z => F z i)) :
    analyticSourceJacobian φ t = jacobianGerm F hF := by
  let hFi (i : Fin n) : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun w => F w i) z :=
    hF.mono fun z hz =>
      (PiLp.proj 2 (fun _ : Fin n => ℂ) i : ComplexModel n →L[ℂ] ℂ).differentiableAt.comp z hz
  have hi (i : Fin n) : φ (algebraMap R A (t i)) = HolGerm.mk (fun z => F z i) (hFi i) :=
    Subtype.ext (hφ i)
  unfold analyticSourceJacobian jacobianGerm
  congr 1
  funext i j
  exact congrArg (HolomorphicGermCoordinateDerivation.coordinatePartial j) (hi i)

end EnvelopeProperty.Char0.AnalyticJacobianGenerator
