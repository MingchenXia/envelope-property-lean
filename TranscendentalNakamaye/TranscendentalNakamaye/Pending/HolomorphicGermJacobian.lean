import TranscendentalNakamaye.Pending.HolomorphicGermCoordinateDerivation
import TranscendentalNakamaye.Pending.DivisorialChangeOfVariables
import TranscendentalNakamaye.Pending.CoordinateDensityGeneral

/-!
# Actual complex Jacobians as whole holomorphic germs

The determinant of actual coordinate derivative germs manufactures the whole
complex Jacobian, without assuming its holomorphy as a new certificate.
Its readback is the existing complexJacobian, and the genuine chain rule
holds even when either determinant vanishes identically.
-/

set_option autoImplicit false

noncomputable section

namespace TranscendentalNakamaye.Pending.HolomorphicGermJacobian

open Filter FirstPass FirstPass.MongeAmpere
open HolomorphicGermCoordinateDerivation DivisorialChangeOfVariables
open HironakaHolomorphicJetChartInvariance
open scoped Topology

variable {n : ℕ}

private theorem component_holomorphic (F : ComplexModel n → ComplexModel n)
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) (i : Fin n) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun w => F w i) z :=
  hF.mono fun z hz => by
    have hi : DifferentiableAt ℂ (fun u : ComplexModel n => u i) (F z) :=
      (PiLp.proj 2 (fun _ : Fin n => ℂ) i).differentiableAt
    exact hi.comp z hz

/-- Manufacture the actual whole complex Jacobian from its actual component derivative germs. -/
def jacobianGerm (F : ComplexModel n → ComplexModel n)
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) : HolGerm (ComplexModel n) :=
  (Matrix.of fun i j => coordinatePartial j
    (HolGerm.mk (fun z => F z i) (component_holomorphic F hF i))).det

/-- Entire original-function readback is exactly the existing complex Jacobian function. -/
theorem jacobianGerm_source (F : ComplexModel n → ComplexModel n)
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) :
    ((jacobianGerm F hF : HolGerm (ComplexModel n)) : Germ (𝓝 (0 : ComplexModel n)) ℂ) =
      (complexJacobian F : Germ (𝓝 (0 : ComplexModel n)) ℂ) := by
  let M : Matrix (Fin n) (Fin n) (ComplexModel n → ℂ) :=
    fun i j z => fderiv ℂ (fun w => F w i) z (EuclideanSpace.single j 1)
  have hmatrix : (holGermSubring (ComplexModel n)).subtype (jacobianGerm F hF) =
      (Germ.coeRingHom (𝓝 (0 : ComplexModel n))) M.det := by
    unfold jacobianGerm
    rw [(holGermSubring (ComplexModel n)).subtype.map_det,
      (Germ.coeRingHom (𝓝 (0 : ComplexModel n))).map_det M]
    rfl
  apply hmatrix.trans
  apply Germ.coe_eq.mpr
  filter_upwards [hF] with z hz
  have he : (fun i j => M i j z) = standardMatrix (fderiv ℂ F z).toLinearMap := by
    funext i j
    rw [standardMatrix_apply]
    have hc : fderiv ℂ (fun w => F w i) z =
        (PiLp.proj 2 (fun _ : Fin n => ℂ) i).comp (fderiv ℂ F z) :=
      by
        have hi : HasFDerivAt (fun u : ComplexModel n => u i)
            (PiLp.proj 2 (fun _ : Fin n => ℂ) i) (F z) :=
          (PiLp.proj 2 (fun _ : Fin n => ℂ) i : ComplexModel n →L[ℂ] ℂ).hasFDerivAt
        exact (hi.comp z hz.hasFDerivAt).fderiv
    change (fderiv ℂ (fun w => F w i) z) (EuclideanSpace.single j 1) = _
    rw [hc]
    rfl
  change (Pi.evalRingHom (fun _ : ComplexModel n => ℂ) z) M.det = _
  rw [(Pi.evalRingHom (fun _ : ComplexModel n => ℂ) z).map_det M]
  rw [show (Pi.evalRingHom (fun _ : ComplexModel n => ℂ) z).mapMatrix M =
    standardMatrix (fderiv ℂ F z).toLinearMap from he]
  exact det_standardMatrix _

private theorem comp_holomorphic (F G : ComplexModel n → ComplexModel n)
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) (hF0 : F 0 = 0)
    (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G ∘ F) z := by
  have ht : Tendsto F (𝓝 0) (𝓝 0) := by simpa only [hF0] using hF.self_of_nhds.continuousAt.tendsto
  filter_upwards [hF, ht.eventually hG] with z hf hg
  exact hg.comp z hf

/-- The actual whole-germ Jacobian chain rule, without a nonvanishing determinant assumption. -/
theorem jacobianGerm_comp (F G : ComplexModel n → ComplexModel n)
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) (hF0 : F 0 = 0)
    (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z) :
    jacobianGerm (G ∘ F) (comp_holomorphic F G hF hF0 hG) =
      compAlgHom F hF hF0 (jacobianGerm G hG) * jacobianGerm F hF := by
  have ht : Tendsto F (𝓝 0) (𝓝 0) := by simpa only [hF0] using hF.self_of_nhds.continuousAt.tendsto
  have hpull : ((compAlgHom F hF hF0 (jacobianGerm G hG) : HolGerm (ComplexModel n)) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) =
        (complexJacobian G ∘ F : Germ (𝓝 (0 : ComplexModel n)) ℂ) := by
    change ((jacobianGerm G hG : HolGerm (ComplexModel n)) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ).compTendsto F ht = _
    rw [jacobianGerm_source]
    rfl
  apply Subtype.ext
  change ((jacobianGerm (G ∘ F) _ : HolGerm (ComplexModel n)) : Germ (𝓝 (0 : ComplexModel n)) ℂ) =
    ((compAlgHom F hF hF0 (jacobianGerm G hG) : HolGerm (ComplexModel n)) : Germ (𝓝 (0 : ComplexModel n)) ℂ) *
      ((jacobianGerm F hF : HolGerm (ComplexModel n)) : Germ (𝓝 (0 : ComplexModel n)) ℂ)
  rw [jacobianGerm_source, hpull, jacobianGerm_source]
  apply Germ.coe_eq.mpr
  filter_upwards [hF, ht.eventually hG] with z hf hg
  change (fderiv ℂ (G ∘ F) z).det = (fderiv ℂ G (F z)).det * (fderiv ℂ F z).det
  rw [fderiv_comp z hg hf, ContinuousLinearMap.det]
  change LinearMap.det ((fderiv ℂ G (F z)).toLinearMap.comp (fderiv ℂ F z).toLinearMap) = _
  exact LinearMap.det_comp _ _

/-- A unit actual target Jacobian preserves the whole principal ideal, even for zero Jacobians. -/
theorem span_jacobianGerm_comp (F G : ComplexModel n → ComplexModel n)
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) (hF0 : F 0 = 0)
    (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z)
    (hGunit : IsUnit (jacobianGerm G hG)) :
    Ideal.span {jacobianGerm (G ∘ F) (comp_holomorphic F G hF hF0 hG)} =
      Ideal.span {jacobianGerm F hF} := by
  rw [jacobianGerm_comp F G hF hF0 hG]
  exact Ideal.span_singleton_mul_left_unit (hGunit.map (compAlgHom F hF hF0).toRingHom) _

end TranscendentalNakamaye.Pending.HolomorphicGermJacobian
