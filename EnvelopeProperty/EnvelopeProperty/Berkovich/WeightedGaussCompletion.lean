/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.GaussCompletion
import EnvelopeProperty.GaussFieldIdeals
import Mathlib.Topology.MetricSpace.Isometry

open scoped Polynomial NNReal Topology
open Polynomial UniformSpace Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.GaussCompletion
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

private abbrev WeightedRing (r : ℝ≥0) (hr : 0<r) := CompletedMonicDivision.Ring (A := K) r hr
private abbrev WeightedSource (r : ℝ≥0) (hr : 0<r) :=
  WeightedPolynomialCompletion.PolynomialRing (A := K) (fun _ : PUnit.{1} => r) (fun _ => hr)

private def originalPolynomial (r : ℝ≥0) (hr : 0<r) : WeightedSource (K := K) r hr →+* K[X] :=
  (MvPolynomial.uniqueAlgEquiv K PUnit.{1}).toRingHom.comp
    (WeightedPolynomialCompletion.polynomialEquiv (fun _ : PUnit.{1} => r) (fun _ => hr)).toRingHom

private theorem gauss_originalPolynomial (r : ℝ≥0) (hr : 0<r) (p : WeightedSource (K := K) r hr) :
    gaussFun (NormedField.valuation (K := K)) r (originalPolynomial r hr p) = ‖p‖₊ := by
  have he (q : K[X]) : gaussFun (NormedField.valuation (K := K)) r q = MonicGaussDivision.gauss r q := by
    simp only [gaussFun,MonicGaussDivision.gauss,NormedField.valuation_apply]
  rw [he,MonicGaussDivision.gauss_eq_weighted,WeightedPolynomialCompletion.nnnorm_polynomial]
  exact congrArg (WeightedPolynomial.gauss (fun _ : PUnit.{1} => r))
    ((MvPolynomial.uniqueAlgEquiv K PUnit.{1}).symm_apply_apply _)

private def originalMap (r : ℝ≥0) (hr : 0<r) : WeightedSource (K := K) r hr →+* Ring (K := K) r hr :=
  (polynomialMap r hr).comp (originalPolynomial r hr)

private theorem isometry_originalMap (r : ℝ≥0) (hr : 0<r) : Isometry (originalMap (K := K) r hr) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro p
  exact congrArg NNReal.toReal ((nnnorm_polynomialMap r hr _).trans (gauss_originalPolynomial r hr p))

private def weightedExtension (r : ℝ≥0) (hr : 0<r) : WeightedRing (K := K) r hr →+* Ring (K := K) r hr :=
  Completion.extensionHom (originalMap r hr) (isometry_originalMap r hr).continuous

private theorem weightedExtension_polynomialMap (r : ℝ≥0) (hr : 0<r) (p : K[X]) :
    weightedExtension r hr (CompletedMonicDivision.polynomialMap r hr p) = polynomialMap r hr p := by
  let q : WeightedSource (K := K) r hr :=
    (WeightedPolynomialCompletion.polynomialEquiv (fun _ : PUnit.{1} => r) (fun _ => hr)).symm
      ((MvPolynomial.uniqueAlgEquiv K PUnit.{1}).symm p)
  change Completion.extensionHom _ _ (q : Completion (WeightedSource (K := K) r hr)) = _
  rw [Completion.extensionHom_coe]
  change polynomialMap r hr ((MvPolynomial.uniqueAlgEquiv K PUnit.{1})
    ((WeightedPolynomialCompletion.polynomialEquiv (fun _ : PUnit.{1} => r) (fun _ => hr))
      ((WeightedPolynomialCompletion.polynomialEquiv (fun _ : PUnit.{1} => r) (fun _ => hr)).symm
        ((MvPolynomial.uniqueAlgEquiv K PUnit.{1}).symm p)))) = _
  rw [RingEquiv.apply_symm_apply,AlgEquiv.apply_symm_apply]

private theorem norm_weightedExtension (r : ℝ≥0) (hr : 0<r) (f : WeightedRing (K := K) r hr) :
    ‖weightedExtension r hr f‖₊ = ‖f‖₊ := by
  exact (CompletedMonicDivision.denseRange_polynomialMap (A := K) r hr).induction_on f
    (isClosed_eq (continuous_nnnorm.comp (show Continuous (weightedExtension (K := K) r hr) from Completion.continuous_extension)) continuous_nnnorm)
    (fun p => by
      rw [weightedExtension_polynomialMap,nnnorm_polynomialMap,CompletedMonicDivision.nnnorm_polynomialMap]
      simp only [gaussFun,MonicGaussDivision.gauss,NormedField.valuation_apply])

private theorem isometry_weightedExtension (r : ℝ≥0) (hr : 0<r) : Isometry (weightedExtension (K := K) r hr) :=
  AddMonoidHomClass.isometry_of_norm (weightedExtension r hr) fun f =>
    congrArg NNReal.toReal (norm_weightedExtension r hr f)

private theorem denseRange_gaussPolynomialMap (r : ℝ≥0) (hr : 0<r) : DenseRange (polynomialMap (K := K) r hr) := by
  change Dense (Set.range ((Completion.coeRingHom : PolynomialRing (K := K) r hr →+* Ring r hr) ∘
    (polynomialEquiv r hr).symm))
  rw [(polynomialEquiv r hr).symm.surjective.range_comp]
  exact Completion.denseRange_coe

private theorem surjective_weightedExtension (r : ℝ≥0) (hr : 0<r) :
    Function.Surjective (weightedExtension (K := K) r hr) := by
  have hd : DenseRange (weightedExtension (K := K) r hr) := by
    intro f
    apply closure_mono ?_ (denseRange_gaussPolynomialMap r hr f)
    rintro _ ⟨p,rfl⟩
    exact ⟨CompletedMonicDivision.polynomialMap r hr p,weightedExtension_polynomialMap r hr p⟩
  intro f
  have hf := hd f
  rw [(isometry_weightedExtension r hr).isClosedEmbedding.isClosed_range.closure_eq] at hf
  exact hf

/-- The genuine whole original polynomial completions are isomorphic, with no completeness of K. -/
def weightedCompletionEquiv (r : ℝ≥0) (hr : 0<r) : WeightedRing (K := K) r hr ≃+* Ring (K := K) r hr :=
  RingEquiv.ofBijective (weightedExtension r hr)
    ⟨(isometry_weightedExtension r hr).injective,surjective_weightedExtension r hr⟩

/-- EVERY original polynomial retains its entire original image under the whole equivalence. -/
@[simp] theorem weightedCompletionEquiv_polynomialMap (r : ℝ≥0) (hr : 0<r) (p : K[X]) :
    weightedCompletionEquiv r hr (CompletedMonicDivision.polynomialMap r hr p) = polynomialMap r hr p :=
  weightedExtension_polynomialMap r hr p

/-- The entire inverse recovers EVERY original polynomial image. -/
@[simp] theorem weightedCompletionEquiv_symm_polynomialMap (r : ℝ≥0) (hr : 0<r) (p : K[X]) :
    (weightedCompletionEquiv r hr).symm (polynomialMap r hr p) = CompletedMonicDivision.polynomialMap r hr p := by
  apply (weightedCompletionEquiv r hr).injective
  rw [RingEquiv.apply_symm_apply,weightedCompletionEquiv_polynomialMap]

/-- The ORIGINAL coefficient map is retained as the original Gauss-completion K-algebra map. -/
@[simp] theorem weightedCompletionEquiv_coefficients (r : ℝ≥0) (hr : 0<r) (a : K) :
    weightedCompletionEquiv r hr (WeightedPolynomialCompletion.coefficients (fun _ : PUnit.{1} => r) (fun _ => hr) a) =
      algebraMap K (Ring (K := K) r hr) a := by
  have hc : (MvPolynomial.uniqueAlgEquiv K PUnit.{1}).symm (C a) = MvPolynomial.C a :=
    (MvPolynomial.uniqueAlgEquiv K PUnit.{1}).symm.commutes a
  change weightedCompletionEquiv r hr
    (WeightedPolynomialCompletion.polynomialMap (fun _ : PUnit.{1} => r) (fun _ => hr) (MvPolynomial.C a)) = _
  rw [← hc]
  exact weightedCompletionEquiv_polynomialMap r hr (C a)

/-- The actual equivalence preserves the whole norm of EVERY original completed function. -/
theorem nnnorm_weightedCompletionEquiv (r : ℝ≥0) (hr : 0<r) (f : WeightedRing (K := K) r hr) :
    ‖weightedCompletionEquiv r hr f‖₊ = ‖f‖₊ := norm_weightedExtension r hr f

/-- The whole equivalence is an actual metric isometry. -/
theorem isometry_weightedCompletionEquiv (r : ℝ≥0) (hr : 0<r) :
    Isometry (weightedCompletionEquiv (K := K) r hr) := isometry_weightedExtension r hr

/-- Both ORIGINAL coefficient structures give an actual K-algebra equivalence. -/
def weightedCompletionAlgEquiv (r : ℝ≥0) (hr : 0<r) :
    let : Algebra K (WeightedRing (K := K) r hr) :=
      (WeightedPolynomialCompletion.coefficients (fun _ : PUnit.{1} => r) (fun _ => hr)).toAlgebra
    WeightedRing (K := K) r hr ≃ₐ[K] Ring (K := K) r hr := by
  let : Algebra K (WeightedRing (K := K) r hr) :=
    (WeightedPolynomialCompletion.coefficients (fun _ : PUnit.{1} => r) (fun _ => hr)).toAlgebra
  exact { weightedCompletionEquiv r hr with commutes' := weightedCompletionEquiv_coefficients r hr }

/-- Multiplicativity of the SAME original weighted completion is derived without assuming it. -/
theorem weightedCompletionNormMulClass (r : ℝ≥0) (hr : 0<r) : NormMulClass (WeightedRing (K := K) r hr) where
  norm_mul f g := by
    have h := nnnorm_weightedCompletionEquiv r hr (f*g)
    rw [map_mul,nnnorm_mul,nnnorm_weightedCompletionEquiv,nnnorm_weightedCompletionEquiv] at h
    exact congrArg NNReal.toReal h.symm

variable [CompleteSpace K]
/-- Actual original Gauss disc-function ideals are principal over every complete ultrametric field. -/
theorem isPrincipalIdealRing_of_complete (r : ℝ≥0) (hr : 0<r) : IsPrincipalIdealRing (Ring (K := K) r hr) := by
  let := CompletedMonicDivision.gaussField_isPrincipalIdealRing (K := K) r hr
  exact IsPrincipalIdealRing.of_surjective (weightedCompletionEquiv (K := K) r hr).toRingHom
    (weightedCompletionEquiv r hr).surjective

/-- The ORIGINAL closed-disc function ring is genuinely Noetherian. -/
theorem isNoetherianRing_of_complete (r : ℝ≥0) (hr : 0<r) : IsNoetherianRing (Ring (K := K) r hr) := by
  let := CompletedMonicDivision.gaussField_isNoetherianRing (K := K) r hr
  exact isNoetherianRing_of_ringEquiv (WeightedRing (K := K) r hr) (weightedCompletionEquiv r hr)

/-- EVERY original Gauss disc-function ideal is closed in the actual original norm topology. -/
theorem isClosed_ideal_of_complete (r : ℝ≥0) (hr : 0<r) (I : Ideal (Ring (K := K) r hr)) :
    IsClosed (I : Set (Ring (K := K) r hr)) := by
  let e := weightedCompletionEquiv (K := K) r hr
  let ei : WeightedRing (K := K) r hr ≃ᵢ Ring (K := K) r hr :=
    { e.toEquiv with isometry_toFun := isometry_weightedCompletionEquiv r hr }
  have h := CompletedMonicDivision.gaussField_isClosed_ideal r hr (I.comap e.toRingHom)
  have he : (I : Set (Ring (K := K) r hr)) = ei.symm ⁻¹' (I.comap e.toRingHom : Set (WeightedRing r hr)) := by
    ext f
    change f ∈ I ↔ e (e.symm f) ∈ I
    rw [RingEquiv.apply_symm_apply]
  rw [he]
  exact h.preimage ei.symm.continuous
end EnvelopeProperty.Berkovich.GaussCompletion
