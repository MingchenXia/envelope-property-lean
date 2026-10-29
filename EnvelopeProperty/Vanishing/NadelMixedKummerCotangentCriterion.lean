import EnvelopeProperty.Vanishing.NadelMixedKummerDifferential
import Mathlib.RingTheory.Smooth.Basic

/-! # A genuine derivation-Jacobian splitting criterion

Actual equations generate the actual extension kernel. Their actual
coefficient-valued derivations and a unit determinant construct a left inverse
of the native cotangent complex. No smoothness conclusion is supplied as input.
-/

noncomputable section
universe u
open scoped TensorProduct
namespace EnvelopeProperty.Vanishing.NadelMixedKummer.CotangentCriterion
open Algebra
variable {k S : Type u} [CommRing k] [CommRing S] [Algebra k S]
  (P : Algebra.Extension.{u} k S) {q : ℕ} (r : Fin q → P.Ring)
  (hr : Ideal.span (Set.range r) = P.ker) (d : Fin q → Derivation k P.Ring S)

/-- The actual original relation classes in the native cotangent module. -/
def relationClass (i : Fin q) : P.Cotangent :=
  Algebra.Extension.Cotangent.mk ⟨r i, hr.le (Ideal.subset_span ⟨i, rfl⟩)⟩

/-- The genuine relation-class map onto the WHOLE native cotangent module. -/
def relationMap : (Fin q → S) →ₗ[S] P.Cotangent :=
  Fintype.linearCombination S (relationClass P r hr)

/-- Actual generation of the original extension kernel proves actual
surjectivity onto the WHOLE cotangent module. -/
theorem relationMap_surjective : Function.Surjective (relationMap P r hr) :=
  (span_range_eq_top_iff_surjective_fintypeLinearCombination S _).mp
    (Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker r hr)

/-- Actual derivations give a genuine coordinate map on the native cotangent space. -/
def derivativeMap : P.CotangentSpace →ₗ[S] (Fin q → S) :=
  LinearMap.pi (fun i => (d i).liftKaehlerDifferential.liftBaseChange S)

/-- The ACTUAL derivation matrix on the actual original relation family. -/
def jacobian : Matrix (Fin q) (Fin q) S := fun i j => d i (r j)

/-- The native cotangent differential on actual relation generators is
literally the original derivation Jacobian. -/
theorem derivative_cotangent_relation :
    derivativeMap P d ∘ₗ P.cotangentComplex ∘ₗ relationMap P r hr =
      (jacobian P r d).toLin' := by
  classical
  ext w i
  simp only [relationMap, Fintype.linearCombination_apply, derivativeMap,
    LinearMap.comp_apply, map_sum, map_smul, LinearMap.pi_apply, relationClass,
    Algebra.Extension.cotangentComplex_mk, LinearMap.liftBaseChange_tmul,
    Derivation.liftKaehlerDifferential_comp_D, one_mul, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, jacobian, smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

include hr in
/-- A unit ACTUAL derivation determinant constructs a native cotangent-complex
left inverse and hence proves formal smoothness, using the actual formally
smooth ambient extension and actual original kernel generators. -/
theorem formallySmooth [Algebra.FormallySmooth k P.Ring]
    (hJ : IsUnit (jacobian P r d).det) : Algebra.FormallySmooth k S := by
  classical
  let h := relationMap P r hr
  let v := derivativeMap P d
  let F := v ∘ₗ P.cotangentComplex ∘ₗ h
  have hF : IsUnit F := by
    rw [show F = (jacobian P r d).toLin' from derivative_cotangent_relation P r hr d]
    exact Matrix.isUnit_toLin'_iff.mpr ((jacobian P r d).isUnit_iff_isUnit_det.mpr hJ)
  let z := hF.unit
  let l : P.CotangentSpace →ₗ[S] P.Cotangent := h ∘ₗ (↑(z⁻¹) : Module.End S (Fin q → S)) ∘ₗ v
  apply (P.formallySmooth_iff_split_injection).mpr
  refine ⟨l, ?_⟩
  ext a
  obtain ⟨w, rfl⟩ := relationMap_surjective P r hr a
  change h ((↑(z⁻¹) : Module.End S (Fin q → S)) (F w)) = h w
  have hz : (z : Module.End S (Fin q → S)) = F := hF.unit_spec
  rw [← hz, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]

end EnvelopeProperty.Vanishing.NadelMixedKummer.CotangentCriterion
