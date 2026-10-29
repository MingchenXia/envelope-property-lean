import EnvelopeProperty.AlgGeom.ProperBirationalFlatSections
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Actual flat local coefficient rings with a prescribed residue field

For any original field-valued point of a finite-type field algebra, tensor with
the prescribed field and localize at the actual evaluation kernel. This
constructs a noetherian flat local original-base algebra with exactly the
prescribed residue field. Completing its actual maximal ideal retains that
field and constructs the complete local flat coefficient space needed for the
geometric formal-functions argument.
-/

open scoped TensorProduct
noncomputable section
universe u

namespace EnvelopeProperty.FcFlatLocalFieldLift

variable {F A K : Type u} [Field F] [CommRing A] [Field K]
variable [Algebra F A] [Algebra F K]

/-- The actual whole evaluation of the original tensor base extension. -/
def tensorEvaluation (w : A →ₐ[F] K) : A ⊗[F] K →ₐ[F] K :=
  Algebra.TensorProduct.lift w (AlgHom.id F K) fun _ _ => Commute.all _ _

/-- Every element of the prescribed field is the evaluation of its actual
coefficient tensor. No finite extension or separability is required. -/
theorem tensorEvaluation_surjective (w : A →ₐ[F] K) :
    Function.Surjective (tensorEvaluation w) := by
  intro k
  refine ⟨1 ⊗ₜ[F] k, ?_⟩
  simp [tensorEvaluation]

/-- The entire original A coefficient homomorphism is retained in evaluation. -/
theorem tensorEvaluation_comp (w : A →ₐ[F] K) :
    (tensorEvaluation w).toRingHom.comp (algebraMap A (A ⊗[F] K)) = w.toRingHom := by
  ext a
  simp [tensorEvaluation]

/-- The actual tensor algebra is noetherian, even for an arbitrary huge
prescribed field, because it is finite type over THAT field. -/
theorem isNoetherianRing_tensor [Algebra.FiniteType F A] :
    IsNoetherianRing (A ⊗[F] K) := by
  let : Algebra K (A ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  have : Algebra.FiniteType K (A ⊗[F] K) :=
    Algebra.FiniteType.equiv (inferInstance : Algebra.FiniteType K (K ⊗[F] A))
      (Algebra.TensorProduct.commRight F K A)
  exact Algebra.FiniteType.isNoetherianRing K (A ⊗[F] K)

/-- The actual evaluation kernel is maximal, so the prescribed point really
constructs an original local tensor coefficient ring. -/
theorem tensorEvaluation_ker_isMaximal (w : A →ₐ[F] K) :
    (RingHom.ker (tensorEvaluation w).toRingHom).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (tensorEvaluation_surjective w)

/-- EVERY actual field-valued point of an actual finite-type field algebra
constructs a noetherian flat LOCAL original-base algebra whose exact residue
field is the prescribed field, retaining the ENTIRE original coefficient map.
No finite/separable extension, local lift or residue identification is input. -/
theorem exists_noetherian_flat_local_lift [Algebra.FiniteType F A] (w : A →ₐ[F] K) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R) (_ : IsNoetherianRing R)
      (_ : IsLocalRing R), Module.Flat A R ∧
      ∃ β : R →+* K, Function.Surjective β ∧ RingHom.ker β = IsLocalRing.maximalIdeal R ∧
        β.comp (algebraMap A R) = w.toRingHom := by
  let T := A ⊗[F] K
  let P := RingHom.ker (tensorEvaluation w).toRingHom
  have hP : P.IsMaximal := tensorEvaluation_ker_isMaximal w
  have : P.IsPrime := hP.isPrime
  have : IsNoetherianRing T := isNoetherianRing_tensor (F := F) (A := A) (K := K)
  let R := Localization.AtPrime P
  have hu (s : P.primeCompl) : IsUnit (tensorEvaluation w s) := by
    apply isUnit_iff_ne_zero.mpr
    exact s.2
  let β : R →+* K := IsLocalization.lift hu
  have hβT (t : T) : β (algebraMap T R t) = tensorEvaluation w t := IsLocalization.lift_eq hu t
  have hβsurj : Function.Surjective β := by
    intro k
    obtain ⟨t, ht⟩ := tensorEvaluation_surjective w k
    exact ⟨algebraMap T R t, (hβT t).trans ht⟩
  have hβker : RingHom.ker β = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective β hβsurj)
  have hflat : Module.Flat A R := Module.Flat.trans A T R
  refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, hflat, β, hβsurj, hβker, ?_⟩
  ext a
  change β (algebraMap T R (algebraMap A T a)) = w a
  rw [hβT]
  exact congrArg (fun g : A →+* K => g a) (tensorEvaluation_comp w)

section Completion

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The actual maximal-adic completion evaluates in the SAME prescribed
residue field through its genuine order-one quotient map. -/
def completionEvaluation (β : R →+* K) (hβ : RingHom.ker β = IsLocalRing.maximalIdeal R) :
    AdicCompletion (IsLocalRing.maximalIdeal R) R →+* K := by
  have hkill (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R) : β r = 0 := by
    change r ∈ RingHom.ker β
    rwa [hβ]
  exact (Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) β hkill).comp
    (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal R)).toRingHom

/-- Every original local coefficient retains its ENTIRE original field value
after passing to the actual completion. -/
theorem completionEvaluation_algebraMap (β : R →+* K)
    (hβ : RingHom.ker β = IsLocalRing.maximalIdeal R) (r : R) :
    completionEvaluation β hβ (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
      β r := rfl

theorem completionEvaluation_surjective (β : R →+* K) (hβs : Function.Surjective β)
    (hβ : RingHom.ker β = IsLocalRing.maximalIdeal R) :
    Function.Surjective (completionEvaluation β hβ) := by
  intro k
  obtain ⟨r, hr⟩ := hβs k
  exact ⟨algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r, hr⟩

/-- The actual completed evaluation has precisely the actual completed maximal
ideal as kernel, so it realizes the EXACT same prescribed residue field. -/
theorem completionEvaluation_ker [IsNoetherianRing R]
    (β : R →+* K) (hβs : Function.Surjective β)
    (hβ : RingHom.ker β = IsLocalRing.maximalIdeal R) :
    RingHom.ker (completionEvaluation β hβ) =
      IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _
    (completionEvaluation_surjective β hβs hβ))

end Completion

/-- Construct the actual noetherian flat local coefficient ring AND its actual
complete flat local completion for EVERY prescribed original field point.
Both exact residue evaluations retain the ENTIRE original A→K map. -/
theorem exists_completed_flat_local_lift [Algebra.FiniteType F A] (w : A →ₐ[F] K) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R) (_ : IsNoetherianRing R)
      (_ : IsLocalRing R), Module.Flat A R ∧
      ∃ β : R →+* K, Function.Surjective β ∧ RingHom.ker β = IsLocalRing.maximalIdeal R ∧
        β.comp (algebraMap A R) = w.toRingHom ∧
        Module.Flat A (AdicCompletion (IsLocalRing.maximalIdeal R) R) ∧
        IsAdicComplete
          (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R))
          (AdicCompletion (IsLocalRing.maximalIdeal R) R) ∧
        ∃ γ : AdicCompletion (IsLocalRing.maximalIdeal R) R →+* K,
          Function.Surjective γ ∧
          RingHom.ker γ = IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ∧
          γ.comp (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal R) R)) = w.toRingHom := by
  obtain ⟨R, hRing, hAlg, hNoeth, hLocal, hFlat, β, hβs, hβker, hβbase⟩ :=
    exists_noetherian_flat_local_lift w
  have : Module.Flat A R := hFlat
  let B := AdicCompletion (IsLocalRing.maximalIdeal R) R
  have hFlatB : Module.Flat A B := Module.Flat.trans A R B
  refine ⟨R, hRing, hAlg, hNoeth, hLocal, hFlat, β, hβs, hβker, hβbase, hFlatB,
    inferInstance, completionEvaluation β hβker, completionEvaluation_surjective β hβs hβker,
    completionEvaluation_ker β hβs hβker, ?_⟩
  ext a
  change completionEvaluation β hβker (algebraMap R B (algebraMap A R a)) = w a
  rw [completionEvaluation_algebraMap]
  exact congrArg (fun g : A →+* K => g a) hβbase

end EnvelopeProperty.FcFlatLocalFieldLift
