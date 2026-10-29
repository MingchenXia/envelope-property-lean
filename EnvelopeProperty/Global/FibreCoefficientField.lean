import EnvelopeProperty.Global.FibreCompletedLocal
import Hironaka.Algebra.Local.CohenIso

/-!
# Coefficient fields and Noetherianity for the actual fibre completion

A genuine residue section gives the existing intrinsic coefficient algebra
in the completion. The accepted arbitrary-coefficient-field Cohen producer
then proves its Noetherianity, in every characteristic. The actual tensor
localization used for original field fibres has such a section canonically.
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u

namespace EnvelopeProperty.FibreCoefficientField

section Section

variable {R K : Type u} [CommRing R] [IsLocalRing R] [Field K]
    (β : R →+* K) (hβs : Function.Surjective β)
    (hβk : RingHom.ker β = IsLocalRing.maximalIdeal R)

/-- The entire genuine local residue field is the SAME prescribed field. -/
def residueEquiv : IsLocalRing.ResidueField R ≃+* K :=
  (Ideal.quotEquivOfEq hβk.symm).trans (RingHom.quotientKerEquivOfSurjective hβs)

/-- Every original local coefficient retains its whole prescribed residue value. -/
theorem residueEquiv_residue (r : R) :
    residueEquiv β hβs hβk (IsLocalRing.residue R r) = β r := by
  rfl

variable (σ : K →+* R) (hσ : β.comp σ = RingHom.id K)

/-- The actual prescribed-field section transports to the true local residue field. -/
def residueSection : IsLocalRing.ResidueField R →+* R :=
  σ.comp (residueEquiv β hβs hβk).toRingHom

include hσ in
/-- The constructed map is a section of the WHOLE actual residue quotient. -/
theorem residueSection_comp :
    (IsLocalRing.residue R).comp (residueSection β hβs hβk σ) =
      RingHom.id (IsLocalRing.ResidueField R) := by
  ext k
  apply (residueEquiv β hβs hβk).injective
  rw [RingHom.comp_apply, residueEquiv_residue]
  exact congrArg (fun q : K →+* K => q (residueEquiv β hβs hβk k)) hσ

variable [IsNoetherianRing R]

/-- The actual field section constructs the completed coefficient algebra. -/
abbrev completionCoefficientAlgebra :
    Algebra (IsLocalRing.ResidueField R) (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  ((algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)).comp
    (residueSection β hβs hβk σ)).toAlgebra

include hσ in
/-- The ENTIRE residue triangle is the existing intrinsic coefficient-field condition. -/
theorem isCoefficientAlgebra_completion :
    letI : Algebra (IsLocalRing.ResidueField R)
      (AdicCompletion (IsLocalRing.maximalIdeal R) R) := completionCoefficientAlgebra β hβs hβk σ
    IsLocalRing.IsCoefficientAlgebra R := by
  let : Algebra (IsLocalRing.ResidueField R)
    (AdicCompletion (IsLocalRing.maximalIdeal R) R) := completionCoefficientAlgebra β hβs hβk σ
  change ∀ k : IsLocalRing.ResidueField R,
    IsLocalRing.residue (AdicCompletion (IsLocalRing.maximalIdeal R) R)
      (algebraMap R _ (residueSection β hβs hβk σ k)) =
        IsLocalRing.ResidueField.map (algebraMap R _) k
  intro k
  rw [← IsLocalRing.ResidueField.map_residue]
  congr 1
  exact congrArg (fun q : IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField R => q k)
    (residueSection_comp β hβs hβk σ hσ)

include hβs hβk hσ in
/-- A genuine actual residue section DERIVES Noetherianity of the whole completion,
using Cohen surjectivity for an arbitrary coefficient field in EVERY characteristic. -/
theorem isNoetherianRing_completion_of_section :
    IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  let : Algebra (IsLocalRing.ResidueField R)
    (AdicCompletion (IsLocalRing.maximalIdeal R) R) := completionCoefficientAlgebra β hβs hβk σ
  obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R))
  exact IsLocalRing.isNoetherianRing_adicCompletion_of_residue R x
    (isCoefficientAlgebra_completion β hβs hβk σ hσ) hx.symm

end Section

section ActualTensorLocal

variable {F A K : Type u} [Field F] [CommRing A] [Field K]
    [Algebra F A] [Algebra F K] (w : A →ₐ[F] K)

private instance tensorEvaluation_ker_prime :
    (RingHom.ker (FcFlatLocalFieldLift.tensorEvaluation w).toRingHom).IsPrime :=
  (FcFlatLocalFieldLift.tensorEvaluation_ker_isMaximal w).isPrime

/-- The literal original tensor localization at the actual given-point evaluation kernel. -/
abbrev localRing :=
  Localization.AtPrime (RingHom.ker (FcFlatLocalFieldLift.tensorEvaluation w).toRingHom)

/-- The whole actual localization evaluation into the SAME original field. -/
def localEvaluation : localRing w →+* K :=
  IsLocalization.lift (fun s : (RingHom.ker
      (FcFlatLocalFieldLift.tensorEvaluation w).toRingHom).primeCompl =>
    isUnit_iff_ne_zero.mpr s.2)

/-- Every actual tensor element retains its ENTIRE original field value. -/
theorem localEvaluation_algebraMap (t : A ⊗[F] K) :
    localEvaluation w (algebraMap (A ⊗[F] K) (localRing w) t) =
      FcFlatLocalFieldLift.tensorEvaluation w t :=
  IsLocalization.lift_eq _ t

/-- The literal coefficient tensor followed by the actual localization. -/
def localCoefficient : K →+* localRing w :=
  (algebraMap (A ⊗[F] K) (localRing w)).comp Algebra.TensorProduct.includeRight.toRingHom

/-- The whole original prescribed field embeds as a genuine section of the same evaluation. -/
theorem localEvaluation_coefficient (k : K) :
    localEvaluation w (localCoefficient w k) = k := by
  change localEvaluation w (algebraMap (A ⊗[F] K) (localRing w) (1 ⊗ₜ[F] k)) = k
  rw [localEvaluation_algebraMap]
  simp [FcFlatLocalFieldLift.tensorEvaluation]

/-- The ENTIRE original field coefficient/evaluation composite is the identity ring map. -/
theorem localEvaluation_comp_coefficient :
    (localEvaluation w).comp (localCoefficient w) = RingHom.id K := by
  ext k
  exact localEvaluation_coefficient w k

/-- The actual local evaluation is surjective, with its own genuine coefficient section. -/
theorem localEvaluation_surjective : Function.Surjective (localEvaluation w) :=
  fun k => ⟨localCoefficient w k, localEvaluation_coefficient w k⟩

/-- Its true kernel is precisely the actual maximal ideal of the literal localization. -/
theorem localEvaluation_ker :
    RingHom.ker (localEvaluation w) = IsLocalRing.maximalIdeal (localRing w) :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (localEvaluation_surjective w))

/-- The actual original A coefficient map is retained ENTIRELY in the localized field evaluation. -/
theorem localEvaluation_comp_original :
    (localEvaluation w).comp (algebraMap A (localRing w)) = w.toRingHom := by
  ext a
  change localEvaluation w (algebraMap (A ⊗[F] K) (localRing w)
    (algebraMap A (A ⊗[F] K) a)) = w a
  rw [localEvaluation_algebraMap]
  exact congrArg (fun q : A →+* K => q a) (FcFlatLocalFieldLift.tensorEvaluation_comp w)

variable [Algebra.FiniteType F A]

/-- Finite type over the actual prescribed field derives Noetherianity of the literal local ring. -/
theorem isNoetherianRing_localRing : IsNoetherianRing (localRing w) := by
  have : IsNoetherianRing (A ⊗[F] K) := FcFlatLocalFieldLift.isNoetherianRing_tensor
  infer_instance

omit [Algebra.FiniteType F A] in
/-- Genuine tensor and localization flatness give the actual original A-flat local lift. -/
theorem flat_localRing : Module.Flat A (localRing w) :=
  Module.Flat.trans A (A ⊗[F] K) (localRing w)

/-- The canonical field section DERIVES Noetherianity of the SAME actual maximal-adic completion,
in every characteristic and for every original field-valued point. -/
theorem isNoetherianRing_completedLocalRing :
    IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal (localRing w)) (localRing w)) := by
  have : IsNoetherianRing (localRing w) := isNoetherianRing_localRing w
  exact isNoetherianRing_completion_of_section (localEvaluation w)
    (localEvaluation_surjective w) (localEvaluation_ker w) (localCoefficient w)
    (localEvaluation_comp_coefficient w)

/-- Every original field-valued point constructs an actual NOETHERIAN complete flat
local coefficient lift with its exact original field and entire original A action.
No field section or completion-Noetherianity is a premise. -/
theorem exists_noetherian_completed_flat_local_lift :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : IsNoetherianRing B)
      (_ : IsLocalRing B), Module.Flat A B ∧
      IsAdicComplete (IsLocalRing.maximalIdeal B) B ∧
      ∃ γ : B →+* K, Function.Surjective γ ∧
        RingHom.ker γ = IsLocalRing.maximalIdeal B ∧
        γ.comp (algebraMap A B) = w.toRingHom := by
  let R := localRing w
  have : IsNoetherianRing R := isNoetherianRing_localRing w
  have : Module.Flat A R := flat_localRing w
  let B := AdicCompletion (IsLocalRing.maximalIdeal R) R
  have hNoethB : IsNoetherianRing B := isNoetherianRing_completedLocalRing w
  let β := localEvaluation w
  let γ := FcFlatLocalFieldLift.completionEvaluation β (localEvaluation_ker w)
  refine ⟨B, inferInstance, inferInstance, hNoethB, inferInstance,
    Module.Flat.trans A R B, inferInstance, γ,
    FcFlatLocalFieldLift.completionEvaluation_surjective β (localEvaluation_surjective w)
      (localEvaluation_ker w),
    FcFlatLocalFieldLift.completionEvaluation_ker β (localEvaluation_surjective w)
      (localEvaluation_ker w), ?_⟩
  ext a
  change FcFlatLocalFieldLift.completionEvaluation β (localEvaluation_ker w)
    (algebraMap R B (algebraMap A R a)) = w a
  rw [FcFlatLocalFieldLift.completionEvaluation_algebraMap]
  exact congrArg (fun q : A →+* K => q a) (localEvaluation_comp_original w)

end ActualTensorLocal

end EnvelopeProperty.FibreCoefficientField
