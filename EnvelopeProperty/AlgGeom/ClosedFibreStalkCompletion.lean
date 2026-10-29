import EnvelopeProperty.AlgGeom.ClosedFibreLocalRing
import Hironaka.Algebra.Local.CompletionEtale

/-!
# Actual closed-fibre point completions and their coefficient-preserving maps

The first completion comparison uses the actual coefficient point-local map.
The tensor-local lift is independently manufactured from the actual original
coefficient maps and their residue evaluations; it preserves ALL coefficients
from both tensor factors before any completion isomorphism is chosen.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open TensorProduct

namespace EnvelopeProperty.ClosedFibreStalkCompletion

open ClosedFibreLocalRing

universe u

variable {R S K A : Type u} [CommRing R] [CommRing S] [Field K] [CommRing A]
  [Algebra R S] [Algebra R K] [Algebra R A]
  (β : S →ₐ[R] K) (p : A →ₐ[R] K)

section Completion

variable (hR : Function.Surjective (algebraMap R K))
  (hker : RingHom.ker β.toRingHom =
    (RingHom.ker (algebraMap R K)).map (algebraMap R S))
  (hp : Function.Surjective p) [Module.Flat R S]

include hR hker hp in
/-- The canonical completion map of the SAME actual original point-local rings is bijective. -/
theorem localCompletionMap_bijective :
    Function.Bijective (IsLocalRing.completionMap (localMap β p)) :=
  IsLocalRing.bijective_completionMap_of_flat_of_map_maximalIdeal (localMap β p)
    (localMap_flat β p) (localMap_map_maximalIdeal β hR hker p hp)
    (localMap_residue_bijective β p hp)

/-- The actual closed-fibre comparison is induced by the literal original local map. -/
def localCompletionEquiv :
    AdicCompletion (IsLocalRing.maximalIdeal (PointLocalRing p)) (PointLocalRing p) ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal (PointLocalRing (pointTensorMap β p)))
        (PointLocalRing (pointTensorMap β p)) :=
  RingEquiv.ofBijective (IsLocalRing.completionMap (localMap β p))
    (localCompletionMap_bijective β p hR hker hp)

/-- Every original local coefficient retains its literal completed image. -/
theorem localCompletionEquiv_algebraMap (b : PointLocalRing p) :
    localCompletionEquiv β p hR hker hp (algebraMap _ _ b) =
      algebraMap _ _ (localMap β p b) :=
  IsLocalRing.completionMap_algebraMap (localMap β p) b

/-- The original comparison carries the WHOLE extension of every original point-local ideal. -/
theorem localCompletionEquiv_map_ideal (I : Ideal (PointLocalRing p)) :
    (I.map (algebraMap _
      (AdicCompletion (IsLocalRing.maximalIdeal (PointLocalRing p)) (PointLocalRing p)))).map
        (localCompletionEquiv β p hR hker hp).toRingHom =
      (I.map (localMap β p)).map (algebraMap _
        (AdicCompletion (IsLocalRing.maximalIdeal (PointLocalRing (pointTensorMap β p)))
          (PointLocalRing (pointTensorMap β p)))) :=
  IsLocalRing.map_completionMap_map (localMap β p) I

end Completion

section LocalLift

variable {F : Type u} [CommRing F] [IsLocalRing F]
  (ε : F →+* K) (γ : A →+* F)
  (hε : RingHom.ker ε = IsLocalRing.maximalIdeal F)
  (hγ : ε.comp γ = p.toRingHom)

include hε hγ in
private theorem pointLocalLift_denominator_unit (s : (pointIdeal p).primeCompl) :
    IsUnit (γ s) := by
  by_contra hu
  have hm : γ s ∈ IsLocalRing.maximalIdeal F := hu
  rw [← hε] at hm
  have he := RingHom.congr_fun hγ s
  change ε (γ s) = p s at he
  have hz : p s = 0 := he.symm.trans hm
  exact s.property hz

/-- Actual residue evaluations manufacture the original point-local lift internally. -/
def pointLocalLift : PointLocalRing p →+* F :=
  IsLocalization.lift (S := PointLocalRing p) (g := γ)
    (pointLocalLift_denominator_unit p ε γ hε hγ)

/-- The original point-local lift keeps every actual original affine coefficient. -/
theorem pointLocalLift_algebraMap (a : A) :
    pointLocalLift p ε γ hε hγ (algebraMap A (PointLocalRing p) a) = γ a :=
  IsLocalization.lift_eq (pointLocalLift_denominator_unit p ε γ hε hγ) a

/-- Localness is derived from the same whole point ideal and original residue evaluation. -/
instance pointLocalLift_isLocalHom : IsLocalHom (pointLocalLift p ε γ hε hγ) := by
  apply ((IsLocalRing.local_hom_TFAE (pointLocalLift p ε γ hε hγ)).out 0 2).mpr
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (pointIdeal p) (PointLocalRing p),
    Ideal.map_map, Ideal.map_le_iff_le_comap]
  intro a ha
  change pointLocalLift p ε γ hε hγ (algebraMap A (PointLocalRing p) a) ∈
    IsLocalRing.maximalIdeal F
  rw [pointLocalLift_algebraMap, ← hε]
  change ε (γ a) = 0
  exact (RingHom.congr_fun hγ a).trans ha

/-- Original point surjectivity derives the whole residue-field bijection of the manufactured lift. -/
theorem pointLocalLift_residue_bijective (hp : Function.Surjective p) :
    Function.Bijective (IsLocalRing.ResidueField.map (pointLocalLift p ε γ hε hγ)) := by
  refine ⟨(IsLocalRing.ResidueField.map (pointLocalLift p ε γ hε hγ)).injective, ?_⟩
  intro y
  obtain ⟨f, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨a, ha⟩ := hp (ε f)
  refine ⟨IsLocalRing.residue _ (algebraMap A (PointLocalRing p) a), ?_⟩
  rw [IsLocalRing.ResidueField.map_residue, pointLocalLift_algebraMap]
  apply Ideal.Quotient.eq.mpr
  rw [← hε]
  change ε (γ a - f) = 0
  rw [map_sub, show ε (γ a) = p a from RingHom.congr_fun hγ a, ha, sub_self]

end LocalLift

section TensorLift

variable {F : Type u} [CommRing F] [IsLocalRing F] [Algebra R F]
  (ε : F →+* K) (γ : A →ₐ[R] F) (δ : S →ₐ[R] F)
  (hε : RingHom.ker ε = IsLocalRing.maximalIdeal F)
  (hγ : ε.comp γ.toRingHom = p.toRingHom)
  (hδ : ε.comp δ.toRingHom = β.toRingHom)

omit [IsLocalRing F] in
/-- The actual common original coefficient action manufactures the WHOLE tensor map. -/
def tensorLift : A ⊗[R] S →ₐ[R] F :=
  Algebra.TensorProduct.lift γ δ (fun _ _ => Commute.all _ _)

omit [IsLocalRing F] in
/-- Literal actual coefficient readback on every pure tensor. -/
theorem tensorLift_tmul (a : A) (s : S) :
    tensorLift γ δ (a ⊗ₜ[R] s) = γ a * δ s := rfl

omit [IsLocalRing F] in
include hγ hδ in
/-- The residue square holds on the ENTIRE original tensor algebra. -/
theorem tensorLift_eval : ε.comp (tensorLift γ δ).toRingHom =
    (pointTensorMap β p).toRingHom := by
  apply Algebra.TensorProduct.ringHom_ext
  · ext a
    change ε (γ a * δ 1) = p a * β 1
    rw [map_one, mul_one, map_one, mul_one]
    exact RingHom.congr_fun hγ a
  · ext s
    change ε (γ 1 * δ s) = p 1 * β s
    rw [map_one, one_mul, map_one, one_mul]
    exact RingHom.congr_fun hδ s

/-- The actual tensor map lifts to the SAME original tensor-point localization. -/
def localTensorLift : PointLocalRing (pointTensorMap β p) →+* F :=
  pointLocalLift (pointTensorMap β p) ε (tensorLift γ δ).toRingHom hε
    (tensorLift_eval β p ε γ δ hγ hδ)

instance localTensorLift_isLocalHom : IsLocalHom (localTensorLift β p ε γ δ hε hγ hδ) := by
  unfold localTensorLift
  infer_instance

/-- The WHOLE actual tensor ring retains its literal local image. -/
theorem localTensorLift_algebraMap (t : A ⊗[R] S) :
    localTensorLift β p ε γ δ hε hγ hδ
      (algebraMap (A ⊗[R] S) (PointLocalRing (pointTensorMap β p)) t) = tensorLift γ δ t :=
  pointLocalLift_algebraMap _ _ _ _ _ t

/-- EVERY original affine coefficient keeps its actual original source formal image. -/
theorem localTensorLift_includeLeft (a : A) :
    localTensorLift β p ε γ δ hε hγ hδ
      (algebraMap (A ⊗[R] S) (PointLocalRing (pointTensorMap β p))
        ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] S) a)) = γ a := by
  rw [localTensorLift_algebraMap]
  change γ a * δ 1 = γ a
  rw [map_one, mul_one]

/-- EVERY coefficient in the WHOLE extended coefficient ring keeps its actual formal pullback. -/
theorem localTensorLift_includeRight (s : S) :
    localTensorLift β p ε γ δ hε hγ hδ
      (algebraMap (A ⊗[R] S) (PointLocalRing (pointTensorMap β p))
        ((Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S) s)) = δ s := by
  rw [localTensorLift_algebraMap]
  change γ 1 * δ s = δ s
  rw [map_one, one_mul]

/-- The ENTIRE original point-local restriction is the original localization of its own coefficient map. -/
theorem localTensorLift_comp_localMap :
    (localTensorLift β p ε γ δ hε hγ hδ).comp (localMap β p) =
      pointLocalLift p ε γ.toRingHom hε hγ := by
  apply IsLocalization.ringHom_ext (pointIdeal p).primeCompl
  ext a
  change localTensorLift β p ε γ δ hε hγ hδ
    (localMap β p (algebraMap A (PointLocalRing p) a)) =
      pointLocalLift p ε γ.toRingHom hε hγ (algebraMap A (PointLocalRing p) a)
  rw [localMap_algebraMap, localTensorLift_includeLeft,
    pointLocalLift_algebraMap]
  rfl

end TensorLift

end EnvelopeProperty.ClosedFibreStalkCompletion
