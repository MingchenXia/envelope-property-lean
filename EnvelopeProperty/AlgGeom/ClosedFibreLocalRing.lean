import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# The same actual field point after coefficient base change

The original residue quotient and its actual whole kernel produce an
isomorphism `K ⊗[R] S ≃ K`, with the literal tensor coefficient formula.
Right exactness then identifies the entire original field-point ideal
after coefficient extension, before localizing at that same point.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open TensorProduct

namespace EnvelopeProperty.ClosedFibreLocalRing

universe u

variable {R S K : Type u} [CommRing R] [CommRing S] [Field K]
  [Algebra R S] [Algebra R K]
  (β : S →ₐ[R] K)

/-- The actual coefficient map on the same original residue-point tensor product. -/
def residueTensorMap : K ⊗[R] S →ₐ[K] K := β.liftEquiv R K S K

/-- Every actual pure tensor has its original coefficient evaluation. -/
theorem residueTensorMap_tmul (c : K) (s : S) :
    residueTensorMap β (c ⊗ₜ[R] s) = c * β s := rfl

variable (hR : Function.Surjective (algebraMap R K))
  (hker : RingHom.ker β.toRingHom =
    (RingHom.ker (algebraMap R K)).map (algebraMap R S))

include hR hker in
/-- The original quotient-kernel identity forces the actual entire tensor relation. -/
theorem one_tmul_eq_residue_tmul (s : S) :
    (1 : K) ⊗ₜ[R] s = β s ⊗ₜ[R] (1 : S) := by
  have hI : (RingHom.ker (algebraMap R K)).map (algebraMap R S) ≤
      RingHom.ker (Algebra.TensorProduct.includeRight : S →ₐ[R] K ⊗[R] S).toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change Algebra.TensorProduct.includeRight (algebraMap R S r) = 0
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R K (K ⊗[R] S),
      RingHom.mem_ker.mp hr, map_zero]
  obtain ⟨r, hr⟩ := hR (β s)
  have hs : s - algebraMap R S r ∈ RingHom.ker β.toRingHom := by
    change β (s - algebraMap R S r) = 0
    rw [map_sub, β.commutes, hr, sub_self]
  rw [hker] at hs
  have he := hI hs
  change Algebra.TensorProduct.includeRight (s - algebraMap R S r) = 0 at he
  rw [map_sub, AlgHom.commutes,
    IsScalarTower.algebraMap_apply R K (K ⊗[R] S), hr, sub_eq_zero] at he
  exact he

/-- The actual residue-point tensor is canonically the SAME original field. -/
def residueTensorEquiv : K ⊗[R] S ≃ₐ[K] K :=
  AlgEquiv.ofAlgHom (residueTensorMap β) (Algebra.ofId K (K ⊗[R] S))
    (Subsingleton.elim _ _)
    (by
      apply Algebra.TensorProduct.ext_ring
      ext s
      change algebraMap K (K ⊗[R] S) (residueTensorMap β ((1 : K) ⊗ₜ[R] s)) =
        (1 : K) ⊗ₜ[R] s
      rw [residueTensorMap_tmul, one_mul]
      exact (one_tmul_eq_residue_tmul β hR hker s).symm)

/-- The whole actual residue isomorphism retains every original pure tensor. -/
theorem residueTensorEquiv_tmul (c : K) (s : S) :
    residueTensorEquiv β hR hker (c ⊗ₜ[R] s) = c * β s := rfl

section Point

variable {A : Type u} [CommRing A] [Algebra R A] (p : A →ₐ[R] K)

/-- The actual SAME field point of the actual coefficient tensor algebra. -/
def pointTensorMap : A ⊗[R] S →ₐ[R] K :=
  ((residueTensorMap β).restrictScalars R).comp
    (Algebra.TensorProduct.map p (AlgHom.id R S))

/-- Every original pure tensor is evaluated by the original field points. -/
theorem pointTensorMap_tmul (a : A) (s : S) :
    pointTensorMap β p (a ⊗ₜ[R] s) = p a * β s := rfl

/-- The original coefficient inclusion retains the SAME original point. -/
theorem pointTensorMap_includeLeft (a : A) :
    pointTensorMap β p ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] S) a) = p a := by
  change pointTensorMap β p (a ⊗ₜ[R] (1 : S)) = p a
  rw [pointTensorMap_tmul, map_one, mul_one]

/-- The actual original field point supplies surjectivity after coefficient extension. -/
theorem pointTensorMap_surjective (hp : Function.Surjective p) :
    Function.Surjective (pointTensorMap β p) := by
  intro c
  obtain ⟨a, ha⟩ := hp c
  exact ⟨(Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] S) a,
    (pointTensorMap_includeLeft β p a).trans ha⟩

include hR hker in
/-- The WHOLE original point ideal extends to the WHOLE actual base-changed point ideal. -/
theorem pointTensorMap_ker (hp : Function.Surjective p) :
    RingHom.ker (pointTensorMap β p).toRingHom =
      (RingHom.ker p.toRingHom).map
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] S).toRingHom := by
  change RingHom.ker
      ((residueTensorEquiv β hR hker).toRingHom.comp
        (Algebra.TensorProduct.map p (AlgHom.id R S)).toRingHom) = _
  exact (RingHom.ker_comp_of_injective
    (f := (residueTensorEquiv β hR hker).toRingHom)
    (Algebra.TensorProduct.map p (AlgHom.id R S)).toRingHom
    (residueTensorEquiv β hR hker).injective).trans
      (Algebra.TensorProduct.rTensor_ker (C := S) p hp)

/-- The actual whole field-point ideal, without a chosen set of generators. -/
def pointIdeal : Ideal A := RingHom.ker p.toRingHom

instance pointIdeal_isPrime : (pointIdeal p).IsPrime := RingHom.ker_isPrime p.toRingHom

/-- The actual original point localization. -/
abbrev PointLocalRing := Localization.AtPrime (pointIdeal p)

/-- The exact original inverse-image point ideal is derived from actual coefficient readback. -/
theorem pointIdeal_comap : pointIdeal p = (pointIdeal (pointTensorMap β p)).comap
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] S).toRingHom := by
  ext a
  change p a = 0 ↔ pointTensorMap β p
    ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] S) a) = 0
  rw [pointTensorMap_includeLeft]

/-- The original coefficient inclusion induces the SAME actual map of point-localizations. -/
def localMap : PointLocalRing p →+* PointLocalRing (pointTensorMap β p) :=
  Localization.localRingHom (pointIdeal p) (pointIdeal (pointTensorMap β p))
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] S).toRingHom
    (pointIdeal_comap β p)

instance localMap_isLocalHom : IsLocalHom (localMap β p) := by
  unfold localMap
  infer_instance

/-- Every original affine coefficient keeps its actual localized tensor image. -/
theorem localMap_algebraMap (a : A) :
    localMap β p (algebraMap A (PointLocalRing p) a) =
      algebraMap (A ⊗[R] S) (PointLocalRing (pointTensorMap β p))
        ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] S) a) :=
  Localization.localRingHom_to_map _ _ _ _ a

include hR hker in
/-- The actual WHOLE point-local maximal ideal is generated by the original maximal ideal. -/
theorem localMap_map_maximalIdeal (hp : Function.Surjective p) :
    (IsLocalRing.maximalIdeal (PointLocalRing p)).map (localMap β p) =
      IsLocalRing.maximalIdeal (PointLocalRing (pointTensorMap β p)) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (pointIdeal p) (PointLocalRing p),
    ← IsLocalization.AtPrime.map_eq_maximalIdeal
      (pointIdeal (pointTensorMap β p)) (PointLocalRing (pointTensorMap β p))]
  change ((pointIdeal p).map (algebraMap A (PointLocalRing p))).map (localMap β p) =
    (RingHom.ker (pointTensorMap β p).toRingHom).map _
  rw [pointTensorMap_ker β hR hker p hp, Ideal.map_map, Ideal.map_map]
  congr 1
  exact RingHom.ext (localMap_algebraMap β p)

/-- The original point evaluations derive a bijection on the actual local residue fields. -/
theorem localMap_residue_bijective (hp : Function.Surjective p) :
    Function.Bijective (IsLocalRing.ResidueField.map (localMap β p)) := by
  let : (pointIdeal (pointTensorMap β p)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (pointTensorMap β p) (pointTensorMap_surjective β p hp)
  refine ⟨(IsLocalRing.ResidueField.map (localMap β p)).injective, ?_⟩
  intro y
  obtain ⟨t, rfl⟩ := (pointIdeal (pointTensorMap β p)).algebraMap_residueField_surjective y
  obtain ⟨a, ha⟩ := hp (pointTensorMap β p t)
  refine ⟨algebraMap A (pointIdeal p).ResidueField a, ?_⟩
  change Ideal.ResidueField.map (pointIdeal p) (pointIdeal (pointTensorMap β p))
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] S).toRingHom (pointIdeal_comap β p)
      (algebraMap A (pointIdeal p).ResidueField a) = _
  rw [Ideal.ResidueField.map_algebraMap]
  apply sub_eq_zero.mp
  rw [← map_sub, Ideal.algebraMap_residueField_eq_zero]
  change pointTensorMap β p
    ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] S) a - t) = 0
  rw [map_sub, pointTensorMap_includeLeft, ha, sub_self]

/-- Genuine coefficient flatness gives flatness of the SAME actual local point map. -/
theorem localMap_flat [Module.Flat R S] : (localMap β p).Flat := by
  have hi : (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] S).toRingHom.Flat := by
    change (algebraMap A (A ⊗[R] S)).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  exact hi.localRingHom _ _ (pointIdeal_comap β p)

end Point

end EnvelopeProperty.ClosedFibreLocalRing
