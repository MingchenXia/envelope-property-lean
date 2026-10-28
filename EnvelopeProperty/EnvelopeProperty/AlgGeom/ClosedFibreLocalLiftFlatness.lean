import EnvelopeProperty.AlgGeom.ClosedFibreStalkCompletion
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Faithful flatness of the SAME actual tensor-local coefficient map

Actual source flatness and whole point-ideal image give the original source
completion comparison. The whole original restriction of the manufactured
tensor-local lift makes its own canonical completion map bijective. Genuine
noetherian completion flatness and target completeness then prove flatness of
that SAME lift, preserving its entire original A and S coefficient action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.ClosedFibreLocalLiftFlatness

open ClosedFibreLocalRing ClosedFibreStalkCompletion

universe u

variable {R S K A : Type u} [CommRing R] [CommRing S] [Field K] [CommRing A]
  [Algebra R S] [Algebra R K] [Algebra R A]
  (β : S →ₐ[R] K) (p : A →ₐ[R] K)

section Source

variable {F : Type u} [CommRing F] [IsLocalRing F]
  (ε : F →+* K) (γ : A →+* F)
  (hε : RingHom.ker ε = IsLocalRing.maximalIdeal F)
  (hγ : ε.comp γ = p.toRingHom)

/-- Flatness of the original actual affine map descends to its manufactured point-local lift. -/
theorem pointLocalLift_flat (hflat : γ.Flat) : (pointLocalLift p ε γ hε hγ).Flat := by
  let B := PointLocalRing p
  let : Algebra A F := γ.toAlgebra
  let : Algebra B F := (pointLocalLift p ε γ hε hγ).toAlgebra
  let : IsScalarTower A B F := IsScalarTower.of_algebraMap_eq fun a =>
    (pointLocalLift_algebraMap p ε γ hε hγ a).symm
  let : Module.Flat A F := hflat
  change Module.Flat B F
  exact (Module.flat_iff_of_isLocalization B (pointIdeal p).primeCompl F).mpr inferInstance

/-- The original whole point-ideal image derives the whole maximal-ideal image of the actual local lift. -/
theorem pointLocalLift_map_maximalIdeal
    (hm : (pointIdeal p).map γ = IsLocalRing.maximalIdeal F) :
    (IsLocalRing.maximalIdeal (PointLocalRing p)).map (pointLocalLift p ε γ hε hγ) =
      IsLocalRing.maximalIdeal F := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (pointIdeal p) (PointLocalRing p),
    Ideal.map_map]
  have hc : (pointLocalLift p ε γ hε hγ).comp (algebraMap A (PointLocalRing p)) = γ :=
    RingHom.ext (pointLocalLift_algebraMap p ε γ hε hγ)
  rw [hc]
  exact hm

/-- The SAME original source coefficient map induces its own canonical completed bijection. -/
theorem pointLocalLift_completionMap_bijective (hp : Function.Surjective p)
    (hflat : γ.Flat) (hm : (pointIdeal p).map γ = IsLocalRing.maximalIdeal F) :
    Function.Bijective (IsLocalRing.completionMap (pointLocalLift p ε γ hε hγ)) :=
  IsLocalRing.bijective_completionMap_of_flat_of_map_maximalIdeal
    (pointLocalLift p ε γ hε hγ) (pointLocalLift_flat p ε γ hε hγ hflat)
    (pointLocalLift_map_maximalIdeal p ε γ hε hγ hm)
    (pointLocalLift_residue_bijective p ε γ hε hγ hp)

end Source

section Tensor

variable {F : Type u} [CommRing F] [IsLocalRing F] [Algebra R F]
  (ε : F →+* K) (γ : A →ₐ[R] F) (δ : S →ₐ[R] F)
  (hε : RingHom.ker ε = IsLocalRing.maximalIdeal F)
  (hγ : ε.comp γ.toRingHom = p.toRingHom)
  (hδ : ε.comp δ.toRingHom = β.toRingHom)
  (hR : Function.Surjective (algebraMap R K))
  (hker : RingHom.ker β.toRingHom =
    (RingHom.ker (algebraMap R K)).map (algebraMap R S))
  (hp : Function.Surjective p)

include hR hker hp in
/-- The actual tensor-local map extends the WHOLE actual tensor-point maximal ideal onto the target one. -/
theorem localTensorLift_map_maximalIdeal
    (hm : (pointIdeal p).map γ.toRingHom = IsLocalRing.maximalIdeal F) :
    (IsLocalRing.maximalIdeal (PointLocalRing (pointTensorMap β p))).map
        (localTensorLift β p ε γ δ hε hγ hδ) = IsLocalRing.maximalIdeal F := by
  rw [← localMap_map_maximalIdeal β hR hker p hp, Ideal.map_map,
    localTensorLift_comp_localMap]
  exact pointLocalLift_map_maximalIdeal p ε γ.toRingHom hε hγ hm

include hR hker hp in
/-- The manufactured map has a CANONICAL completed bijection, derived from its actual whole restriction. -/
theorem localTensorLift_completionMap_bijective [Module.Flat R S]
    (hflat : γ.toRingHom.Flat)
    (hm : (pointIdeal p).map γ.toRingHom = IsLocalRing.maximalIdeal F) :
    Function.Bijective (IsLocalRing.completionMap (localTensorLift β p ε γ δ hε hγ hδ)) := by
  have hB := localCompletionMap_bijective β p hR hker hp
  have hF := pointLocalLift_completionMap_bijective p ε γ.toRingHom hε hγ hp hflat hm
  have hc : (IsLocalRing.completionMap (localTensorLift β p ε γ δ hε hγ hδ)).comp
      (IsLocalRing.completionMap (localMap β p)) =
        IsLocalRing.completionMap (pointLocalLift p ε γ.toRingHom hε hγ) := by
    rw [← IsLocalRing.completionMap_comp]
    congr 1
    exact localTensorLift_comp_localMap β p ε γ δ hε hγ hδ
  apply (Function.Bijective.of_comp_iff
    (IsLocalRing.completionMap (localTensorLift β p ε γ δ hε hγ hδ)) hB).mp
  change Function.Bijective ((IsLocalRing.completionMap
    (localTensorLift β p ε γ δ hε hγ hδ)).comp
      (IsLocalRing.completionMap (localMap β p)))
  rw [hc]
  exact hF

include hR hker hp in
/-- Actual noetherian completion and actual target completeness prove flatness of the SAME original tensor-local map. -/
theorem localTensorLift_flat [Module.Flat R S]
    [IsNoetherianRing (PointLocalRing (pointTensorMap β p))]
    [IsAdicComplete (IsLocalRing.maximalIdeal F) F]
    (hflat : γ.toRingHom.Flat)
    (hm : (pointIdeal p).map γ.toRingHom = IsLocalRing.maximalIdeal F) :
    (localTensorLift β p ε γ δ hε hγ hδ).Flat := by
  let D := PointLocalRing (pointTensorMap β p)
  let Dhat := AdicCompletion (IsLocalRing.maximalIdeal D) D
  let Fhat := AdicCompletion (IsLocalRing.maximalIdeal F) F
  let liftHom := localTensorLift β p ε γ δ hε hγ hδ
  have hi : (algebraMap D Dhat).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hl : (IsLocalRing.completionMap liftHom).Flat := RingHom.Flat.of_bijective
    (localTensorLift_completionMap_bijective β p ε γ δ hε hγ hδ hR hker hp hflat hm)
  have hc : ((IsLocalRing.completionMap liftHom).comp (algebraMap D Dhat)).Flat := hi.comp hl
  have he : (IsLocalRing.completionMap liftHom).comp (algebraMap D Dhat) =
      (algebraMap F Fhat).comp liftHom :=
    RingHom.ext (IsLocalRing.completionMap_algebraMap liftHom)
  rw [he] at hc
  have hb : Function.Bijective (algebraMap F Fhat) := by
    change Function.Bijective (AdicCompletion.of _ _)
    exact AdicCompletion.of_bijective _ _
  exact (RingHom.Flat.comp_iff_of_bijective_left hb).mp hc

include hR hker hp in
/-- The SAME actual whole-coefficient tensor-local map is faithfully flat, with no completed-comparison input. -/
theorem localTensorLift_faithfullyFlat [Module.Flat R S]
    [IsNoetherianRing (PointLocalRing (pointTensorMap β p))]
    [IsAdicComplete (IsLocalRing.maximalIdeal F) F]
    (hflat : γ.toRingHom.Flat)
    (hm : (pointIdeal p).map γ.toRingHom = IsLocalRing.maximalIdeal F) :
    (localTensorLift β p ε γ δ hε hγ hδ).FaithfullyFlat := by
  let : Algebra (PointLocalRing (pointTensorMap β p)) F :=
    (localTensorLift β p ε γ δ hε hγ hδ).toAlgebra
  let : Module.Flat (PointLocalRing (pointTensorMap β p)) F :=
    localTensorLift_flat β p ε γ δ hε hγ hδ hR hker hp hflat hm
  let : IsLocalHom (algebraMap (PointLocalRing (pointTensorMap β p)) F) :=
    localTensorLift_isLocalHom β p ε γ δ hε hγ hδ
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end Tensor

end EnvelopeProperty.ClosedFibreLocalLiftFlatness
