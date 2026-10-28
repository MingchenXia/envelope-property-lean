import EnvelopeProperty.Algebra.SurfacePrimeHeight
import EnvelopeProperty.AlgGeom.KrullDim
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Topology.LocallyClosed

/-! # Actual original codimension-one stalks on integral Jacobson surfaces -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.NormalSurfaceStalk
variable {X : Scheme.{u}} [IsIntegral X] [JacobsonSpace X]
    (hdim : topologicalKrullDim X ≤ 2) (x : X)
    (hx : x ≠ genericPoint X) (hxc : ¬ IsClosed ({x} : Set X))

include hdim hx hxc in
private theorem affine_prime_height (U : X.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U) :
    (hU.primeIdealOf ⟨x,hxU⟩).asIdeal.height = 1 := by
  let : Nonempty U := ⟨⟨x,hxU⟩⟩
  let A : Type u := Γ(X,U)
  let p : Spec (.of A) := hU.primeIdealOf ⟨x,hxU⟩
  have hp : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x,hxU⟩
  let : IsDominant hU.fromSpec := ⟨hU.fromSpec.opensRange.isOpen.dense
    ⟨x,p,hp⟩⟩
  have hg : hU.fromSpec (⊥ : PrimeSpectrum A) = genericPoint X := by
    rw [← genericPoint_eq_bot_of_affine]
    apply ((genericPoint_spec X).eq _).symm
    have hs := (genericPoint_spec (Spec (.of A))).image hU.fromSpec.continuous
    simp only [Set.image_univ] at hs
    change IsGenericPoint (hU.fromSpec (genericPoint (Spec (.of A))))
      (closure (Set.range hU.fromSpec)) at hs
    rwa [hU.fromSpec.denseRange.closure_range] at hs
  have hp0 : p.asIdeal ≠ ⊥ := by
    intro hz
    have hh : p = (⊥ : PrimeSpectrum A) := PrimeSpectrum.ext hz
    exact hx (hp.symm.trans ((congrArg hU.fromSpec hh).trans hg))
  have hpmax : ¬ p.asIdeal.IsMaximal := by
    intro hm
    have hc : IsClosed ({p} : Set (Spec (.of A))) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr hm
    have hl := hc.isLocallyClosed.image hU.fromSpec.isOpenEmbedding.isEmbedding.isInducing
      hU.fromSpec.isOpenEmbedding.isOpen_range.isLocallyClosed
    apply hxc
    apply isClosed_singleton_of_isLocallyClosed_singleton
    simpa only [Set.image_singleton,hp] using hl
  have hA : ringKrullDim A ≤ 2 := by
    have hh := hU.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le.trans hdim
    change topologicalKrullDim (PrimeSpectrum A) ≤ 2 at hh
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at hh
  exact SurfacePrimeHeight.height_eq_one hA p.asIdeal hp0 hpmax

include hdim hx hxc in
/-- EVERY actual nongeneric nonclosed original Jacobson surface point has SAME stalk dimension one. -/
theorem stalk_dimension_eq_one : ringKrullDim (X.presheaf.stalk x) = 1 := by
  obtain ⟨U,hU,hxU,_⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨x,hxU⟩⟩
  let p := hU.primeIdealOf ⟨x,hxU⟩
  have hp : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x,hxU⟩
  rw [← hp]
  have e := (asIso (hU.fromSpec.stalkMap p)).commRingCatIsoToRingEquiv.trans
    (Spec.stalkIso Γ(X,U) p).commRingCatIsoToRingEquiv
  rw [ringKrullDim_eq_of_ringEquiv e,
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal)]
  rw [affine_prime_height hdim x hx hxc U hU hxU]
  rfl

include hdim hx hxc in
/-- Actual normality and Noetherianity internally DERIVE a genuine same original surface stalk DVR. -/
theorem stalk_isDiscreteValuationRing [IsLocallyNoetherian X]
    [IsIntegrallyClosed (X.presheaf.stalk x)] : IsDiscreteValuationRing (X.presheaf.stalk x) := by
  have hd := stalk_dimension_eq_one hdim x hx hxc
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := Ring.krullDimLE_iff.mpr hd.le
  let : IsPrincipalIdealRing (X.presheaf.stalk x) := by
    apply (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk x)).out 3 0 |>.mp
    refine ⟨inferInstance,fun P hP hPrime => ?_⟩
    exact IsLocalRing.eq_maximalIdeal (hPrime.isMaximal_of_ne_bot hP)
  refine {not_a_field' := ?_}
  intro hz
  let : Field (X.presheaf.stalk x) := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hz).toField
  have hh := ringKrullDim_eq_zero_of_field (X.presheaf.stalk x)
  rw [hd] at hh
  norm_num at hh

end EnvelopeProperty.NormalSurfaceStalk
