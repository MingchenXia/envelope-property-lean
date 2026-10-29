import EnvelopeProperty.Alterations.Algebra.IntegralClosureFiniteType
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.EssentialFiniteness

/-! # Actual normalization finiteness for essentially finite type domains -/
noncomputable section
open scoped nonZeroDivisors
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.EssentiallyFiniteTypeNormalization
private theorem fractionField_of_localization_tower
    {R S F : Type*} [CommRing R] [CommRing S] [Field F]
    [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F]
    [FaithfulSMul R F] (M : Submonoid R) [IsLocalization M S] [IsFractionRing S F] :
    IsFractionRing R F := by
  apply IsFractionRing.of_field R F
  intro z
  obtain ⟨f, g, _, hz⟩ := IsFractionRing.div_surjective S z
  obtain ⟨a, b, s, ha, hb⟩ := IsLocalization.surj₂ M S f g
  have hs : algebraMap R F (s : R) ≠ 0 := by
    have h := (IsLocalization.map_units S s).map (algebraMap S F)
    simpa only [IsScalarTower.algebraMap_apply R S F] using h.ne_zero
  have haF : algebraMap S F f * algebraMap R F (s : R) = algebraMap R F a := by
    simpa only [map_mul, IsScalarTower.algebraMap_apply R S F] using
      congrArg (algebraMap S F) ha
  have hbF : algebraMap S F g * algebraMap R F (s : R) = algebraMap R F b := by
    simpa only [map_mul, IsScalarTower.algebraMap_apply R S F] using
      congrArg (algebraMap S F) hb
  refine ⟨a, b, ?_⟩
  rw [← hz, ← haF, ← hbF, mul_div_mul_right _ _ hs]

universe u
variable (k D K : Type u) [Field k] [CommRing D] [IsDomain D] [Algebra k D]
  [Algebra.EssFiniteType k D] [Field K] [Algebra D K] [IsFractionRing D K]

include k

/-- The SAME actual integral closure is finite for an arbitrary essentially
finite type domain over ANY original field. No normalization certificate. -/
theorem finite_integralClosure : Module.Finite D (integralClosure D K) := by
  let C := Algebra.EssFiniteType.subalgebra k D
  let M := Algebra.EssFiniteType.submonoid k D
  let : Algebra C K := ((algebraMap D K).comp C.val.toRingHom).toAlgebra
  let : SMul C D := (inferInstance : Algebra C D).toSMul
  let : SMul C K := (inferInstance : Algebra C K).toSMul
  let : IsScalarTower C D K := .of_algebraMap_eq fun _ => rfl
  let : FaithfulSMul C K := (faithfulSMul_iff_algebraMap_injective C K).mpr
    ((IsFractionRing.injective D K).comp Subtype.val_injective)
  let : IsFractionRing C K := fractionField_of_localization_tower (S := D) M
  let : Module.Finite C (integralClosure C K) :=
    Alterations.Algebra.IntegralClosureFiniteType.finite_integralClosure k C K
  let : Algebra C (integralClosure D K) :=
    ((algebraMap D (integralClosure D K)).comp (algebraMap C D)).toAlgebra
  let : SMul C (integralClosure D K) := (inferInstance : Algebra C (integralClosure D K)).toSMul
  let : IsScalarTower C D (integralClosure D K) := .of_algebraMap_eq fun _ => rfl
  let q : integralClosure C K →+* integralClosure D K :=
    (integralClosure C K).val.toRingHom.codRestrict (integralClosure D K)
      (fun a => a.2.tower_top)
  let : Algebra (integralClosure C K) (integralClosure D K) := q.toAlgebra
  let : IsScalarTower (integralClosure C K) (integralClosure D K) K :=
    .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower C (integralClosure C K) (integralClosure D K) :=
    .of_algebraMap_eq fun _ => Subtype.ext rfl
  let : IsLocalization (Algebra.algebraMapSubmonoid K M) K :=
    IsLocalization.of_le_isUnit (by
      rintro _ ⟨m,hm,rfl⟩
      exact (IsLocalization.map_units D (⟨m,hm⟩ : M)).map (algebraMap D K))
  let : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure C K) M)
      (integralClosure D K) := IsLocalization.integralClosure (S := K) (Rf := D) (Sf := K) M
  exact Module.Finite.of_isLocalization C (integralClosure C K) M

/-- The SAME original normalization is Noetherian; its finiteness is derived. -/
theorem isNoetherianRing_integralClosure : IsNoetherianRing (integralClosure D K) := by
  let : IsNoetherianRing D := Algebra.EssFiniteType.isNoetherianRing k D
  let : Module.Finite D (integralClosure D K) := finite_integralClosure k D K
  exact Algebra.FiniteType.isNoetherianRing D (integralClosure D K)

end EnvelopeProperty.EssentiallyFiniteTypeNormalization
