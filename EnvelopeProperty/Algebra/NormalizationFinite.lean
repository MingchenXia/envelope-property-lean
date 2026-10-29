/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Finiteness of normalization over a perfect field

Let `k` be a perfect field and let `D` be a finitely generated `k`-algebra which is a domain.
We prove that the integral closure of `D` in any finite extension `L` of its fraction field
(in particular in its fraction field itself) is a finite `D`-module. Consequently the
normalization of `D` is a finitely generated `k`-algebra and a Noetherian integrally closed
domain.

This is `thm:bj-normalization-finite` of the blueprint (`bj22.tex`, used for the Rees valuations
of `def:bj-rees`). Mathlib only contains the separable case `IsIntegralClosure.finite` (via the
trace form); the point here is the inseparable case in positive characteristic.

## Strategy

By Noether normalization (`exists_finite_inj_algHom_of_fg`) there is a polynomial ring
`A = k[z₁, …, z_s] ⊆ D` over which `D` is finite, and the integral closure of `D` in `L` is the
integral closure of `A` in `L`, a finite extension of `K = Frac A`. So it suffices to treat a
finitely generated, integrally closed `k`-domain `A`
(`finite_of_isIntegralClosure_of_isIntegrallyClosed`).

Let `p` be the exponential characteristic and let `Kₛ` be the separable closure of `K` in `L`.
The extension `L / Kₛ` is purely inseparable and finite, so it has an exponent `n`: `x ^ q ∈ Kₛ`
for all `x ∈ L`, where `q = p ^ n`. The integral closure `Cₛ` of `A` in `Kₛ` is a finite
`A`-module by the separable case. The map `ψ : x ↦ x ^ q` is an injective ring homomorphism
from the integral closure `C` of `A` in `L` to `Cₛ`, and it is semilinear with respect to the
Frobenius `σ : a ↦ a ^ q` of `A`. Since `k` is perfect, `A` is a finite module over itself via
`σ` (`finite_iterateFrobenius`): it is integral (`a` is a root of `T ^ q - σ a`) and of finite
type (the image of `σ` contains `k`). Hence `Cₛ` is finite over `A` via `σ`, and `C`, which
embeds into it compatibly with `σ`, is finite over the Noetherian ring `A`
(`finite_of_injective_comp`).

This replaces the blueprint's argument with `K_q = k(z^{1/q})` inside an algebraic closure by
its image under the Frobenius, so that no algebraic closure or `q`-th roots are needed.

## Main results

* `EnvelopeProperty.finite_of_isIntegralClosure_of_finiteType`: the integral closure of a
  finitely generated domain `D` over a perfect field in a finite extension of `Frac D` is a
  finite `D`-module.
* `EnvelopeProperty.finite_integralClosure`: the case of the fraction field itself.
* `EnvelopeProperty.finiteType_integralClosure`, `EnvelopeProperty.isNoetherianRing_integralClosure`,
  `EnvelopeProperty.isIntegrallyClosed_integralClosure`: the normalization is a finitely
  generated `k`-algebra and a Noetherian integrally closed domain.
-/

open Polynomial

namespace EnvelopeProperty

/-- If `f : A →+* B` is finite, `A` is Noetherian, and `g : A →+* C` factors as `f = ψ ∘ g` with
`ψ : C →+* B` injective, then `g` is finite: `C` is an `A`-submodule of the Noetherian
`A`-module `B`. -/
theorem finite_of_injective_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsNoetherianRing A] {f : A →+* B} {g : A →+* C} (hf : f.Finite) (ψ : C →+* B)
    (hψ : Function.Injective ψ) (h : ψ.comp g = f) : g.Finite := by
  let _ := f.toAlgebra
  let _ := g.toAlgebra
  let _ := ψ.toAlgebra
  have : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq' h.symm
  have : Module.Finite A B := hf
  have : IsNoetherian A B := isNoetherian_of_isNoetherianRing_of_finite A B
  have : IsNoetherian A C :=
    isNoetherian_of_injective (IsScalarTower.toAlgHom A C B).toLinearMap hψ
  exact Module.IsNoetherian.finite A C

/-- A finitely generated algebra `A` over a perfect ring `k` of exponential characteristic `p` is
a finite module over itself via the iterated Frobenius `a ↦ a ^ p ^ n`. -/
theorem finite_iterateFrobenius (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (p n : ℕ) [ExpChar k p] [PerfectRing k p] [ExpChar A p] :
    (iterateFrobenius A p n).Finite := by
  apply RingHom.IsIntegral.to_finite
  · intro x
    refine ⟨X ^ (p ^ n) - C x, monic_X_pow_sub_C _ (expChar_pow_pos A p n).ne', ?_⟩
    simp [iterateFrobenius_def]
  · have h : algebraMap k A = (iterateFrobenius A p n).comp
        ((algebraMap k A).comp (iterateFrobeniusEquiv k p n).symm.toRingHom) := by
      ext c
      have hc := (iterateFrobeniusEquiv k p n).apply_symm_apply c
      rw [iterateFrobeniusEquiv_def] at hc
      simp only [RingHom.comp_apply, iterateFrobenius_def, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe, ← map_pow, hc]
    have hft : (algebraMap k A).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance
    rw [h] at hft
    exact RingHom.FiniteType.of_comp_finiteType hft

/-- **Finiteness of normalization, normal base.** Let `k` be a perfect field and `A` a finitely
generated `k`-algebra which is an integrally closed domain, with fraction field `K`. Then the
integral closure `C` of `A` in a finite extension `L` of `K` is a finite `A`-module. No
separability of `L / K` is assumed. -/
theorem finite_of_isIntegralClosure_of_isIntegrallyClosed (k A K L C : Type*) [Field k]
    [PerfectField k] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] [CommRing C] [Algebra C L]
    [Algebra A C] [IsScalarTower A C L] [IsIntegralClosure C A L] :
    Module.Finite A C := by
  obtain ⟨p, hp⟩ := ExpChar.exists k
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : ExpChar A p := expChar_of_injective_algebraMap (algebraMap k A).injective p
  have : ExpChar K p := expChar_of_injective_algebraMap (IsFractionRing.injective A K) p
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  -- The separable closure `Kₛ` of `K` in `L`; `L / Kₛ` is purely inseparable of exponent `n`.
  let Ks := separableClosure K L
  have : IsScalarTower A Ks L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : ExpChar Ks p := expChar_of_injective_algebraMap (algebraMap K Ks).injective p
  set n := IsPurelyInseparable.exponent Ks L
  let ψ : L →+* Ks := IsPurelyInseparable.iterateFrobenius Ks L p le_rfl
  have hψ (x : L) : algebraMap Ks L (ψ x) = x ^ p ^ n :=
    IsPurelyInseparable.algebraMap_iterateFrobenius Ks p le_rfl x
  -- The separable case.
  have hCs : Module.Finite A (integralClosure A Ks) :=
    IsIntegralClosure.finite A K Ks (integralClosure A Ks)
  -- `x ↦ x ^ q` maps `C` injectively into the integral closure of `A` in `Kₛ`.
  have hint (c : C) : ψ (algebraMap C L c) ∈ integralClosure A Ks := by
    rw [mem_integralClosure_iff, ← isIntegral_algHom_iff (IsScalarTower.toAlgHom A Ks L)
      (algebraMap Ks L).injective, IsScalarTower.coe_toAlgHom', hψ]
    exact (IsIntegralClosure.isIntegral A L c).algebraMap.pow _
  let Ψ : C →+* integralClosure A Ks := (ψ.comp (algebraMap C L)).codRestrict _ hint
  have hΨ : Function.Injective Ψ := by
    intro x y hxy
    have := congrArg (fun z : integralClosure A Ks => (z : Ks)) hxy
    exact IsIntegralClosure.algebraMap_injective C A L (ψ.injective this)
  refine RingHom.finite_algebraMap.mp (finite_of_injective_comp
    (f := (algebraMap A (integralClosure A Ks)).comp (iterateFrobenius A p n))
    (RingHom.Finite.comp (RingHom.finite_algebraMap.mpr hCs) (finite_iterateFrobenius k A p n))
    Ψ hΨ ?_)
  ext a
  change algebraMap Ks L (ψ (algebraMap C L (algebraMap A C a))) =
    algebraMap Ks L (algebraMap A Ks (iterateFrobenius A p n a))
  rw [hψ, iterateFrobenius_def, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply, map_pow]

open scoped nonZeroDivisors in
/-- **Finiteness of normalization** (`thm:bj-normalization-finite`). Let `k` be a perfect field
and `D` a finitely generated `k`-algebra which is a domain, with fraction field `K`. Then the
integral closure `C` of `D` in a finite extension `L` of `K` is a finite `D`-module. -/
theorem finite_of_isIntegralClosure_of_finiteType (k D K L C : Type*) [Field k] [PerfectField k]
    [CommRing D] [IsDomain D] [Algebra k D] [Algebra.FiniteType k D] [Field K] [Algebra D K]
    [IsFractionRing D K] [Field L] [Algebra K L] [Algebra D L] [IsScalarTower D K L]
    [FiniteDimensional K L] [CommRing C] [Algebra C L] [Algebra D C] [IsScalarTower D C L]
    [IsIntegralClosure C D L] :
    Module.Finite D C := by
  -- Noether normalization: `D` is finite over a polynomial ring `A`.
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k D
  let A := MvPolynomial (Fin s) k
  let F := FractionRing A
  let _ : Algebra A D := g.toRingHom.toAlgebra
  have : Module.Finite A D := hfin
  have : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hg
  -- The tower `A ⊆ D ⊆ K ⊆ L` and `A ⊆ F = Frac A ⊆ K`.
  let _ : Algebra A K := ((algebraMap D K).comp (algebraMap A D)).toAlgebra
  have : IsScalarTower A D K := IsScalarTower.of_algebraMap_eq' rfl
  have : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr
    ((IsFractionRing.injective D K).comp hg)
  let _ : Algebra F K := FractionRing.liftAlgebra A K
  have : IsScalarTower A F K := FractionRing.isScalarTower_liftAlgebra A K
  have : FiniteDimensional F K := Module.Finite.of_isLocalization A D A⁰
  let _ : Algebra A L := ((algebraMap D L).comp (algebraMap A D)).toAlgebra
  have : IsScalarTower A D L := IsScalarTower.of_algebraMap_eq' rfl
  let _ : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  have : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A K L := IsScalarTower.to₁₃₄ A D K L
  have : IsScalarTower A F L := IsScalarTower.to₁₂₄ A F K L
  have : FiniteDimensional F L := Module.Finite.trans K L
  -- `C` is also the integral closure of `A` in `L`.
  let _ : Algebra A C := ((algebraMap D C).comp (algebraMap A D)).toAlgebra
  have : IsScalarTower A D C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A C L := IsScalarTower.to₁₃₄ A D C L
  have : Algebra.IsIntegral A D := Algebra.IsIntegral.of_finite A D
  have : IsIntegralClosure C A L := by
    refine ⟨IsIntegralClosure.algebraMap_injective C D L, fun {x} => ?_⟩
    rw [← IsIntegralClosure.isIntegral_iff (A := C) (R := D)]
    exact ⟨fun h => h.tower_top, fun h => isIntegral_trans x h⟩
  have : Module.Finite A C := finite_of_isIntegralClosure_of_isIntegrallyClosed k A F L C
  exact Module.Finite.of_restrictScalars_finite A D C

section integralClosure

variable (k D L : Type*) [Field k] [PerfectField k] [CommRing D] [IsDomain D] [Algebra k D]
  [Algebra.FiniteType k D] [Field L] [Algebra D L] [IsFractionRing D L]

include k

/-- The normalization of a finitely generated domain over a perfect field is a finite module.
Here `L` is any fraction field of `D`, e.g. `FractionRing D`. -/
theorem finite_integralClosure : Module.Finite D (integralClosure D L) :=
  finite_of_isIntegralClosure_of_finiteType k D L L (integralClosure D L)

/-- The normalization of a finitely generated domain over a perfect field is Noetherian. -/
theorem isNoetherianRing_integralClosure : IsNoetherianRing (integralClosure D L) :=
  have := finite_integralClosure k D L
  have := Algebra.FiniteType.isNoetherianRing k D
  Algebra.FiniteType.isNoetherianRing D (integralClosure D L)

/-- The normalization of a finitely generated domain over a perfect field is a finitely generated
algebra. -/
theorem finiteType_integralClosure [Algebra k L] [IsScalarTower k D L] :
    Algebra.FiniteType k (integralClosure D L) :=
  have := finite_integralClosure k D L
  Algebra.FiniteType.trans (S := D) inferInstance inferInstance

end integralClosure

/-- The normalization of a domain is integrally closed (no finiteness hypotheses needed). -/
theorem isIntegrallyClosed_integralClosure (D L : Type*) [CommRing D] [IsDomain D] [Field L]
    [Algebra D L] [IsFractionRing D L] : IsIntegrallyClosed (integralClosure D L) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension L

end EnvelopeProperty
