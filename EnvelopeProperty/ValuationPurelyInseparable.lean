/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.RingHom.PurelyInseparable
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Group.Torsion


/-!
# Genuine valuation uniqueness under purely inseparable domain extensions

Actual inseparable power representations and positive-power injectivity in
an ordered value monoid determine every valuation from its restriction.
The source coefficient ring is a field, the target need only be a commutative
domain, and arbitrary linearly ordered commutative value monoids with zero
are allowed. No norm, completeness or characteristic-zero assumption is used.
-/

noncomputable section
namespace EnvelopeProperty.Valuation

/-- Genuine inseparable power representations determine every value of a valuation from its restriction. -/
theorem comap_injective_of_isPurelyInseparable
    {K L Γ : Type*} [Field K] [CommRing L] [IsDomain L] [LinearOrderedCommMonoidWithZero Γ]
    (φ : K →+* L) (hφ : φ.IsPurelyInseparable) :
    Function.Injective (fun ν : _root_.Valuation L Γ => ν.comap φ) := by
  let : Algebra K L := φ.toAlgebra
  let : IsPurelyInseparable K L := hφ
  obtain ⟨q, hq⟩ := ExpChar.exists K
  let : ExpChar K q := hq
  intro v w h
  apply _root_.Valuation.ext
  intro x
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem K q x
  apply pow_left_injective (pow_ne_zero n (expChar_ne_zero K q))
  change v x ^ (q ^ n) = w x ^ (q ^ n)
  rw [← map_pow, ← map_pow, ← ha]
  exact congrArg (fun ν : _root_.Valuation K Γ => ν a) h

end EnvelopeProperty.Valuation
