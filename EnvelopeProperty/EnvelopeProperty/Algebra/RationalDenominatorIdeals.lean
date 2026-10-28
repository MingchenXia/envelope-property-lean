import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Module.Equiv.Basic

/-! # Actual denominator ideals and reciprocal multiplication in the SAME fraction field -/
noncomputable section
universe u
namespace EnvelopeProperty.RationalDenominatorIdeals
open scoped nonZeroDivisors
variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]

/-- The ACTUAL original denominator ideal: original scalars whose product
with the SAME actual rational function is an ORIGINAL ring element. -/
def denominatorIdeal (f : K) : Ideal R where
  carrier := {a | ∃ b : R, algebraMap R K b = algebraMap R K a * f}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    exact ⟨a' + b', by rw [map_add, map_add, ha, hb, add_mul]⟩
  smul_mem' := by
    rintro r a ⟨b, hb⟩
    exact ⟨r * b, by simp only [smul_eq_mul, map_mul, hb, mul_assoc]⟩

/-- Membership is the genuine SAME-field clearing identity with an original numerator. -/
theorem mem_denominatorIdeal_iff (f : K) (a : R) :
    a ∈ denominatorIdeal R K f ↔ ∃ b : R, algebraMap R K b = algebraMap R K a * f := Iff.rfl

variable [IsDomain R] [IsFractionRing R K]

/-- Actual fraction-field surjectivity DERIVES a nonzero original denominator. -/
theorem denominatorIdeal_ne_bot (f : K) : denominatorIdeal R K f ≠ ⊥ := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors R) f
  have hmem : (s : R) ∈ denominatorIdeal R K f := ⟨a, by rw [← hs, mul_comm]⟩
  intro h
  have hz : (s : R) = 0 := by simpa only [h, Ideal.mem_bot] using hmem
  exact (mem_nonZeroDivisors_iff_ne_zero.mp s.property) hz

/-- The actual ORIGINAL cleared numerator of an actual original denominator. -/
def clearedNumerator (f : K) (a : denominatorIdeal R K f) : R := a.property.choose

omit [IsDomain R] [IsFractionRing R K] in
/-- The numerator satisfies the literal ORIGINAL fraction-field product equality. -/
theorem algebraMap_clearedNumerator (f : K) (a : denominatorIdeal R K f) :
    algebraMap R K (clearedNumerator R K f a) = algebraMap R K a * f := a.property.choose_spec

/-- Actual multiplication by the SAME rational function, as an original-ring linear map. -/
def clearedNumeratorLinearMap (f : K) : denominatorIdeal R K f →ₗ[R] R where
  toFun := clearedNumerator R K f
  map_add' a b := by
    apply IsFractionRing.injective R K
    simp only [algebraMap_clearedNumerator, Submodule.coe_add, map_add, add_mul]
  map_smul' r a := by
    apply IsFractionRing.injective R K
    simp only [algebraMap_clearedNumerator, Submodule.coe_smul, smul_eq_mul, map_mul, mul_assoc, RingHom.id_apply]

/-- The ACTUAL product by f is an original denominator for f⁻¹. -/
def reciprocalMap (f : K) (hf : f ≠ 0) :
    denominatorIdeal R K f →ₗ[R] denominatorIdeal R K f⁻¹ :=
  (clearedNumeratorLinearMap R K f).codRestrict _ fun a =>
    ⟨a, by
      change algebraMap R K a = algebraMap R K (clearedNumerator R K f a) * f⁻¹
      rw [algebraMap_clearedNumerator, mul_inv_cancel_right₀ hf]⟩

/-- Reciprocal denominator ideals are genuinely linearly isomorphic by
multiplication by the SAME ORIGINAL rational function. -/
def reciprocalEquiv (f : K) (hf : f ≠ 0) :
    denominatorIdeal R K f ≃ₗ[R] denominatorIdeal R K f⁻¹ := by
  refine LinearEquiv.ofBijective (reciprocalMap R K f hf) ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    apply IsFractionRing.injective R K
    apply mul_right_cancel₀ hf
    have h := congrArg (fun c : denominatorIdeal R K f⁻¹ => algebraMap R K c) hab
    change algebraMap R K (clearedNumerator R K f a) =
      algebraMap R K (clearedNumerator R K f b) at h
    simpa only [algebraMap_clearedNumerator] using h
  · intro b
    let a : R := clearedNumerator R K f⁻¹ b
    have ha : a ∈ denominatorIdeal R K f := by
      refine ⟨b, ?_⟩
      rw [show algebraMap R K a = algebraMap R K b * f⁻¹ from
        algebraMap_clearedNumerator R K f⁻¹ b, mul_assoc, inv_mul_cancel₀ hf, mul_one]
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    apply IsFractionRing.injective R K
    change algebraMap R K (clearedNumerator R K f ⟨a, ha⟩) = algebraMap R K b
    rw [algebraMap_clearedNumerator, show algebraMap R K a = algebraMap R K b * f⁻¹ from
      algebraMap_clearedNumerator R K f⁻¹ b, mul_assoc, inv_mul_cancel₀ hf, mul_one]

omit [IsDomain R] in
/-- The actual linear isomorphism is literal multiplication by f in the SAME field. -/
theorem reciprocalEquiv_coefficient (f : K) (hf : f ≠ 0) (a : denominatorIdeal R K f) :
    algebraMap R K (reciprocalEquiv R K f hf a) = algebraMap R K a * f :=
  algebraMap_clearedNumerator R K f a


omit [IsDomain R] [IsFractionRing R K] in
/-- Genuine localization of the original denominator ideal, in the SAME field.
Both denominators are cleared in the actual original localization; no
ideal-localization or rational-function comparison is supplied. -/
theorem denominatorIdeal_map (S : Type u) [CommRing S] [Algebra R S]
    [Algebra S K] [IsScalarTower R S K] (M : Submonoid R)
    [IsLocalization M S] (f : K) :
    (denominatorIdeal R K f).map (algebraMap R S) = denominatorIdeal S K f := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rintro a ⟨b, hb⟩
    refine ⟨algebraMap R S b, ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply R S K] using hb
  · intro s hs
    obtain ⟨b, hbf⟩ := hs
    obtain ⟨⟨a, t⟩, ht⟩ := IsLocalization.surj M s
    obtain ⟨⟨c, v⟩, hv⟩ := IsLocalization.surj M b
    have htK : algebraMap S K s * algebraMap R K t = algebraMap R K a := by
      simpa only [map_mul, ← IsScalarTower.algebraMap_apply R S K] using
        congrArg (algebraMap S K) ht
    have hvK : algebraMap S K b * algebraMap R K v = algebraMap R K c := by
      simpa only [map_mul, ← IsScalarTower.algebraMap_apply R S K] using
        congrArg (algebraMap S K) hv
    have hav : a * v.val ∈ denominatorIdeal R K f := by
      refine ⟨c * t.val, ?_⟩
      rw [map_mul, ← hvK, hbf]
      calc
        (algebraMap S K s * f * algebraMap R K v.val) * algebraMap R K t.val =
            (algebraMap S K s * algebraMap R K t.val) * algebraMap R K v.val * f := by ring
        _ = algebraMap R K a * algebraMap R K v.val * f := by rw [htK]
        _ = algebraMap R K (a * v.val) * f := by rw [map_mul]
    apply (IsLocalization.mem_map_algebraMap_iff M S).mpr
    refine ⟨(⟨a * v.val, hav⟩, t * v), ?_⟩
    change s * algebraMap R S (t.val * v.val) = algebraMap R S (a * v.val)
    rw [map_mul, ← mul_assoc, ht, map_mul]

end EnvelopeProperty.RationalDenominatorIdeals
