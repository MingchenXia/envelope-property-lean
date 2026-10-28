import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Finiteness.Basic
import EnvelopeProperty.Algebra.NonflatCharpoly

/-!
# Constructing the actual common principal open of a finite birational algebra

A finite algebra embedded in the fraction field of its base has one common
nonzero denominator. Clearing it constructs a genuine localization isomorphism.
The common open is a conclusion of the finite birational data.
-/

open scoped Classical
noncomputable section

namespace EnvelopeProperty.FcFiniteBirationalOpen

variable {C A K : Type*} [CommRing C] [IsDomain C] [CommRing A] [Field K]
variable [Algebra C A] [Algebra C K] [IsFractionRing C K] [Module.Finite C A]

/-- A finite actual subalgebra of the fraction field has one nonzero common
denominator for every one of its elements, constructed from finite generators. -/
theorem exists_common_denominator (ρ : A →ₐ[C] K) (hiρ : Function.Injective ρ) :
    ∃ g : C, g ≠ 0 ∧ ∀ a : A, ∃ c : C,
      algebraMap C A c = algebraMap C A g * a := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := C) (M := A)
  obtain ⟨g, hg⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors C) (fun i : Fin n => ρ (s i))
  have hall (a : A) : IsLocalization.IsInteger C ((g : C) • ρ a) := by
    have ha : a ∈ Submodule.span C (Set.range s) := by rw [hs]; trivial
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      exact hg i
    | zero =>
      rw [map_zero, smul_zero]
      exact IsLocalization.isInteger_zero
    | add a b ha hb iha ihb =>
      rw [map_add, smul_add]
      exact IsLocalization.isInteger_add iha ihb
    | smul c a ha ih =>
      rw [map_smul, smul_comm (g : C) c]
      exact IsLocalization.isInteger_smul ih
  refine ⟨g, nonZeroDivisors.ne_zero g.2, ?_⟩
  intro a
  obtain ⟨c, hc⟩ := hall a
  refine ⟨c, hiρ ?_⟩
  simpa only [ρ.commutes, map_mul, Algebra.smul_def] using hc

/-- The genuine common principal open is constructed from the finite algebra's
actual embedding in the fraction field, rather than supplied as an isomorphism. -/
theorem exists_commonPrincipalOpen_equiv (ρ : A →ₐ[C] K) (hiρ : Function.Injective ρ) :
    ∃ g : C, g ≠ 0 ∧
      ∃ e : Localization.Away g ≃ₐ[C] Localization.Away (algebraMap C A g),
        ∀ c : C, e (algebraMap C (Localization.Away g) c) =
          algebraMap A (Localization.Away (algebraMap C A g)) (algebraMap C A c) := by
  obtain ⟨g, hg, hden⟩ := exists_common_denominator ρ hiρ
  let δ : C →ₐ[C] A := { algebraMap C A with commutes' := fun c => by simp }
  let loc := IsLocalization.Away.mapₐ (Localization.Away g)
    (Localization.Away (algebraMap C A g)) δ g
  have hiδ : Function.Injective δ := by
    intro c d he
    apply IsFractionRing.injective C K
    change algebraMap C A c = algebraMap C A d at he
    simpa only [ρ.commutes] using congrArg ρ he
  have hiloc : Function.Injective loc := IsLocalization.Away.mapₐ_injective_of_injective
    (Aₚ := Localization.Away g) (Bₚ := Localization.Away (algebraMap C A g)) g hiδ
  have hsloc : Function.Surjective loc := by
    change Function.Surjective (IsLocalization.Away.map (Localization.Away g)
      (Localization.Away (algebraMap C A g)) (algebraMap C A) g)
    apply (IsLocalization.Away.map_surjective_iff (Localization.Away g)
      (Localization.Away (algebraMap C A g)) (algebraMap C A) g).mpr
    intro a
    obtain ⟨c, hc⟩ := hden a
    exact ⟨c, 1, by simpa only [pow_one] using hc⟩
  let e := AlgEquiv.ofBijective loc ⟨hiloc, hsloc⟩
  refine ⟨g, hg, e, ?_⟩
  intro c
  change IsLocalization.Away.mapₐ (Localization.Away g)
    (Localization.Away (algebraMap C A g)) δ g (algebraMap C (Localization.Away g) c) = _
  simp only [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq]
  rfl

/-- The constructed common open preserves an existing coefficient-field
structure and the entire original subalgebra map, as required by curve closures. -/
theorem exists_commonPrincipalOpen_equiv_over_field
    {F : Type*} [Field F] [Algebra F C] [Algebra F A] [IsScalarTower F C A]
    (ρ : A →ₐ[C] K) (hiρ : Function.Injective ρ) :
    ∃ g : C, g ≠ 0 ∧
      ∃ e : Localization.Away g ≃ₐ[F] Localization.Away (algebraMap C A g),
        ∀ c : C, e (algebraMap C (Localization.Away g) c) =
          algebraMap A (Localization.Away (algebraMap C A g)) (algebraMap C A c) := by
  obtain ⟨g, hg, e, he⟩ := exists_commonPrincipalOpen_equiv ρ hiρ
  exact ⟨g, hg, e.restrictScalars F, he⟩

/-- The common open can be controlled by a nonzero element of the original
normal finite base: its image is divisible by the constructed conductor. This
makes the common open contain every rational fibre over that base principal open. -/
theorem exists_commonPrincipalOpen_with_base_denominator
    {F R : Type*} [Field F] [Algebra F C] [Algebra F A] [IsScalarTower F C A]
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra R C]
    [FaithfulSMul R C] [Module.Finite R C]
    (ρ : A →ₐ[C] K) (hiρ : Function.Injective ρ) :
    ∃ (h : C) (g : R), h ≠ 0 ∧ g ≠ 0 ∧ h ∣ algebraMap R C g ∧
      ∃ e : Localization.Away h ≃ₐ[F] Localization.Away (algebraMap C A h),
        ∀ c : C, e (algebraMap C (Localization.Away h) c) =
          algebraMap A (Localization.Away (algebraMap C A h)) (algebraMap C A c) := by
  obtain ⟨h, hh, e, he⟩ := exists_commonPrincipalOpen_equiv_over_field (F := F) ρ hiρ
  exact ⟨h, (nonflatCharpoly R C h).coeff 0, hh, coeff_zero_nonflatCharpoly_ne_zero hh,
    dvd_algebraMap_coeff_zero_nonflatCharpoly h, e, he⟩

end EnvelopeProperty.FcFiniteBirationalOpen
