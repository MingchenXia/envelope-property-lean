/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.Spectrum

/-!
# Principal opens of general seminorm spectra

For an arbitrary commutative ring, localization away from `f` identifies its
real-valued seminorm spectrum with the open locus where `f` has nonzero value.
The inverse is the genuine extension of a valuation to the localization.

The construction also respects any prescribed real-valued seminorm on an arbitrary
commutative base ring, provided the algebra structure maps form a scalar tower.
Zero or nilpotent `f` are allowed; their nonvanishing loci are empty.
-/

open scoped NNReal ENNReal Topology
open Topology

noncomputable section

namespace EnvelopeProperty.Berkovich

namespace Spectrum

variable {A : Type*} [CommRing A]

theorem isOpen_setOf_val_ne_zero (f : A) : IsOpen {x : Spectrum A | x.val f ≠ 0} :=
  isOpen_compl_singleton.preimage (continuous_abs f)

namespace Away

variable (B : Type*) [CommRing B] [Algebra A B]

/-- Restriction along the structure map of an algebra. -/
def comap : Spectrum B → Spectrum A := Spectrum.comap (algebraMap A B)

@[simp]
theorem comap_val_apply (y : Spectrum B) (a : A) :
    (comap B y).val a = y.val (algebraMap A B a) := rfl

@[fun_prop]
theorem continuous_comap : Continuous (comap (A := A) B) := Spectrum.continuous_comap _

variable (f : A) [IsLocalization.Away f B]

/-- Every element in a principal localization has a fraction representation. -/
theorem exists_eq_mk' (b : B) :
    ∃ (a : A) (n : ℕ),
      b = IsLocalization.mk' B a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f) := by
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) b
  exact ⟨a, n, rfl⟩

theorem comap_val_ne_zero (y : Spectrum B) : (comap B y).val f ≠ 0 :=
  ((IsLocalization.Away.algebraMap_isUnit (S := B) f).map y.val).ne_zero

/-- Values on fractions are determined by restriction to the original ring. -/
theorem val_mk' (y : Spectrum B) (a : A) (n : ℕ) :
    y.val (IsLocalization.mk' B a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)) =
      (comap B y).val a / ((comap B y).val f) ^ n := by
  have hne := comap_val_ne_zero B f y
  rw [eq_div_iff (pow_ne_zero n hne)]
  have h := IsLocalization.mk'_spec B a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
  simp only [comap_val_apply] at hne ⊢
  rw [← h, map_mul, map_pow, map_pow]

theorem logAbs_mk' (y : Spectrum B) (a : A) (n : ℕ) :
    logAbs (IsLocalization.mk' B a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)) y =
      logAbs a (comap B y) - n * logAbs f (comap B y) := by
  have hne := comap_val_ne_zero B f y
  simp only [logAbs, val_mk' B f y a n]
  rw [ENNReal.coe_div (pow_ne_zero n hne), div_eq_mul_inv, ENNReal.log_mul_add,
    ENNReal.log_inv, ENNReal.coe_pow, ENNReal.log_pow, sub_eq_add_neg]

theorem val_invSelf (y : Spectrum B) :
    y.val (IsLocalization.Away.invSelf f) = ((comap B y).val f)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [comap_val_apply, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]

theorem logAbs_invSelf (y : Spectrum B) :
    logAbs (IsLocalization.Away.invSelf f) y = -logAbs f (comap B y) := by
  simp only [logAbs, val_invSelf B f y]
  rw [ENNReal.coe_inv (comap_val_ne_zero B f y), ENNReal.log_inv]

include f in
theorem comap_injective : Function.Injective (comap (A := A) B) := by
  intro y₁ y₂ h
  refine Spectrum.ext_val fun b => ?_
  obtain ⟨a, n, rfl⟩ := exists_eq_mk' B f b
  rw [val_mk' B f y₁, val_mk' B f y₂, h]

theorem powers_le_primeCompl (x : Spectrum A) (hx : x.val f ≠ 0) :
    Submonoid.powers f ≤ x.val.supp.primeCompl := by
  rintro _ ⟨n, rfl⟩
  rw [Ideal.mem_primeCompl_iff, Valuation.mem_supp_iff, map_pow]
  exact pow_ne_zero n hx

/-- The valuation extension to a principal localization on its nonvanishing locus. -/
def lift (x : Spectrum A) (hx : x.val f ≠ 0) : Spectrum B :=
  ⟨x.val.extendToLocalization (powers_le_primeCompl f x hx) B⟩

@[simp]
theorem lift_val_algebraMap (x : Spectrum A) (hx : x.val f ≠ 0) (a : A) :
    (lift B f x hx).val (algebraMap A B a) = x.val a :=
  x.val.extendToLocalization_apply_map_apply (powers_le_primeCompl f x hx) B a

@[simp]
theorem comap_lift (x : Spectrum A) (hx : x.val f ≠ 0) : comap B (lift B f x hx) = x :=
  Spectrum.ext_val fun a => lift_val_algebraMap B f x hx a

@[simp]
theorem lift_comap (y : Spectrum B) : lift B f (comap B y) (comap_val_ne_zero B f y) = y :=
  comap_injective B f (comap_lift B f _ _)

theorem lift_val_mk' (x : Spectrum A) (hx : x.val f ≠ 0) (a : A) (n : ℕ) :
    (lift B f x hx).val (IsLocalization.mk' B a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)) =
      x.val a / x.val f ^ n := by
  rw [val_mk', comap_lift]

theorem lift_val_invSelf (x : Spectrum A) (hx : x.val f ≠ 0) :
    (lift B f x hx).val (IsLocalization.Away.invSelf f) = (x.val f)⁻¹ := by
  rw [val_invSelf, comap_lift]

theorem range_comap : Set.range (comap (A := A) B) = {x | x.val f ≠ 0} := by
  ext x
  refine ⟨?_, fun hx => ⟨lift B f x hx, comap_lift B f x hx⟩⟩
  rintro ⟨y, rfl⟩
  exact comap_val_ne_zero B f y

@[fun_prop]
theorem continuous_lift :
    Continuous fun x : {x : Spectrum A // x.val f ≠ 0} => lift B f x.1 x.2 := by
  rw [Spectrum.continuous_iff]
  intro b
  obtain ⟨a, n, rfl⟩ := exists_eq_mk' B f b
  simp only [lift_val_mk']
  exact ((continuous_abs a).comp continuous_subtype_val).div₀
    (((continuous_abs f).comp continuous_subtype_val).pow n) fun x => pow_ne_zero n x.2

/-- Principal localization is homeomorphic to its nonvanishing open subset. -/
def homeomorph : Spectrum B ≃ₜ {x : Spectrum A // x.val f ≠ 0} where
  toFun y := ⟨comap B y, comap_val_ne_zero B f y⟩
  invFun x := lift B f x.1 x.2
  left_inv := lift_comap B f
  right_inv x := Subtype.ext (comap_lift B f x.1 x.2)
  continuous_toFun := (continuous_comap B).subtype_mk _
  continuous_invFun := continuous_lift B f

@[simp]
theorem homeomorph_apply_coe (y : Spectrum B) :
    (homeomorph B f y : Spectrum A) = comap B y := rfl

include f in
theorem isOpenEmbedding_comap : IsOpenEmbedding (comap (A := A) B) := by
  refine ⟨IsEmbedding.subtypeVal.comp (homeomorph B f).isEmbedding, ?_⟩
  rw [range_comap B f]
  exact isOpen_setOf_val_ne_zero f

end Away

variable (f : A)

def awayComap : Spectrum (Localization.Away f) → Spectrum A :=
  Away.comap (Localization.Away f)

def awayLift (x : Spectrum A) (hx : x.val f ≠ 0) : Spectrum (Localization.Away f) :=
  Away.lift (Localization.Away f) f x hx

def awayHomeomorph : Spectrum (Localization.Away f) ≃ₜ {x : Spectrum A // x.val f ≠ 0} :=
  Away.homeomorph (Localization.Away f) f

@[simp]
theorem awayComap_val_apply (y : Spectrum (Localization.Away f)) (a : A) :
    (awayComap f y).val a = y.val (algebraMap A (Localization.Away f) a) := rfl

@[simp]
theorem awayLift_val_algebraMap (x : Spectrum A) (hx : x.val f ≠ 0) (a : A) :
    (awayLift f x hx).val (algebraMap A (Localization.Away f) a) = x.val a :=
  Away.lift_val_algebraMap _ f x hx a

theorem range_awayComap : Set.range (awayComap f) = {x | x.val f ≠ 0} :=
  Away.range_comap _ f

theorem isOpenEmbedding_awayComap : IsOpenEmbedding (awayComap f) :=
  Away.isOpenEmbedding_comap _ f

end Spectrum

namespace RelativeSpectrum

variable {R : Type*} [CommRing R] (v : Valuation R ℝ≥0)
variable {A : Type*} [CommRing A] [Algebra R A]

theorem isOpen_setOf_val_ne_zero (f : A) :
    IsOpen {x : RelativeSpectrum v A | x.1.val f ≠ 0} :=
  (Spectrum.isOpen_setOf_val_ne_zero f).preimage continuous_subtype_val

namespace Away

variable (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Restriction along a structure map compatible with the prescribed base seminorm. -/
def comap : RelativeSpectrum v B → RelativeSpectrum v A :=
  RelativeSpectrum.comap (IsScalarTower.toAlgHom R A B)

@[simp]
theorem comap_val_apply (y : RelativeSpectrum v B) (a : A) :
    (comap v B y).1.val a = y.1.val (algebraMap A B a) := rfl

@[fun_prop]
theorem continuous_comap : Continuous (comap (A := A) v B) :=
  RelativeSpectrum.continuous_comap _

variable (f : A) [IsLocalization.Away f B]

theorem comap_val_ne_zero (y : RelativeSpectrum v B) : (comap v B y).1.val f ≠ 0 :=
  Spectrum.Away.comap_val_ne_zero B f y.1

theorem val_mk' (y : RelativeSpectrum v B) (a : A) (n : ℕ) :
    y.1.val (IsLocalization.mk' B a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)) =
      (comap v B y).1.val a / ((comap v B y).1.val f) ^ n :=
  Spectrum.Away.val_mk' B f y.1 a n

theorem val_invSelf (y : RelativeSpectrum v B) :
    y.1.val (IsLocalization.Away.invSelf f) = ((comap v B y).1.val f)⁻¹ :=
  Spectrum.Away.val_invSelf B f y.1

include f in
theorem comap_injective : Function.Injective (comap (A := A) v B) := by
  intro y₁ y₂ h
  exact Subtype.ext (Spectrum.Away.comap_injective B f (congrArg Subtype.val h))

/-- The absolute valuation extension retains the prescribed values on the base ring. -/
def lift (x : RelativeSpectrum v A) (hx : x.1.val f ≠ 0) : RelativeSpectrum v B :=
  ⟨Spectrum.Away.lift B f x.1 hx, fun r => by
    rw [IsScalarTower.algebraMap_apply R A B, Spectrum.Away.lift_val_algebraMap]
    exact x.2 r⟩

@[simp]
theorem lift_val_algebraMap (x : RelativeSpectrum v A) (hx : x.1.val f ≠ 0) (a : A) :
    (lift v B f x hx).1.val (algebraMap A B a) = x.1.val a :=
  Spectrum.Away.lift_val_algebraMap B f x.1 hx a

@[simp]
theorem comap_lift (x : RelativeSpectrum v A) (hx : x.1.val f ≠ 0) :
    comap v B (lift v B f x hx) = x :=
  RelativeSpectrum.ext_val fun a => lift_val_algebraMap v B f x hx a

@[simp]
theorem lift_comap (y : RelativeSpectrum v B) :
    lift v B f (comap v B y) (comap_val_ne_zero v B f y) = y :=
  comap_injective v B f (comap_lift v B f _ _)

theorem lift_val_mk' (x : RelativeSpectrum v A) (hx : x.1.val f ≠ 0) (a : A) (n : ℕ) :
    (lift v B f x hx).1.val
        (IsLocalization.mk' B a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)) =
      x.1.val a / x.1.val f ^ n :=
  Spectrum.Away.lift_val_mk' B f x.1 hx a n

theorem lift_val_invSelf (x : RelativeSpectrum v A) (hx : x.1.val f ≠ 0) :
    (lift v B f x hx).1.val (IsLocalization.Away.invSelf f) = (x.1.val f)⁻¹ :=
  Spectrum.Away.lift_val_invSelf B f x.1 hx

theorem range_comap : Set.range (comap (A := A) v B) = {x | x.1.val f ≠ 0} := by
  ext x
  refine ⟨?_, fun hx => ⟨lift v B f x hx, comap_lift v B f x hx⟩⟩
  rintro ⟨y, rfl⟩
  exact comap_val_ne_zero v B f y

@[fun_prop]
theorem continuous_lift :
    Continuous fun x : {x : RelativeSpectrum v A // x.1.val f ≠ 0} =>
      lift v B f x.1 x.2 := by
  rw [RelativeSpectrum.continuous_iff]
  intro b
  obtain ⟨a, n, rfl⟩ := Spectrum.Away.exists_eq_mk' B f b
  simp only [RelativeSpectrum.val_apply, lift_val_mk']
  exact ((RelativeSpectrum.continuous_val_apply a).comp continuous_subtype_val).div₀
    (((RelativeSpectrum.continuous_val_apply f).comp continuous_subtype_val).pow n)
      fun x => pow_ne_zero n x.2

/-- Relative principal localization identifies with the nonvanishing relative locus. -/
def homeomorph : RelativeSpectrum v B ≃ₜ {x : RelativeSpectrum v A // x.1.val f ≠ 0} where
  toFun y := ⟨comap v B y, comap_val_ne_zero v B f y⟩
  invFun x := lift v B f x.1 x.2
  left_inv := lift_comap v B f
  right_inv x := Subtype.ext (comap_lift v B f x.1 x.2)
  continuous_toFun := (continuous_comap v B).subtype_mk _
  continuous_invFun := continuous_lift v B f

@[simp]
theorem homeomorph_apply_coe (y : RelativeSpectrum v B) :
    (homeomorph v B f y : RelativeSpectrum v A) = comap v B y := rfl

include f in
theorem isOpenEmbedding_comap : IsOpenEmbedding (comap (A := A) v B) := by
  refine ⟨IsEmbedding.subtypeVal.comp (homeomorph v B f).isEmbedding, ?_⟩
  rw [range_comap v B f]
  exact isOpen_setOf_val_ne_zero v f

end Away

variable (f : A)

def awayComap : RelativeSpectrum v (Localization.Away f) → RelativeSpectrum v A :=
  Away.comap v (Localization.Away f)

def awayLift (x : RelativeSpectrum v A) (hx : x.1.val f ≠ 0) :
    RelativeSpectrum v (Localization.Away f) :=
  Away.lift v (Localization.Away f) f x hx

def awayHomeomorph :
    RelativeSpectrum v (Localization.Away f) ≃ₜ {x : RelativeSpectrum v A // x.1.val f ≠ 0} :=
  Away.homeomorph v (Localization.Away f) f

@[simp]
theorem awayComap_val_apply (y : RelativeSpectrum v (Localization.Away f)) (a : A) :
    (awayComap v f y).1.val a = y.1.val (algebraMap A (Localization.Away f) a) := rfl

@[simp]
theorem awayLift_val_algebraMap (x : RelativeSpectrum v A) (hx : x.1.val f ≠ 0) (a : A) :
    (awayLift v f x hx).1.val (algebraMap A (Localization.Away f) a) = x.1.val a :=
  Away.lift_val_algebraMap v _ f x hx a

theorem range_awayComap : Set.range (awayComap v f) = {x | x.1.val f ≠ 0} :=
  Away.range_comap v _ f

theorem isOpenEmbedding_awayComap : IsOpenEmbedding (awayComap v f) :=
  Away.isOpenEmbedding_comap v _ f

end RelativeSpectrum

end EnvelopeProperty.Berkovich
