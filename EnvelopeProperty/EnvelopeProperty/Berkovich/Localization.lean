/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.Basic
import EnvelopeProperty.Berkovich.SpectrumBridge
import EnvelopeProperty.Berkovich.SpectrumLocalization

/-!
# Analytification of a principal open subset

Let `A` be a commutative `k`-algebra, `Y = Spec A`, and `f ∈ A`. The principal open subset
`Y_f = Spec A_f` has analytification
`(Y_f)^an = {x ∈ Y^an : |f|_x ≠ 0} = {log |f| > -∞}`,
an open subset of `Y^an`. This is the identification `P_s^an ⊆ P^an` used throughout
Section 5 of Fang–Han–Xia (`sec:normal-local-regularization`; see the discussion around
`eq:reference-potential`, where functions such as `σ_j / s` are evaluated on `P_s^an`).

We prove that the map `(Y_f)^an → Y^an` induced by `A → A_f` is an open embedding with
image `{x | |f|_x ≠ 0}`, and record the value formula
`|a / f ^ n|_y = |a|_x / |f|_x ^ n`, i.e. `log |a / f ^ n| = log |a| - n log |f|`.

Everything is first proved for an arbitrary `k`-algebra `B` which is a localization of `A` away
from `f` (namespace `EnvelopeProperty.Berk.Away`, with `B` an explicit argument), and then
specialized to `Localization.Away f` under the names `awayComap`, `awayLift`, ….

## Main definitions

* `EnvelopeProperty.Berk.Away.comap B`: the map `Berk k B → Berk k A` induced by `A → B`.
* `EnvelopeProperty.Berk.Away.lift B f x hx`: for `|f|_x ≠ 0`, the unique point of `Berk k B`
  over `x`, given by `Valuation.extendToLocalization`.
* `EnvelopeProperty.Berk.awayComap f`, `EnvelopeProperty.Berk.awayLift f x hx`: the same for
  `B = Localization.Away f`.

## Main results

* `EnvelopeProperty.Berk.Away.isOpenEmbedding_comap`: `(Y_f)^an → Y^an` is an open embedding.
* `EnvelopeProperty.Berk.Away.range_comap`: its image is `{x | |f|_x ≠ 0}`.
* `EnvelopeProperty.Berk.Away.val_mk'`, `EnvelopeProperty.Berk.Away.logAbs_mk'`: value formulas.
* `EnvelopeProperty.Berk.Away.comap_triv`: the trivial valuation maps to the trivial valuation.
* `EnvelopeProperty.Berk.Away.adjoin_eq_top`: generators of `A` together with `1 / f`
  generate `A_f`.
-/

open scoped NNReal ENNReal Topology

open Topology

noncomputable section

namespace EnvelopeProperty

namespace Berk

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- The locus `{x | |f|_x ≠ 0} = {log |f| > -∞}` is open in the analytification. -/
theorem isOpen_setOf_val_ne_zero (f : A) : IsOpen {x : Berk k A | x.val f ≠ 0} :=
  isOpen_compl_singleton.preimage (continuous_abs f)

namespace Away

/-! ### General localizations away from `f` -/

section general

variable (B : Type*) [CommRing B] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- The map `Berk k B → Berk k A` induced by the structure map `A → B`. When `B` is a
localization of `A` away from `f`, this is the inclusion `(Y_f)^an → Y^an`. -/
def comap : Berk k B → Berk k A :=
  Berk.comap (IsScalarTower.toAlgHom k A B)

@[simp]
theorem comap_val_apply (y : Berk k B) (a : A) :
    (comap B y).val a = y.val (algebraMap A B a) := rfl

@[fun_prop]
theorem continuous_comap : Continuous (comap (k := k) (A := A) B) :=
  Berk.continuous_comap _

theorem logAbs_algebraMap (y : Berk k B) (a : A) :
    logAbs (algebraMap A B a) y = logAbs a (comap B y) := rfl

variable (f : A) [IsLocalization.Away f B]

/-- Every element of a localization away from `f` has the form `a / f ^ n`. -/
theorem exists_eq_mk' (b : B) :
    ∃ (a : A) (n : ℕ),
      b = IsLocalization.mk' B a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f) := by
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) b
  exact ⟨a, n, rfl⟩

/-- `a / f ^ n = a · (1 / f) ^ n` in a localization away from `f`. -/
theorem mk'_eq_algebraMap_mul_invSelf_pow (a : A) (n : ℕ) :
    IsLocalization.mk' B a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f) =
      algebraMap A B a * IsLocalization.Away.invSelf f ^ n := by
  symm
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  calc algebraMap A B a * IsLocalization.Away.invSelf f ^ n * algebraMap A B (f ^ n)
      = algebraMap A B a * (algebraMap A B f * IsLocalization.Away.invSelf f) ^ n := by
        rw [map_pow]; ring
    _ = algebraMap A B a := by rw [IsLocalization.Away.mul_invSelf, one_pow, mul_one]

omit [Algebra k A] [IsScalarTower k A B] in
theorem val_algebraMap_ne_zero (y : Berk k B) : y.val (algebraMap A B f) ≠ 0 :=
  ((IsLocalization.Away.algebraMap_isUnit (S := B) f).map y.val).ne_zero

/-- Points of `(Y_f)^an` lie in `{|f| ≠ 0}`. -/
theorem comap_val_ne_zero (y : Berk k B) : (comap B y).val f ≠ 0 :=
  val_algebraMap_ne_zero B f y

theorem logAbs_comap_ne_bot (y : Berk k B) : logAbs f (comap B y) ≠ ⊥ := by
  rw [Ne, logAbs_eq_bot_iff]
  exact comap_val_ne_zero B f y

/-- The value formula `|a / f ^ n|_y = |a|_x / |f|_x ^ n`, where `x` is the image of `y`. -/
theorem val_mk' (y : Berk k B) (a : A) (n : ℕ) :
    y.val (IsLocalization.mk' B a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)) =
      (comap B y).val a / ((comap B y).val f) ^ n := by
  have hne := comap_val_ne_zero B f y
  rw [eq_div_iff (pow_ne_zero n hne)]
  have h := IsLocalization.mk'_spec B a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
  simp only [comap_val_apply] at hne ⊢
  rw [← h, map_mul, map_pow, map_pow]

/-- The value formula `log |a / f ^ n| = log |a| - n log |f|`, where `log |f|` is finite. -/
theorem logAbs_mk' (y : Berk k B) (a : A) (n : ℕ) :
    logAbs (IsLocalization.mk' B a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)) y =
      logAbs a (comap B y) - n * logAbs f (comap B y) := by
  have hne := comap_val_ne_zero B f y
  simp only [logAbs, val_mk' B f y a n]
  rw [ENNReal.coe_div (pow_ne_zero n hne), div_eq_mul_inv, ENNReal.log_mul_add, ENNReal.log_inv,
    ENNReal.coe_pow, ENNReal.log_pow, sub_eq_add_neg]

theorem val_invSelf (y : Berk k B) :
    y.val (IsLocalization.Away.invSelf f) = ((comap B y).val f)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [comap_val_apply, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]

/-- `log |1 / f| = - log |f|`. -/
theorem logAbs_invSelf (y : Berk k B) :
    logAbs (IsLocalization.Away.invSelf f) y = -logAbs f (comap B y) := by
  simp only [logAbs, val_invSelf B f y]
  rw [ENNReal.coe_inv (comap_val_ne_zero B f y), ENNReal.log_inv]

include f in
/-- `(Y_f)^an → Y^an` is injective. -/
theorem comap_injective : Function.Injective (comap (k := k) (A := A) B) := by
  intro y₁ y₂ h
  refine Berk.ext (Valuation.ext fun b => ?_)
  obtain ⟨a, n, rfl⟩ := exists_eq_mk' B f b
  rw [val_mk' B f y₁, val_mk' B f y₂, h]

theorem powers_le_primeCompl (x : Berk k A) (hx : x.val f ≠ 0) :
    Submonoid.powers f ≤ x.val.supp.primeCompl := by
  rintro _ ⟨n, rfl⟩
  rw [Ideal.mem_primeCompl_iff, Valuation.mem_supp_iff, map_pow]
  exact pow_ne_zero n hx

/-- For `x ∈ Y^an` with `|f|_x ≠ 0`, the point of `(Y_f)^an` over `x`: the extension of the
valuation `|·|_x` to the localization. -/
def lift (x : Berk k A) (hx : x.val f ≠ 0) : Berk k B where
  val := x.val.extendToLocalization (powers_le_primeCompl f x hx) B
  val_algebraMap c hc := by
    rw [IsScalarTower.algebraMap_apply k A B, Valuation.extendToLocalization_apply_map_apply,
      x.val_algebraMap c hc]

@[simp]
theorem lift_val_algebraMap (x : Berk k A) (hx : x.val f ≠ 0) (a : A) :
    (lift B f x hx).val (algebraMap A B a) = x.val a :=
  x.val.extendToLocalization_apply_map_apply (powers_le_primeCompl f x hx) B a

@[simp]
theorem comap_lift (x : Berk k A) (hx : x.val f ≠ 0) : comap B (lift B f x hx) = x :=
  Berk.ext (Valuation.ext fun a => lift_val_algebraMap B f x hx a)

@[simp]
theorem lift_comap (y : Berk k B) : lift B f (comap B y) (comap_val_ne_zero B f y) = y :=
  comap_injective B f (comap_lift B f _ _)

theorem lift_val_mk' (x : Berk k A) (hx : x.val f ≠ 0) (a : A) (n : ℕ) :
    (lift B f x hx).val (IsLocalization.mk' B a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)) =
      x.val a / x.val f ^ n := by
  rw [val_mk', comap_lift]

/-- The image of `(Y_f)^an → Y^an` is `{x | |f|_x ≠ 0}`. -/
theorem range_comap : Set.range (comap (k := k) (A := A) B) = {x | x.val f ≠ 0} := by
  ext x
  refine ⟨?_, fun hx => ⟨lift B f x hx, comap_lift B f x hx⟩⟩
  rintro ⟨y, rfl⟩
  exact comap_val_ne_zero B f y

/-- The inverse `{x | |f|_x ≠ 0} → (Y_f)^an` is continuous: `|a / f ^ n| = |a| / |f| ^ n`. -/
theorem continuous_lift :
    Continuous fun x : {x : Berk k A // x.val f ≠ 0} => lift B f x.1 x.2 := by
  rw [continuous_iff]
  intro b
  obtain ⟨a, n, rfl⟩ := exists_eq_mk' B f b
  simp only [lift_val_mk']
  exact ((continuous_abs a).comp continuous_subtype_val).div₀
    (((continuous_abs f).comp continuous_subtype_val).pow n) fun x => pow_ne_zero n x.2

open Classical in
/-- The principal-open homeomorphism specializes the general relative-spectrum construction. -/
def homeomorph : Berk k B ≃ₜ {x : Berk k A // x.val f ≠ 0} :=
  ((relativeSpectrumHomeomorph (k := k) (A := B)).trans
    (Berkovich.RelativeSpectrum.Away.homeomorph (1 : Valuation k ℝ≥0) B f)).trans
      ((relativeSpectrumHomeomorph (k := k) (A := A)).symm.subtype fun _ => Iff.rfl)

@[simp]
theorem homeomorph_apply_coe (y : Berk k B) :
    (homeomorph B f y : Berk k A) = comap B y := rfl

@[simp]
theorem homeomorph_symm_apply (x : {x : Berk k A // x.val f ≠ 0}) :
    (homeomorph B f).symm x = lift B f x.1 x.2 := rfl

include f in
/-- The analytification of the principal open `Y_f` is an open embedding into `Y^an`. -/
theorem isOpenEmbedding_comap : IsOpenEmbedding (comap (k := k) (A := A) B) := by
  refine ⟨IsEmbedding.subtypeVal.comp (homeomorph B f).isEmbedding, ?_⟩
  rw [range_comap B f]
  exact isOpen_setOf_val_ne_zero f

include f in
/-- The trivial valuation of `A_f` restricts to the trivial valuation of `A`. -/
theorem comap_triv [IsDomain A] [IsDomain B] :
    comap B (triv : Berk k B) = (triv : Berk k A) := by
  have hf : f ≠ 0 := by
    rintro rfl
    have h := IsLocalization.Away.algebraMap_isUnit (S := B) (0 : A)
    rw [map_zero] at h
    exact not_isUnit_zero h
  have hinj : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  refine Berk.ext (Valuation.ext fun a => ?_)
  by_cases ha : a = 0
  · simp [ha]
  · rw [comap_val_apply, triv_val_of_ne_zero ha,
      triv_val_of_ne_zero ((map_ne_zero_iff _ hinj).2 ha)]

/-- If `S` generates `A` as a `k`-algebra, then `S` together with `1 / f` generates `A_f`. -/
theorem adjoin_eq_top {S : Set A} (hS : Algebra.adjoin k S = ⊤) :
    Algebra.adjoin k (insert (IsLocalization.Away.invSelf f) (algebraMap A B '' S)) = ⊤ := by
  rw [eq_top_iff]
  rintro b -
  obtain ⟨a, n, rfl⟩ := exists_eq_mk' B f b
  have h1 : algebraMap A B a ∈ Algebra.adjoin k (algebraMap A B '' S) := by
    have ha : a ∈ Algebra.adjoin k S := hS ▸ Algebra.mem_top
    have h := (Subalgebra.mem_map (f := IsScalarTower.toAlgHom k A B)).2 ⟨a, ha, rfl⟩
    rw [AlgHom.map_adjoin, IsScalarTower.coe_toAlgHom'] at h
    exact h
  rw [mk'_eq_algebraMap_mul_invSelf_pow]
  exact Subalgebra.mul_mem _ (Algebra.adjoin_mono (Set.subset_insert _ _) h1)
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) n)

/-- Finset version of `adjoin_eq_top`. -/
theorem adjoin_finset_eq_top [DecidableEq B] {S : Finset A}
    (hS : Algebra.adjoin k (S : Set A) = ⊤) :
    Algebra.adjoin k
      ((insert (IsLocalization.Away.invSelf f) (S.image (algebraMap A B)) : Finset B) : Set B) =
      ⊤ := by
  rw [Finset.coe_insert, Finset.coe_image]
  exact adjoin_eq_top B f hS

end general

end Away

/-! ### The localization `Localization.Away f` -/

section localizationAway

variable (f : A)

/-- The map `(Y_f)^an → Y^an` for `Y_f = Spec (Localization.Away f)`, induced by
`A → Localization.Away f`. -/
def awayComap : Berk k (Localization.Away f) → Berk k A :=
  Away.comap (Localization.Away f)

theorem awayComap_eq :
    awayComap (k := k) f = comap (IsScalarTower.toAlgHom k A (Localization.Away f)) := rfl

@[simp]
theorem awayComap_val_apply (y : Berk k (Localization.Away f)) (a : A) :
    (awayComap f y).val a = y.val (algebraMap A (Localization.Away f) a) := rfl

theorem awayComap_val_ne_zero (y : Berk k (Localization.Away f)) : (awayComap f y).val f ≠ 0 :=
  Away.comap_val_ne_zero _ f y

theorem logAbs_awayComap_ne_bot (y : Berk k (Localization.Away f)) :
    logAbs f (awayComap f y) ≠ ⊥ :=
  Away.logAbs_comap_ne_bot _ f y

@[fun_prop]
theorem continuous_awayComap : Continuous (awayComap (k := k) f) :=
  Away.continuous_comap _

theorem awayComap_injective : Function.Injective (awayComap (k := k) f) :=
  Away.comap_injective _ f

/-- For `|f|_x ≠ 0`, the point of `(Y_f)^an` over `x`. -/
def awayLift (x : Berk k A) (hx : x.val f ≠ 0) : Berk k (Localization.Away f) :=
  Away.lift (Localization.Away f) f x hx

/-- The canonical principal localization is homeomorphic to its nonvanishing open locus. -/
def awayHomeomorph : Berk k (Localization.Away f) ≃ₜ {x : Berk k A // x.val f ≠ 0} :=
  Away.homeomorph (Localization.Away f) f

@[simp]
theorem awayLift_val_algebraMap (x : Berk k A) (hx : x.val f ≠ 0) (a : A) :
    (awayLift f x hx).val (algebraMap A (Localization.Away f) a) = x.val a :=
  Away.lift_val_algebraMap _ f x hx a

@[simp]
theorem awayComap_awayLift (x : Berk k A) (hx : x.val f ≠ 0) :
    awayComap f (awayLift f x hx) = x :=
  Away.comap_lift _ f x hx

@[simp]
theorem awayLift_awayComap (y : Berk k (Localization.Away f)) :
    awayLift f (awayComap f y) (awayComap_val_ne_zero f y) = y :=
  Away.lift_comap _ f y

theorem range_awayComap : Set.range (awayComap (k := k) f) = {x | x.val f ≠ 0} :=
  Away.range_comap _ f

theorem continuous_awayLift :
    Continuous fun x : {x : Berk k A // x.val f ≠ 0} => awayLift f x.1 x.2 :=
  Away.continuous_lift _ f

/-- `(Y_f)^an → Y^an` is an open embedding with image `{x | |f|_x ≠ 0}`. -/
theorem isOpenEmbedding_awayComap : IsOpenEmbedding (awayComap (k := k) f) :=
  Away.isOpenEmbedding_comap _ f

/-- `|a / f ^ n|_y = |a|_x / |f|_x ^ n`. -/
theorem awayComap_val_mk' (y : Berk k (Localization.Away f)) (a : A) (n : ℕ) :
    y.val (IsLocalization.mk' (Localization.Away f) a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)) =
      (awayComap f y).val a / ((awayComap f y).val f) ^ n :=
  Away.val_mk' _ f y a n

theorem awayLift_val_mk' (x : Berk k A) (hx : x.val f ≠ 0) (a : A) (n : ℕ) :
    (awayLift f x hx).val
        (IsLocalization.mk' (Localization.Away f) a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)) =
      x.val a / x.val f ^ n :=
  Away.lift_val_mk' _ f x hx a n

/-- `log |a / f ^ n| = log |a| - n log |f|` on `(Y_f)^an`. -/
theorem logAbs_awayComap_mk' (y : Berk k (Localization.Away f)) (a : A) (n : ℕ) :
    logAbs
        (IsLocalization.mk' (Localization.Away f) a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)) y =
      logAbs a (awayComap f y) - n * logAbs f (awayComap f y) :=
  Away.logAbs_mk' _ f y a n

theorem logAbs_awayComap_algebraMap (y : Berk k (Localization.Away f)) (a : A) :
    logAbs (algebraMap A (Localization.Away f) a) y = logAbs a (awayComap f y) := rfl

theorem awayComap_val_invSelf (y : Berk k (Localization.Away f)) :
    y.val (IsLocalization.Away.invSelf f) = ((awayComap f y).val f)⁻¹ :=
  Away.val_invSelf _ f y

theorem logAbs_awayComap_invSelf (y : Berk k (Localization.Away f)) :
    logAbs (IsLocalization.Away.invSelf f : Localization.Away f) y =
      -logAbs f (awayComap f y) :=
  Away.logAbs_invSelf _ f y

/-- `Localization.Away f` is a domain when `A` is a domain and `f ≠ 0`. Not an instance since
it depends on `f ≠ 0`; use `haveI := isDomain_localizationAway hf`. -/
theorem isDomain_localizationAway [IsDomain A] {f : A} (hf : f ≠ 0) :
    IsDomain (Localization.Away f) :=
  IsLocalization.Away.isDomain _ hf

/-- The trivial valuation of `A_f` restricts to the trivial valuation of `A`. The instance
`IsDomain (Localization.Away f)` can be supplied by `isDomain_localizationAway`. -/
theorem awayComap_triv [IsDomain A] [IsDomain (Localization.Away f)] :
    awayComap f (triv : Berk k (Localization.Away f)) = (triv : Berk k A) :=
  Away.comap_triv _ f

/-- If `S` generates `A` as a `k`-algebra, then `S` and `1 / f` generate `Localization.Away f`. -/
theorem adjoin_awayInvSelf_eq_top {S : Set A} (hS : Algebra.adjoin k S = ⊤) :
    Algebra.adjoin k (insert (IsLocalization.Away.invSelf f)
      (algebraMap A (Localization.Away f) '' S)) = ⊤ :=
  Away.adjoin_eq_top _ f hS

end localizationAway

end Berk

end EnvelopeProperty
