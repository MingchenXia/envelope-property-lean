import EnvelopeProperty.AlgGeom.CyclicSectionSNCNormalizationRounded
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # Actual multicomponent root rescaling on the entire integral closure

The actual original product coefficient determines the generic and raw quotient
maps. Native integral-closure transport then restricts the SAME ambient map;
no rounded-span formula or preservation certificate is assumed.
-/

noncomputable section
universe v w
namespace EnvelopeProperty.CyclicSectionSNCIntegralClosureRescaling
open CyclicSectionAlgebra CyclicSectionSNCNormalizationRounded
open scoped BigOperators
variable {R : Type v} [CommRing R]
variable {J : Type w} [Fintype J]

private theorem coefficient_eq (n : ℕ) (α : J → ℕ) (a b : R) (f : J → R)
    (v : Rˣ) (h : b = (v : R) ^ n * a) :
    b * ∏ j, f j ^ α j = (v : R) ^ n * (a * ∏ j, f j ^ α j) := by
  rw [h, mul_assoc]

private theorem fraction_coefficient_eq (n : ℕ) (α : J → ℕ) (a b : R) (f : J → R)
    (v : Rˣ) (h : b = (v : R) ^ n * a) :
    algebraMap R (FractionRing R) (b * ∏ j, f j ^ α j) =
      ((Units.map (algebraMap R (FractionRing R)).toMonoidHom v : (FractionRing R)ˣ) :
        FractionRing R) ^ n * algebraMap R (FractionRing R) (a * ∏ j, f j ^ α j) := by
  change algebraMap R (FractionRing R) (b * ∏ j, f j ^ α j) =
    (algebraMap R (FractionRing R) (v : R)) ^ n * _
  rw [coefficient_eq n α a b f v h, map_mul, map_pow]

variable (n : ℕ) (α : J → ℕ) (a b : R) (f : J → R)
variable (v : Rˣ) (h : b = (v : R) ^ n * a)
local notation "Qa" => GenericRootRing n α a f
local notation "Qb" => GenericRootRing n α b f

/-- The SAME original raw quotient rescaling uses the actual entire original
product coefficient equality, derived from the original frame relation. -/
def rawRescaleEquiv : RootRing n (b * ∏ j, f j ^ α j) ≃ₐ[R]
    RootRing n (a * ∏ j, f j ^ α j) :=
  rescaleEquiv n (a * ∏ j, f j ^ α j) (b * ∏ j, f j ^ α j) v
    (coefficient_eq n α a b f v h)

/-- The actual raw map sends the SAME original root in the v direction. -/
theorem rawRescaleEquiv_root :
    rawRescaleEquiv n α a b f v h (root n (b * ∏ j, f j ^ α j)) =
      algebraMap R (RootRing n (a * ∏ j, f j ^ α j)) (v : R) *
        root n (a * ∏ j, f j ^ α j) :=
  rescaleEquiv_root n _ _ v (coefficient_eq n α a b f v h)

/-- The actual entire original generic quotient map is the native SAME-root
rescaling over the original fraction ring, restricted to R. -/
def genericRescaleEquiv : Qb ≃ₐ[R] Qa :=
  (rescaleEquiv n (algebraMap R (FractionRing R) (a * ∏ j, f j ^ α j))
    (algebraMap R (FractionRing R) (b * ∏ j, f j ^ α j))
    (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)
    (fraction_coefficient_eq n α a b f v h)).restrictScalars R

/-- The actual original generic root has precisely its original v coefficient. -/
theorem genericRescaleEquiv_root :
    genericRescaleEquiv n α a b f v h
      (root n (algebraMap R (FractionRing R) (b * ∏ j, f j ^ α j))) =
      algebraMap R Qa (v : R) *
        root n (algebraMap R (FractionRing R) (a * ∏ j, f j ^ α j)) := by
  change rescaleEquiv n _ _
    (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)
    (fraction_coefficient_eq n α a b f v h) _ = _
  rw [rescaleEquiv_root]
  rfl

/-- The ENTIRE original fraction-ring coefficient square commutes. -/
theorem genericRescaleEquiv_fraction_coefficients :
    (genericRescaleEquiv n α a b f v h).toRingHom.comp
        (algebraMap (FractionRing R) Qb) = algebraMap (FractionRing R) Qa := by
  ext r
  exact (rescaleEquiv n _ _
    (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)
    (fraction_coefficient_eq n α a b f v h)).commutes r

/-- The ENTIRE actual original raw/generic quotient square is the existing
native coefficient-extension/rescaling square for the actual product coefficients. -/
theorem genericRescaleEquiv_comp_coefficientMap :
    (genericRescaleEquiv n α a b f v h).toAlgHom.comp
        (CyclicSectionBaseChange.coefficientMap n (b * ∏ j, f j ^ α j)
          (algebraMap R (FractionRing R) (b * ∏ j, f j ^ α j)) rfl) =
      (CyclicSectionBaseChange.coefficientMap n (a * ∏ j, f j ^ α j)
        (algebraMap R (FractionRing R) (a * ∏ j, f j ^ α j)) rfl).comp
        (rawRescaleEquiv n α a b f v h).toAlgHom :=
  (CyclicSectionBaseChange.coefficientMap_rescale n
    (a * ∏ j, f j ^ α j) (b * ∏ j, f j ^ α j)
    (algebraMap R (FractionRing R) (a * ∏ j, f j ^ α j))
    (algebraMap R (FractionRing R) (b * ∏ j, f j ^ α j)) v
    (coefficient_eq n α a b f v h) rfl rfl).symm

/-- Identity frame change fixes the ENTIRE original multicomponent quotient. -/
theorem genericRescaleEquiv_one (n : ℕ) (α : J → ℕ) (a : R) (f : J → R) :
    genericRescaleEquiv n α a a f 1 (by simp) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  simp only [genericRescaleEquiv, map_one, rescaleEquiv_one,
    AlgEquiv.restrictScalars_apply]
  rfl

/-- The ENTIRE actual generic quotient maps compose with the original ordered
frame-unit product, with the same entire branch presentation. -/
theorem genericRescaleEquiv_trans (n : ℕ) (α : J → ℕ) (a b c : R) (f : J → R)
    (v w : Rˣ) (hb : b = (v : R) ^ n * a) (hc : c = (w : R) ^ n * b) :
    (genericRescaleEquiv n α b c f w hc).trans (genericRescaleEquiv n α a b f v hb) =
      genericRescaleEquiv n α a c f (w * v)
        (by rw [hc, hb]; simp only [Units.val_mul, mul_pow, mul_assoc]) := by
  have ht := rescaleEquiv_trans n
    (algebraMap R (FractionRing R) (a * ∏ j, f j ^ α j))
    (algebraMap R (FractionRing R) (b * ∏ j, f j ^ α j))
    (algebraMap R (FractionRing R) (c * ∏ j, f j ^ α j))
    (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)
    (Units.map (algebraMap R (FractionRing R)).toMonoidHom w)
    (fraction_coefficient_eq n α a b f v hb) (fraction_coefficient_eq n α b c f w hc)
  apply AlgEquiv.ext
  intro x
  simpa only [genericRescaleEquiv, map_mul, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply] using DFunLike.congr_fun ht x

/-- Native integrality transport applies to EVERY actual original generic
element, with no rounded-membership or normality premise. -/
theorem genericRescaleEquiv_isIntegral_iff (x : Qb) :
    IsIntegral R (genericRescaleEquiv n α a b f v h x) ↔ IsIntegral R x :=
  isIntegral_algEquiv (genericRescaleEquiv n α a b f v h)

/-- The image of the ENTIRE actual original integral closure is the entire
actual target integral closure; native transport proves preservation internally. -/
theorem genericRescaleEquiv_map_integralClosure :
    (integralClosure R Qb).map (genericRescaleEquiv n α a b f v h).toAlgHom =
      integralClosure R Qa :=
  integralClosure_map_algEquiv (genericRescaleEquiv n α a b f v h)

/-- The actual SAME generic rescaling restricts to the WHOLE original integral
closures, using the native actual algebra-equivalence restriction. -/
def integralClosureEquiv : integralClosure R Qb ≃ₐ[R] integralClosure R Qa :=
  (genericRescaleEquiv n α a b f v h).mapIntegralClosure

/-- Every actual integral element retains its SAME ambient rescaling value. -/
theorem integralClosureEquiv_coe (x : integralClosure R Qb) :
    (integralClosureEquiv n α a b f v h x : Qa) =
      genericRescaleEquiv n α a b f v h (x : Qb) := rfl

/-- The WHOLE original integral-closure/generic inclusion square commutes. -/
theorem integralClosureEquiv_comp_val :
    (integralClosure R Qa).val.comp (integralClosureEquiv n α a b f v h).toAlgHom =
      (genericRescaleEquiv n α a b f v h).toAlgHom.comp (integralClosure R Qb).val := rfl

/-- Identity change fixes the ENTIRE actual original integral closure. -/
theorem integralClosureEquiv_one (n : ℕ) (α : J → ℕ) (a : R) (f : J → R) :
    integralClosureEquiv n α a a f 1 (by simp) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  change genericRescaleEquiv n α a a f 1 (by simp) (x : GenericRootRing n α a f) = x
  rw [genericRescaleEquiv_one]
  rfl

/-- The exact original frame cocycle holds on the WHOLE actual integral closure,
without assuming any rounded-algebra formula or preservation certificate. -/
theorem integralClosureEquiv_trans (n : ℕ) (α : J → ℕ) (a b c : R) (f : J → R)
    (v w : Rˣ) (hb : b = (v : R) ^ n * a) (hc : c = (w : R) ^ n * b) :
    (integralClosureEquiv n α b c f w hc).trans (integralClosureEquiv n α a b f v hb) =
      integralClosureEquiv n α a c f (w * v)
        (by rw [hc, hb]; simp only [Units.val_mul, mul_pow, mul_assoc]) := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  change genericRescaleEquiv n α a b f v hb
      (genericRescaleEquiv n α b c f w hc (x : GenericRootRing n α c f)) =
    genericRescaleEquiv n α a c f (w * v)
      (by rw [hc, hb]; simp only [Units.val_mul, mul_pow, mul_assoc]) x
  exact DFunLike.congr_fun (genericRescaleEquiv_trans n α a b c f v w hb hc) x.val

end EnvelopeProperty.CyclicSectionSNCIntegralClosureRescaling
