import EnvelopeProperty.DeligneIllusie.WittTwoRelativeDifferential
import EnvelopeProperty.DeligneIllusie.DividedCoordinateDifferential

/-!
# Witt Two Divided Lift

Actual coefficient-linear division of the entire original relative lift differential. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

namespace EnvelopeProperty.DeligneIllusie.WittTwoDividedLift

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoRelativeLift.residueCopyAlgebra WittTwoRelativeDifferential.liftAlgebra
  WittTwoSmoothDifferentials.differentials_flat

variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A]

private abbrev T := WittTwoRelativeLift.TwistAlgebra p k A
private abbrev B := WittTwoSmoothDifferentials.ResidueAlgebra p k A
private abbrev M := KaehlerDifferential (WittTwo.Ring p k) A

/-- The original prime-image differential module with its full original A-coefficients. -/
def primeForms : Submodule A (M p k A) :=
  LinearMap.range ((p : A) • (LinearMap.id : M p k A →ₗ[A] M p k A))

/-- Every original prime multiple belongs to this same original A-submodule. -/
def primeForm (w : M p k A) : primeForms p k A := ⟨(p : A) • w, ⟨w, rfl⟩⟩

private def toWittPrime (x : primeForms p k A) :
    WittTwoModuleDivision.primeSubmodule p k (M p k A) :=
  ⟨x.val, by
    obtain ⟨w, hw⟩ := x.property
    refine ⟨w, ?_⟩
    change (p : A) • w = x.val at hw
    change (p : WittTwo.Ring p k) • w = x.val
    simpa only [Nat.cast_smul_eq_nsmul] using hw⟩

private def divisionFunction (x : primeForms p k A) : KaehlerDifferential k (B p k A) :=
  WittTwoSmoothDifferentials.divideDifferentialEquiv p k A (toWittPrime p k A x)

private theorem divisionFunction_primeForm (w : M p k A) :
    divisionFunction p k A (primeForm p k A w) =
      KaehlerDifferential.map (WittTwo.Ring p k) k A (B p k A) w := by
  have h : toWittPrime p k A (primeForm p k A w) =
      WittTwoModuleDivision.primeMultiple p k _ w := by
    apply Subtype.ext
    change (p : A) • w = (p : WittTwo.Ring p k) • w
    simp only [Nat.cast_smul_eq_nsmul]
  rw [divisionFunction, h, WittTwoSmoothDifferentials.divideDifferentialEquiv_primeMultiple]

/-- Canonical original division is linear for ALL original A-coefficients. -/
def divisionLinear : primeForms p k A →ₗ[A] KaehlerDifferential k (B p k A) where
  toFun := divisionFunction p k A
  map_add' x y := (WittTwoSmoothDifferentials.divideDifferentialEquiv p k A).map_add
    (toWittPrime p k A x) (toWittPrime p k A y)
  map_smul' a x := by
    obtain ⟨w, hw⟩ := x.property
    have hx : x = primeForm p k A w := by
      apply Subtype.ext
      exact hw.symm
    rw [hx]
    have hs : a • primeForm p k A w = primeForm p k A (a • w) := by
      apply Subtype.ext
      change a • ((p : A) • w) = (p : A) • (a • w)
      exact smul_comm a (p : A) w
    rw [hs, divisionFunction_primeForm, divisionFunction_primeForm]
    exact (KaehlerDifferential.map (WittTwo.Ring p k) k A (B p k A)).map_smul a w

/-- The SAME original A-linear divided map has the original value on EVERY prime form. -/
theorem divisionLinear_primeForm (w : M p k A) :
    divisionLinear p k A (primeForm p k A w) =
      KaehlerDifferential.map (WittTwo.Ring p k) k A (B p k A) w :=
  divisionFunction_primeForm p k A w

/-- The original target coefficient action is the SAME actual reduced lifted ring map. -/
@[instance_reducible] def residueLiftAlgebra : Algebra (T p k A) (B p k A) :=
  ((algebraMap A (B p k A)).comp (WittTwoRelativeDifferential.liftRingMap p k A)).toAlgebra

attribute [local instance] residueLiftAlgebra

/-- The ENTIRE original lifted differential takes values in its actual prime-image submodule. -/
def liftPrimeFormsMap : KaehlerDifferential (ULift.{0} (WittTwo.Ring p k)) (T p k A) →ₗ[T p k A]
    (primeForms p k A).restrictScalars (T p k A) :=
  (WittTwoRelativeDifferential.liftDifferential p k A).codRestrict _ (by
    intro w
    obtain ⟨z, hz⟩ := WittTwoRelativeDifferential.liftDifferential_prime_image p k A w
    refine ⟨z, ?_⟩
    change (p : A) • z = WittTwoRelativeDifferential.liftDifferential p k A w
    simpa only [Nat.cast_smul_eq_nsmul] using hz.symm)

/-- The actual WHOLE original relative lift differential divided by the actual prime. -/
def dividedLiftDifferential : KaehlerDifferential (ULift.{0} (WittTwo.Ring p k)) (T p k A) →ₗ[T p k A]
    KaehlerDifferential k (B p k A) := by
  letI : IsScalarTower (T p k A) A (B p k A) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ((divisionLinear p k A).restrictScalars (T p k A)).comp (liftPrimeFormsMap p k A)

/-- Every actual original prime preimage has its true original reduction as divided value. -/
theorem dividedLiftDifferential_value
    (w : KaehlerDifferential (ULift.{0} (WittTwo.Ring p k)) (T p k A)) (z : M p k A)
    (h : WittTwoRelativeDifferential.liftDifferential p k A w = (p : WittTwo.Ring p k) • z) :
    dividedLiftDifferential p k A w =
      KaehlerDifferential.map (WittTwo.Ring p k) k A (B p k A) z := by
  have hp : liftPrimeFormsMap p k A w = primeForm p k A z := by
    apply Subtype.ext
    change WittTwoRelativeDifferential.liftDifferential p k A w = (p : A) • z
    simpa only [Nat.cast_smul_eq_nsmul] using h
  unfold dividedLiftDifferential
  rw [LinearMap.comp_apply, LinearMap.coe_restrictScalars]
  exact (congrArg (fun x : (primeForms p k A).restrictScalars (T p k A) =>
    divisionLinear p k A x) hp).trans (divisionLinear_primeForm p k A z)

/-- The original source prime-image submodule in the SAME actual source Kähler module. -/
def sourcePrimeForms : Submodule (T p k A)
    (KaehlerDifferential (ULift.{0} (WittTwo.Ring p k)) (T p k A)) :=
  LinearMap.range ((p : T p k A) • LinearMap.id)

/-- The SAME whole divided map kills EVERY original prime multiple in its source. -/
theorem dividedLiftDifferential_prime_zero
    (w : KaehlerDifferential (ULift.{0} (WittTwo.Ring p k)) (T p k A)) :
    dividedLiftDifferential p k A ((p : T p k A) • w) = 0 := by
  rw [map_smul]
  change (algebraMap (T p k A) (B p k A) p) • dividedLiftDifferential p k A w = 0
  rw [map_natCast]
  have hp : (p : B p k A) = 0 := by
    rw [← map_natCast (algebraMap k (B p k A)) p, CharP.cast_eq_zero, map_zero]
  rw [hp, zero_smul]

/-- The original whole divided map descends to the actual original source prime quotient. -/
def reductionDividedLift :
    ((KaehlerDifferential (ULift.{0} (WittTwo.Ring p k)) (T p k A)) ⧸ sourcePrimeForms p k A)
      →ₗ[T p k A] KaehlerDifferential k (B p k A) :=
  (sourcePrimeForms p k A).liftQ (dividedLiftDifferential p k A) (by
    rintro w ⟨z, rfl⟩
    exact dividedLiftDifferential_prime_zero p k A z)

/-- The SAME original quotient map retains every actual original divided value. -/
theorem reductionDividedLift_mk
    (w : KaehlerDifferential (ULift.{0} (WittTwo.Ring p k)) (T p k A)) :
    reductionDividedLift p k A ((sourcePrimeForms p k A).mkQ w) =
      dividedLiftDifferential p k A w := rfl

/-- The actual lift PRODUCES a correction and the SAME whole map has its true coordinate value. -/
theorem dividedLiftDifferential_coordinate (a : A) :
    ∃ b : A, WittTwoRelativeDifferential.liftRingMap p k A
        ((1 : ULift.{0} (WittTwo.Ring p k)) ⊗ₜ[WittTwo.Ring p k] a) = a ^ p + (p : A) * b ∧
      dividedLiftDifferential p k A
        (KaehlerDifferential.D (ULift.{0} (WittTwo.Ring p k)) (T p k A)
          ((1 : ULift.{0} (WittTwo.Ring p k)) ⊗ₜ[WittTwo.Ring p k] a)) =
        ((1 : k) ⊗ₜ[WittTwo.Ring p k] a) ^ (p-1) •
            KaehlerDifferential.D k (B p k A) ((1 : k) ⊗ₜ[WittTwo.Ring p k] a) +
          KaehlerDifferential.D k (B p k A) ((1 : k) ⊗ₜ[WittTwo.Ring p k] b) := by
  let := WittTwoRelativeLift.copyAlgebra p k A
  obtain ⟨b, hb⟩ := WittTwoRelativeLift.relativeLift_coordinate_correction p k A a
  change WittTwoRelativeDifferential.liftRingMap p k A
    ((1 : ULift.{0} (WittTwo.Ring p k)) ⊗ₜ[WittTwo.Ring p k] a) = a ^ p + (p : A) * b at hb
  refine ⟨b, hb, ?_⟩
  have hd : WittTwoRelativeDifferential.liftDifferential p k A
      (KaehlerDifferential.D (ULift.{0} (WittTwo.Ring p k)) (T p k A)
        ((1 : ULift.{0} (WittTwo.Ring p k)) ⊗ₜ[WittTwo.Ring p k] a)) =
      (p : WittTwo.Ring p k) •
        (a ^ (p-1) • KaehlerDifferential.D (WittTwo.Ring p k) A a +
          KaehlerDifferential.D (WittTwo.Ring p k) A b) := by
    rw [WittTwoRelativeDifferential.liftDifferential_D, hb]
    exact DividedCoordinateDifferential.differential_prime p k A a b
  rw [dividedLiftDifferential_value _ _ _ _ _ hd, map_add, map_smul,
    KaehlerDifferential.map_D, KaehlerDifferential.map_D]
  congr 1
  change (algebraMap A (B p k A) (a ^ (p-1))) • KaehlerDifferential.D k (B p k A)
      (algebraMap A (B p k A) a) =
    ((1 : k) ⊗ₜ[WittTwo.Ring p k] a) ^ (p-1) •
      KaehlerDifferential.D k (B p k A) ((1 : k) ⊗ₜ[WittTwo.Ring p k] a)
  rw [map_pow]
  rfl

end EnvelopeProperty.DeligneIllusie.WittTwoDividedLift
