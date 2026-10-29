import EnvelopeProperty.DeligneIllusie.WittTwoResidue
import Mathlib.RingTheory.Smooth.Flat

/-!
# Witt Two Algebra Division

Canonical original coefficient-linear division on the actual smooth algebra residue kernel. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

namespace EnvelopeProperty.DeligneIllusie.WittTwoAlgebraDivision
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A]
private abbrev B := k ⊗[WittTwo.Ring p k] A

/-- The original kernel IDEAL of the SAME actual residue algebra map. -/
def Kernel : Ideal A := RingHom.ker (algebraMap A (B p k A))

/-- Every original prime multiple as an actual element of the SAME original kernel ideal. -/
def primeElement (a : A) : Kernel p k A :=
  ⟨(p : A) * a, by
    have hp : (p : B p k A) = 0 := by
      rw [← map_natCast (algebraMap k (B p k A)) p, CharP.cast_eq_zero, map_zero]
    change algebraMap A (B p k A) ((p : A) * a) = 0
    rw [map_mul, map_natCast, hp, zero_mul]⟩

/-- Actual smooth-flat residue exactness PRODUCES an original prime preimage for EVERY kernel element. -/
theorem kernel_prime (x : Kernel p k A) : ∃ a : A, x = primeElement p k A a := by
  have hx : WittTwoResidue.tensorReduction p k A x.val = 0 := x.property
  obtain ⟨a, ha⟩ := (WittTwoResidue.tensorReduction_exact p k A x.val).mp hx
  refine ⟨a, ?_⟩
  apply Subtype.ext
  change (p : WittTwo.Ring p k) • a = x.val at ha
  rw [Algebra.smul_def, map_natCast] at ha
  exact ha.symm

private def toWittPrime (x : Kernel p k A) : WittTwoModuleDivision.primeSubmodule p k A :=
  ⟨x.val, by
    obtain ⟨a, ha⟩ := kernel_prime p k A x
    refine ⟨a, ?_⟩
    change (p : WittTwo.Ring p k) • a = x.val
    rw [Algebra.smul_def, map_natCast]
    exact congrArg Subtype.val ha.symm⟩

private def divisionFunction (x : Kernel p k A) : B p k A :=
  WittTwoResidue.dividePrimeTensorEquiv p k A (toWittPrime p k A x)

private theorem divisionFunction_primeElement (a : A) :
    divisionFunction p k A (primeElement p k A a) = algebraMap A (B p k A) a := by
  have h : toWittPrime p k A (primeElement p k A a) =
      WittTwoModuleDivision.primeMultiple p k A a := by
    apply Subtype.ext
    change (p : A) * a = (p : WittTwo.Ring p k) • a
    rw [Algebra.smul_def, map_natCast]
  rw [divisionFunction, h, WittTwoResidue.dividePrimeTensorEquiv_primeMultiple]
  rfl

/-- The SAME actual canonical division is linear for EVERY original A-coefficient. -/
def dividePrimeLinear : Kernel p k A →ₗ[A] B p k A where
  toFun := divisionFunction p k A
  map_add' x y := (WittTwoResidue.dividePrimeTensorEquiv p k A).map_add
    (toWittPrime p k A x) (toWittPrime p k A y)
  map_smul' a x := by
    obtain ⟨b, rfl⟩ := kernel_prime p k A x
    have hs : a • primeElement p k A b = primeElement p k A (a*b) := by
      apply Subtype.ext
      change a * ((p : A)*b) = (p : A)*(a*b)
      ring
    rw [hs, divisionFunction_primeElement, divisionFunction_primeElement, map_mul]
    rfl

/-- EVERY original prime multiple has its SAME original residue as canonical divided value. -/
theorem dividePrime_primeElement (a : A) :
    dividePrimeLinear p k A (primeElement p k A a) = algebraMap A (B p k A) a :=
  divisionFunction_primeElement p k A a

/-- Bijectivity is DERIVED for the SAME actual coefficient-linear original kernel division. -/
theorem dividePrime_bijective : Function.Bijective (dividePrimeLinear p k A) := by
  constructor
  · intro x y h
    have he : toWittPrime p k A x = toWittPrime p k A y :=
      (WittTwoResidue.dividePrimeTensorEquiv p k A).injective h
    apply Subtype.ext
    exact congrArg (fun z : WittTwoModuleDivision.primeSubmodule p k A => z.val) he
  · intro z
    obtain ⟨a, ha⟩ := WittTwoResidue.tensorReduction_surjective p k A z
    refine ⟨primeElement p k A a, ?_⟩
    rw [dividePrime_primeElement]
    exact ha

/-- The original kernel ideal and the actual residue algebra are genuinely A-linearly equivalent. -/
def dividePrimeEquiv : Kernel p k A ≃ₗ[A] B p k A :=
  LinearEquiv.ofBijective (dividePrimeLinear p k A) (dividePrime_bijective p k A)

end EnvelopeProperty.DeligneIllusie.WittTwoAlgebraDivision
