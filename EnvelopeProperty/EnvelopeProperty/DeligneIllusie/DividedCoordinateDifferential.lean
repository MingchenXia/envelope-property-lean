import EnvelopeProperty.DeligneIllusie.WittTwoSmoothDifferentials

/-! Actual ordinary coordinate divided differentials and their actual correction differences. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

namespace EnvelopeProperty.DeligneIllusie.DividedCoordinateDifferential

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
variable (A : Type*) [CommRing A] [Algebra (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A]

/-- The actual ordinary coordinate Frobenius-lift expression in the original lifted ring. -/
def liftValue (a b : A) : A := a ^ p + (p : A) * b

omit [CharP k p] [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A] in
/-- Actual differentiation of the original lift expression produces a genuine prime multiple. -/
theorem differential_prime (a b : A) :
    KaehlerDifferential.D (WittTwo.Ring p k) A (liftValue p A a b) =
      (p : WittTwo.Ring p k) •
        (a ^ (p-1) • KaehlerDifferential.D (WittTwo.Ring p k) A a +
          KaehlerDifferential.D (WittTwo.Ring p k) A b) := by
  simp [liftValue, Derivation.leibniz_pow, Derivation.leibniz, smul_add,
    Nat.cast_smul_eq_nsmul]

attribute [local instance] WittTwoSmoothDifferentials.differentials_flat

/-- The original lift differential as an element of the actual prime-image module. -/
def liftCycle (a b : A) :
    WittTwoModuleDivision.primeSubmodule p k (KaehlerDifferential (WittTwo.Ring p k) A) :=
  ⟨KaehlerDifferential.D (WittTwo.Ring p k) A (liftValue p A a b),
    ⟨a ^ (p-1) • KaehlerDifferential.D (WittTwo.Ring p k) A a +
      KaehlerDifferential.D (WittTwo.Ring p k) A b, (differential_prime p k A a b).symm⟩⟩

/-- Canonical division of the SAME actual original ordinary coordinate lift differential. -/
def dividedDifferential (a b : A) :
    KaehlerDifferential k (WittTwoSmoothDifferentials.ResidueAlgebra p k A) :=
  WittTwoSmoothDifferentials.divideDifferentialEquiv p k A (liftCycle p k A a b)

/-- The actual ordinary divided-Frobenius coordinate formula on the actual residue module. -/
theorem dividedDifferential_formula (a b : A) :
    dividedDifferential p k A a b =
      ((1 : k) ⊗ₜ[WittTwo.Ring p k] a) ^ (p-1) •
          KaehlerDifferential.D k (WittTwoSmoothDifferentials.ResidueAlgebra p k A)
            ((1 : k) ⊗ₜ a) +
        KaehlerDifferential.D k (WittTwoSmoothDifferentials.ResidueAlgebra p k A)
          ((1 : k) ⊗ₜ b) := by
  have h : liftCycle p k A a b = WittTwoModuleDivision.primeMultiple p k _
      (a ^ (p-1) • KaehlerDifferential.D (WittTwo.Ring p k) A a +
        KaehlerDifferential.D (WittTwo.Ring p k) A b) := by
    apply Subtype.ext
    exact differential_prime p k A a b
  rw [dividedDifferential, h, WittTwoSmoothDifferentials.divideDifferentialEquiv_primeMultiple,
    map_add, map_smul, KaehlerDifferential.map_D, KaehlerDifferential.map_D]
  congr 1
  change (algebraMap A (WittTwoSmoothDifferentials.ResidueAlgebra p k A) (a ^ (p-1))) •
      KaehlerDifferential.D k (WittTwoSmoothDifferentials.ResidueAlgebra p k A)
        (algebraMap A (WittTwoSmoothDifferentials.ResidueAlgebra p k A) a) =
    ((1 : k) ⊗ₜ[WittTwo.Ring p k] a) ^ (p-1) •
      KaehlerDifferential.D k (WittTwoSmoothDifferentials.ResidueAlgebra p k A) ((1 : k) ⊗ₜ a)
  rw [map_pow]
  rfl

/-- The SAME two actual divided values differ by the actual correction-difference differential. -/
theorem dividedDifferential_difference (a b c : A) :
    dividedDifferential p k A a b - dividedDifferential p k A a c =
      KaehlerDifferential.D k (WittTwoSmoothDifferentials.ResidueAlgebra p k A)
        ((1 : k) ⊗ₜ[WittTwo.Ring p k] (b-c)) := by
  rw [dividedDifferential_formula, dividedDifferential_formula, TensorProduct.tmul_sub, map_sub]
  abel

end EnvelopeProperty.DeligneIllusie.DividedCoordinateDifferential
