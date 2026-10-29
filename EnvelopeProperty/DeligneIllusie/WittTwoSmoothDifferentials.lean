import EnvelopeProperty.DeligneIllusie.WittTwoResidue
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# Witt Two Smooth Differentials

Division on actual smooth lifted Kähler modules, with native residue identification. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

namespace EnvelopeProperty.DeligneIllusie.WittTwoSmoothDifferentials

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra

variable (A : Type*) [CommRing A] [Algebra (WittTwo.Ring p k) A]

abbrev ResidueAlgebra := k ⊗[WittTwo.Ring p k] A

variable [Algebra.Smooth (WittTwo.Ring p k) A]

omit [CharP k p] [PerfectRing k p] in
/-- Smoothness proves actual W2-flatness of the SAME original Kähler module. -/
theorem differentials_flat :
    Module.Flat (WittTwo.Ring p k) (KaehlerDifferential (WittTwo.Ring p k) A) :=
  Module.Flat.trans (WittTwo.Ring p k) A (KaehlerDifferential (WittTwo.Ring p k) A)

attribute [local instance] differentials_flat

/-- The original prime image in lifted differentials is the actual residue Kähler module. -/
def divideDifferentialEquiv :
    WittTwoModuleDivision.primeSubmodule p k (KaehlerDifferential (WittTwo.Ring p k) A)
      ≃ₗ[WittTwo.Ring p k] KaehlerDifferential k (ResidueAlgebra p k A) :=
  (WittTwoResidue.dividePrimeTensorEquiv p k (KaehlerDifferential (WittTwo.Ring p k) A)).trans
    ((KaehlerDifferential.tensorKaehlerEquivBase (WittTwo.Ring p k) k A
      (ResidueAlgebra p k A)).restrictScalars (WittTwo.Ring p k))

/-- Every original prime multiple retains its original canonical differential reduction. -/
theorem divideDifferentialEquiv_primeMultiple (w : KaehlerDifferential (WittTwo.Ring p k) A) :
    divideDifferentialEquiv p k A (WittTwoModuleDivision.primeMultiple p k _ w) =
      KaehlerDifferential.map (WittTwo.Ring p k) k A (ResidueAlgebra p k A) w := by
  rw [divideDifferentialEquiv, LinearEquiv.trans_apply,
    WittTwoResidue.dividePrimeTensorEquiv_primeMultiple]
  change KaehlerDifferential.tensorKaehlerEquivBase (WittTwo.Ring p k) k A
    (ResidueAlgebra p k A) ((1 : k) ⊗ₜ w) = _
  rw [KaehlerDifferential.tensorKaehlerEquivBase_tmul, one_smul]

/-- In particular p da maps to the true differential of the original residue of a. -/
theorem divideDifferentialEquiv_primeDifferential (a : A) :
    divideDifferentialEquiv p k A (WittTwoModuleDivision.primeMultiple p k _
      (KaehlerDifferential.D (WittTwo.Ring p k) A a)) =
        KaehlerDifferential.D k (ResidueAlgebra p k A) ((1 : k) ⊗ₜ a) := by
  rw [divideDifferentialEquiv_primeMultiple, KaehlerDifferential.map_D]
  rfl

/-- The SAME actual native Kähler reduction, with only original W2 scalars retained. -/
def reductionDifferential : KaehlerDifferential (WittTwo.Ring p k) A →ₗ[WittTwo.Ring p k]
    KaehlerDifferential k (ResidueAlgebra p k A) :=
  (KaehlerDifferential.map (WittTwo.Ring p k) k A (ResidueAlgebra p k A)).restrictScalars _

/-- The actual canonical Kähler reduction has exactly the original prime image as kernel. -/
theorem reductionDifferential_eq_zero_iff (w : KaehlerDifferential (WittTwo.Ring p k) A) :
    reductionDifferential p k A w = 0 ↔
      ∃ z : KaehlerDifferential (WittTwo.Ring p k) A,
        w = (p : WittTwo.Ring p k) • z := by
  let e := KaehlerDifferential.tensorKaehlerEquivBase (WittTwo.Ring p k) k A
    (ResidueAlgebra p k A)
  have he : e ((1 : k) ⊗ₜ w) = reductionDifferential p k A w := by
    exact (KaehlerDifferential.tensorKaehlerEquivBase_tmul (WittTwo.Ring p k) k A
      (ResidueAlgebra p k A) 1 w).trans (one_smul k _)
  constructor
  · intro hw
    have ht : (1 : k) ⊗ₜ[WittTwo.Ring p k] w = 0 := by
      apply e.injective
      exact he.trans (hw.trans e.map_zero.symm)
    obtain ⟨z, hz⟩ := (WittTwoResidue.tensorReduction_exact p k _ w).mp ht
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩
    have ht := (WittTwoResidue.tensorReduction_exact p k _ w).mpr ⟨z, hz.symm⟩
    exact he.symm.trans ((congrArg e ht).trans e.map_zero)

end EnvelopeProperty.DeligneIllusie.WittTwoSmoothDifferentials
