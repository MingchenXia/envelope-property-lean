import EnvelopeProperty.DeligneIllusie.WittTwoResidueUntwist
import EnvelopeProperty.DeligneIllusie.WittTwoLiftHomotopy

/-! Actual whole residue coefficient action of the SAME native divided maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace EnvelopeProperty.DeligneIllusie.WittTwoResidueCoefficients
universe u
private theorem nativeCoefficientLaw {T C B M V : Type u}
    [CommRing T] [CommRing C] [CommRing B] [Algebra T C] [Algebra T B]
    [AddCommGroup M] [Module C M] [Module T M] [IsScalarTower T C M]
    [AddCommGroup V] [Module B V] [Module T V] [IsScalarTower T B V]
    (F : M →ₗ[T] V) (h : Function.Surjective (algebraMap T C))
    (b : C →+* B) (hb : ∀ t, algebraMap T B t = b (algebraMap T C t)) (c : C) (w : M) :
    F (c • w) = b c • F w := by
  obtain ⟨t, rfl⟩ := h c
  rw [IsScalarTower.algebraMap_smul C, F.map_smul,
    ← IsScalarTower.algebraMap_smul B, hb]

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoSourceResidue.twistSMul WittTwoRelativeLift.residueCopyAlgebra
  WittTwoSourceResidue.sourceOriginalSMul WittTwoSourceResidue.sourceOriginalModule
  WittTwoSourceResidue.sourceBaseTower
  WittTwoLiftDifference.frobeniusAlgebra
  WittTwoLiftDifference.sourceBaseSMul WittTwoLiftDifference.sourceBaseModule
  WittTwoLiftDifference.residueBaseSMul WittTwoLiftDifference.residueBaseModule
  WittTwoLiftDifference.residueBaseTower
  WittTwoArbitraryLiftDifferential.residueFormBaseSMul
  WittTwoArbitraryLiftDifferential.residueFormBaseModule
  WittTwoArbitraryLiftDifferential.residueFormBaseTower
  WittTwoArbitraryLiftDifferential.residueFormSourceTower
variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]
private abbrev T := WittTwoRelativeLift.TwistAlgebra p k A
private abbrev B := WittTwoSmoothDifferentials.ResidueAlgebra p k A
private abbrev C := k ⊗[WittTwo.Ring p k] T p k A

local instance residueSourceAlgebra : Algebra (T p k A) (C p k A) :=
  Algebra.TensorProduct.rightAlgebra

/-- EVERY original residue coefficient has its derived actual Frobenius scalar action. -/
theorem residueCoefficientLaw {V : Type u} [AddCommGroup V]
    [Module (B p k A) V] [Module (T p k A) V] [IsScalarTower (T p k A) (B p k A) V]
    (F : KaehlerDifferential k (C p k A) →ₗ[T p k A] V)
    (c : C p k A) (w : KaehlerDifferential k (C p k A)) :
    F (c • w) = (WittTwoResidueUntwist.residueUntwist p k A c) ^ p • F w := by
  let b : C p k A →+* B p k A := (Cartier.AlgebraFrobenius.map k (B p k A) p).comp
    (WittTwoResidueUntwist.residueUntwist p k A).toRingHom
  have hb (t : T p k A) : algebraMap (T p k A) (B p k A) t =
      b ((1 : k) ⊗ₜ[WittTwo.Ring p k] t) := by
    dsimp only [b, RingHom.comp_apply]
    rw [Cartier.AlgebraFrobenius.map_apply]
    exact WittTwoResidueUntwist.residueFrobenius_untwist p k A t
  have hs : Function.Surjective (fun t : T p k A =>
      ((1 : k) ⊗ₜ[WittTwo.Ring p k] t : C p k A)) := by
    intro c
    obtain ⟨t, ht⟩ := WittTwoResidue.tensorReduction_surjective p k (T p k A) c
    exact ⟨t, ht⟩
  have h := nativeCoefficientLaw (T := T p k A) (C := C p k A) (B := B p k A)
    (M := KaehlerDifferential k (C p k A)) (V := V) F hs b hb c w
  exact h.trans (congrArg (fun x : B p k A => x • F w)
    (Cartier.AlgebraFrobenius.map_apply k (B p k A) p _))

variable [Algebra.Smooth (WittTwo.Ring p k) A]
variable (f g : WittTwoLiftDifference.Lift p k A)
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable (hg : ∀ t, algebraMap A (B p k A) (g t) = WittTwoRelativeLift.residueFrobenius p k A t)

/-- The SAME original whole native-residue divided map retains every actual coefficient. -/
theorem dividedDifferential_smul (c : C p k A) (w : KaehlerDifferential k (C p k A)) :
    WittTwoLiftHomotopy.residueDividedDifferential p k A f hf (c • w) =
      (WittTwoResidueUntwist.residueUntwist p k A c) ^ p •
        WittTwoLiftHomotopy.residueDividedDifferential p k A f hf w :=
  residueCoefficientLaw p k A _ c w

/-- The SAME original whole native-residue difference map retains every actual coefficient. -/
theorem differenceLinear_smul (c : C p k A) (w : KaehlerDifferential k (C p k A)) :
    WittTwoLiftHomotopy.residueDifferenceLinear p k A f g hf hg (c • w) =
      (WittTwoResidueUntwist.residueUntwist p k A c) ^ p •
        WittTwoLiftHomotopy.residueDifferenceLinear p k A f g hf hg w :=
  residueCoefficientLaw p k A _ c w
end EnvelopeProperty.DeligneIllusie.WittTwoResidueCoefficients
