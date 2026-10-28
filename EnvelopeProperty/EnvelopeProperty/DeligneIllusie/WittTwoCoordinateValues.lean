import EnvelopeProperty.DeligneIllusie.WittTwoOriginalCotangentMaps
import EnvelopeProperty.DeligneIllusie.WittTwoAlgebraDivision
import EnvelopeProperty.DeligneIllusie.DividedCoordinateDifferential

/-! Actual coordinate corrections and genuine universal differential values of EVERY actual relative lift. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace EnvelopeProperty.DeligneIllusie.WittTwoCoordinateValues
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoSourceResidue.twistSMul WittTwoRelativeLift.residueCopyAlgebra
  WittTwoLiftDifference.frobeniusAlgebra
  WittTwoOriginalCotangentMaps.sourceRing WittTwoOriginalCotangentMaps.sourceCommSemiring
  WittTwoOriginalCotangentMaps.sourceSemiring WittTwoOriginalCotangentMaps.sourceResidueRing
  WittTwoOriginalCotangentMaps.originalResidueRing WittTwoOriginalCotangentMaps.residueAlgebra
variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A]
private abbrev T := WittTwoRelativeLift.TwistAlgebra p k A
private abbrev B := WittTwoSmoothDifferentials.ResidueAlgebra p k A
variable (f : WittTwoLiftDifference.Lift p k A)
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)

include hf in
/-- EVERY actual lift PRODUCES an original correction by true whole smooth-flat kernel exactness. -/
theorem coordinate_correction (a : A) :
    ∃ b : A, f ((1 : ULift.{0} (WittTwo.Ring p k)) ⊗ₜ[WittTwo.Ring p k] a) =
      a ^ p + (p : A) * b := by
  let t : T p k A := (1 : ULift.{0} (WittTwo.Ring p k)) ⊗ₜ[WittTwo.Ring p k] a
  let x : WittTwoAlgebraDivision.Kernel p k A := ⟨f t - a ^ p, by
    change algebraMap A (B p k A) (f t - a ^ p) = 0
    rw [map_sub, map_pow, hf t, WittTwoResidueUntwist.residueFrobenius_untwist]
    dsimp only [t]
    rw [WittTwoResidueUntwist.sourceUntwist_one_tmul]
    exact sub_self _⟩
  obtain ⟨b, hb⟩ := WittTwoAlgebraDivision.kernel_prime p k A x
  have hb' : f t - a ^ p = (p : A) * b := congrArg Subtype.val hb
  refine ⟨b, ?_⟩
  exact sub_eq_iff_eq_add.mp hb' |>.trans (add_comm _ _)

/-- EVERY original coordinate retains the SAME actual lift correction and genuine original divided value. -/
theorem divided_coordinate (a : A) :
    ∃ b : A, f ((1 : ULift.{0} (WittTwo.Ring p k)) ⊗ₜ[WittTwo.Ring p k] a) =
        a ^ p + (p : A) * b ∧
      WittTwoOriginalCotangentMaps.divided p k A f hf
        (KaehlerDifferential.D k (B p k A) ((1 : k) ⊗ₜ[WittTwo.Ring p k] a)) =
        ((1 : k) ⊗ₜ[WittTwo.Ring p k] a) ^ (p-1) •
            KaehlerDifferential.D k (B p k A) ((1 : k) ⊗ₜ[WittTwo.Ring p k] a) +
          KaehlerDifferential.D k (B p k A) ((1 : k) ⊗ₜ[WittTwo.Ring p k] b) := by
  obtain ⟨b, hb⟩ := coordinate_correction p k A f hf a
  refine ⟨b, hb, ?_⟩
  have hd : KaehlerDifferential.D (WittTwo.Ring p k) A
      (f ((1 : ULift.{0} (WittTwo.Ring p k)) ⊗ₜ[WittTwo.Ring p k] a)) =
      (p : WittTwo.Ring p k) •
        (a ^ (p-1) • KaehlerDifferential.D (WittTwo.Ring p k) A a +
          KaehlerDifferential.D (WittTwo.Ring p k) A b) := by
    rw [hb]
    exact DividedCoordinateDifferential.differential_prime p k A a b
  rw [WittTwoOriginalCotangentMaps.divided_coordinate,
    WittTwoArbitraryLiftDifferential.dividedDifferential_prime _ _ _ _ _ _ _ hd,
    map_add, map_smul, KaehlerDifferential.map_D, KaehlerDifferential.map_D]
  congr 1
  change (algebraMap A (B p k A) (a ^ (p-1))) • KaehlerDifferential.D k (B p k A)
      (algebraMap A (B p k A) a) =
    ((1 : k) ⊗ₜ[WittTwo.Ring p k] a) ^ (p-1) •
      KaehlerDifferential.D k (B p k A) ((1 : k) ⊗ₜ[WittTwo.Ring p k] a)
  rw [map_pow]
  rfl

/-- EVERY original residue function has its actual Cartier generator plus a genuinely exact original form. -/
theorem divided_universalD (c : B p k A) :
    ∃ z : B p k A, WittTwoOriginalCotangentMaps.divided p k A f hf
        (KaehlerDifferential.D k (B p k A) c) =
      c ^ (p-1) • KaehlerDifferential.D k (B p k A) c + KaehlerDifferential.D k (B p k A) z := by
  obtain ⟨a, ha⟩ := WittTwoResidue.tensorReduction_surjective p k A c
  change (1 : k) ⊗ₜ[WittTwo.Ring p k] a = c at ha
  obtain ⟨b, _, hb⟩ := divided_coordinate p k A f hf a
  exact ⟨(1 : k) ⊗ₜ[WittTwo.Ring p k] b, ha ▸ hb⟩
end EnvelopeProperty.DeligneIllusie.WittTwoCoordinateValues
