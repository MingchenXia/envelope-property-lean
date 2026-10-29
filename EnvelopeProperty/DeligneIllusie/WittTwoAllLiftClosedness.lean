import EnvelopeProperty.DeligneIllusie.WittTwoLiftHomotopy
import EnvelopeProperty.DeligneIllusie.WittTwoDividedLiftClosed

/-!
# Witt Two All Lift Closedness

Every actual relative Frobenius lift has closed whole divided image, with original native residue comparison. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

namespace EnvelopeProperty.DeligneIllusie.WittTwoAllLiftClosedness
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoRelativeLift.residueCopyAlgebra WittTwoLiftDifference.frobeniusAlgebra
  WittTwoLiftDifference.sourceBaseSMul WittTwoLiftDifference.sourceBaseModule
variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A]
private abbrev W' := ULift.{0} (WittTwo.Ring p k)
private abbrev T := WittTwoRelativeLift.TwistAlgebra p k A
private abbrev B := WittTwoSmoothDifferentials.ResidueAlgebra p k A
variable {n : ℕ} (v : Fin n → B p k A)
  (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)

omit [CharP k p] [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A] in
private theorem closedDerivative_D (b : B p k A) :
    WittTwoDividedLiftClosed.closedDerivative p k A v hv (KaehlerDifferential.D k (B p k A) b) = 0 := by
  unfold WittTwoDividedLiftClosed.closedDerivative
  run_tac do
    let env ← Lean.getEnv
    let some (name, _) := env.constants.toList.find? (fun entry =>
      entry.1.toString.startsWith "_private.EnvelopeProperty.DeligneIllusie.WittTwoDividedLiftClosed." &&
        entry.1.toString.endsWith ".nativeClosedDerivative")
      | throwError "Original native closed derivative definition is missing"
    Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent name)))
  rw [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  convert Cartier.EtaleDifferentialLeibniz.differential_universalD v hv b using 1

variable (f : WittTwoLiftDifference.Lift p k A)
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)

/-- EVERY actual relative lift has genuinely closed image on the ENTIRE original source Kähler module. -/
theorem dividedDifferential_closed (w : KaehlerDifferential (W' p k) (T p k A)) :
    WittTwoDividedLiftClosed.closedDerivative p k A v hv
      (WittTwoArbitraryLiftDifferential.dividedDifferential p k A f hf w) = 0 := by
  have hd := LinearMap.congr_fun (WittTwoLiftHomotopy.dividedDifferential_sub p k A f
    (WittTwoArbitraryLiftDifferential.producedLift p k A) hf
    (WittTwoArbitraryLiftDifferential.producedLift_reduction p k A)) w
  have he : WittTwoArbitraryLiftDifferential.dividedDifferential p k A f hf w =
      KaehlerDifferential.D k (B p k A) (WittTwoLiftDifference.differenceLinear p k A f
        (WittTwoArbitraryLiftDifferential.producedLift p k A) hf
        (WittTwoArbitraryLiftDifferential.producedLift_reduction p k A) w) +
      WittTwoArbitraryLiftDifferential.dividedDifferential p k A
        (WittTwoArbitraryLiftDifferential.producedLift p k A)
        (WittTwoArbitraryLiftDifferential.producedLift_reduction p k A) w :=
    sub_eq_iff_eq_add.mp hd
  rw [he, map_add, closedDerivative_D, zero_add,
    WittTwoArbitraryLiftDifferential.dividedDifferential_produced]
  exact WittTwoDividedLiftClosed.dividedLift_closed p k A v hv w

/-- EVERY native residue source form has genuinely closed image for EVERY actual lift. -/
theorem residueDividedDifferential_closed
    (w : KaehlerDifferential k (WittTwoSourceResidue.SourceResidue p k A)) :
    WittTwoDividedLiftClosed.closedDerivative p k A v hv
      (WittTwoLiftHomotopy.residueDividedDifferential p k A f hf w) = 0 := by
  obtain ⟨z, rfl⟩ := WittTwoSourceResidue.sourceReduction_surjective p k A w
  rw [WittTwoLiftHomotopy.residueDividedDifferential_reduction]
  exact dividedDifferential_closed p k A v hv f hf z

/-- The SAME actual produced lift retains the PRE-EXISTING original native residue divided map on EVERY form. -/
theorem residueDividedDifferential_produced
    (w : KaehlerDifferential k (WittTwoSourceResidue.SourceResidue p k A)) :
    WittTwoLiftHomotopy.residueDividedDifferential p k A
        (WittTwoArbitraryLiftDifferential.producedLift p k A)
        (WittTwoArbitraryLiftDifferential.producedLift_reduction p k A) w =
      WittTwoSourceResidue.residueDividedLift p k A w := by
  obtain ⟨z, rfl⟩ := WittTwoSourceResidue.sourceReduction_surjective p k A w
  rw [WittTwoLiftHomotopy.residueDividedDifferential_reduction,
    WittTwoSourceResidue.residueDividedLift_reduction,
    WittTwoArbitraryLiftDifferential.dividedDifferential_produced]

end EnvelopeProperty.DeligneIllusie.WittTwoAllLiftClosedness
