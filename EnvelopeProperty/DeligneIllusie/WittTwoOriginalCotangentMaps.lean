import EnvelopeProperty.DeligneIllusie.WittTwoResidueCoefficients
import EnvelopeProperty.DeligneIllusie.WittTwoAllLiftClosedness
import EnvelopeProperty.Algebra.KaehlerAlgebraEquivalence

/-!
# Witt Two Original Cotangent Maps

Actual divided maps on the SAME original residue cotangent module and its genuine Frobenius scalars. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace EnvelopeProperty.DeligneIllusie.WittTwoOriginalCotangentMaps
universe u
local instance inversePair {R C B : Type u} [CommRing R] [CommRing C] [CommRing B]
    [Algebra R C] [Algebra R B] (e : C ≃ₐ[R] B) : RingHomInvPair e.toRingHom e.symm.toRingHom where
  comp_eq := by ext c; exact e.symm_apply_apply c
  comp_eq₂ := by ext b; exact e.apply_symm_apply b

private def nativeInverseTransport {R C B : Type u} [CommRing R] [CommRing C] [CommRing B]
    [Algebra R C] [Algebra R B] (e : C ≃ₐ[R] B) :
    KaehlerDifferential R B →ₛₗ[e.symm.toRingHom] KaehlerDifferential R C :=
  (KaehlerAlgebraEquivalence.equiv e).symm.toLinearMap

private theorem nativeInverseTransport_D {R C B : Type u} [CommRing R] [CommRing C] [CommRing B]
    [Algebra R C] [Algebra R B] (e : C ≃ₐ[R] B) (b : B) :
    nativeInverseTransport e (KaehlerDifferential.D R B b) = KaehlerDifferential.D R C (e.symm b) :=
  KaehlerAlgebraEquivalence.equiv_symm_D e b

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoSourceResidue.twistSMul WittTwoRelativeLift.residueCopyAlgebra
  WittTwoLiftDifference.frobeniusAlgebra
  WittTwoLiftDifference.sourceBaseSMul WittTwoLiftDifference.sourceBaseModule
  WittTwoLiftDifference.residueBaseSMul WittTwoLiftDifference.residueBaseModule
  WittTwoLiftDifference.residueBaseTower
  WittTwoArbitraryLiftDifferential.residueFormBaseSMul
  WittTwoArbitraryLiftDifferential.residueFormBaseModule
  WittTwoArbitraryLiftDifferential.residueFormBaseTower
  WittTwoArbitraryLiftDifferential.residueFormSourceTower
variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]
private abbrev T := ULift.{0} (WittTwo.Ring p k) ⊗[WittTwo.Ring p k] A
private abbrev B := WittTwoSmoothDifferentials.ResidueAlgebra p k A
private abbrev C := k ⊗[WittTwo.Ring p k] T p k A
private abbrev N := KaehlerDifferential k (B p k A)

local instance sourceRing : CommRing (T p k A) := inferInstance
local instance sourceCommSemiring : CommSemiring (T p k A) := (sourceRing p k A).toCommSemiring
local instance sourceSemiring : Semiring (T p k A) := (sourceRing p k A).toCommSemiring.toSemiring
local instance sourceResidueRing : CommRing (C p k A) := inferInstance
local instance originalResidueRing : CommRing (B p k A) := inferInstance

local instance residueAlgebra : Algebra A (B p k A) := Algebra.TensorProduct.rightAlgebra
local instance residueSourceAlgebra : Algebra (T p k A) (C p k A) :=
  Algebra.TensorProduct.rightAlgebra

private def residueEquiv : C p k A ≃ₐ[k] B p k A :=
  WittTwoResidueUntwist.residueUntwist p k A

private theorem residueEquiv_apply_symm (b : B p k A) :
    WittTwoResidueUntwist.residueUntwist p k A ((residueEquiv p k A).symm b) = b :=
  (residueEquiv p k A).apply_symm_apply b

/-- The genuine native inverse Kähler map along the SAME actual original residue untwist. -/
def sourceTransport : N p k A →ₛₗ[(residueEquiv p k A).symm.toRingHom]
    KaehlerDifferential k (C p k A) :=
  nativeInverseTransport (residueEquiv p k A)

/-- EVERY coefficient is transported along the SAME actual inverse residue algebra equivalence. -/
theorem sourceTransport_smul (b : B p k A) (w : N p k A) :
    sourceTransport p k A (b • w) =
      (residueEquiv p k A).symm b • sourceTransport p k A w :=
  (sourceTransport p k A).map_smulₛₗ b w

/-- EVERY original universal coordinate is retained in its genuine original source residue tensor. -/
theorem sourceTransport_coordinate (a : A) :
    sourceTransport p k A (KaehlerDifferential.D k (B p k A) ((1 : k) ⊗ₜ[WittTwo.Ring p k] a)) =
      KaehlerDifferential.D k (C p k A)
        ((1 : k) ⊗ₜ[WittTwo.Ring p k] ((1 : ULift.{0} (WittTwo.Ring p k)) ⊗ₜ[WittTwo.Ring p k] a)) := by
  change nativeInverseTransport (R := k) (C := C p k A) (B := B p k A)
    (residueEquiv p k A) (KaehlerDifferential.D k (B p k A) _) = _
  rw [nativeInverseTransport_D]
  congr 1
  apply (residueEquiv p k A).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (WittTwoResidueUntwist.residueUntwist_one_coordinate p k A a).symm

variable [Algebra.Smooth (WittTwo.Ring p k) A]
variable (f g : WittTwoLiftDifference.Lift p k A)
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable (hg : ∀ t, algebraMap A (B p k A) (g t) = WittTwoRelativeLift.residueFrobenius p k A t)

/-- The SAME actual divided map on the ORIGINAL native cotangent module with true Frobenius scalar law. -/
def divided : N p k A →ₛₗ[Cartier.AlgebraFrobenius.map k (B p k A) p] N p k A where
  toFun w := WittTwoLiftHomotopy.residueDividedDifferential p k A f hf (sourceTransport p k A w)
  map_add' z w := by rw [map_add, map_add]
  map_smul' b w := by
    rw [sourceTransport_smul, WittTwoResidueCoefficients.dividedDifferential_smul,
      residueEquiv_apply_symm, Cartier.AlgebraFrobenius.map_apply]

/-- The SAME actual difference map on ORIGINAL native forms with the SAME true Frobenius scalar law. -/
def difference : N p k A →ₛₗ[Cartier.AlgebraFrobenius.map k (B p k A) p] B p k A where
  toFun w := WittTwoLiftHomotopy.residueDifferenceLinear p k A f g hf hg (sourceTransport p k A w)
  map_add' z w := by rw [map_add, map_add]
  map_smul' b w := by
    rw [sourceTransport_smul, WittTwoResidueCoefficients.differenceLinear_smul,
      residueEquiv_apply_symm, Cartier.AlgebraFrobenius.map_apply]

/-- EVERY original divided form retains its actual original native-residue value. -/
theorem divided_apply (w : N p k A) : divided p k A f hf w =
    WittTwoLiftHomotopy.residueDividedDifferential p k A f hf (sourceTransport p k A w) := rfl

/-- EVERY original difference value retains its actual original native-residue value. -/
theorem difference_apply (w : N p k A) : difference p k A f g hf hg w =
    WittTwoLiftHomotopy.residueDifferenceLinear p k A f g hf hg (sourceTransport p k A w) := rfl

/-- EVERY original coordinate retains the SAME actual whole divided value in the original twisted source. -/
theorem divided_coordinate (a : A) :
    divided p k A f hf (KaehlerDifferential.D k (B p k A) ((1 : k) ⊗ₜ[WittTwo.Ring p k] a)) =
      WittTwoArbitraryLiftDifferential.dividedDifferential p k A f hf
        (KaehlerDifferential.D (ULift.{0} (WittTwo.Ring p k)) (T p k A)
          ((1 : ULift.{0} (WittTwo.Ring p k)) ⊗ₜ[WittTwo.Ring p k] a)) := by
  rw [divided_apply, sourceTransport_coordinate, ← WittTwoSourceResidue.sourceReduction_D,
    WittTwoLiftHomotopy.residueDividedDifferential_reduction]

/-- EVERY original coordinate retains the SAME genuine whole divided-difference value. -/
theorem difference_coordinate (a : A) :
    difference p k A f g hf hg (KaehlerDifferential.D k (B p k A) ((1 : k) ⊗ₜ[WittTwo.Ring p k] a)) =
      WittTwoLiftDifference.differenceLinear p k A f g hf hg
        (KaehlerDifferential.D (ULift.{0} (WittTwo.Ring p k)) (T p k A)
          ((1 : ULift.{0} (WittTwo.Ring p k)) ⊗ₜ[WittTwo.Ring p k] a)) := by
  rw [difference_apply, sourceTransport_coordinate, ← WittTwoSourceResidue.sourceReduction_D,
    WittTwoLiftHomotopy.residueDifferenceLinear_reduction]

/-- The ACTUAL whole homotopy holds on EVERY SAME ORIGINAL residue cotangent form. -/
theorem divided_sub (w : N p k A) :
    divided p k A f hf w - divided p k A g hg w =
      KaehlerDifferential.D k (B p k A) (difference p k A f g hf hg w) := by
  rw [divided_apply, divided_apply, difference_apply]
  exact WittTwoLiftHomotopy.residueDividedDifferential_sub p k A f g hf hg (sourceTransport p k A w)

/-- EVERY SAME ORIGINAL divided form is closed under the genuine original etale de Rham differential. -/
theorem divided_closed {n : ℕ} (v : Fin n → B p k A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (w : N p k A) :
    WittTwoDividedLiftClosed.closedDerivative p k A v hv (divided p k A f hf w) = 0 := by
  rw [divided_apply]
  exact WittTwoAllLiftClosedness.residueDividedDifferential_closed p k A v hv f hf (sourceTransport p k A w)
omit [CharP k p] [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A] in
/-- The SAME original closed derivative has its actual whole native exterior differential value. -/
theorem closedDerivative_apply {n : ℕ} (v : Fin n → B p k A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (w : N p k A) :
    WittTwoDividedLiftClosed.closedDerivative p k A v hv w =
      Cartier.EtaleDeRham.differential v hv 1
        ((exteriorPower.oneEquiv (B p k A) (N p k A)).symm w) := by
  unfold WittTwoDividedLiftClosed.closedDerivative
  run_tac do
    let env ← Lean.getEnv
    let some (name, _) := env.constants.toList.find? (fun entry =>
      entry.1.toString.startsWith "_private.EnvelopeProperty.DeligneIllusie.WittTwoDividedLiftClosed." &&
      entry.1.toString.endsWith ".nativeClosedDerivative")
      | throwError "Original native closed derivative definition is missing"
    Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent name)))
  rw [AddMonoidHom.coe_mk, ZeroHom.coe_mk]

/-- EVERY original divided image is an actual cycle of the SAME genuine original exterior complex. -/
theorem divided_closed_native {n : ℕ} (v : Fin n → B p k A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (w : N p k A) :
    Cartier.EtaleDeRham.differential v hv 1
      ((exteriorPower.oneEquiv (B p k A) (N p k A)).symm (divided p k A f hf w)) = 0 := by
  rw [← closedDerivative_apply]
  exact divided_closed p k A f hf v hv w

end EnvelopeProperty.DeligneIllusie.WittTwoOriginalCotangentMaps
