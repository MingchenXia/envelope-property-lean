import EnvelopeProperty.DeligneIllusie.WittTwoAlgebraDivision
import EnvelopeProperty.DeligneIllusie.WittTwoRelativeLift

/-! Actual divided differences of genuine relative Frobenius lifts and their native derivations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

namespace EnvelopeProperty.DeligneIllusie.WittTwoLiftDifference
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoRelativeLift.residueCopyAlgebra
variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A]
private abbrev W' := ULift.{0} (WittTwo.Ring p k)
private abbrev T := WittTwoRelativeLift.TwistAlgebra p k A
private abbrev B := WittTwoSmoothDifferentials.ResidueAlgebra p k A

/-- Actual copied-base algebra maps on the SAME original twisted algebra. -/
abbrev Lift := letI := WittTwoRelativeLift.copyAlgebra p k A; T p k A →ₐ[W' p k] A

/-- The SAME actual residue relative Frobenius induces the original target coefficient action. -/
@[instance_reducible] def frobeniusAlgebra : Algebra (T p k A) (B p k A) :=
  (WittTwoRelativeLift.residueFrobenius p k A).toAlgebra
attribute [local instance] frobeniusAlgebra

local instance sourceBaseSMul : SMul (W' p k) (T p k A) :=
  (Algebra.TensorProduct.leftAlgebra : Algebra (W' p k) (T p k A)).toSMul
local instance sourceBaseModule : Module (W' p k) (T p k A) :=
  (Algebra.TensorProduct.leftAlgebra : Algebra (W' p k) (T p k A)).toModule
local instance residueBaseSMul : SMul (W' p k) (B p k A) :=
  (WittTwoRelativeLift.residueCopyAlgebra p k A).toSMul
local instance residueBaseModule : Module (W' p k) (B p k A) :=
  (WittTwoRelativeLift.residueCopyAlgebra p k A).toModule
local instance residueBaseTower : IsScalarTower (W' p k) (T p k A) (B p k A) :=
  IsScalarTower.of_algebraMap_eq (fun w => (WittTwoRelativeLift.residueFrobenius p k A).commutes w |>.symm)

variable (f g : Lift p k A)
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable (hg : ∀ t, algebraMap A (B p k A) (g t) = WittTwoRelativeLift.residueFrobenius p k A t)

/-- The difference of the two ACTUAL original lifts lies in the SAME original residue kernel. -/
def differenceElement (t : T p k A) : WittTwoAlgebraDivision.Kernel p k A :=
  ⟨f t - g t, by
    change algebraMap A (B p k A) (f t - g t) = 0
    rw [map_sub, hf t, hg t, sub_self]⟩

omit [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A] in
private theorem differenceElement_add (s t : T p k A) :
    differenceElement p k A f g hf hg (s+t) =
      differenceElement p k A f g hf hg s + differenceElement p k A f g hf hg t := by
  apply Subtype.ext
  change f (s+t) - g (s+t) = (f s-g s)+(f t-g t)
  rw [map_add, map_add]
  abel

omit [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A] in
private theorem differenceElement_smul (w : W' p k) (t : T p k A) :
    differenceElement p k A f g hf hg (w • t) =
      algebraMap (WittTwo.Ring p k) A w.down • differenceElement p k A f g hf hg t := by
  let := WittTwoRelativeLift.copyAlgebra p k A
  apply Subtype.ext
  change f (w • t) - g (w • t) = algebraMap (W' p k) A w * (f t-g t)
  rw [Algebra.smul_def w t, map_mul, map_mul, f.commutes, g.commutes]
  ring

omit [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A] in
private theorem differenceElement_mul (s t : T p k A) :
    differenceElement p k A f g hf hg (s*t) =
      g s • differenceElement p k A f g hf hg t +
      f t • differenceElement p k A f g hf hg s := by
  apply Subtype.ext
  change f (s*t)-g (s*t) = g s*(f t-g t)+f t*(f s-g s)
  rw [map_mul, map_mul]
  ring

private def differenceFunction (t : T p k A) : B p k A :=
  WittTwoAlgebraDivision.dividePrimeLinear p k A (differenceElement p k A f g hf hg t)

private def differenceBaseLinear : T p k A →ₗ[W' p k] B p k A where
  toFun := differenceFunction p k A f g hf hg
  map_add' s t := by
    unfold differenceFunction
    rw [differenceElement_add, map_add]
  map_smul' w t := by
    let := WittTwoRelativeLift.copyAlgebra p k A
    unfold differenceFunction
    rw [differenceElement_smul, map_smul]
    have hc := (WittTwoRelativeLift.reductionMap p k A).commutes w
    change algebraMap A (B p k A) (algebraMap (W' p k) A w) * _ =
      algebraMap (W' p k) (B p k A) w * _
    rw [show algebraMap A (B p k A) (algebraMap (W' p k) A w) =
      algebraMap (W' p k) (B p k A) w from hc]

/-- The actual divided difference is a genuine native relative derivation for the SAME original Frobenius action. -/
def differenceDerivation : Derivation (W' p k) (T p k A) (B p k A) :=
  Derivation.mk' (differenceBaseLinear p k A f g hf hg) (by
    intro s t
    change differenceFunction p k A f g hf hg (s*t) =
      s • differenceFunction p k A f g hf hg t + t • differenceFunction p k A f g hf hg s
    unfold differenceFunction
    rw [differenceElement_mul, map_add, map_smul, map_smul]
    change algebraMap A (B p k A) (g s) * _ + algebraMap A (B p k A) (f t) * _ =
      WittTwoRelativeLift.residueFrobenius p k A s * _ +
      WittTwoRelativeLift.residueFrobenius p k A t * _
    rw [hg s, hf t])

/-- Every actual prime expression for a genuine lift difference has its TRUE residue as divided value. -/
theorem differenceDerivation_prime (t : T p k A) (a : A) (h : f t-g t = (p : A)*a) :
    differenceDerivation p k A f g hf hg t = algebraMap A (B p k A) a := by
  have he : differenceElement p k A f g hf hg t = WittTwoAlgebraDivision.primeElement p k A a := by
    apply Subtype.ext
    exact h
  change WittTwoAlgebraDivision.dividePrimeLinear p k A
    (differenceElement p k A f g hf hg t) = _
  rw [he, WittTwoAlgebraDivision.dividePrime_primeElement]

/-- The actual divided difference induces the genuine native original Kähler linear map. -/
def differenceLinear : KaehlerDifferential (W' p k) (T p k A) →ₗ[T p k A] B p k A :=
  (differenceDerivation p k A f g hf hg).liftKaehlerDifferential

/-- EVERY original universal differential has the actual divided-difference derivation value. -/
theorem differenceLinear_D (t : T p k A) :
    differenceLinear p k A f g hf hg (KaehlerDifferential.D (W' p k) (T p k A) t) =
      differenceDerivation p k A f g hf hg t :=
  Derivation.liftKaehlerDifferential_comp_D _ t

/-- A repeated actual lift gives the genuine ZERO native map on the WHOLE original Kähler module. -/
theorem differenceLinear_self : differenceLinear p k A f f hf hf = 0 := by
  apply Derivation.liftKaehlerDifferential_unique
  apply Derivation.ext
  intro t
  change differenceLinear p k A f f hf hf (KaehlerDifferential.D (W' p k) (T p k A) t) = 0
  rw [differenceLinear_D]
  have he : differenceElement p k A f f hf hf t = 0 := by
    apply Subtype.ext
    exact sub_self _
  change WittTwoAlgebraDivision.dividePrimeLinear p k A (differenceElement p k A f f hf hf t) = 0
  rw [he, map_zero]

/-- Three ACTUAL lifts give the genuine additive overlap identity on the WHOLE native Kähler module. -/
theorem differenceLinear_cocycle (h : Lift p k A)
    (hh : ∀ t, algebraMap A (B p k A) (h t) = WittTwoRelativeLift.residueFrobenius p k A t) :
    differenceLinear p k A f h hf hh =
      differenceLinear p k A f g hf hg + differenceLinear p k A g h hg hh := by
  apply Derivation.liftKaehlerDifferential_unique
  apply Derivation.ext
  intro t
  change differenceLinear p k A f h hf hh (KaehlerDifferential.D (W' p k) (T p k A) t) =
    differenceLinear p k A f g hf hg (KaehlerDifferential.D (W' p k) (T p k A) t) +
      differenceLinear p k A g h hg hh (KaehlerDifferential.D (W' p k) (T p k A) t)
  rw [differenceLinear_D, differenceLinear_D, differenceLinear_D]
  have he : differenceElement p k A f h hf hh t =
      differenceElement p k A f g hf hg t + differenceElement p k A g h hg hh t := by
    apply Subtype.ext
    change f t-h t = (f t-g t)+(g t-h t)
    abel
  change WittTwoAlgebraDivision.dividePrimeLinear p k A (differenceElement p k A f h hf hh t) =
    WittTwoAlgebraDivision.dividePrimeLinear p k A (differenceElement p k A f g hf hg t) +
      WittTwoAlgebraDivision.dividePrimeLinear p k A (differenceElement p k A g h hg hh t)
  rw [he, map_add]

end EnvelopeProperty.DeligneIllusie.WittTwoLiftDifference
