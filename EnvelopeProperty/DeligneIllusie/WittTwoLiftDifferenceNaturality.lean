import EnvelopeProperty.DeligneIllusie.WittTwoAlgebraDivisionNaturality
import EnvelopeProperty.DeligneIllusie.WittTwoLiftDifference

/-! # Actual original lifted algebra diagrams derive entire divided-difference naturality -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoLiftDifferenceNaturality
open scoped TensorProduct
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoRelativeLift.residueCopyAlgebra
variable {A A' : Type u} [CommRing A] [CommRing A']
  [Algebra (WittTwo.Ring p k) A] [Algebra (WittTwo.Ring p k) A']
private abbrev W' := ULift.{0} (WittTwo.Ring p k)
local instance copiedSMul : SMul (WittTwo.Ring p k) (W' p k) :=
  (WittTwoRelativeLift.twistBaseAlgebra p k).toSMul
local instance copiedTower : IsScalarTower (WittTwo.Ring p k) (WittTwo.Ring p k) (W' p k) where
  smul_assoc a b c := by
    change algebraMap (WittTwo.Ring p k) (W' p k) (a*b) * c =
      algebraMap (WittTwo.Ring p k) (W' p k) a *
        (algebraMap (WittTwo.Ring p k) (W' p k) b * c)
    rw [map_mul, mul_assoc]
private abbrev T (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A] :=
  WittTwoRelativeLift.TwistAlgebra p k A
private abbrev B (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A] :=
  WittTwoSmoothDifferentials.ResidueAlgebra p k A

/-- The actual original tensor map of SAME copied-base Frobenius twists. -/
def twistMap (β : A →ₐ[WittTwo.Ring p k] A') : T p k A →ₐ[W' p k] T p k A' where
  toRingHom := (Algebra.TensorProduct.map (AlgHom.id (WittTwo.Ring p k) (W' p k)) β).toRingHom
  commutes' c := by
    change (Algebra.TensorProduct.map (AlgHom.id (WittTwo.Ring p k) (W' p k)) β)
      (c ⊗ₜ[WittTwo.Ring p k] (1 : A)) = c ⊗ₜ[WittTwo.Ring p k] (1 : A')
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]

omit [PerfectRing k p] in
/-- EVERY original copied coefficient and actual algebra coordinate is retained in the twist image. -/
theorem twistMap_tmul (β : A →ₐ[WittTwo.Ring p k] A') (c : W' p k) (a : A) :
    twistMap p k β (c ⊗ₜ[WittTwo.Ring p k] a) = c ⊗ₜ[WittTwo.Ring p k] β a := by
  change (Algebra.TensorProduct.map (AlgHom.id (WittTwo.Ring p k) (W' p k)) β)
    (c ⊗ₜ[WittTwo.Ring p k] a) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

omit [PerfectRing k p] in
/-- The SAME ENTIRE original relative residue Frobenius square is derived on EVERY original element. -/
theorem residueFrobenius_naturality (β : A →ₐ[WittTwo.Ring p k] A') (t : T p k A) :
    WittTwoAlgebraDivisionNaturality.residueMap p k β (WittTwoRelativeLift.residueFrobenius p k A t) =
      WittTwoRelativeLift.residueFrobenius p k A' (twistMap p k β t) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul c a =>
    rw [twistMap_tmul, WittTwoRelativeLift.residueFrobenius_tmul,
      WittTwoRelativeLift.residueFrobenius_tmul, map_mul, map_pow,
      WittTwoAlgebraDivisionNaturality.residueMap_tmul,
      WittTwoAlgebraDivisionNaturality.residueMap_tmul, map_one]
  | add t s ht hs => rw [map_add, map_add, map_add, map_add, ht, hs]

variable [Algebra.Smooth (WittTwo.Ring p k) A] [Algebra.Smooth (WittTwo.Ring p k) A']
variable (β : A →ₐ[WittTwo.Ring p k] A')
variable (f g : WittTwoLiftDifference.Lift p k A) (f' g' : WittTwoLiftDifference.Lift p k A')
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable (hg : ∀ t, algebraMap A (B p k A) (g t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable (hf' : ∀ t, algebraMap A' (B p k A') (f' t) = WittTwoRelativeLift.residueFrobenius p k A' t)
variable (hg' : ∀ t, algebraMap A' (B p k A') (g' t) = WittTwoRelativeLift.residueFrobenius p k A' t)
variable (hff' : ∀ t, β (f t) = f' (twistMap p k β t))
variable (hgg' : ∀ t, β (g t) = g' (twistMap p k β t))
include hff' hgg'

omit [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A'] in
/-- Literal actual lifted algebra diagrams DERIVE the SAME actual kernel-difference square. -/
theorem differenceElement_naturality (t : T p k A) :
    WittTwoAlgebraDivisionNaturality.kernelMap p k β
      (WittTwoLiftDifference.differenceElement p k A f g hf hg t) =
    WittTwoLiftDifference.differenceElement p k A' f' g' hf' hg' (twistMap p k β t) := by
  apply Subtype.ext
  change β (f t-g t) = f' (twistMap p k β t)-g' (twistMap p k β t)
  rw [map_sub, hff', hgg']

/-- EVERY original element retains its SAME original divided-difference derivation under the actual map. -/
theorem differenceDerivation_naturality (t : T p k A) :
    WittTwoAlgebraDivisionNaturality.residueMap p k β
      (WittTwoLiftDifference.differenceDerivation p k A f g hf hg t) =
    WittTwoLiftDifference.differenceDerivation p k A' f' g' hf' hg' (twistMap p k β t) := by
  change WittTwoAlgebraDivisionNaturality.residueMap p k β
      (WittTwoAlgebraDivision.dividePrimeLinear p k A
        (WittTwoLiftDifference.differenceElement p k A f g hf hg t)) =
    WittTwoAlgebraDivision.dividePrimeLinear p k A'
      (WittTwoLiftDifference.differenceElement p k A' f' g' hf' hg' (twistMap p k β t))
  rw [← WittTwoAlgebraDivisionNaturality.dividePrime_naturality,
    differenceElement_naturality p k β f g f' g' hf hg hf' hg' hff' hgg']

end EnvelopeProperty.DeligneIllusie.WittTwoLiftDifferenceNaturality
