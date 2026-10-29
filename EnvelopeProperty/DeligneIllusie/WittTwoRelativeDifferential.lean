import EnvelopeProperty.DeligneIllusie.WittTwoRelativeLift
import EnvelopeProperty.Algebra.KaehlerBaseRingEquivalence

/-!
# Witt Two Relative Differential

Actual full relative lifted differential on the original Witt-twisted algebra. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

namespace EnvelopeProperty.DeligneIllusie.WittTwoRelativeDifferential

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoRelativeLift.residueCopyAlgebra

variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A]

private abbrev T := WittTwoRelativeLift.TwistAlgebra p k A
private abbrev B := WittTwoSmoothDifferentials.ResidueAlgebra p k A

/-- The actual copied coefficient base gives an actual original Kähler equivalence. -/
def copiedBaseEquiv :
    letI := WittTwoRelativeLift.copyAlgebra p k A
    KaehlerDifferential (ULift.{0} (WittTwo.Ring p k)) A ≃ₗ[A]
      KaehlerDifferential (WittTwo.Ring p k) A := by
  letI := WittTwoRelativeLift.copyAlgebra p k A
  exact KaehlerBaseRingEquivalence.equiv ULift.ringEquiv (fun _ => rfl)

omit [CharP k p] [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A] in
/-- The SAME copied-base equivalence retains every original universal differential. -/
theorem copiedBaseEquiv_D (a : A) :
    letI := WittTwoRelativeLift.copyAlgebra p k A
    copiedBaseEquiv p k A (KaehlerDifferential.D (ULift.{0} (WittTwo.Ring p k)) A a) =
      KaehlerDifferential.D (WittTwo.Ring p k) A a := by
  let := WittTwoRelativeLift.copyAlgebra p k A
  exact KaehlerBaseRingEquivalence.equiv_D ULift.ringEquiv (fun _ => rfl) a

/-- The SAME constructed actual relative lift as its whole original ring map. -/
def liftRingMap : T p k A →+* A := by
  letI := WittTwoRelativeLift.copyAlgebra p k A
  exact (WittTwoRelativeLift.relativeLift p k A).toRingHom

/-- The original target algebra structure is induced by this SAME actual lifted ring map. -/
@[instance_reducible] def liftAlgebra : Algebra (T p k A) A := (liftRingMap p k A).toAlgebra

attribute [local instance] liftAlgebra

/-- The SAME underlying original lift still has its actual whole relative Frobenius reduction. -/
theorem liftRingMap_reduction (z : T p k A) :
    ((1 : k) ⊗ₜ[WittTwo.Ring p k] (liftRingMap p k A z)) =
      WittTwoRelativeLift.residueFrobenius p k A z := by
  let := WittTwoRelativeLift.copyAlgebra p k A
  exact AlgHom.congr_fun (WittTwoRelativeLift.relativeLift_reduction p k A) z

/-- The actual whole lifted differential takes values in the SAME original W2 Kähler module. -/
def liftDifferential : KaehlerDifferential (ULift.{0} (WittTwo.Ring p k)) (T p k A) →ₗ[T p k A]
    KaehlerDifferential (WittTwo.Ring p k) A := by
  letI := WittTwoRelativeLift.copyAlgebra p k A
  letI : SMul (ULift.{0} (WittTwo.Ring p k)) (ULift.{0} (WittTwo.Ring p k)) :=
    (Algebra.id (ULift.{0} (WittTwo.Ring p k))).toSMul
  letI : Module (ULift.{0} (WittTwo.Ring p k)) (ULift.{0} (WittTwo.Ring p k)) :=
    (Algebra.id (ULift.{0} (WittTwo.Ring p k))).toModule
  let aT : Algebra (ULift.{0} (WittTwo.Ring p k)) (T p k A) :=
    Algebra.TensorProduct.leftAlgebra
  letI : SMul (ULift.{0} (WittTwo.Ring p k)) (T p k A) := aT.toSMul
  letI : Module (ULift.{0} (WittTwo.Ring p k)) (T p k A) := aT.toModule
  letI : SMul (ULift.{0} (WittTwo.Ring p k)) A :=
    (WittTwoRelativeLift.copyAlgebra p k A).toSMul
  letI : Module (ULift.{0} (WittTwo.Ring p k)) A :=
    (WittTwoRelativeLift.copyAlgebra p k A).toModule
  letI : IsScalarTower (ULift.{0} (WittTwo.Ring p k)) (ULift.{0} (WittTwo.Ring p k)) A :=
    ⟨fun r s a => by
      change algebraMap (WittTwo.Ring p k) A (r.down * s.down) * a =
        algebraMap (WittTwo.Ring p k) A r.down * (algebraMap (WittTwo.Ring p k) A s.down * a)
      rw [map_mul, mul_assoc]⟩
  letI : IsScalarTower (ULift.{0} (WittTwo.Ring p k)) (T p k A) A :=
    IsScalarTower.of_algebraMap_eq (fun r =>
      (WittTwoRelativeLift.relativeLift p k A).commutes r |>.symm)
  exact ((copiedBaseEquiv p k A).toLinearMap.restrictScalars (T p k A)).comp
    (KaehlerDifferential.map (ULift.{0} (WittTwo.Ring p k)) (ULift.{0} (WittTwo.Ring p k))
      (T p k A) A)

/-- Every original universal source differential has the SAME actual lifted differential value. -/
theorem liftDifferential_D (z : T p k A) :
    liftDifferential p k A (KaehlerDifferential.D (ULift.{0} (WittTwo.Ring p k)) (T p k A) z) =
      KaehlerDifferential.D (WittTwo.Ring p k) A (liftRingMap p k A z) := by
  let := WittTwoRelativeLift.copyAlgebra p k A
  unfold liftDifferential
  rw [LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    KaehlerDifferential.map_D]
  exact copiedBaseEquiv_D p k A (liftRingMap p k A z)

omit [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A] in
private theorem prime_power_differential_zero (b : B p k A) :
    KaehlerDifferential.D k (B p k A) (b ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]

omit [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A] in
/-- The ENTIRE actual residue relative Frobenius has zero original differential. -/
theorem residueFrobenius_differential_zero (z : T p k A) :
    KaehlerDifferential.D k (B p k A) (WittTwoRelativeLift.residueFrobenius p k A z) = 0 := by
  let r : T p k A →+* B p k A := (WittTwoRelativeLift.residueFrobenius p k A).toRingHom
  change KaehlerDifferential.D k (B p k A) (r z) = 0
  induction z using TensorProduct.induction_on with
  | zero => rw [r.map_zero, (KaehlerDifferential.D k (B p k A)).map_zero]
  | add z w hz hw =>
    rw [r.map_add, (KaehlerDifferential.D k (B p k A)).map_add, hz, hw, add_zero]
  | tmul w a =>
    change KaehlerDifferential.D k (B p k A)
      (WittTwoRelativeLift.residueFrobenius p k A (w ⊗ₜ[WittTwo.Ring p k] a)) = 0
    rw [WittTwoRelativeLift.residueFrobenius_tmul, Derivation.leibniz,
      prime_power_differential_zero, smul_zero, zero_add]
    change (((1 : k) ⊗ₜ[WittTwo.Ring p k] a) ^ p) •
      KaehlerDifferential.D k (B p k A) (algebraMap k (B p k A) (WittTwo.reduction p k w.down)) = 0
    rw [Derivation.map_algebraMap, smul_zero]

private theorem reduction_liftDifferential_D (z : T p k A) :
    WittTwoSmoothDifferentials.reductionDifferential p k A
      (liftDifferential p k A (KaehlerDifferential.D (ULift.{0} (WittTwo.Ring p k)) (T p k A) z)) = 0 := by
  rw [liftDifferential_D]
  change KaehlerDifferential.map (WittTwo.Ring p k) k A (B p k A)
    (KaehlerDifferential.D (WittTwo.Ring p k) A (liftRingMap p k A z)) = 0
  rw [KaehlerDifferential.map_D]
  change KaehlerDifferential.D k (B p k A) (((1 : k) ⊗ₜ[WittTwo.Ring p k] liftRingMap p k A z)) = 0
  rw [liftRingMap_reduction]
  exact residueFrobenius_differential_zero p k A z

/-- The WHOLE actual original lifted differential is genuinely in the SAME original prime image. -/
theorem liftDifferential_prime_image
    (w : KaehlerDifferential (ULift.{0} (WittTwo.Ring p k)) (T p k A)) :
    ∃ z : KaehlerDifferential (WittTwo.Ring p k) A,
      liftDifferential p k A w = (p : WittTwo.Ring p k) • z := by
  have hw : w ∈ Submodule.span (T p k A)
      (Set.range (KaehlerDifferential.D (ULift.{0} (WittTwo.Ring p k)) (T p k A))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  have hz : WittTwoSmoothDifferentials.reductionDifferential p k A (liftDifferential p k A w) = 0 := by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      exact reduction_liftDifferential_D p k A z
    | zero => rw [map_zero, map_zero]
    | add x y hx hy ihx ihy => rw [map_add, map_add, ihx, ihy, add_zero]
    | smul a x hx ih =>
      rw [map_smul]
      change KaehlerDifferential.map (WittTwo.Ring p k) k A (B p k A)
        (liftRingMap p k A a • liftDifferential p k A x) = 0
      rw [map_smul]
      change liftRingMap p k A a • WittTwoSmoothDifferentials.reductionDifferential p k A
        (liftDifferential p k A x) = 0
      rw [ih, smul_zero]
  exact (WittTwoSmoothDifferentials.reductionDifferential_eq_zero_iff p k A _).mp hz

end EnvelopeProperty.DeligneIllusie.WittTwoRelativeDifferential
