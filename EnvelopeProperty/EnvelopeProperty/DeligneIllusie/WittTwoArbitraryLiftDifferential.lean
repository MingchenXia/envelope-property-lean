import EnvelopeProperty.DeligneIllusie.WittTwoLiftDifference
import EnvelopeProperty.DeligneIllusie.WittTwoDividedLift

/-! The genuine entire divided differential for every actual relative Frobenius lift. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

namespace EnvelopeProperty.DeligneIllusie.WittTwoArbitraryLiftDifferential
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoRelativeLift.residueCopyAlgebra WittTwoLiftDifference.frobeniusAlgebra
  WittTwoLiftDifference.sourceBaseSMul WittTwoLiftDifference.sourceBaseModule
  WittTwoLiftDifference.residueBaseSMul WittTwoLiftDifference.residueBaseModule
  WittTwoLiftDifference.residueBaseTower WittTwoSmoothDifferentials.differentials_flat
variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A]
private abbrev W' := ULift.{0} (WittTwo.Ring p k)
private abbrev T := WittTwoRelativeLift.TwistAlgebra p k A
private abbrev B := WittTwoSmoothDifferentials.ResidueAlgebra p k A
private abbrev M := KaehlerDifferential (WittTwo.Ring p k) A
private abbrev N := KaehlerDifferential k (B p k A)
variable (f : WittTwoLiftDifference.Lift p k A)
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)

/-- Actual native universal differentiation of EVERY lifted function lies in the original prime image. -/
def primeDifferential (t : T p k A) : WittTwoDividedLift.primeForms p k A :=
  ⟨KaehlerDifferential.D (WittTwo.Ring p k) A (f t), by
    have hz : WittTwoSmoothDifferentials.reductionDifferential p k A
        (KaehlerDifferential.D (WittTwo.Ring p k) A (f t)) = 0 := by
      change KaehlerDifferential.map (WittTwo.Ring p k) k A (B p k A)
        (KaehlerDifferential.D (WittTwo.Ring p k) A (f t)) = 0
      rw [KaehlerDifferential.map_D, hf t]
      exact WittTwoRelativeDifferential.residueFrobenius_differential_zero p k A t
    obtain ⟨z, hz⟩ := (WittTwoSmoothDifferentials.reductionDifferential_eq_zero_iff p k A _).mp hz
    refine ⟨z, ?_⟩
    change (p : A) • z = KaehlerDifferential.D (WittTwo.Ring p k) A (f t)
    simpa only [Nat.cast_smul_eq_nsmul] using hz.symm⟩

private theorem primeDifferential_add (s t : T p k A) :
    primeDifferential p k A f hf (s+t) =
      primeDifferential p k A f hf s + primeDifferential p k A f hf t := by
  apply Subtype.ext
  change KaehlerDifferential.D (WittTwo.Ring p k) A (f (s+t)) = _
  rw [map_add, map_add]
  rfl

private theorem primeDifferential_smul (w : W' p k) (t : T p k A) :
    primeDifferential p k A f hf (w • t) =
      algebraMap (WittTwo.Ring p k) A w.down • primeDifferential p k A f hf t := by
  let := WittTwoRelativeLift.copyAlgebra p k A
  apply Subtype.ext
  change KaehlerDifferential.D (WittTwo.Ring p k) A (f (w • t)) =
    algebraMap (WittTwo.Ring p k) A w.down • KaehlerDifferential.D (WittTwo.Ring p k) A (f t)
  rw [Algebra.smul_def w t, map_mul, f.commutes]
  change KaehlerDifferential.D (WittTwo.Ring p k) A
    (algebraMap (WittTwo.Ring p k) A w.down * f t) = _
  rw [Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero]

private theorem primeDifferential_mul (s t : T p k A) :
    primeDifferential p k A f hf (s*t) =
      f s • primeDifferential p k A f hf t + f t • primeDifferential p k A f hf s := by
  apply Subtype.ext
  change KaehlerDifferential.D (WittTwo.Ring p k) A (f (s*t)) = _
  rw [map_mul, Derivation.leibniz]
  rfl

private def dividedFunction (t : T p k A) : N p k A :=
  WittTwoDividedLift.divisionLinear p k A (primeDifferential p k A f hf t)

local instance residueFormBaseSMul : SMul (W' p k) (N p k A) :=
  (Module.compHom (N p k A) (algebraMap (W' p k) (B p k A))).toSMul
local instance residueFormBaseModule : Module (W' p k) (N p k A) :=
  Module.compHom (N p k A) (algebraMap (W' p k) (B p k A))
local instance residueFormBaseTower : IsScalarTower (W' p k) (B p k A) (N p k A) :=
  ⟨fun w b z => by
    change (algebraMap (W' p k) (B p k A) w * b) • z =
      algebraMap (W' p k) (B p k A) w • (b • z)
    exact mul_smul _ _ _⟩
local instance residueFormSourceTower : IsScalarTower (W' p k) (T p k A) (N p k A) :=
  ⟨fun w t z => by
    rw [← IsScalarTower.algebraMap_smul (B p k A) (w • t),
      ← IsScalarTower.algebraMap_smul (B p k A) t]
    change algebraMap (T p k A) (B p k A) (w • t) • z =
      algebraMap (W' p k) (B p k A) w • (algebraMap (T p k A) (B p k A) t • z)
    rw [← mul_smul]
    congr 1
    rw [Algebra.smul_def w t, map_mul]
    exact congrArg (fun b => b * algebraMap (T p k A) (B p k A) t)
      ((WittTwoRelativeLift.residueFrobenius p k A).commutes w)⟩

private def dividedBaseLinear : T p k A →ₗ[W' p k] N p k A where
  toFun := dividedFunction p k A f hf
  map_add' s t := by unfold dividedFunction; rw [primeDifferential_add, map_add]
  map_smul' w t := by
    let := WittTwoRelativeLift.copyAlgebra p k A
    unfold dividedFunction
    rw [primeDifferential_smul, map_smul]
    simp only [RingHom.id_apply]
    rw [← IsScalarTower.algebraMap_smul (B p k A)
      (algebraMap (WittTwo.Ring p k) A w.down),
      ← IsScalarTower.algebraMap_smul (B p k A) w]
    have hc := (WittTwoRelativeLift.reductionMap p k A).commutes w
    have hc' : algebraMap A (B p k A) (algebraMap (WittTwo.Ring p k) A w.down) =
        algebraMap (W' p k) (B p k A) w := hc
    rw [hc']

/-- Canonical division of actual native lifted universal differentiation is a genuine relative derivation. -/
def dividedDerivation : Derivation (W' p k) (T p k A) (N p k A) :=
  Derivation.mk' (dividedBaseLinear p k A f hf) (by
    intro s t
    change dividedFunction p k A f hf (s*t) =
      s • dividedFunction p k A f hf t + t • dividedFunction p k A f hf s
    unfold dividedFunction
    rw [primeDifferential_mul, map_add, map_smul, map_smul]
    rw [← IsScalarTower.algebraMap_smul (B p k A) (f s),
      ← IsScalarTower.algebraMap_smul (B p k A) (f t),
      ← IsScalarTower.algebraMap_smul (B p k A) s,
      ← IsScalarTower.algebraMap_smul (B p k A) t]
    rw [hf s, hf t]
    rfl)

/-- The genuine WHOLE native divided differential of the actual original relative lift. -/
def dividedDifferential : KaehlerDifferential (W' p k) (T p k A) →ₗ[T p k A] N p k A :=
  (dividedDerivation p k A f hf).liftKaehlerDifferential

/-- EVERY original universal source differential has its SAME actual divided native value. -/
theorem dividedDifferential_D (t : T p k A) :
    dividedDifferential p k A f hf (KaehlerDifferential.D (W' p k) (T p k A) t) =
      dividedDerivation p k A f hf t :=
  Derivation.liftKaehlerDifferential_comp_D _ t

/-- Every original prime expression for lifted universal differentiation retains its actual reduction. -/
theorem dividedDifferential_prime (t : T p k A) (z : M p k A)
    (h : KaehlerDifferential.D (WittTwo.Ring p k) A (f t) = (p : WittTwo.Ring p k) • z) :
    dividedDifferential p k A f hf (KaehlerDifferential.D (W' p k) (T p k A) t) =
      KaehlerDifferential.map (WittTwo.Ring p k) k A (B p k A) z := by
  rw [dividedDifferential_D]
  have he : primeDifferential p k A f hf t = WittTwoDividedLift.primeForm p k A z := by
    apply Subtype.ext
    change KaehlerDifferential.D (WittTwo.Ring p k) A (f t) = (p : A) • z
    simpa only [Nat.cast_smul_eq_nsmul] using h
  change WittTwoDividedLift.divisionLinear p k A (primeDifferential p k A f hf t) = _
  rw [he, WittTwoDividedLift.divisionLinear_primeForm]

/-- The SAME actual relative Frobenius lift produced by original smooth infinitesimal lifting. -/
def producedLift : WittTwoLiftDifference.Lift p k A := by
  letI := WittTwoRelativeLift.copyAlgebra p k A
  exact WittTwoRelativeLift.relativeLift p k A

/-- Its actual entire residue identity supplies its defining relative Frobenius lift condition. -/
theorem producedLift_reduction (t : T p k A) :
    algebraMap A (B p k A) (producedLift p k A t) = WittTwoRelativeLift.residueFrobenius p k A t := by
  let := WittTwoRelativeLift.copyAlgebra p k A
  exact AlgHom.congr_fun (WittTwoRelativeLift.relativeLift_reduction p k A) t

private theorem originalDivided_smul (t : T p k A)
    (w : KaehlerDifferential (W' p k) (T p k A)) :
    WittTwoDividedLift.dividedLiftDifferential p k A (t • w) =
      algebraMap A (B p k A) (producedLift p k A t) •
        WittTwoDividedLift.dividedLiftDifferential p k A w := by
  let := WittTwoDividedLift.residueLiftAlgebra p k A
  have hs := (WittTwoDividedLift.dividedLiftDifferential p k A).map_smul t w
  exact hs.trans (IsScalarTower.algebraMap_smul (B p k A) t _).symm

private theorem produced_D_comparison (t : T p k A) :
    dividedDifferential p k A (producedLift p k A) (producedLift_reduction p k A)
      (KaehlerDifferential.D (W' p k) (T p k A) t) =
    WittTwoDividedLift.dividedLiftDifferential p k A
      (KaehlerDifferential.D (W' p k) (T p k A) t) := by
  rw [dividedDifferential_D]
  have he : primeDifferential p k A (producedLift p k A) (producedLift_reduction p k A) t =
      WittTwoDividedLift.liftPrimeFormsMap p k A (KaehlerDifferential.D (W' p k) (T p k A) t) := by
    apply Subtype.ext
    change KaehlerDifferential.D (WittTwo.Ring p k) A (producedLift p k A t) =
      WittTwoRelativeDifferential.liftDifferential p k A (KaehlerDifferential.D (W' p k) (T p k A) t)
    rw [WittTwoRelativeDifferential.liftDifferential_D]
    rfl
  change WittTwoDividedLift.divisionLinear p k A
    (primeDifferential p k A (producedLift p k A) (producedLift_reduction p k A) t) = _
  unfold WittTwoDividedLift.dividedLiftDifferential
  rw [LinearMap.comp_apply, LinearMap.coe_restrictScalars]
  exact congrArg (WittTwoDividedLift.divisionLinear p k A) he

/-- The SAME actual produced-lift whole map equals the PRE-EXISTING original whole divided map on EVERY form. -/
theorem dividedDifferential_produced (w : KaehlerDifferential (W' p k) (T p k A)) :
    dividedDifferential p k A (producedLift p k A) (producedLift_reduction p k A) w =
      WittTwoDividedLift.dividedLiftDifferential p k A w := by
  have hw : w ∈ Submodule.span (T p k A)
      (Set.range (KaehlerDifferential.D (W' p k) (T p k A))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    exact produced_D_comparison p k A t
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul t x _ hx =>
    rw [map_smul, originalDivided_smul, hx, producedLift_reduction]
    exact IsScalarTower.algebraMap_smul (B p k A) t _ |>.symm

end EnvelopeProperty.DeligneIllusie.WittTwoArbitraryLiftDifferential
