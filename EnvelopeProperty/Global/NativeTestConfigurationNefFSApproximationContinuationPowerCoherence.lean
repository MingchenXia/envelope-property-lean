import EnvelopeProperty.Global.NativeTestConfigurationNefFSApproximationContinuationTensorComparisons
import EnvelopeProperty.AlgGeom.BundleTensorPowerPullbackCoherence

/-! # Power coherence of the unit-open and product line comparisons

For the power data of `…ContinuationTensorComparisons`,

* `unitOpenLineIso_power_comparisons`: the unit-open comparison of `M^{⊗ n}` built from
  `powerLineActionComparison`, `powerFibreOneComparison` is the canonical power
  `C.unitOpenLinePowerIso M L α e n` of the comparison of `M`;
* `productTotalLineIso_power_comparisons`: the same for the product comparison.

The comparison is derived by nine whole pullback-power coherence squares
(`BundleTensorPowerPullbackCoherence`), before any norm or potential calculation.  This is
the power half of "`φ_{b 𝓛} = b φ_𝓛`" for PL functions of test configurations (FHX §2.3).
-/
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfigurationNefFSPowerCoherence

private theorem square_inverse {D : Type*} [Category D]
    {A B A' B' : D} (a : A ≅ B) (p : A ≅ A') (q : B ≅ B') (a' : A' ≅ B')
    (h : a ≪≫ q = p ≪≫ a') : a.symm ≪≫ p = q ≪≫ a'.symm := by
  have hh := congrArg (fun E => a.symm ≪≫ E ≪≫ a'.symm) h
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id, Iso.trans_refl]
    using hh.symm

private theorem mapped_conjugate_square {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) {A B A' B' : D} {P Q : E}
    (a : A ≅ A') (e : A' ≅ B') (b : B ≅ B') (p : F.obj A' ≅ P) (q : F.obj B' ≅ Q)
    (v : P ≅ Q) (h : F.mapIso e ≪≫ q = p ≪≫ v) :
    F.mapIso (a ≪≫ e ≪≫ b.symm) ≪≫ (F.mapIso b ≪≫ q) =
      (F.mapIso a ≪≫ p) ≪≫ v := by
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc,
    Iso.symm_self_id_assoc]
  rw [h]

/-- The power of a nine-fold composite, in the association pattern of the unit-open
line comparison, is the composite of the powers. -/
private theorem powerIso_nine {X : Scheme.{u}}
    {M₀ M₁ M₂ M₃ M₄ M₅ M₆ M₇ M₈ M₉ : X.Modules}
    (d₀ : M₀ ≅ M₁) (d₁ : M₁ ≅ M₂) (d₂ : M₂ ≅ M₃) (d₃ : M₃ ≅ M₄) (d₄ : M₄ ≅ M₅)
    (d₅ : M₅ ≅ M₆) (d₆ : M₆ ≅ M₇) (d₇ : M₇ ≅ M₈) (d₈ : M₈ ≅ M₉) (n : ℕ) :
    BundleTensorPowerPullback.powerIso
        (d₀ ≪≫ (d₁ ≪≫ d₂ ≪≫ d₃) ≪≫ d₄ ≪≫ d₅ ≪≫ d₆ ≪≫ d₇ ≪≫ d₈) n =
      BundleTensorPowerPullback.powerIso d₀ n ≪≫
        (BundleTensorPowerPullback.powerIso d₁ n ≪≫ BundleTensorPowerPullback.powerIso d₂ n ≪≫
          BundleTensorPowerPullback.powerIso d₃ n) ≪≫
        BundleTensorPowerPullback.powerIso d₄ n ≪≫ BundleTensorPowerPullback.powerIso d₅ n ≪≫
        BundleTensorPowerPullback.powerIso d₆ n ≪≫ BundleTensorPowerPullback.powerIso d₇ n ≪≫
        BundleTensorPowerPullback.powerIso d₈ n := by
  simp only [BundleTensorPowerPullbackCoherence.powerIso_trans]

end EnvelopeProperty.NativeTestConfigurationNefFSPowerCoherence

namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open CanonicalGeometry BundleTensorPowerPullback BundleTensorPowerPullbackCoherence
open NativeTestConfigurationNefFSPowerCoherence NativeTestConfigurationNefFSTensorComparisons
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : TestConfiguration k X) (M : C.total.Modules) (L : X.left.Modules)
    (alpha : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e : (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L)

/-- The internally constructed original power action and fibre-one data give
the actual canonical whole power of the SAME original unit-open comparison. -/
theorem unitOpenLineIso_power_comparisons (n : ℕ) :
    C.unitOpenLineIso (bundleTensorPower M n) (bundleTensorPower L n)
      (C.powerLineActionComparison M alpha n) (C.powerFibreOneComparison M L e n) =
        C.unitOpenLinePowerIso M L alpha e n := by
  let a := C.unitOpenActionLift.left
  let g := C.lineActionMap
  let h := C.lineProjectionMap
  let v := C.unitOpenInclusion.left
  let z := C.unitOpenFibreProjection.left
  let i := C.fibreOneInclusion.left
  let j := C.fibreOneIso.hom.left
  let w := C.unitOpenOriginalProjection.left
  let h0 := C.lineActionLift_action.symm
  let h4 := C.lineActionLift_projection
  let h8 := C.lineActionLift_original
  let d0 := (pullbackCongr h0).app M
  let d1 := ((pullbackComp a g).app M).symm
  let d2 := (pullback a).mapIso alpha
  let d3 := (pullbackComp a h).app M
  let d4 := (pullbackCongr h4).app M
  let d5 := ((pullbackComp z i).app M).symm
  let d6 := (pullback z).mapIso e
  let d7 := (pullbackComp z j).app L
  let d8 := (pullbackCongr h8).app L
  let D0 := (pullbackCongr h0).app (bundleTensorPower M n)
  let D1 := ((pullbackComp a g).app (bundleTensorPower M n)).symm
  let D2 := (pullback a).mapIso (C.powerLineActionComparison M alpha n)
  let D3 := (pullbackComp a h).app (bundleTensorPower M n)
  let D4 := (pullbackCongr h4).app (bundleTensorPower M n)
  let D5 := ((pullbackComp z i).app (bundleTensorPower M n)).symm
  let D6 := (pullback z).mapIso (C.powerFibreOneComparison M L e n)
  let D7 := (pullbackComp z j).app (bundleTensorPower L n)
  let D8 := (pullbackCongr h8).app (bundleTensorPower L n)
  let p0 := pullbackIso v M n
  let p1 := pullbackIso (a ≫ g) M n
  let p2 := (pullback a).mapIso (pullbackIso g M n) ≪≫
    pullbackIso a ((pullback g).obj M) n
  let p3 := (pullback a).mapIso (pullbackIso h M n) ≪≫
    pullbackIso a ((pullback h).obj M) n
  let p4 := pullbackIso (a ≫ h) M n
  let p5 := pullbackIso (z ≫ i) M n
  let p6 := (pullback z).mapIso (pullbackIso i M n) ≪≫
    pullbackIso z ((pullback i).obj M) n
  let p7 := (pullback z).mapIso (pullbackIso j L n) ≪≫
    pullbackIso z ((pullback j).obj L) n
  let p8 := pullbackIso (z ≫ j) L n
  let p9 := pullbackIso w L n
  have s0 : D0 ≪≫ p1 = p0 ≪≫ powerIso d0 n := pullbackIso_congr h0 M n
  have s1 : D1 ≪≫ p2 = p1 ≪≫ powerIso d1 n := by
    have hh := square_inverse ((pullbackComp a g).app (bundleTensorPower M n))
      p2 p1 (powerIso ((pullbackComp a g).app M) n) (pullbackIso_comp a g M n).symm
    exact hh.trans (congrArg (fun E => p1 ≪≫ E)
      (powerIso_symm ((pullbackComp a g).app M) n).symm)
  have s2 : D2 ≪≫ p3 = p2 ≪≫ powerIso d2 n :=
    mapped_conjugate_square (pullback a) (pullbackIso g M n) (powerIso alpha n)
      (pullbackIso h M n) (pullbackIso a ((pullback g).obj M) n)
      (pullbackIso a ((pullback h).obj M) n)
      (powerIso ((pullback a).mapIso alpha) n) (pullbackIso_naturality a alpha n)
  have s3 : D3 ≪≫ p4 = p3 ≪≫ powerIso d3 n := (pullbackIso_comp a h M n).symm
  have s4 : D4 ≪≫ p5 = p4 ≪≫ powerIso d4 n := pullbackIso_congr h4 M n
  have s5 : D5 ≪≫ p6 = p5 ≪≫ powerIso d5 n := by
    have hh := square_inverse ((pullbackComp z i).app (bundleTensorPower M n))
      p6 p5 (powerIso ((pullbackComp z i).app M) n) (pullbackIso_comp z i M n).symm
    exact hh.trans (congrArg (fun E => p5 ≪≫ E)
      (powerIso_symm ((pullbackComp z i).app M) n).symm)
  have s6 : D6 ≪≫ p7 = p6 ≪≫ powerIso d6 n :=
    mapped_conjugate_square (pullback z) (pullbackIso i M n) (powerIso e n)
      (pullbackIso j L n) (pullbackIso z ((pullback i).obj M) n)
      (pullbackIso z ((pullback j).obj L) n)
      (powerIso ((pullback z).mapIso e) n) (pullbackIso_naturality z e n)
  have s7 : D7 ≪≫ p8 = p7 ≪≫ powerIso d7 n := (pullbackIso_comp z j L n).symm
  have s8 : D8 ≪≫ p9 = p8 ≪≫ powerIso d8 n := pullbackIso_congr h8 L n
  have ht :
      C.unitOpenLineIso (bundleTensorPower M n) (bundleTensorPower L n)
          (C.powerLineActionComparison M alpha n) (C.powerFibreOneComparison M L e n) ≪≫
        pullbackIso w L n =
      pullbackIso v M n ≪≫ powerIso (C.unitOpenLineIso M L alpha e) n := by
    change (D0 ≪≫ (D1 ≪≫ D2 ≪≫ D3) ≪≫ D4 ≪≫ D5 ≪≫ D6 ≪≫ D7 ≪≫ D8) ≪≫ p9 =
      p0 ≪≫ powerIso (d0 ≪≫ (d1 ≪≫ d2 ≪≫ d3) ≪≫ d4 ≪≫ d5 ≪≫ d6 ≪≫ d7 ≪≫ d8) n
    exact (isoSquare_nine s0 s1 s2 s3 s4 s5 s6 s7 s8).trans
      (congrArg (fun E => p0 ≪≫ E) (powerIso_nine d0 d1 d2 d3 d4 d5 d6 d7 d8 n).symm)
  exact (isoCancelRight ht).trans (Iso.trans_assoc _ _ _)

/-- The same internally constructed power data give the actual canonical
whole product power comparison, preserving the original action and fibre one. -/
theorem productTotalLineIso_power_comparisons (n : ℕ) :
    C.productTotalLineIso (bundleTensorPower M n) (bundleTensorPower L n)
      (C.powerLineActionComparison M alpha n) (C.powerFibreOneComparison M L e n) =
        C.productTotalLinePowerIso M L alpha e n := by
  exact congrArg (fun E => ((pullbackComp C.unitOpenIso.inv.left C.unitOpenInclusion.left).app
      (bundleTensorPower M n)).symm ≪≫ (pullback C.unitOpenIso.inv.left).mapIso E ≪≫
      (pullbackComp C.unitOpenIso.inv.left C.unitOpenOriginalProjection.left).app
        (bundleTensorPower L n) ≪≫
      (pullbackCongr C.unitOpenIso_inv_originalProjection).app (bundleTensorPower L n))
    (C.unitOpenLineIso_power_comparisons M L alpha e n)

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
