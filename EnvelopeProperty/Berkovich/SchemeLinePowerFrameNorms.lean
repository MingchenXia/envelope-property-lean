import EnvelopeProperty.AlgGeom.SchemeTensorPowerFrames
import EnvelopeProperty.Berkovich.SchemeLineModelTensorNorms

/-! # Actual generic power frames and true original proper-model norm coherence -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
open scoped NNReal
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeLinePowerFrameNorms
open CanonicalGeometry SchemeModuleFrameCoefficients SchemeTensorPowerFrames RelativeSchemeValuedPoint
open SchemeResidueFrameComparison SchemeResidueFrameTransition
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance {X Y : Scheme.{u}} (g : X ⟶ Y) : (pullback g).Monoidal :=
  Scheme.Modules.pullbackMonoidal g
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} {p : X ⟶ Spec (.of R)} (y : RelativeSchemeValuedPoint v p)

/-- The actual native tensorator and true explicit tensor comparison give an entire original generic tensor frame. -/
def genericTensorFrame {M N : X.Modules}
    (e : genericLineModule y M ≅ unitObj (Spec (X.residueField y.1.point)))
    (d : genericLineModule y N ≅ unitObj (Spec (X.residueField y.1.point))) :
    genericLineModule y (Scheme.Modules.tensorObj M N) ≅ unitObj (Spec (X.residueField y.1.point)) :=
  (pullback (X.fromSpecResidueField y.1.point)).mapIso (ModularCurves.monoidalTensorObjIso M N).symm ≪≫
    (Functor.Monoidal.μIso (pullback (X.fromSpecResidueField y.1.point)) M N).symm ≪≫
      tensorFrame e d

/-- Its actual inverse unit section is exactly the true native generic tensor of original units. -/
theorem genericTensorFrame_unitSection {M N : X.Modules}
    (e : genericLineModule y M ≅ unitObj (Spec (X.residueField y.1.point)))
    (d : genericLineModule y N ≅ unitObj (Spec (X.residueField y.1.point))) :
    unitSection (genericTensorFrame y e d) = genericTensorSection y (unitSection e) (unitSection d) := by
  have hu := unitSection_precompIso
    (Functor.Monoidal.μIso (pullback (X.fromSpecResidueField y.1.point)) M N).symm (tensorFrame e d)
  have ht := congrArg (fun z =>
    (Functor.Monoidal.μIso (pullback (X.fromSpecResidueField y.1.point)) M N).hom.app ⊤ z)
    (tensorFrame_unitSection e d)
  have hp := unitSection_precompIso
    ((pullback (X.fromSpecResidueField y.1.point)).mapIso (ModularCurves.monoidalTensorObjIso M N).symm)
    ((Functor.Monoidal.μIso (pullback (X.fromSpecResidueField y.1.point)) M N).symm ≪≫ tensorFrame e d)
  exact hp.trans (congrArg (fun z =>
    ((pullback (X.fromSpecResidueField y.1.point)).map (ModularCurves.monoidalTensorObjIso M N).hom).app ⊤ z)
    (hu.trans ht))

/-- The actual generic original explicit tensor powers have genuinely compatible entire native frames. -/
def genericPowerFrame {M : X.Modules}
    (e : genericLineModule y M ≅ unitObj (Spec (X.residueField y.1.point))) :
    (n : ℕ) → genericLineModule y (bundleTensorPower M n) ≅ unitObj (Spec (X.residueField y.1.point))
  | 0 => pullbackUnitIso (X.fromSpecResidueField y.1.point)
  | n + 1 => genericTensorFrame y (genericPowerFrame e n) e

/-- Each actual inverse power-frame unit is the actual previous generic unit tensored with the original one. -/
theorem genericPowerFrame_unitSection_succ {M : X.Modules}
    (e : genericLineModule y M ≅ unitObj (Spec (X.residueField y.1.point))) (n : ℕ) :
    unitSection (genericPowerFrame y e (n + 1)) =
      genericTensorSection y (unitSection (genericPowerFrame y e n)) (unitSection e) :=
  genericTensorFrame_unitSection y (genericPowerFrame y e n) e

/-- The ACTUAL native generic power-frame transition unit is the original degree-one unit to that power. -/
theorem transitionUnit_genericPowerFrame {M : X.Modules}
    (e₀ e₁ : genericLineModule y M ≅ unitObj (Spec (X.residueField y.1.point))) (n : ℕ) :
    transitionUnit (genericPowerFrame y e₀ n) (genericPowerFrame y e₁ n) = transitionUnit e₀ e₁ ^ n := by
  induction n with
  | zero =>
    exact (transitionUnit_self (pullbackUnitIso (X.fromSpecResidueField y.1.point))).trans (pow_zero _).symm
  | succ n ih =>
    have h₀ := transitionUnit_precompIso
      ((pullback (X.fromSpecResidueField y.1.point)).mapIso
        (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).symm)
      ((Functor.Monoidal.μIso (pullback (X.fromSpecResidueField y.1.point)) (bundleTensorPower M n) M).symm ≪≫
        tensorFrame (genericPowerFrame y e₀ n) e₀)
      ((Functor.Monoidal.μIso (pullback (X.fromSpecResidueField y.1.point)) (bundleTensorPower M n) M).symm ≪≫
        tensorFrame (genericPowerFrame y e₁ n) e₁)
    have h₁ := transitionUnit_precompIso
      (Functor.Monoidal.μIso (pullback (X.fromSpecResidueField y.1.point)) (bundleTensorPower M n) M).symm
      (tensorFrame (genericPowerFrame y e₀ n) e₀) (tensorFrame (genericPowerFrame y e₁ n) e₁)
    have ht := transitionUnit_tensorFrame (genericPowerFrame y e₀ n) (genericPowerFrame y e₁ n) e₀ e₁
    have hp := congrArg (fun u => u * transitionUnit e₀ e₁) ih
    exact h₀.trans (h₁.trans (ht.trans (hp.trans (pow_succ _ _).symm)))

/-- Every actual residue valuation derives c_n=c_1^n for the actual compatible native power frames. -/
theorem transitionUnit_genericPowerFrame_value {M : X.Modules}
    (e₀ e₁ : genericLineModule y M ≅ unitObj (Spec (X.residueField y.1.point)))
    (ν : Valuation (X.residueField y.1.point) ℝ≥0) (n : ℕ) :
    ν (transitionUnit (genericPowerFrame y e₀ n) (genericPowerFrame y e₁ n)).val =
      ν (transitionUnit e₀ e₁).val ^ n := by
  have h := congrArg (fun u => ν (Units.val u)) (transitionUnit_genericPowerFrame y e₀ e₁ n)
  exact h.trans (ν.map_pow _ n)

section Norm
variable [IsProper p] (hb : ∀ r, v r ≤ 1)

/-- True original proper-model norms multiply on the actual entire generic tensor-frame units. -/
theorem modelLineNorm_genericTensorFrame_unitSection {M N : X.Modules}
    (hM : IsInvertible M) (hN : IsInvertible N)
    (e : genericLineModule y M ≅ unitObj (Spec (X.residueField y.1.point)))
    (d : genericLineModule y N ≅ unitObj (Spec (X.residueField y.1.point))) :
    modelLineNorm hb y (hM.tensorObj hN) (unitSection (genericTensorFrame y e d)) =
      modelLineNorm hb y hM (unitSection e) * modelLineNorm hb y hN (unitSection d) :=
  (congrArg (modelLineNorm hb y (hM.tensorObj hN)) (genericTensorFrame_unitSection y e d)).trans
    (modelLineNorm_genericTensorSection hb y hM hN (unitSection e) (unitSection d))
/-- The TRUE proper-model inverse-unit norm of actual compatible original generic power frames is the degree-one norm to that power. -/
theorem modelLineNorm_genericPowerFrame_unitSection {M : X.Modules} (hM : IsInvertible M)
    (e : genericLineModule y M ≅ unitObj (Spec (X.residueField y.1.point))) (n : ℕ) :
    modelLineNorm hb y (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n)
        (unitSection (genericPowerFrame y e n)) = modelLineNorm hb y hM (unitSection e) ^ n := by
  induction n with
  | zero =>
    have hm : modelLineNorm hb y (isInvertible_unit (X := X))
        (unitSection (pullbackUnitIso (X.fromSpecResidueField y.1.point))) = 1 := by
      refine (modelLineNorm_unit hb y _).trans ?_
      change y.1.residueVal ((Scheme.ΓSpecIso (X.residueField y.1.point)).hom
        (coefficient (pullbackUnitIso (X.fromSpecResidueField y.1.point))
          (unitSection (pullbackUnitIso (X.fromSpecResidueField y.1.point))))) = 1
      rw [coefficient_unitSection, map_one, map_one]
    exact hm.trans (pow_zero _).symm
  | succ n ih =>
    have ht := modelLineNorm_genericTensorFrame_unitSection y hb
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n) hM (genericPowerFrame y e n) e
    have hp := congrArg (fun a => a * modelLineNorm hb y hM (unitSection e)) ih
    exact ht.trans (hp.trans (pow_succ _ _).symm)

/-- Actual original proper-center frames are raised through genuine native center tensor comparisons. -/
def centerPowerFrame {M : X.Modules}
    (e : centerLineModule hb y M ≅ unitObj (Spec (.of (CenterRing y)))) :
    (n : ℕ) → centerLineModule hb y (bundleTensorPower M n) ≅ unitObj (Spec (.of (CenterRing y)))
  | 0 => pullbackUnitIso (centerLift hb y)
  | n + 1 => (pullback (centerLift hb y)).mapIso
      (ModularCurves.monoidalTensorObjIso (bundleTensorPower M n) M).symm ≪≫
        centerTensorFrame hb y (centerPowerFrame e n) e

private theorem centerFrameGenericIso_unit :
    centerFrameGenericIso hb y (pullbackUnitIso (centerLift hb y)) =
      pullbackUnitIso (X.fromSpecResidueField y.1.point) := by
  apply Iso.ext
  apply (cancel_epi (centerLineGenericIso hb y (unitObj X)).hom).mp
  simp only [centerFrameGenericIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]
  have hg := ModularCurves.pullbackUnitIso_congr (centerLift_generic hb y)
  have hc := ModularCurves.pullbackUnitIso_compLow (centerGenericMap y) (centerLift hb y)
  change (pullback (centerGenericMap y)).map (pullbackUnitIso (centerLift hb y)).hom ≫
      (pullbackUnitIso (centerGenericMap y)).hom =
    (pullbackComp (centerGenericMap y) (centerLift hb y)).hom.app (unitObj X) ≫
      (pullbackCongr (centerLift_generic hb y)).hom.app (unitObj X) ≫
        (pullbackUnitIso (X.fromSpecResidueField y.1.point)).hom
  have ht := congrArg (fun a => (pullbackComp (centerGenericMap y) (centerLift hb y)).hom.app (unitObj X) ≫ a) hg
  exact hc.symm.trans ht.symm

private theorem centerFrameGenericIso_explicitTensor {M N : X.Modules}
    (e : centerLineModule hb y M ≅ unitObj (Spec (.of (CenterRing y))))
    (d : centerLineModule hb y N ≅ unitObj (Spec (.of (CenterRing y)))) :
    centerFrameGenericIso hb y
        ((pullback (centerLift hb y)).mapIso (ModularCurves.monoidalTensorObjIso M N).symm ≪≫
          centerTensorFrame hb y e d) =
      genericTensorFrame y (centerFrameGenericIso hb y e) (centerFrameGenericIso hb y d) := by
  have hn := centerFrameGenericIso_natural hb y (ModularCurves.monoidalTensorObjIso M N).symm
    (centerTensorFrame hb y e d)
  have ht := congrArg (fun E => (pullback (X.fromSpecResidueField y.1.point)).mapIso
      (ModularCurves.monoidalTensorObjIso M N).symm ≪≫ E)
    (centerFrameGenericIso_tensor hb y e d)
  exact hn.trans ht

/-- ACTUAL proper-center power frames restrict to EXACTLY the compatible original generic power frames as WHOLE isos. -/
theorem centerFrameGenericIso_centerPowerFrame {M : X.Modules}
    (e : centerLineModule hb y M ≅ unitObj (Spec (.of (CenterRing y)))) (n : ℕ) :
    centerFrameGenericIso hb y (centerPowerFrame y hb e n) =
      genericPowerFrame y (centerFrameGenericIso hb y e) n := by
  induction n with
  | zero => exact centerFrameGenericIso_unit y hb
  | succ n ih =>
    have ht := centerFrameGenericIso_explicitTensor y hb (centerPowerFrame y hb e n) e
    have hp := congrArg (fun E => genericTensorFrame y E (centerFrameGenericIso hb y e)) ih
    exact ht.trans hp

/-- The ACTUAL compatible proper-center power frame units have TRUE original model norm one at every degree. -/
theorem modelLineNorm_centerPowerFrame_unitSection {M : X.Modules} (hM : IsInvertible M)
    (e : centerLineModule hb y M ≅ unitObj (Spec (.of (CenterRing y)))) (n : ℕ) :
    modelLineNorm hb y (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n)
      (unitSection (centerFrameGenericIso hb y (centerPowerFrame y hb e n))) = 1 := by
  rw [modelLineNorm_eq_frame hb y (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM n)
    (centerPowerFrame y hb e n)]
  change y.1.residueVal ((Scheme.ΓSpecIso (X.residueField y.1.point)).hom
    (coefficient (centerFrameGenericIso hb y (centerPowerFrame y hb e n))
      (unitSection (centerFrameGenericIso hb y (centerPowerFrame y hb e n))))) = 1
  rw [coefficient_unitSection, map_one, map_one]

end Norm

end EnvelopeProperty.Berkovich.SchemeLinePowerFrameNorms
