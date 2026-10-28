import EnvelopeProperty.AlgGeom.NativeAmpleModelSectionBlocks
import EnvelopeProperty.AlgGeom.SchemeGlobalSectionTensorPowerNorms

/-! # Actual arbitrary original section powers in the SAME genuine ample model -/
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Opposite
open DeJongAlterations Scheme.Modules
open scoped Classical NNReal ENNReal
noncomputable section
universe u
namespace EnvelopeProperty.NativeAmpleModelPoweredSections
open Berkovich RelativeSchemeValuedPoint CanonicalGeometry
open NativePulledProjectiveLineFrames NativeAmpleModelSectionBlocks
open SchemeGlobalSectionModelNormIsometries SchemeGlobalSectionTensorPowerNorms
open ProjectiveChartFunctionFieldGeneration ProjectiveFixedNativeAnalyticGluing
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (i : Fin (m + 1))
  [IsClosedImmersion f] [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)]
  (L : X.Modules) (r : ℕ) (e : line f (0 : Fin (m + 1)) 1 ≅ bundleTensorPower L r)

private local instance originalNativeStructureProper : IsProper (f ≫ projectiveSpaceStructure k m) := by
  let : IsProper (projectiveSpaceStructure k m) :=
    (GeneratedLineFamilyProjectiveEmbedding.polynomialFamily_isProjectiveFactorization k
      (fun _ : Fin 1 => m) 0).isProper
  infer_instance

/-- EVERY original section of L^d is actually raised to the rth tensor power,
transported through true original exponent isomorphisms, then mapped into SAME whole model degree d. -/
def poweredSection (d : ℕ) (s : Γ(bundleTensorPower L d,⊤)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (fullFieldModel f i).sections (fun _ => (d : ℤ)) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  exact sectionBlockEquiv f i L r e d
    (SchemeModuleIsoGlobalSections.moduleIsoTopEquiv
      (eqToIso (congrArg (bundleTensorPower L) (Nat.mul_comm d r))) (blockPowerSection L d s r))

/-- The SAME actual model coefficient of EVERY original section power has
TRUE model section norm exactly the rth power of the original proper-model norm. -/
theorem poweredSection_norm (hL : IsInvertible L) (d : ℕ)
    (s : Γ(bundleTensorPower L d,⊤))
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (fullFieldModel f i).secAbs (nativeModelHomeomorph f i y).1 (fun _ => (d : ℤ))
      (poweredSection f i L r e d s) =
        globalSectionNorm _root_.Valuation.one_apply_le_one y (bundleTensorPower L d)
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL d) s ^ r := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  unfold poweredSection
  rw [← sectionBlockNorm f i L r e hL d y]
  exact (globalSectionNorm_moduleIso _root_.Valuation.one_apply_le_one y
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL (d*r))
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL (r*d))
    (eqToIso (congrArg (bundleTensorPower L) (Nat.mul_comm d r))) _).symm.trans
      (globalSectionNorm_blockPowerSection _root_.Valuation.one_apply_le_one y L hL d s r)

/-- Actual pointwise nonvanishing is retained EXACTLY by the true original positive section power. -/
theorem poweredSection_norm_ne_zero_iff (hr : 0 < r) (hL : IsInvertible L) (d : ℕ)
    (s : Γ(bundleTensorPower L d,⊤))
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (fullFieldModel f i).secAbs (nativeModelHomeomorph f i y).1 (fun _ => (d : ℤ))
      (poweredSection f i L r e d s) ≠ 0 ↔
        globalSectionNorm _root_.Valuation.one_apply_le_one y (bundleTensorPower L d)
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL d) s ≠ 0 := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  rw [poweredSection_norm f i L r e hL d s y,pow_ne_zero_iff (Nat.ne_of_gt hr)]

/-- EVERY actual original log norm retains true exponent multiplication, including zero norms. -/
theorem poweredSection_logNorm (hL : IsInvertible L) (d : ℕ)
    (s : Γ(bundleTensorPower L d,⊤))
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (fullFieldModel f i).logSecAbs (nativeModelHomeomorph f i y).1 (fun _ => (d : ℤ))
      (poweredSection f i L r e d s) = ((r : ℝ) : EReal) *
        ENNReal.log (globalSectionNorm _root_.Valuation.one_apply_le_one y (bundleTensorPower L d)
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL d) s : ℝ≥0∞) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  rw [MultiModel.logSecAbs,poweredSection_norm f i L r e hL d s y,ENNReal.coe_pow,ENNReal.log_pow]
  rfl

end EnvelopeProperty.NativeAmpleModelPoweredSections
