import EnvelopeProperty.AlgGeom.SchemeLineAmpleness
import EnvelopeProperty.AlgGeom.NativePulledProjectiveLinearSections
import EnvelopeProperty.AlgGeom.SchemeGlobalSectionModelNormIsometries
import EnvelopeProperty.AlgGeom.PositivePowerProjectiveGeneration

/-! # Actual ample original lines internally give WHOLE global-section and true metric exponent blocks -/
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Opposite
open Alterations Scheme.Modules
open scoped Classical NNReal ENNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.NativeAmpleModelSectionBlocks
open Berkovich CanonicalGeometry NativePulledProjectiveLineFrames
open NativePulledProjectiveModelSections NativePulledProjectiveSectionNorms
open ProjectiveChartFunctionFieldGeneration ProjectiveFixedNativeAnalyticGluing
open SchemeGlobalSectionModelNormIsometries
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (i : Fin (m + 1))
  [IsClosedImmersion f] [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)]
  (L : X.Modules) (r : ℕ) (e : line f (0 : Fin (m + 1)) 1 ≅ bundleTensorPower L r)

/-- Actual positive-power geometric data give the ENTIRE original field-linear
section equivalence on EVERY exponent block, with original native field coefficients. -/
def sectionBlockEquiv (d : ℕ) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    AffineModuleFlatBaseChange.sections (f ≫ projectiveSpaceStructure k m) (bundleTensorPower L (r*d)) ≃ₗ[k]
      (fullFieldModel f i).sections (fun _ => (d : ℤ)) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let α : bundleTensorPower L (r*d) ≅ line f (0 : Fin (m + 1)) d :=
    PositivePowerProjectiveGeneration.blockTwistIso f L r (0 : Fin (m + 1)) e d
  exact (SchemeModuleIsoGlobalSections.moduleIsoTopOverBase (f ≫ projectiveSpaceStructure k m) α).trans
    (((SchemeScalarModulePresheaf.topSectionsIso (f ≫ projectiveSpaceStructure k m)
      (line f (0 : Fin (m + 1)) d)).symm.toLinearEquiv).trans
        (NativePulledProjectiveLinearSections.sectionLinearEquiv f (0 : Fin (m + 1)) d i))

/-- EVERY actual original block section retains its literal actual generic coefficient
through the genuine entire original block line isomorphism. -/
theorem sectionBlockEquiv_apply (d : ℕ)
    (s : AffineModuleFlatBaseChange.sections (f ≫ projectiveSpaceStructure k m) (bundleTensorPower L (r*d))) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (sectionBlockEquiv f i L r e d s : X.functionField) =
      coefficient f i (0 : Fin (m + 1)) d
        (SchemeModuleIsoGlobalSections.moduleIsoTopEquiv
          (PositivePowerProjectiveGeneration.blockTwistIso f L r (0 : Fin (m + 1)) e d) s) := rfl

private local instance originalNativeStructureProper : IsProper (f ≫ projectiveSpaceStructure k m) := by
  let : IsProper (projectiveSpaceStructure k m) :=
    (GeneratedLineFamilyProjectiveEmbedding.polynomialFamily_isProjectiveFactorization k
      (fun _ : Fin 1 => m) 0).isProper
  infer_instance

/-- EVERY actual original block global section retains its TRUE original proper-model
norm as genuine whole model secAbs under THE SAME entire original native homeomorphism. -/
theorem sectionBlockNorm (hL : IsInvertible L) (d : ℕ)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m))
    (s : AffineModuleFlatBaseChange.sections (f ≫ projectiveSpaceStructure k m) (bundleTensorPower L (r*d))) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    globalSectionNorm _root_.Valuation.one_apply_le_one y (bundleTensorPower L (r*d))
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL (r*d)) s =
        (fullFieldModel f i).secAbs (nativeModelHomeomorph f i y).1 (fun _ => (d : ℤ))
          (sectionBlockEquiv f i L r e d s) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  rw [sectionBlockEquiv_apply]
  let α := PositivePowerProjectiveGeneration.blockTwistIso f L r (0 : Fin (m + 1)) e d
  exact (globalSectionNorm_moduleIso _root_.Valuation.one_apply_le_one y
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL (r*d)) (line_isInvertible f (0 : Fin (m + 1)) d)
    α s).trans (sectionNorm_eq_secAbs f i (0 : Fin (m + 1)) d y _)

/-- Original geometric ampleness INTERNALLY gives a SAME-X actual closed embedding,
nonempty original pivot, and ONE true full-native-field model realizing EVERY whole
original exponent-block section module and true metric, without desired comparison input. -/
theorem exists_model_section_blocks (p : X ⟶ Spec (.of k)) (A : X.Modules)
    (hA : SchemeLineAmpleness.IsAmple p A) :
    ∃ r : ℕ,0 < r ∧ ∃ n : ℕ,∃ f : X ⟶ projectiveSpace k n,∃ hf : IsClosedImmersion f,
      f ≫ projectiveSpaceStructure k n = p ∧ ∃ i : Fin (n+1),
      ∃ hi : Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i),
        letI := hf
        letI := hi
        letI := (f ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
        ∀ d : ℕ,∃ E : AffineModuleFlatBaseChange.sections (f ≫ projectiveSpaceStructure k n)
            (bundleTensorPower A (r*d)) ≃ₗ[k] (fullFieldModel f i).sections (fun _ => (d : ℤ)),
          ∀ (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k n)) s,
            globalSectionNorm _root_.Valuation.one_apply_le_one y (bundleTensorPower A (r*d))
              (TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.isInvertible (r*d)) s =
            (fullFieldModel f i).secAbs (nativeModelHomeomorph f i y).1 (fun _ => (d : ℤ)) (E s) := by
  obtain ⟨hL,r,hr,n,f,hf,hfp,⟨e⟩⟩ := hA
  let : IsClosedImmersion f := hf
  have hx : f (genericPoint X) ∈ ⨆ i : Fin (n+1),coordinateOpen (R := k) i := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hx
  let hn : Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i) := ⟨⟨genericPoint X,hi⟩⟩
  let := hn
  refine ⟨r,hr,n,f,hf,hfp,i,hn,?_⟩
  exact fun d => ⟨sectionBlockEquiv f i A r e d,fun y s => sectionBlockNorm f i A r e hL d y s⟩

end EnvelopeProperty.NativeAmpleModelSectionBlocks
