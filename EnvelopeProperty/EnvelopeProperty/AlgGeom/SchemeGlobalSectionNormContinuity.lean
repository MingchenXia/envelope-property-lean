import EnvelopeProperty.AlgGeom.NativeAmpleLineNormContinuity
import EnvelopeProperty.AlgGeom.SchemeGlobalSectionTensorProductNorms
import EnvelopeProperty.AlgGeom.GeneratedLineBaseIdealUnit
import EnvelopeProperty.Berkovich.SchemeLineGlobalGeneratorNorms
import EnvelopeProperty.AlgGeom.SchemeAmpleLineGlobalGeneration
import EnvelopeProperty.AlgGeom.AmpleLineTwistGeneration

/-! # True original whole-section norms are continuous for EVERY original invertible line

An actual ample twist and true original finite global generators are
constructed internally. Their actual tensor norms recover the original
norm by an exact finite maximum. No norm/comparison/continuity certificate.
-/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open TopologicalSpace DeJongAlterations MvPolynomial
open scoped Classical NNReal ENNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.SchemeGlobalSectionNormContinuity
open Berkovich RelativeSchemeValuedPoint CanonicalGeometry
open SchemeGlobalSectionModelNormIsometries SchemeGlobalSectionTensorProductNorms
open GeneratedLineBaseIdealUnit
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
section Bounded
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} {p : X ⟶ Spec (.of R)} [IsProper p]
    (hb : ∀ r,v r ≤ 1) (y : RelativeSchemeValuedPoint v p)

/-- Every original whole global line section is integral at its actual proper center. -/
theorem globalSectionNorm_le_one (M : X.Modules) (hM : IsInvertible M) (s : Γ(M,⊤)) :
    globalSectionNorm hb y M hM s ≤ 1 := by
  rw [globalSectionNorm,modelLineNorm_fibreSection]
  exact modelHomNorm_le_one hb y (Scheme.Modules.isInvertible_unit (X := X)) hM
    (SchemeModuleGlobalSections.sectionHom M s)

/-- Genuine original global generation DERIVES a SAME original top section of norm one. -/
theorem exists_generator_norm_one (T : X.Modules) (hT : IsInvertible T) (G : T.GeneratingSections) :
    ∃ i : G.I,globalSectionNorm hb y T hT (topSection G i) = 1 := by
  simpa only [globalSectionNorm,sectionHom_topSection] using
    exists_modelLineNorm_generatorHom_eq_one hb y hT G

/-- EVERY actual original section norm is the finite maximum of the TRUE original tensor-generator norms. -/
theorem globalSectionNorm_tensor_generators_sup (M T : X.Modules)
    (hM : IsInvertible M) (hT : IsInvertible T) (s : Γ(M,⊤))
    (G : T.GeneratingSections) [Fintype G.I] :
    Finset.univ.sup (fun i : G.I => globalSectionNorm hb y (M ⊗ T) (hM.monoidalTensor hT)
      (ModularCurves.tensorSection M T ⊤ s (topSection G i))) = globalSectionNorm hb y M hM s := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    rw [globalSectionNorm_tensorSection hb y M T hM hT]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (globalSectionNorm_le_one hb y T hT (topSection G i))
      (show 0 ≤ globalSectionNorm hb y M hM s from zero_le)
  · obtain ⟨i,hi⟩ := exists_generator_norm_one hb y T hT G
    have h := Finset.le_sup (f := fun i : G.I => globalSectionNorm hb y (M ⊗ T) (hM.monoidalTensor hT)
      (ModularCurves.tensorSection M T ⊤ s (topSection G i))) (Finset.mem_univ i)
    simpa only [globalSectionNorm_tensorSection hb y M T hM hT,hi,mul_one] using h
end Bounded

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProjective p]
private local instance projectiveProper : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

omit [IsIntegral X] in
private theorem exists_ample_line : ∃ A : X.Modules,SchemeLineAmpleness.IsAmple p A := by
  obtain ⟨n,f,hf,hp⟩ := ProjectiveFactorizationRingIso.of_isProjective p
  let A := (Scheme.Modules.pullback f).obj (coordinateHyperplaneTwist (R := k) (0 : Fin (n+1)) 1)
  have hA : SchemeLineAmpleness.IsVeryAmple p A := ⟨n,f,hf,hp,⟨Iso.refl A⟩⟩
  exact ⟨A,AmpleLineTwistGeneration.isAmple_of_isVeryAmple hA⟩

/-- On integral original projective X, EVERY original invertible line's whole-section
norm is genuinely continuous, from internally constructed actual ample twist and finite GG. -/
theorem continuous_globalSectionNorm (M : X.Modules) (hM : IsInvertible M) (s : Γ(M,⊤)) :
    Continuous (fun y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p =>
      globalSectionNorm _root_.Valuation.one_apply_le_one y M hM s) := by
  obtain ⟨A,hA⟩ := exists_ample_line p
  obtain ⟨N,hN⟩ := AmpleLineTwistGeneration.exists_eventual_isVeryAmple p A hA M hM
  obtain ⟨Q,hQ⟩ := SchemeAmpleLineGlobalGeneration.exists_eventual_generatingSections p A hA
  let m := max N Q
  let T := bundleTensorPower A m
  have hT : IsInvertible T := TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.isInvertible m
  obtain ⟨G,hG⟩ := hQ m (le_max_right N Q)
  let : Finite G.I := hG.finite
  let : Fintype G.I := Fintype.ofFinite G.I
  have hMT : SchemeLineAmpleness.IsAmple p (M ⊗ T) :=
    AmpleTensorLines.ample_of_iso (AmpleLineTwistGeneration.isAmple_of_isVeryAmple
      (hN m (le_max_left N Q))) (β_ T M)
  have hc : Continuous (fun y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p =>
      Finset.univ.sup (fun i : G.I => globalSectionNorm _root_.Valuation.one_apply_le_one y
        (M ⊗ T) hMT.isInvertible (ModularCurves.tensorSection M T ⊤ s (topSection G i)))) :=
    Continuous.finset_sup_apply (fun i _ => continuous_of_isAmple p (M ⊗ T) hMT
      (ModularCurves.tensorSection M T ⊤ s (topSection G i)))
  exact hc.congr (fun y => globalSectionNorm_tensor_generators_sup _root_.Valuation.one_apply_le_one
    y M T hM hT s G)

end EnvelopeProperty.SchemeGlobalSectionNormContinuity
