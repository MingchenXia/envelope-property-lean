import EnvelopeProperty.Projective.SubvarietyMultiplierOriginalGenerationPullback
import EnvelopeProperty.Char0.EnvelopeGradedBaseIdealsGenerators
import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdeals
import EnvelopeProperty.Char0.NadelClearedTwistProjective

/-! # Finite actual generators of the SAME original obstacle ideal sequence

The finite forms, their whole images and all polarized generators are produced
internally from the original obstacle construction. No unrelated full-section
base ideal or supplied span/image/generation certificate replaces that family.
-/

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory MvPolynomial
open scoped Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierOriginalGeneration
open ProjBerk Scheme.Modules InvertibleSectionFamilyImage
open MultiplierBaseIdeals Char0.NadelClearedTwist
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- Finitely many of the SAME original obstacle forms, with their true degree,
have whole actual evaluation image equal to the ENTIRE original ambient ideal.
No finite set, span or evaluation-image certificate is an input. -/
theorem exists_original_homogeneous_evaluation_image (d : ℕ) (φ : X.an → ℝ) (m : ℕ) :
    ∃ (G : Finset (MvPolynomial (Fin (M + 1)) k[X]))
      (hG : ∀ F ∈ G, F.IsHomogeneous (m * d)),
      (G : Set _) ⊆ originalGeneratorSet X d φ m ∧
      parameterObstacleIdeal X d φ m = Ideal.span (G : Set _) ∧
      let hL := coordinateHyperplanePoleSheafPower_isInvertible (R := k[X]) (0 : Fin (M + 1)) (m * d)
      let s := fun F : G => ProjectiveHomogeneousSections.homogeneousSection
        (0 : Fin (M + 1)) (m * d) F.1 (hG F.1 F.2)
      let _ := freeTensorDual_isQuasicoherent hL G
      QuasicoherentImageIdeal.imageIdeal _ (familyEvaluation hL s) = ambientSchemeIdeal X d φ m := by
  obtain ⟨G, hsub, hspan, hG⟩ := exists_finite_original_homogeneous_generators X d φ m
  refine ⟨G, hG, hsub, hspan, ?_⟩
  exact MultiplierOriginalGenerationCore.homogeneousEvaluation_imageIdeal
    (0 : Fin (M + 1)) (m * d) (homogeneousObstacleIdeal X d φ m) G hG hspan

/-- The literal pullback of the SAME original finite homogeneous evaluation,
followed by the native unit comparison, has exactly the WHOLE original scheme
ideal as its image on the original family. -/
theorem exists_original_family_evaluation_image (d : ℕ) (φ : X.an → ℝ) (m : ℕ) :
    ∃ (G : Finset (MvPolynomial (Fin (M + 1)) k[X]))
      (hG : ∀ F ∈ G, F.IsHomogeneous (m * d)),
      (G : Set _) ⊆ originalGeneratorSet X d φ m ∧
      parameterObstacleIdeal X d φ m = Ideal.span (G : Set _) ∧
      let hL := coordinateHyperplanePoleSheafPower_isInvertible (R := k[X]) (0 : Fin (M + 1)) (m * d)
      let s := fun F : G => ProjectiveHomogeneousSections.homogeneousSection
        (0 : Fin (M + 1)) (m * d) F.1 (hG F.1 F.2)
      let S := (tensorRight (dualObj (coordinateHyperplanePoleSheafPower (R := k[X])
        (0 : Fin (M + 1)) (m * d)))).obj
        (SheafOfModules.free (R := (NativeProjectiveScheme k[X] M).ringCatSheaf) G)
      let _ := freeTensorDual_isQuasicoherent hL G
      let _ : ((pullback (familyInclusion X)).obj S).IsQuasicoherent :=
        MultiplierOriginalGenerationCore.pullbackFreeTensorDual_isQuasicoherent
          (familyInclusion X) _ hL G
      QuasicoherentImageIdeal.imageIdeal ((pullback (familyInclusion X)).obj S)
        ((pullback (familyInclusion X)).map (familyEvaluation hL s) ≫
          (pullbackUnitIso (familyInclusion X)).hom) = schemeIdeal X d φ m := by
  obtain ⟨G, hG, hsub, hspan, hi⟩ := exists_original_homogeneous_evaluation_image X d φ m
  refine ⟨G, hG, hsub, hspan, ?_⟩
  let hL := coordinateHyperplanePoleSheafPower_isInvertible (R := k[X]) (0 : Fin (M + 1)) (m * d)
  let s := fun F : G => ProjectiveHomogeneousSections.homogeneousSection
    (0 : Fin (M + 1)) (m * d) F.1 (hG F.1 F.2)
  let _ := freeTensorDual_isQuasicoherent hL G
  let _ : ((pullback (familyInclusion X)).obj
      ((tensorRight (dualObj (coordinateHyperplanePoleSheafPower (R := k[X])
        (0 : Fin (M + 1)) (m * d)))).obj
        (SheafOfModules.free (R := (NativeProjectiveScheme k[X] M).ringCatSheaf) G))).IsQuasicoherent :=
    MultiplierOriginalGenerationCore.pullbackFreeTensorDual_isQuasicoherent
      (familyInclusion X) _ hL G
  exact MultiplierOriginalGenerationCore.pullbackEvaluation_imageIdeal (familyInclusion X)
    _ (familyEvaluation hL s) (ambientSchemeIdeal X d φ m) hi

private theorem finiteGenerators_of_iso {Y : Scheme.{u}}
    {A B : SheafOfModules.{u} Y.ringCatSheaf}
    (G : A.GeneratingSections) [G.IsFiniteType] (e : A ≅ B) :
    ∃ H : B.GeneratingSections, H.IsFiniteType :=
  ⟨G.ofEpi e.hom, inferInstance⟩

/-- The original sequence, with SAME original obstacle and parameter family,
has genuine finite generators at its EXACT original hyperplane degree md.
All natural indices, including m=0 and d=0, are retained. -/
theorem exists_generatingSections (d : ℕ) (φ : X.an → ℝ) (m : ℕ) :
    ∃ G : ((schemeIdeal X d φ m).toModules ⊗
      CanonicalGeometry.bundleTensorPower (hyperplane (familyInclusion X)) (m * d)).GeneratingSections,
      G.IsFiniteType := by
  obtain ⟨F, _hsub, hspan, hF⟩ := exists_finite_original_homogeneous_generators X d φ m
  obtain ⟨G, hG⟩ := MultiplierOriginalGenerationCore.exists_pullback_generatingSections_of_homogeneous_span
    (familyInclusion X) (0 : Fin (M + 1)) (m * d)
    (homogeneousObstacleIdeal X d φ m) F hF hspan
  let : G.IsFiniteType := hG
  let e : (tensorRight ((pullback (familyInclusion X)).obj
      (coordinateHyperplanePoleSheafPower (R := k[X]) (0 : Fin (M + 1)) (m * d)))).obj
      (schemeIdeal X d φ m).toModules ≅
      (schemeIdeal X d φ m).toModules ⊗
        CanonicalGeometry.bundleTensorPower (hyperplane (familyInclusion X)) (m * d) :=
    Iso.refl (schemeIdeal X d φ m).toModules ⊗ᵢ
      (hyperplanePowerIso (familyInclusion X) (m * d)).symm
  exact finiteGenerators_of_iso G e

/-- The exact SAME original sequence is finitely generated after tensoring
by the m-th power of the SAME original polarization H^d, as required by the
uniform multiplier consumer; the iterated-power comparison is constructed. -/
theorem exists_generatingSections_polarization_power (d : ℕ) (φ : X.an → ℝ) (m : ℕ) :
    ∃ G : ((schemeIdeal X d φ m).toModules ⊗
      CanonicalGeometry.bundleTensorPower
        (CanonicalGeometry.bundleTensorPower (hyperplane (familyInclusion X)) d) m).GeneratingSections,
      G.IsFiniteType := by
  obtain ⟨G, hG⟩ := exists_generatingSections X d φ m
  let : G.IsFiniteType := hG
  let e : CanonicalGeometry.bundleTensorPower (hyperplane (familyInclusion X)) (m * d) ≅
      CanonicalGeometry.bundleTensorPower
        (CanonicalGeometry.bundleTensorPower (hyperplane (familyInclusion X)) d) m :=
    eqToIso (congrArg (CanonicalGeometry.bundleTensorPower (hyperplane (familyInclusion X)))
      (Nat.mul_comm m d)) ≪≫
      (BundleTensorPowerPullback.powerMulIso (hyperplane (familyInclusion X)) d m).symm
  let E : ((schemeIdeal X d φ m).toModules ⊗
      CanonicalGeometry.bundleTensorPower (hyperplane (familyInclusion X)) (m * d)) ≅
      ((schemeIdeal X d φ m).toModules ⊗ CanonicalGeometry.bundleTensorPower
        (CanonicalGeometry.bundleTensorPower (hyperplane (familyInclusion X)) d) m) :=
    Iso.refl (schemeIdeal X d φ m).toModules ⊗ᵢ e
  exact finiteGenerators_of_iso G E

end EnvelopeProperty.ProjSubvariety.MultiplierOriginalGeneration
