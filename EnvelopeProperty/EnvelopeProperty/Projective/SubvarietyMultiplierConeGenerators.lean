import EnvelopeProperty.Projective.SubvarietyMultiplierConeGeneratorsAlgebra
import EnvelopeProperty.Char0.AsymptoticMultiplierUniformGenerationOriginalShift
import EnvelopeProperty.Char0.RelativeHomogeneousSectionLiftPolynomial

/-! # Nadel constructs actual bounded polynomial generators of the original cone ideals

Only the named Nadel proposition and original smooth charts are supplied.
Every whole generating family, homogeneous lift, ideal image and saturation
comparison is produced internally on the same original parameter family.
-/

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierConeGenerators
open Scheme.Modules MultiplierBaseIdeals MultiplierConeGeneratorsEvaluation
open MultiplierConeGeneratorsAlgebra
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
  MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem finiteGenerators_of_iso {Y : Scheme.{u}}
    {A B : SheafOfModules.{u} Y.ringCatSheaf}
    (G : A.GeneratingSections) [G.IsFiniteType] (e : A ≅ B) :
    ∃ H : B.GeneratingSections, H.IsFiniteType :=
  ⟨G.ofEpi e.hom, inferInstance⟩

/-- A single degree buffer, chosen BEFORE every polarization degree, original
obstacle, lower bound and index, gives actual finite original polynomial cone
generators with both true ideal bounds. No global-generation, polynomial-lift,
whole-image, saturation or desired Fubini--Study certificate is a premise. -/
theorem exists_uniform_bounded_polynomial_generators
    {k : Type u} [Field k] [CharZero k] {M : ℕ} (X : ProjSubvariety k M)
    (hNadel : Char0.RelativeAmpleNadelVanishingInput k) (hs : X.HasSmoothCharts) :
    ∃ c : ℕ, ∀ (d : ℕ) (φ : X.an → ℝ) (C : ℝ) (hC : ∀ v, C ≤ φ v) (m : ℕ),
      X.HasBoundedPolynomialConeGenerators
        (originalMultiplierConeIdeal X hs d φ hC m) (m * d + c) := by
  classical
  let : Smooth (familyAbsoluteStructure X) :=
    Char0.MultiplierFamilySmoothness.familyAbsoluteStructure_smooth X hs
  obtain ⟨c, hgen⟩ :=
    Char0.AsymptoticMultiplierUniformGenerationOriginalShift.exists_uniform_literal_twist_generatingSections_shift
      X hNadel hs
  obtain ⟨b, hlift⟩ := Char0.RelativeHomogeneousSectionLift.exists_polynomial_lift_bound
    (familyInclusion X)
  refine ⟨c + b, fun d φ C hC m => ?_⟩
  let e := m * d + c + b
  let K := schemeMultiplierSequence X d φ hC m
  let L := (Scheme.Modules.pullback (familyInclusion X)).obj
    (coordinateHyperplaneTwist (R := Polynomial k) (0 : Fin (M + 1)) (e : ℤ))
  have he : b ≤ e := by dsimp [e]; omega
  obtain ⟨G₀, hG₀⟩ := hgen b d φ C hC m
  let : G₀.IsFiniteType := hG₀
  let E : L ⊗ K.toModules ≅ K.toModules ⊗ L := β_ L K.toModules
  obtain ⟨G, hG⟩ := finiteGenerators_of_iso G₀ E
  have hrep (a : G.I) : ∃ F : MvPolynomial (Fin (M + 1)) (Polynomial k),
      ∃ hF : F.IsHomogeneous e,
        affinePullbackUnitTop (familyInclusion X)
          (coordinateHyperplaneTwist (R := Polynomial k) (0 : Fin (M + 1)) (e : ℤ))
          (ProjectiveHomogeneousSections.homogeneousSection (0 : Fin (M + 1)) e F hF) =
          includedSection K L G a :=
    hlift e he (includedSection K L G a)
  choose F hF hFrep using hrep
  have hbounded := hasBoundedPolynomialConeGenerators_of_lifts X K e G hG F hF hFrep
  rw [Char0.AsymptoticMultiplierUniformGenerationOriginal.originalMultiplierConeIdeal_eq_coneIdeal
    X hs d φ hC m]
  simpa only [e, Nat.add_assoc] using hbounded

end EnvelopeProperty.ProjSubvariety.MultiplierConeGenerators
