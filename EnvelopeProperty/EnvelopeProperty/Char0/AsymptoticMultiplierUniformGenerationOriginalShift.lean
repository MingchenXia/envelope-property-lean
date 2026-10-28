import EnvelopeProperty.Char0.AsymptoticMultiplierUniformGenerationOriginal
import EnvelopeProperty.AlgGeom.ProjectiveTwistGlobalGeneration
import EnvelopeProperty.AlgGeom.ClosedProjectiveGlobalGeneration

/-! # The SAME actual original uniform multiplier twist grows by every nonnegative hyperplane buffer -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open Scheme.Modules
universe u
namespace EnvelopeProperty.Char0.AsymptoticMultiplierUniformGenerationOriginalShift
open CanonicalGeometry NadelClearedTwist
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
  MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] [CharZero k] {M : ℕ} (X : ProjSubvariety k M)
local notation "Y" => ProjSubvariety.MultiplierBaseIdeals.familyScheme X
local notation "p" => ProjSubvariety.MultiplierBaseIdeals.familyAbsoluteStructure X
local notation "i" => ProjSubvariety.MultiplierBaseIdeals.familyInclusion X
local notation "H" => hyperplane (ProjSubvariety.MultiplierBaseIdeals.familyInclusion X)

omit [CharZero k] in
/-- Actual original coordinate-power generators and genuine pullback DERIVE finite generators
of every nonnegative original family hyperplane twist, including b=0. -/
theorem exists_nonnegative_hyperplane_generatingSections (b : ℕ) :
    ∃ G : ((pullback i).obj (coordinateHyperplaneTwist (R := Polynomial k)
      (0 : Fin (M + 1)) (b : ℤ))).GeneratingSections, G.IsFiniteType := by
  let G := ProjectiveTwistGlobalGeneration.generatingSections (R := Polynomial k) (0 : Fin (M + 1)) b
  let : G.IsFiniteType := ProjectiveTwistGlobalGeneration.generatingSections_isFiniteType _ _
  exact ⟨ClosedProjectiveGlobalGeneration.pullback_generatingSections i G,
    ClosedProjectiveGlobalGeneration.pullback_generatingSections_isFiniteType i G⟩

/-- Native original associators, symmetry, power addition and actual hyperplane comparisons
construct the whole shifted module, retaining the SAME original ideal/module K literally. -/
def literalShiftIso (a b : ℕ) (K : (ProjSubvariety.MultiplierBaseIdeals.familyScheme X).Modules) :
    (((pullback i).obj (coordinateHyperplaneTwist (R := Polynomial k) (0 : Fin (M + 1)) (a : ℤ)) ⊗ K) ⊗
      (pullback i).obj (coordinateHyperplaneTwist (R := Polynomial k) (0 : Fin (M + 1)) (b : ℤ))) ≅
    ((pullback i).obj (coordinateHyperplaneTwist (R := Polynomial k) (0 : Fin (M + 1)) ((a + b : ℕ) : ℤ)) ⊗ K) := by
  let A := (pullback i).obj (coordinateHyperplaneTwist (R := Polynomial k) (0 : Fin (M + 1)) (a : ℤ))
  let B := (pullback i).obj (coordinateHyperplaneTwist (R := Polynomial k) (0 : Fin (M + 1)) (b : ℤ))
  let e : A ⊗ B ≅ (pullback i).obj
      (coordinateHyperplaneTwist (R := Polynomial k) (0 : Fin (M + 1)) ((a + b : ℕ) : ℤ)) :=
    ((hyperplanePowerIso i a).symm ⊗ᵢ (hyperplanePowerIso i b).symm) ≪≫
      TensorPowerBaseIdealGrading.tensorPowerAddIso H a b ≪≫ hyperplanePowerIso i (a + b)
  exact (α_ A K B) ≪≫ (Iso.refl A ⊗ᵢ β_ K B) ≪≫ (α_ A B K).symm ≪≫
    (e ⊗ᵢ Iso.refl K)

/-- The SAME c is chosen BEFORE all extra b,d,phi,lower-bound,m.
Actual original finite hyperplane generators and whole-module tensor coherence are internal;
no shifted or asymptotic generation certificate is supplied. -/
theorem exists_uniform_literal_twist_generatingSections_shift
    (hNadel : RelativeAmpleNadelVanishingInput k) (hs : X.HasSmoothCharts) :
    letI : Smooth p := MultiplierFamilySmoothness.familyAbsoluteStructure_smooth X hs
    ∃ c : ℕ, ∀ (b d : ℕ) (φ : X.an → ℝ) (C : ℝ) (hC : ∀ v, C ≤ φ v) (m : ℕ),
      ∃ G : (((pullback i).obj
        (coordinateHyperplaneTwist (R := Polynomial k) (0 : Fin (M + 1)) ((m * d + c + b : ℕ) : ℤ)) ⊗
        (ProjSubvariety.MultiplierBaseIdeals.schemeMultiplierSequence X d φ hC m).toModules)).GeneratingSections,
        G.IsFiniteType := by
  let : Smooth p := MultiplierFamilySmoothness.familyAbsoluteStructure_smooth X hs
  obtain ⟨c, hgen⟩ := AsymptoticMultiplierUniformGenerationOriginal.exists_uniform_literal_twist_generatingSections
    X hNadel hs
  refine ⟨c, fun b d φ C hC m => ?_⟩
  let A := (pullback i).obj (coordinateHyperplaneTwist (R := Polynomial k) (0 : Fin (M + 1)) ((m * d + c : ℕ) : ℤ))
  let B := (pullback i).obj (coordinateHyperplaneTwist (R := Polynomial k) (0 : Fin (M + 1)) (b : ℤ))
  let K := (ProjSubvariety.MultiplierBaseIdeals.schemeMultiplierSequence X d φ hC m).toModules
  have hB : IsInvertible B :=
    (coordinateHyperplaneTwist_isInvertible (R := Polynomial k) (0 : Fin (M + 1)) (b : ℤ)).pullback i
  obtain ⟨G, hG⟩ := MultiplierUniformGenerationBuffer.exists_tensor_generatingSections
    (A ⊗ K) B hB (hgen d φ C hC m) (exists_nonnegative_hyperplane_generatingSections X b)
  let : G.IsFiniteType := hG
  exact ⟨G.ofEpi (literalShiftIso X (m * d + c) b K).hom, inferInstance⟩

end EnvelopeProperty.Char0.AsymptoticMultiplierUniformGenerationOriginalShift
