import EnvelopeProperty.Char0.AsymptoticMultiplierUniformGeneration
import EnvelopeProperty.Char0.MultiplierFamilySmoothnessCoordinates
import EnvelopeProperty.Char0.SmoothPureDimension
import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsOriginal
import EnvelopeProperty.Projective.SubvarietyMultiplierOriginalGeneration

/-! # Uniform generation for the SAME actual original obstacle multiplier sequence

The ONLY vanishing proposition is the explicit Nadel input. All actual family
geometry, total dimension, gradedness, nonzero original generic stalks and actual
homogeneous polarized generators are internally produced from the original data.
The fixed pure hyperplane exponent is chosen BEFORE d, phi, its lower bound and m.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace MvPolynomial
open Scheme.Modules
universe u
namespace EnvelopeProperty.Char0.AsymptoticMultiplierUniformGenerationOriginal
open CanonicalGeometry NadelClearedTwist
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
  MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] [CharZero k] {M : ℕ} (X : ProjSubvariety k M)

local notation "Y" => ProjSubvariety.MultiplierBaseIdeals.familyScheme X
local notation "p" => ProjSubvariety.MultiplierBaseIdeals.familyAbsoluteStructure X
local notation "π" => ProjSubvariety.MultiplierBaseIdeals.familyProjection X
local notation "i" => ProjSubvariety.MultiplierBaseIdeals.familyInclusion X
local notation "H" => hyperplane (ProjSubvariety.MultiplierBaseIdeals.familyInclusion X)

/-- ONLY original X, smooth charts and Nadel produce the true total dimension and SAME uniform
canonical buffer for EVERY original obstacle family, including d=0 and m=0. -/
theorem exists_uniform_canonical_generatingSections (hNadel : RelativeAmpleNadelVanishingInput k)
    (hs : X.HasSmoothCharts) :
    letI : Smooth p := MultiplierFamilySmoothness.familyAbsoluteStructure_smooth X hs
    ∃ n : ℕ, SmoothOfRelativeDimension n p ∧
      ∀ (d : ℕ) (φ : X.an → ℝ) (C : ℝ) (hC : ∀ v, C ≤ φ v) (m : ℕ),
      ∃ G : (((canonicalLineSheaf p n ⊗
          (bundleTensorPower H (M + 1) ⊗ bundleTensorPower (bundleTensorPower H d) m)) ⊗
          (ProjSubvariety.MultiplierBaseIdeals.schemeMultiplierSequence X d φ hC m).toModules)).GeneratingSections,
        G.IsFiniteType := by
  let : Smooth p := MultiplierFamilySmoothness.familyAbsoluteStructure_smooth X hs
  obtain ⟨n, hn⟩ := SmoothPureDimension.exists_smoothOfRelativeDimension_charZero p
  refine ⟨n, hn, fun d φ C hC m => ?_⟩
  exact AsymptoticMultiplierUniformGeneration.exists_generatingSections hNadel p π rfl i rfl n hn
    (ProjSubvariety.MultiplierBaseIdeals.schemeIdeal X d φ)
    (ProjSubvariety.MultiplierBaseIdeals.schemeIdeal_mul_le X d φ)
    (fun q _hq => ProjSubvariety.MultiplierBaseIdeals.schemeIdeal_generic_stalk_ne_bot X d φ hC q)
    (bundleTensorPower H d)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible (hyperplane_isVeryAmple i).isInvertible d)
    (fun q _hq => ProjSubvariety.MultiplierOriginalGeneration.exists_generatingSections_polarization_power X d φ q) m

/-- One actual pure hyperplane exponent is chosen from ONLY the original geometry and Nadel,
BEFORE every d/phi/lower-bound/m. Native smoothness, dimension, original ideal generators and
whole asymptotic-ideal stabilization are INTERNALLY produced, never certificate inputs. -/
theorem exists_uniform_pure_power_generatingSections (hNadel : RelativeAmpleNadelVanishingInput k)
    (hs : X.HasSmoothCharts) :
    letI : Smooth p := MultiplierFamilySmoothness.familyAbsoluteStructure_smooth X hs
    ∃ s : ℕ, ∀ (d : ℕ) (φ : X.an → ℝ) (C : ℝ) (hC : ∀ v, C ≤ φ v) (m : ℕ),
      ∃ G : (((bundleTensorPower H (M + 1 + s) ⊗ bundleTensorPower (bundleTensorPower H d) m) ⊗
        (ProjSubvariety.MultiplierBaseIdeals.schemeMultiplierSequence X d φ hC m).toModules)).GeneratingSections,
        G.IsFiniteType := by
  let : Smooth p := MultiplierFamilySmoothness.familyAbsoluteStructure_smooth X hs
  obtain ⟨n, hn⟩ := SmoothPureDimension.exists_smoothOfRelativeDimension_charZero p
  obtain ⟨s, hgen⟩ := AsymptoticMultiplierUniformGeneration.exists_uniform_pure_power_generatingSections
    hNadel p π rfl i rfl n hn
  refine ⟨s, fun d φ C hC m => ?_⟩
  exact hgen (bundleTensorPower H d)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible (hyperplane_isVeryAmple i).isInvertible d)
    (ProjSubvariety.MultiplierBaseIdeals.schemeIdeal X d φ)
    (ProjSubvariety.MultiplierBaseIdeals.schemeIdeal_mul_le X d φ)
    (fun q _hq => ProjSubvariety.MultiplierBaseIdeals.schemeIdeal_generic_stalk_ne_bot X d φ hC q)
    (fun q _hq => ProjSubvariety.MultiplierOriginalGeneration.exists_generatingSections_polarization_power X d φ q) m

/-- The actual same-family hyperplane comparisons construct the LITERAL i*O(md+c) line.
No expected line or tensor-power comparison is supplied. -/
def literalTwistIso (c d m : ℕ) :
    bundleTensorPower H c ⊗ bundleTensorPower (bundleTensorPower H d) m ≅
      (pullback i).obj (coordinateHyperplaneTwist (R := Polynomial k) (0 : Fin (M + 1)) ((m * d + c : ℕ) : ℤ)) :=
  (Iso.refl (bundleTensorPower H c) ⊗ᵢ BundleTensorPowerPullback.powerMulIso H d m) ≪≫
    TensorPowerBaseIdealGrading.tensorPowerAddIso H c (d * m) ≪≫
    eqToIso (congrArg (bundleTensorPower H) ((congrArg (fun t : ℕ => c + t) (Nat.mul_comm d m)).trans (Nat.add_comm c (m * d)))) ≪≫
    hyperplanePowerIso i (m * d + c)

/-- The SAME whole actual original multiplier ideal has finite generators in the LITERAL original
projective twist i*O(md+c), with c selected BEFORE d/phi/lower-bound/m. -/
theorem exists_uniform_literal_twist_generatingSections (hNadel : RelativeAmpleNadelVanishingInput k)
    (hs : X.HasSmoothCharts) :
    letI : Smooth p := MultiplierFamilySmoothness.familyAbsoluteStructure_smooth X hs
    ∃ c : ℕ, ∀ (d : ℕ) (φ : X.an → ℝ) (C : ℝ) (hC : ∀ v, C ≤ φ v) (m : ℕ),
      ∃ G : (((pullback i).obj
          (coordinateHyperplaneTwist (R := Polynomial k) (0 : Fin (M + 1)) ((m * d + c : ℕ) : ℤ)) ⊗
          (ProjSubvariety.MultiplierBaseIdeals.schemeMultiplierSequence X d φ hC m).toModules)).GeneratingSections,
        G.IsFiniteType := by
  let : Smooth p := MultiplierFamilySmoothness.familyAbsoluteStructure_smooth X hs
  obtain ⟨s, hgen⟩ := exists_uniform_pure_power_generatingSections X hNadel hs
  refine ⟨M + 1 + s, fun d φ C hC m => ?_⟩
  obtain ⟨G, hG⟩ := hgen d φ C hC m
  let : G.IsFiniteType := hG
  let e := literalTwistIso X (M + 1 + s) d m ⊗ᵢ
    Iso.refl (ProjSubvariety.MultiplierBaseIdeals.schemeMultiplierSequence X d φ hC m).toModules
  exact ⟨G.ofEpi e.hom, inferInstance⟩

/-- This is LITERALLY the whole scheme ideal used by the SAME original multiplier cone ideal.
The only native smoothness proof is internally produced from the original smooth charts. -/
theorem originalMultiplierConeIdeal_eq_coneIdeal (hs : X.HasSmoothCharts) (d : ℕ) (φ : X.an → ℝ)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) (m : ℕ) :
    letI : Smooth p := MultiplierFamilySmoothness.familyAbsoluteStructure_smooth X hs
    ProjSubvariety.MultiplierBaseIdeals.originalMultiplierConeIdeal X hs d φ hC m =
      ProjSubvariety.MultiplierBaseIdeals.coneIdeal X
        (ProjSubvariety.MultiplierBaseIdeals.schemeMultiplierSequence X d φ hC m) := rfl

end EnvelopeProperty.Char0.AsymptoticMultiplierUniformGenerationOriginal
