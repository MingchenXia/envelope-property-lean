import EnvelopeProperty.Vanishing.NadelBoundedCanonicalProjectionFormula
import EnvelopeProperty.Vanishing.NadelBoundedCanonicalDegreeScalar
import EnvelopeProperty.Vanishing.NadelWholeRoundedPushforwardKodaira

/-! # Conditional assembly of the original rounded canonical retraction

These private support lemmas take a canonical trace and its differential
degree identity as explicit hypotheses. They do not construct that trace or
claim the actual Nadel endpoint. The bounded map, degree automorphism,
projection comparison and upper pushforward vanishing are the existing
actual producers, with no incoming factor, scalar or projection certificate.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalDescentCore
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelGlobalAdaptedRoots NadelBoundedCanonicalPushforward
open NadelBoundedCanonicalProjectionFormula NadelBoundedCanonicalDegreeScalar
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private theorem retraction_from_degree_factor
    {C : Type*} [Category C] {A B P : C}
    (j : A ⟶ B) (inc : B ⟶ P) (δ : A ⟶ P) (T : P ⟶ A) (d : A ≅ A)
    (hj : j ≫ inc = δ) (hT : δ ≫ T = d.hom) :
    j ≫ (inc ≫ T ≫ d.inv) = 𝟙 A := by
  calc
    j ≫ (inc ≫ T ≫ d.inv) = (j ≫ inc) ≫ T ≫ d.inv := by
      simp only [Category.assoc]
    _ = (δ ≫ T) ≫ d.inv := by rw [hj, Category.assoc]
    _ = d.hom ≫ d.inv := by rw [hT]
    _ = 𝟙 A := d.hom_inv_id

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      Scheme.Modules.tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
    {k : Type u} [Field k] [CharZero k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)
local notation "ωX" => canonicalLineSheaf f n
local notation "ωY" => canonicalLineSheaf (π ≫ f) n
local notation "D" => NadelWholeCoverDegree.degree (NadelAdaptedChartMatching.Joined.degree F n m)

include hD hG hRows hm hfield

private theorem wholeRoundedCanonicalPullback_retract_of_trace_degree
    (a : F.ι → ℕ) (ha : ∀ i, a i < m i)
    (T : (pushforward π).obj ωY ⟶ ωX)
    (hT : (pullbackPushforwardAdjunction π).unit.app ωX ≫
      (pushforward π).map (exteriorCotangentSheafPullbackMap f π n) ≫ T = D • 𝟙 ωX) :
    ∃ r : (pushforward π).obj
        (Scheme.Modules.tensorObj ωY (wholeRoundedIdeal F n L m σ hL a).toModules) ⟶ ωX,
      wholeRoundedCanonicalPullback F n L m σ hL hD f hG hRows hm hfield a ha ≫ r = 𝟙 ωX := by
  let inc := (pushforward π).map
    (SchemeTensorObjMorphisms.tensorObjIdealMap ωY
      (wholeRoundedIdeal F n L m σ hL a).toModules
      (wholeRoundedIdeal F n L m σ hL a).toModulesInclusion)
  let δ := (pullbackPushforwardAdjunction π).unit.app ωX ≫
    (pushforward π).map (exteriorCotangentSheafPullbackMap f π n)
  let d := originalDegreeScalarIso F n m hm f ωX
  refine ⟨inc ≫ T ≫ d.inv, ?_⟩
  apply retraction_from_degree_factor _ inc δ T d
  · exact wholeRoundedCanonicalPullback_inclusion F n L m σ hL hD f hG hRows hm hfield a ha
  · change δ ≫ T = (originalDegreeScalarIso F n m hm f ωX).hom
    rw [originalDegreeScalarIso_hom]
    simpa only [δ, Category.assoc] using hT

private theorem wholeRoundedCanonicalTwistedPullback_retract_of_trace_degree
    (M : X.Modules) (hM : IsInvertible M) (a : F.ι → ℕ) (ha : ∀ i, a i < m i)
    (T : (pushforward π).obj ωY ⟶ ωX)
    (hT : (pullbackPushforwardAdjunction π).unit.app ωX ≫
      (pushforward π).map (exteriorCotangentSheafPullbackMap f π n) ≫ T = D • 𝟙 ωX) :
    ∃ r : (pushforward π).obj
        (Scheme.Modules.tensorObj ωY (wholeRoundedLine F n L m σ hL M a)) ⟶ ωX ⊗ M,
      wholeRoundedCanonicalTwistedPullback F n L m σ hL f hD hG hRows hm hfield M hM a ha ≫ r =
        𝟙 (ωX ⊗ M) := by
  obtain ⟨r, hr⟩ := wholeRoundedCanonicalPullback_retract_of_trace_degree
    F n L m σ hL hD f hG hRows hm hfield a ha T hT
  let j := wholeRoundedCanonicalPullback F n L m σ hL hD f hG hRows hm hfield a ha
  let E := wholeRoundedProjectionFormulaIso F n L m σ hL f M hM a
  let sj : SplitMono j := ⟨r, hr⟩
  let st := sj.map (tensorRight M)
  refine ⟨E.inv ≫ st.retraction, ?_⟩
  change ((tensorRight M).map j ≫ E.hom) ≫ (E.inv ≫ st.retraction) = _
  calc
    ((tensorRight M).map j ≫ E.hom) ≫ (E.inv ≫ st.retraction) =
        (tensorRight M).map j ≫ st.retraction := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = 𝟙 (ωX ⊗ M) := st.id

private theorem canonicalLine_kodaira_of_trace_degree
    (M : X.Modules) (hM : IsInvertible M) (a : F.ι → ℕ) (ha : ∀ i, a i < m i)
    (hA : SchemeLineAmpleness.IsAmple f
      (Scheme.Modules.tensorObj (bundleTensorPower M (commonRootDegree F m))
        (clearedRoundedIdeal F m a (commonRootDegree F m)).toModules))
    (T : (pushforward π).obj ωY ⟶ ωX)
    (hT : (pullbackPushforwardAdjunction π).unit.app ωX ≫
      (pushforward π).map (exteriorCotangentSheafPullbackMap f π n) ≫ T = D • 𝟙 ωX)
    (q : ℕ) : Subsingleton (CategoryTheory.Sheaf.H (ωX ⊗ M).sheaf (q + 1)) := by
  obtain ⟨r, hr⟩ := wholeRoundedCanonicalTwistedPullback_retract_of_trace_degree
    F n L m σ hL hD f hG hRows hm hfield M hM a ha T hT
  exact AffinePushforwardCohomology.subsingleton_H_of_retract
    (wholeRoundedCanonicalTwistedPullback F n L m σ hL f hD hG hRows hm hfield M hM a ha)
    r hr (q + 1)
    (NadelWholeRoundedPushforwardKodaira.wholeRoundedCanonicalPushforward_kodaira
      F n L m σ hL hD f hG hRows hm M hM a hA q)

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalDescentCore
