import EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafFactor

/-! # The actual bounded canonical pullback into the whole rounded pushforward

The map is obtained from the internally produced original canonical factor
and the original pullback/pushforward adjunction unit. Its inclusion composite
is the same original canonical unit/differential map. No trace or splitting
is an input, and no trace retraction is asserted here.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalPushforward
open AlgebraicGeometry CategoryTheory Scheme.Modules CanonicalGeometry
open NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedRoots
universe u v w z
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem mappedFactor
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    (F : C ⥤ D) {A B N : C} {M : D}
    (η : M ⟶ F.obj A) (θ : A ⟶ B) (inc : B ⟶ N) (δ : A ⟶ N)
    (hθ : θ ≫ inc = δ) :
    (η ≫ F.map θ) ≫ F.map inc = η ≫ F.map δ := by
  rw [Category.assoc, ← F.map_comp, hθ]

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
    {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))
    (a : F.ι → ℕ) (ha : ∀ i, a i < m i)

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)
local notation "ωX" => exteriorCotangentSheaf f n
local notation "ωY" => exteriorCotangentSheaf (π ≫ f) n
local notation "J" => wholeRoundedIdeal F n L m σ hL a

include hD f hG hRows hm hfield ha
private def actualRoundedFactor :
    (pullback π).obj ωX ⟶ Scheme.Modules.tensorObj ωY (J).toModules :=
  Classical.choose
    (NadelBoundedCanonicalSheafFactor.exists_wholeRoundedIdeal_canonical_factor
      F n L m σ hL hD f hG hRows hm hfield a ha)

private theorem actualRoundedFactor_inclusion :
    actualRoundedFactor F n L m σ hL hD f hG hRows hm hfield a ha ≫
      SchemeTensorObjMorphisms.tensorObjIdealMap ωY (J).toModules (J).toModulesInclusion =
        exteriorCotangentSheafPullbackMap f π n :=
  Classical.choose_spec
    (NadelBoundedCanonicalSheafFactor.exists_wholeRoundedIdeal_canonical_factor
      F n L m σ hL hD f hG hRows hm hfield a ha)

/-- The original canonical unit factors through the actual whole rounded
canonical pushforward, using only internally produced original geometry. -/
def wholeRoundedCanonicalPullback :
    ωX ⟶ (pushforward π).obj (Scheme.Modules.tensorObj ωY (J).toModules) :=
  (pullbackPushforwardAdjunction π).unit.app ωX ≫
    (pushforward π).map
      (actualRoundedFactor F n L m σ hL hD f hG hRows hm hfield a ha)

/-- Its entire original inclusion composite is the same original adjunction
unit followed by the same original canonical differential. -/
theorem wholeRoundedCanonicalPullback_inclusion :
    wholeRoundedCanonicalPullback F n L m σ hL hD f hG hRows hm hfield a ha ≫
      (pushforward π).map
        (SchemeTensorObjMorphisms.tensorObjIdealMap ωY (J).toModules (J).toModulesInclusion) =
      (pullbackPushforwardAdjunction π).unit.app ωX ≫
        (pushforward π).map (exteriorCotangentSheafPullbackMap f π n) := by
  exact mappedFactor (pushforward π) ((pullbackPushforwardAdjunction π).unit.app ωX)
    (actualRoundedFactor F n L m σ hL hD f hG hRows hm hfield a ha)
    (SchemeTensorObjMorphisms.tensorObjIdealMap ωY (J).toModules (J).toModulesInclusion)
    (exteriorCotangentSheafPullbackMap f π n)
    (actualRoundedFactor_inclusion F n L m σ hL hD f hG hRows hm hfield a ha)

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalPushforward
