import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRationalNativeNaturality
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceFunctorCancellation

/-! # The frozen original generic canonical map is retained in the native calculation

The generic map is an ordinary module map, and its differential identity
is the ordinary geometric hypothesis of this framework. The original
SNC application will use the already proved frozen original map and
identity, preserving all of its original native source/target data.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  for (short, original) in [
      (`frozenOriginalModuleSquareMap,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalModuleSquareMap),
      (`frozenGenericSourceComparison,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.genericSourceComparison),
      (`frozenWholeFieldLineTrace,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.wholeFieldLineTrace)] do
    let name := Lean.mkPrivateNameCore
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational original
    unless (← Lean.getEnv).contains name do
      throwError "missing frozen original rational-trace helper {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

variable {X Y : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (π : Y ⟶ X) [IsFinite π]
    (n : ℕ) [SmoothOfRelativeDimension n f]

local notation "γ" => X.fromSpecStalk (genericPoint X)
local notation "pη" => pullback.fst π γ
local notation "qη" => pullback.snd π γ
local notation "ωX" => canonicalLineSheaf f n
local notation "ωY" => canonicalLineSheaf (π ≫ f) n
local notation "δ" => exteriorCotangentSheafPullbackMap f π n

/-- Native geometric naturality with the original generic canonical map
kept opaque. The actual original application supplies this map and its
native differential identity internally from the frozen original producer. -/
theorem native_rational_differential_core_factor
    (α : (Scheme.Modules.pullback pη).obj ωY ⟶
      (Scheme.Modules.pullback qη).obj ((Scheme.Modules.pullback γ).obj ωX))
    (hα : (Scheme.Modules.pullback pη).map δ ≫ α =
      (frozenGenericSourceComparison π ωX).hom) :
    let T := frozenWholeFieldLineTrace X.functionField (Field.toIsField X.functionField) qη
      ((Scheme.Modules.pullback γ).obj ωX) ((canonicalLineSheaf_isInvertible f n).pullback γ)
    (pushforward π).map δ ≫
      (frozenOriginalModuleSquareMap π qη pη γ pullback.condition ωY ≫
        (pushforward γ).map ((pushforward qη).map α ≫ T)) =
      frozenOriginalModuleSquareMap π qη pη γ pullback.condition
          ((Scheme.Modules.pullback π).obj ωX) ≫
        (pushforward γ).map
          ((pushforward qη).map (frozenGenericSourceComparison π ωX).hom ≫ T) := by
  let Δ : (Scheme.Modules.pullback π).obj ωX ⟶ ωY := by
    dsimp only [canonicalLineSheaf]
    exact δ
  let T := frozenWholeFieldLineTrace X.functionField (Field.toIsField X.functionField) qη
    ((Scheme.Modules.pullback γ).obj ωX) ((canonicalLineSheaf_isInvertible f n).pullback γ)
  exact naturality_factor_comp_two (pushforward π) (Scheme.Modules.pullback pη)
    (pushforward qη) (pushforward γ)
    (M := (Scheme.Modules.pullback π).obj ωX) (N := ωY)
    (Z := (Scheme.Modules.pullback qη).obj ((Scheme.Modules.pullback γ).obj ωX))
    (W := (Scheme.Modules.pullback γ).obj ωX) Δ
    (frozenOriginalModuleSquareMap π qη pη γ pullback.condition
      ((Scheme.Modules.pullback π).obj ωX))
    (frozenOriginalModuleSquareMap π qη pη γ pullback.condition ωY)
    (moduleSquareMap_naturality π qη pη γ pullback.condition Δ)
    α (frozenGenericSourceComparison π ωX).hom hα T

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
