import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceOpenEtaleCancellation
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureChartGenericFiber

/-! # Actual whole-chart cancellation into the SAME original generic target

The actual whole chart is cartesian over the original cover. Its intersection
with the internally produced etale neighborhood is again etale, by two genuine
pullback squares. The original generic field point factors through that open.
The existing etale-open cancellation theorem therefore applies without a new
chart function field, a component choice or a supplied etale certificate.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelGlobalAdaptedModel NadelGlobalStructureTrace
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem chart_etale_on_original_open
    {X Y A B V : Scheme.{u}} (π : Y ⟶ X) (β : B ⟶ A)
    (a : A ⟶ X) (g : B ⟶ Y) (H : IsPullback β g a π)
    (j : V ⟶ X) [Etale (pullback.snd π j)] :
    Etale (pullback.snd β (pullback.snd j a)) := by
  have hrect := (IsPullback.of_hasPullback β (pullback.snd j a)).paste_horiz H.flip
  have hbase : pullback.snd j a ≫ a = pullback.fst j a ≫ j :=
    (pullback.condition (f := j) (g := a)).symm
  rw [hbase] at hrect
  exact MorphismProperty.of_isPullback
    (IsPullback.of_right' hrect (IsPullback.of_hasPullback π j))
    (inferInstance : Etale (pullback.snd π j))

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

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)

include hL hD f hG hRows hm hfield

/-- The original canonical differential of an actual WHOLE affine chart
can be canceled in maps to its SAME original generic-field pushforward.
The etale open and the original generic-point factor are produced inside
the proof from the original cover and the chart's actual cartesian square. -/
theorem wholeFreeChart_differential_genericTarget_hom_ext
    {D : ℕ} (C : WholeFreeChart π D) [Nonempty C.base.1]
    (N : (Spec X.functionField).Modules)
    (a b : (pushforward C.scalarMap).obj
      (exteriorCotangentSheaf (C.scalarMap ≫ (C.base.2.fromSpec ≫ f)) n) ⟶
        (pushforward C.genericBaseMap).obj N)
    (h : (pushforward C.scalarMap).map
        (exteriorCotangentSheafPullbackMap (C.base.2.fromSpec ≫ f) C.scalarMap n) ≫ a =
      (pushforward C.scalarMap).map
        (exteriorCotangentSheafPullbackMap (C.base.2.fromSpec ≫ f) C.scalarMap n) ≫ b) :
    a = b := by
  obtain ⟨R, j, t, hj, ht, hq⟩ :=
    NadelGlobalCanonicalTraceGenericBranch.exists_original_etale_neighborhood
      F n L m σ hL hD f hG hRows hm hfield
  let : IsOpenImmersion j := hj
  let : Etale (pullback.snd π j) := hq
  let i := pullback.snd j C.base.2.fromSpec
  let : IsOpenImmersion i := inferInstance
  let : Etale (pullback.snd C.scalarMap i) :=
    chart_etale_on_original_open π C.scalarMap C.base.2.fromSpec C.sourceMap C.isPullback j
  let tC : Spec X.functionField ⟶ pullback j C.base.2.fromSpec :=
    pullback.lift t C.genericBaseMap (ht.trans C.genericBaseMap_over_original.symm)
  have htC : tC ≫ i = C.genericBaseMap := pullback.lift_snd _ _ _
  let : SmoothOfRelativeDimension n (C.base.2.fromSpec ≫ f) := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (C.base.2.fromSpec ≫ f))
  exact differential_target_hom_ext_of_etale_open
    (C.base.2.fromSpec ≫ f) C.scalarMap n i C.genericBaseMap tC htC N a b h

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
