import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRatioNormalization
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceChartNativeDifferentialSquare
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRegularPulledLineChartRestriction

/-!
# The point candidates normalize the restricted canonical differential

Let `π : Y' → X` be the normalized adapted Kummer cover of an SNC datum on a smooth integral
`k`-scheme `X`, `ω_X = Ω^n_{X/k}`, `ω_{Y'} = Ω^n_{Y'/k}`, and let
`dπ : π^* ω_X ⟶ ω_{Y'}` be the canonical differential. Every point `x ∈ X` carries a whole free
chart `C = producedCanonicalCandidateChart … x`: an affine open `U ∋ x`, the ratio algebra
`B_r` over `Γ(X, U)` with `π⁻¹ U ≅ Spec B_r`, and the ratio candidate
`τ_x : p_* ω_{Spec B_r} ⟶ ω_U` (`producedCanonicalCandidate`). Transported along the fixed
native comparisons `(π_* ω_{Y'})|_U ≅ p_* ω_{Spec B_r}` and `ω_X|_U ≅ ω_U` it becomes the point
candidate `θ_x : (π_* ω_{Y'})|_U ⟶ ω_X|_U` (`producedOriginalCanonicalCandidate`).

Main result, `producedOriginalCanonicalCandidate_differential`: under
`MixedCanonicalCandidateNormalization k`,
`(π_* dπ)|_U ≫ θ_x = (T_π)|_U`,
where `T_π : π_* π^* ω_X ⟶ ω_X` is the regular pulled-line trace
(`regularPulledCanonicalTrace`, the structure-sheaf trace of the finite flat cover tensored with
`ω_X`). This is the local normalization step of the construction of the canonical trace of the
cover (relative Nadel vanishing via the Kawamata covering trick, Lazarsfeld II, Thm 9.4.8 and
Kollár–Mori 2.64). The proof composes three squares:

* the chart normalization `p_*(dp) ≫ τ_x = T_p` (`ratioCanonicalSheafCandidate_differential`),
* the fixed chart differential square `(π_* dπ)|_U ≫ e_S = e_P ≫ p_*(dp)`
  (`WholeFreeChart.canonicalSourceRestrictionIso_differential`),
* the chart restriction of the pulled-line trace `(T_π)|_U ≫ e_B = e_P ≫ T_p`
  (`regularPulledCanonicalTrace_wholeChart_fixed_restriction_captured`),

assembled by the abstract lemma `point_normalization_assembly`.

## Implementation notes

No two concrete composites of morphisms of sheaves of modules are compared, by the unifier or
by the kernel, unless they are syntactically identical: `CategoryStruct.comp`, `Functor.map` and
`Iso.hom` are projections, so a comparison of composites that differ only by folded definitions
(`C.scalarMap` against its unfolding, `Spec Γ(X, U)` against `Spec (CommRingCat.of ↑Γ(X, U))`)
unfolds the concrete composition down to the structure sheaf (a kernel deterministic timeout on
the chart traces). Only applications of regular definitions are compared with differing
arguments, which both checkers do argument by argument. Concretely:

* the captured chart-restriction square is transported by the abstract congruence
  `point_square_congr`; three of its side identities unfold one definition into a syntactically
  equal term;
* its fourth side identifies the production map `T_N` with the chart trace through the regular
  definition `pointLineTraceWord`, whose body is `T_N` word for word, and the generic identity
  `affinePulledLineTrace_eq_pointLineTraceWord` (proved once, for arbitrary rings);
* the chart normalization is obtained by `apply`, where the metavariables of the ratio theorem
  are assigned by first-order unification.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Scheme.Modules CanonicalGeometry
open NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedModel
open NadelGlobalStructureTrace
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Assembly of three commuting squares in an arbitrary category: if
`d ≫ e_S = e_P ≫ d'`, `d' ≫ τ = T_N` and `T_p ≫ e_B = e_P ≫ T_N`, then
`d ≫ (e_S ≫ τ ≫ e_B⁻¹) = T_p`. -/
private theorem point_normalization_assembly {E : Type*} [Category E] {P Q R S V W : E}
    (d : P ⟶ Q) (eS : Q ≅ R) (eP : P ≅ S) (d' : S ⟶ R) (τ : R ⟶ W) (eB : V ≅ W)
    (TN : S ⟶ W) (Tp : P ⟶ V)
    (hsq : d ≫ eS.hom = eP.hom ≫ d') (hchart : d' ≫ τ = TN)
    (hglobal : Tp ≫ eB.hom = eP.hom ≫ TN) :
    d ≫ (eS.hom ≫ τ ≫ eB.inv) = Tp := by
  rw [← Category.assoc, hsq, Category.assoc, ← Category.assoc d' τ, hchart, ← Category.assoc,
    ← hglobal, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Transport of a commuting square `a ≫ b = c ≫ d` along equalities of its four sides, in an
arbitrary category. -/
private theorem point_square_congr {E : Type*} [Category E] {P Q R S : E}
    {a a' : P ⟶ Q} {b b' : Q ⟶ R} {c c' : P ⟶ S} {d d' : S ⟶ R}
    (h : a ≫ b = c ≫ d) (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    a' ≫ b' = c' ≫ d' := by
  subst ha hb hc hd
  exact h

section PointLineTraceWord

/- The monoidal structure and the left-unit constraint of the production pulled-line traces
(`NadelGlobalCanonicalTraceOriginalLineTraceFixedRestriction`), so that `pointLineTraceWord`
elaborates to the same term as their `TN`. -/
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

run_cmd
  let name := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.actualLeftUnit
  unless (← Lean.getEnv).contains name do
    throwError "missing the left-unit constraint of the global pulled-line trace {name}"
  Lean.Elab.Command.modifyScope fun scope =>
    { scope with openDecls := Lean.OpenDecl.explicit `pointLineLeftUnit name :: scope.openDecls }

/-- The pulled-line trace word of a morphism `q : T ⟶ S` with coefficients in an invertible
`𝒪_S`-module `N`, for a structure trace `ν : q_* 𝒪_T ⟶ 𝒪_S`:
`q_* q^* N ≅ q_*(𝒪 ⊗ q^* N) ≅ q_* 𝒪 ⊗ N → 𝒪 ⊗ N ≅ N`.
Its body is word for word the map `TN` of
`originalLineTrace_nativeFixedLineRestriction`, with the same left-unit constraint. -/
private def pointLineTraceWord {S T : Scheme.{u}} (q : T ⟶ S) (N : S.Modules)
    (hN : IsInvertible N) (ν : (pushforward q).obj (unitObj T) ⟶ unitObj S) :
    (pushforward q).obj ((pullback q).obj N) ⟶ N :=
  (pushforward q).map (pointLineLeftUnit ((pullback q).obj N)).inv ≫
    (SchemeLineProjectionFormula.lineProjectionFormulaObj q N hN (unitObj T)).inv ≫
    (MonoidalCategory.tensorRight N).map ν ≫ (pointLineLeftUnit N).hom

-- Heartbeats (lane NV8): this generic bridge is proved by `rfl` for arbitrary rings, about 15 s of
-- elaboration and 15 s of kernel checking, once; NV3's `affinePulledLineTrace` equals the TN
-- pattern `pointLineTraceWord` definitionally but not syntactically.
set_option maxHeartbeats 400000 in
/-- The affine pulled-line trace is the pulled-line trace word of the spectrum map with the
affine structure trace. The two sides differ only by the forms `Spec (CommRingCat.of ↑A)` and
`Spec A` of the same schemes in implicit positions (the body of `affinePulledLineTrace` uses
both), so the identification is a definitional unfolding through the monoidal structure of
`(Spec A).Modules`. It is proved once for arbitrary `A`, `B` (about 15 s of elaboration and 15 s
of kernel checking, hence the raised heartbeat budget) and only instantiated on concrete
charts. -/
private theorem affinePulledLineTrace_eq_pointLineTraceWord (A B : CommRingCat.{u})
    (_ : Algebra A B) (_ : Module.Free A B) (_ : Module.Finite A B) (M : (Spec A).Modules)
    (hM : IsInvertible M) :
    affinePulledLineTrace A B M hM =
      pointLineTraceWord (Spec.map (CommRingCat.ofHom (algebraMap A B))) M hM
        (affineStructureTrace A B) := by
  rfl

end PointLineTraceWord

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
    {k : Type u} [Field k] [PerfectField k] [CharZero k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))
    (hmix : MixedCanonicalCandidateNormalization k)

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)
local notation "𝒞" x:max => producedCanonicalCandidateChart F n L m σ hL hD f hG hRows hm hfield x

run_cmd
  let name := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePointSheafCandidate
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.pointCanonicalCandidateData
  unless (← Lean.getEnv).contains name do
    throwError "missing original point canonical candidate producer"
  Lean.Elab.Command.modifyScope fun scope =>
    { scope with openDecls :=
        Lean.OpenDecl.explicit `originalPointCanonicalCandidateData name :: scope.openDecls }

/-- The affine pulled-line trace of a whole free chart, with coefficients in the canonical
line `ω_U` of its base. -/
private def chartCanonicalPulledTrace {D : ℕ} (C : WholeFreeChart π D) :
    (pushforward C.scalarMap).obj
      ((pullback C.scalarMap).obj (canonicalLineSheaf (C.base.2.fromSpec ≫ f) n)) ⟶
        canonicalLineSheaf (C.base.2.fromSpec ≫ f) n := by
  let _ := C.algebra
  let _ : Module.Free Γ(X, C.base.1) C.coeff := Module.Free.of_basis C.basis
  let _ : Module.Finite Γ(X, C.base.1) C.coeff := Module.Finite.of_basis C.basis
  let : IsIso (exteriorCotangentSheafPullbackMap f C.base.2.fromSpec n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion f C.base.2.fromSpec n
  let hN : IsInvertible (canonicalLineSheaf (C.base.2.fromSpec ≫ f) n) :=
    ((canonicalLineSheaf_isInvertible f n).pullback C.base.2.fromSpec).of_iso
      (asIso (exteriorCotangentSheafPullbackMap f C.base.2.fromSpec n)).symm
  exact affinePulledLineTrace Γ(X, C.base.1) C.coeff _ hN

include hL hD f hG hRows hm hfield

omit [CharZero k] in
/-- The chart restriction of the regular pulled-line trace, on an arbitrary whole free chart:
`(T_π)|_U ≫ e_B = e_P ≫ T_p`. This is the captured production square, with its four sides
identified with the fixed comparisons `canonicalBaseRestrictionIso`,
`canonicalPullbackRestrictionIso`, the regular pulled-line trace and the chart trace. -/
private theorem regularPulledCanonicalTrace_chart_square
    (C : WholeFreeChart π
      (NadelWholeCoverDegree.degree (NadelAdaptedChartMatching.Joined.degree F n m)))
    [Nonempty C.base.1] :
    (restrictFunctor C.base.2.fromSpec).map
        (regularPulledCanonicalTrace F n L m σ hL hD f hG hRows hm hfield) ≫
      (C.canonicalBaseRestrictionIso f n).hom =
    (C.canonicalPullbackRestrictionIso f n).hom ≫ chartCanonicalPulledTrace F n L m σ f C := by
  refine point_square_congr (regularPulledCanonicalTrace_wholeChart_fixed_restriction_captured
    F n L m σ hL hD f hG hRows hm hfield C) ?_ ?_ ?_ ?_
  · refine congrArg (fun t => (restrictFunctor _).map t) ?_
    delta regularPulledCanonicalTrace
    rfl
  · refine congrArg Iso.hom ?_
    rfl
  · refine congrArg Iso.hom ?_
    rfl
  · -- `T_N` is the pulled-line trace word of `C.scalarMap`; the chart trace is the same word
    -- for the unfolded spectrum map, by the generic identification.
    refine Eq.trans (b := pointLineTraceWord C.scalarMap _ _ _) rfl ?_
    delta chartCanonicalPulledTrace
    dsimp only
    exact (affinePulledLineTrace_eq_pointLineTraceWord _ _ _ _ _ _ _).symm

include hmix

/-- The point chart candidate normalizes the chart's own canonical differential:
`p_*(dp) ≫ τ_x = T_p` on the produced chart of `x`. -/
private theorem producedCanonicalCandidate_chart_differential (x : X) :
    (pushforward (𝒞 x).scalarMap).map
        (exteriorCotangentSheafPullbackMap ((𝒞 x).base.2.fromSpec ≫ f) (𝒞 x).scalarMap n) ≫
      producedCanonicalCandidate F n L m σ hL hD f hG hRows hm hfield x =
    chartCanonicalPulledTrace F n L m σ f (𝒞 x) := by
  delta producedCanonicalCandidateChart producedCanonicalCandidate
    originalPointCanonicalCandidateData chartCanonicalPulledTrace WholeFreeChart.scalarMap
  dsimp only
  -- `[Nonempty U.1]` of the ratio theorem is assigned by unification, not synthesized.
  apply -synthAssignedInstances @ratioCanonicalSheafCandidate_differential
  exact hmix

/-- **Point normalization.** Under the normalization of the mixed candidate, the point
candidate `θ_x` composed with the restriction to the chart base `U ∋ x` of the pushed canonical
differential `π_* dπ` is the restriction to `U` of the regular pulled-line trace. -/
theorem producedOriginalCanonicalCandidate_differential (x : X) :
    (restrictFunctor (𝒞 x).base.2.fromSpec).map
        ((pushforward π).map (exteriorCotangentSheafPullbackMap f π n)) ≫
      producedOriginalCanonicalCandidate F n L m σ hL hD f hG hRows hm hfield x =
    (restrictFunctor (𝒞 x).base.2.fromSpec).map
      (regularPulledCanonicalTrace F n L m σ hL hD f hG hRows hm hfield) := by
  have : Nonempty (𝒞 x).base.1 :=
    ⟨⟨x, mem_producedCanonicalCandidateChart F n L m σ hL hD f hG hRows hm hfield x⟩⟩
  have hchart := producedCanonicalCandidate_chart_differential F n L m σ hL hD f hG hRows hm
    hfield hmix x
  have hglobal := regularPulledCanonicalTrace_chart_square F n L m σ hL hD f hG hRows hm hfield
    (𝒞 x)
  exact point_normalization_assembly _ _ _ _ _ _ _ _
    ((𝒞 x).canonicalSourceRestrictionIso_differential f n) hchart hglobal

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
