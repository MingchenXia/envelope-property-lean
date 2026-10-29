import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.StepOneSeq
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.GeneralSeqFinite

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The canonical resolution invariant: induction on the dimension

A resolution invariant is `ResolutionInvariantSeq.ResolutionInvariant` (properties (1)--(7), (4')
and the per-sequence local finiteness (8')).  Sources: Włodarczyk, *Simple Hironaka resolution in characteristic zero*
(arXiv:math/0401401), Proposition 3.0.8 (induction on the dimension; the values are discrete, so
the procedure terminates); Bierstone--Milman 2008.

## Main results

* `stepDrop_of_isInvValue`, **`seqLocallyFinite_of_wellFoundedLT`**: properties (3), (4) give the
  drop of the values along canonical segments, so along a growing sequence of canonical segments the values of the nonempty
  centres form ONE strictly decreasing list growing by appending (`StepOnePhase.pairwise_centreValues`,
  `GeneralPhaseCount.centreValues_isPrefix_succ`); with well-founded values its length is bounded
  (`GeneralPhaseCount.exists_bound_of_isPrefix`), and it bounds the numbers of centres meeting any set.  So **property (8') holds
  for every value function with (1)--(7), (4') and well-founded values** (`ofWellFounded`); likewise for the marked ideals of
  maximal order (`seqLocallyFiniteMaxOrder_of_wellFoundedLT`, the hypothesis of `GeneralSeqFinite.ofMaxOrder`);
* **`generalStep`** (`0 < n`): a resolution invariant in dimension `≤ k` with well-founded values gives one in
  dimension `≤ k + 1` with well-founded values: the general value of the masked Step 1 value (`StepOneSeq`,
  `GeneralStepValue.isInvValue_genInv`, `NonmonomialOrderGlobalPhase.wellFoundedLT_genValue`);
* `ValTy k`: the value types, by recursion (`ValTy 0 = ℕ`, `ValTy (k + 1)` the value type of the general step over `ValTy k`),
  linearly and well ordered;
* **`invFamily`** (`0 < n`): a resolution invariant in dimension `≤ k` with values in `ValTy k`, for
  every `k`, by induction (`ResolutionInvariantSeq.ResolutionInvariant.ofDimZero` for `k = 0`);
* **`canonicalInvariant n`**: a resolution invariant in dimension `≤ n` on complex manifolds of dimension `n`, every `n`
  (`n = 0`: `ofDimZero`); **`exists_resolutionInvariant`**: for `k ≤ n` there is a resolution invariant in dimension `≤ k` with
  well-ordered values.

This module does not import, even transitively, `AnalyticGeometry.RelativePrincipalization` or
`AnalyticGeometry.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace ComplexGeometry.AnalyticGeometry.CanonicalCentres

open Pluripotential Pluripotential.HolomorphicIdealSheaves Pluripotential.BlowupSequences
open ComplexGeometry.AnalyticGeometry.MarkedIdeals ComplexGeometry.AnalyticGeometry.MarkedIdeals.MarkedIdeal
  ComplexGeometry.AnalyticGeometry.BlowupTowers ComplexGeometry.AnalyticGeometry.BlowupTowerTransforms
  ComplexGeometry.AnalyticGeometry.ResolutionInvariantSeq ComplexGeometry.AnalyticGeometry.StepOnePhase
  ComplexGeometry.AnalyticGeometry.StepOneWellFounded ComplexGeometry.AnalyticGeometry.MaxOrderValue
  ComplexGeometry.AnalyticGeometry.GeneralValue
open ComplexGeometry.AnalyticGeometry.ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
open ComplexGeometry.AnalyticGeometry.ResolutionDriver (maxLocus)
open ComplexGeometry.AnalyticGeometry.MonomialInvariant (Val)

noncomputable section

variable {n : ℕ}

/-! ### Property (8') from well-founded values -/

section WellFounded

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Properties (3) and (4) give the drop along canonical segments** (`StepOneWellFounded.StepDrop`): after a step of a
canonical segment a point of the new cosupport lies over the cosupport, with a smaller value over the centre and the same value
off it. -/
theorem stepDrop_of_isInvValue (hI : IsInvValue n k inv) {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) : StepDrop 𝔪 (inv 𝔪) := by
  intro Y Z T C π hπ hcan z hz
  have hTs := hI.isGeoTestTower_of_isCanonical h _ hcan
  obtain ⟨hT, hC⟩ : IsCanonical 𝔪 (inv 𝔪) T ∧
      (C = ∅ ∨ C = maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := hcan
  refine ⟨proj_mem_cosupp_step h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T C π hπ hTs hz, ?_⟩
  rcases hC with hC | hC
  · refine ⟨fun hzC => ?_, fun _ => hI.emptyStep 𝔪 h T C π hπ hC hT z hz⟩
    rw [hC] at hzC
    exact absurd hzC (notMem_empty _)
  · by_cases hne : C.Nonempty
    · exact hI.decrease 𝔪 h T C π hπ hT hne hC z hz
    · have hC0 : C = ∅ := not_nonempty_iff_eq_empty.mp hne
      refine ⟨fun hzC => ?_, fun _ => hI.emptyStep 𝔪 h T C π hπ hC0 hT z hz⟩
      rw [hC0] at hzC
      exact absurd hzC (notMem_empty _)

/-- **Property (8') is free for well-founded values**: a value function with properties
(1)--(7), (4') and well-founded values has property (8') -- along every growing sequence of canonical segments the numbers of
centres meeting any set are bounded. -/
theorem seqLocallyFinite_of_wellFoundedLT [WellFoundedLT Λ] (hI : IsInvValue n k inv) : SeqLocallyFinite n k inv := by
  intro X 𝔪 h K _ s hs
  have hdrop : StepDrop 𝔪 (inv 𝔪) := stepDrop_of_isInvValue hI h
  obtain ⟨m, hm⟩ := GeneralPhaseCount.exists_bound_of_isPrefix (fun i => centreValues (inv 𝔪) (s.stage i).2)
    (fun i => GeneralPhaseCount.centreValues_isPrefix_succ (inv 𝔪) s i)
    (fun i => pairwise_centreValues hdrop _ (hs i)) (fun _ => True) (fun _ _ _ => trivial)
    (fun g _ => not_strictAnti_of_wellFoundedLT g)
  exact ⟨m, fun i => (countCentresMeeting_le_length_centreValues (inv 𝔪) K (s.stage i).2).trans (hm i)⟩

variable (n k) in
/-- **A value function with (1)--(7), (4') and well-founded values is a resolution invariant.** -/
def ofWellFounded [WellFoundedLT Λ]
    (inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    (hI : IsInvValue n k inv) : ResolutionInvariant.{u, v} n k Λ :=
  ⟨inv, hI, seqLocallyFinite_of_wellFoundedLT hI⟩

/-- **The same for the marked ideals of maximal order**: a value function for them with well-founded values has property (8')
for them (the hypothesis `hM8` of `GeneralSeqFinite.ofMaxOrder`). -/
theorem seqLocallyFiniteMaxOrder_of_wellFoundedLT [WellFoundedLT Λ]
    {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}
    (hM : IsMaxOrderValue n k M) : GeneralSeqFinite.SeqLocallyFiniteMaxOrder n k M := by
  intro X 𝔍 h hmax K _ s hs
  have hdrop : StepDrop 𝔍 (M 𝔍) := hM.stepDrop h hmax
  obtain ⟨m, hm⟩ := GeneralPhaseCount.exists_bound_of_isPrefix (fun i => centreValues (M 𝔍) (s.stage i).2)
    (fun i => GeneralPhaseCount.centreValues_isPrefix_succ (M 𝔍) s i)
    (fun i => pairwise_centreValues hdrop _ (hs i)) (fun _ => True) (fun _ _ _ => trivial)
    (fun g _ => not_strictAnti_of_wellFoundedLT g)
  exact ⟨m, fun i => (countCentresMeeting_le_length_centreValues (M 𝔍) K (s.stage i).2).trans (hm i)⟩

end WellFounded

/-! ### The general step -/

section Step

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **The general step** (`0 < n`): from a resolution invariant `R` in dimension `≤ k` with well-founded
values, the general value of the masked Step 1 value of `R` is a resolution invariant in dimension `≤ k + 1`. -/
def generalStep [WellFoundedLT Λ] (R : ResolutionInvariant.{u, v} n k Λ) (hn : 0 < n) :
    ResolutionInvariant.{u, v} n (k + 1) (ℕ ×ₗ (WithBot Val ⊕ₗ WithTop (ℕ ×ₗ WithTop Λ))) :=
  haveI := NonmonomialOrderGlobalPhase.wellFoundedLT_genValue (Λ := ℕ ×ₗ WithTop Λ)
  ofWellFounded n (k + 1) (genInv fun {X} 𝔍 {Y} T y => Seq.StepOneValueMasked.stepOneInvM (X := X) R 𝔍 (Y := Y) T y)
    (GeneralStepValue.isInvValue_genInv (StepOneSeq.isMaxOrderValue_stepOneInvM (k := k + 1) R hn) hn)

/-- The invariant of the general step is the general value of the masked Step 1 value. -/
theorem generalStep_inv [WellFoundedLT Λ] (R : ResolutionInvariant.{u, v} n k Λ) (hn : 0 < n) {X : CMfd.{u} n}
    (𝔪 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    (generalStep R hn).inv 𝔪 T y =
      genInv (fun {X} 𝔍 {Y} T y => Seq.StepOneValueMasked.stepOneInvM (X := X) R 𝔍 (Y := Y) T y) 𝔪 T y :=
  rfl

end Step

/-! ### The value types and the induction -/

/-- **The value types**, by recursion on the dimension: `ℕ` in dimension `0`, and in dimension `k + 1` the value type of the
general step over `ValTy k` (lexicographic). -/
def ValTy : ℕ → Type
  | 0 => ℕ
  | k + 1 => ℕ ×ₗ (WithBot Val ⊕ₗ WithTop (ℕ ×ₗ WithTop (ValTy k)))

/-- The linear order and the well-foundedness of `ValTy k`, by recursion. -/
def valTyInst : (k : ℕ) → Σ' _ : LinearOrder (ValTy k), WellFoundedLT (ValTy k)
  | 0 => ⟨(inferInstance : LinearOrder ℕ), (inferInstance : WellFoundedLT ℕ)⟩
  | k + 1 =>
    letI : LinearOrder (ValTy k) := (valTyInst k).1
    haveI : WellFoundedLT (ValTy k) := (valTyInst k).2
    ⟨(inferInstance : LinearOrder (ℕ ×ₗ (WithBot Val ⊕ₗ WithTop (ℕ ×ₗ WithTop (ValTy k))))),
      NonmonomialOrderGlobalPhase.wellFoundedLT_genValue (Λ := ℕ ×ₗ WithTop (ValTy k))⟩

instance (k : ℕ) : LinearOrder (ValTy k) := (valTyInst k).1

instance (k : ℕ) : WellFoundedLT (ValTy k) := (valTyInst k).2

/-- The order of `ValTy (k + 1)` is the lexicographic order built from that of `ValTy k`. -/
theorem linearOrder_valTy_succ (k : ℕ) :
    (inferInstance : LinearOrder (ValTy (k + 1))) =
      (inferInstance : LinearOrder (ℕ ×ₗ (WithBot Val ⊕ₗ WithTop (ℕ ×ₗ WithTop (ValTy k))))) :=
  rfl

/-- **The canonical resolution invariants** (`0 < n`): for every `k`, a resolution invariant in
dimension `≤ k` on complex manifolds of dimension `n`, with values in `ValTy k`; `ofDimZero` for `k = 0`, the general step
(`generalStep`) from `k` to `k + 1`. -/
def invFamily (hn : 0 < n) : (k : ℕ) → ResolutionInvariant.{u, 0} n k (ValTy k)
  | 0 => ResolutionInvariant.ofDimZero (ValTy 0) (0 : ℕ)
  | k + 1 => generalStep (invFamily hn k) hn

/-- The invariant in dimension `≤ k + 1` is the general step of the one in dimension `≤ k`. -/
theorem invFamily_succ (hn : 0 < n) (k : ℕ) : invFamily.{u} hn (k + 1) = generalStep (invFamily.{u} hn k) hn :=
  rfl

variable (n) in
/-- **The canonical resolution invariant in dimension `≤ n`** on complex manifolds of dimension `n` (used in the
proofs of `RelativePrincipalization.exists_factorizationData` and
`EmbeddedResolution.exists_embeddedResolution_smoothData`): `invFamily` for `0 < n`, `ofDimZero` for `n = 0`. -/
def canonicalInvariant : ResolutionInvariant.{u, 0} n n (ValTy n) :=
  match n with
  | 0 => ResolutionInvariant.ofDimZero (ValTy 0) (0 : ℕ)
  | n + 1 => invFamily (Nat.succ_pos n) (n + 1)

/-- **Canonical resolution invariants exist**: for every `n` and every `k ≤ n` there is a resolution
invariant in dimension `≤ k` on complex manifolds of dimension `n` (in the sense of `ResolutionInvariantSeq`), with
well-ordered values. -/
theorem exists_resolutionInvariant (n k : ℕ) (hk : k ≤ n) :
    ∃ (Λ : Type) (_ : LinearOrder Λ) (_ : WellFoundedLT Λ), Nonempty (ResolutionInvariant.{u, 0} n k Λ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : k = 0 := Nat.le_zero.mp hk
    exact ⟨ValTy 0, inferInstance, inferInstance, ⟨ResolutionInvariant.ofDimZero (ValTy 0) (0 : ℕ)⟩⟩
  · exact ⟨ValTy k, inferInstance, inferInstance, ⟨invFamily hn k⟩⟩

end

end ComplexGeometry.AnalyticGeometry.CanonicalCentres
