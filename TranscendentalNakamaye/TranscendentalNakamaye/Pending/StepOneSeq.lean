import TranscendentalNakamaye.Pending.ExtSeqTransport
import TranscendentalNakamaye.Pending.MaxOrderValue
import TranscendentalNakamaye.Pending.StepOnePhase

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Step 1 (maximal-order) value for a lower invariant with per-sequence local finiteness

Blueprint `hir:step-one-seq` (`blueprint/src/hironaka.tex`, Hironaka phase H4).  Human decision I-1139 C-0001 (option (b)):
a resolution invariant is `ResolutionInvariantSeq.ResolutionInvariant`.  The orchestrator's review of 3 October 2026
(`.archon-horizon/scratch/orchestrator-review-seq-induction-20261003.md`, finding F1): the Step 1 value `stepOneInvM` and its
properties were formalized for a lower invariant `R : ResolutionInvariantExt.ResolutionInvariant n (k - 1) Λ` (uniform (8)),
which the induction of `hir:canonical-centres` cannot supply.

**The Step 1 stack for the new structure.**  The command `transport_ext_to_seq_module` (`ExtSeqTransport`) adds, for every
declaration of the modules listed below that depends on `ResolutionInvariantExt.ResolutionInvariant`, a kernel-checked copy in
the namespace `TranscendentalNakamaye.Pending.Seq` (e.g. `Seq.StepOneValueMasked.stepOneInvM`,
`Seq.StepOneBridge.admissible_field`, `Seq.MaxOrderValue.isMaxOrderValue_stepOneInvM`), stated for
`R : ResolutionInvariantSeq.ResolutionInvariant`, with `R.f` replaced by `R.isInvValue.f` for the fields (1)--(7), (4').  That the
command succeeds shows that none of these proofs uses property (8) of the lower invariant.

## Main results (stated here as ordinary theorems)

* **`isMaxOrderValue_stepOneInvM`**: for `R : ResolutionInvariantSeq.ResolutionInvariant n (k - 1) Λ` and `0 < n`, the masked
  Step 1 value `Seq.StepOneValueMasked.stepOneInvM R` is a value function for the marked ideals of maximal order in dimension
  `≤ k` (`MaxOrderValue.IsMaxOrderValue`);
* `stepOneInvM_ofExt`: for an invariant of the old structure, the new value of `ofExt R` is the old value of `R` (by `rfl`), so
  the old results are the new ones read through `ResolutionInvariantSeq.ResolutionInvariant.ofExt`;
* `stepDrop_stepOneInvM`, `isAdmissibleCentre_maxLocus_stepOneInvM`, `exists_isGeoResolution_stepOneInvM`: the drop along
  canonical segments, the admissibility of the maximum locus, and the resolution of a marked ideal of maximal order for
  well-founded `Λ` (`StepOneWellFounded`), for the new structure.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Pending.RelativePrincipalization` or `Pending.EmbeddedResolution`.  Sorry-free.
-/

open TranscendentalNakamaye.Pending.ExtSeqTransport

/-! ### The transport of the Step 1 stack -/

transport_ext_to_seq_module
  TranscendentalNakamaye.Pending.BlowupTowerSplit TranscendentalNakamaye.Pending.MaxLocusLocal
  TranscendentalNakamaye.Pending.InvDomainRebase TranscendentalNakamaye.Pending.MaximalOrderStepOneB
  TranscendentalNakamaye.Pending.ContactStageRebase TranscendentalNakamaye.Pending.ContactMarkedCanonical
  TranscendentalNakamaye.Pending.ContactRepresentative TranscendentalNakamaye.Pending.ContactStageKept
  TranscendentalNakamaye.Pending.ContactEmptyPrefix TranscendentalNakamaye.Pending.ContactLowerValue
  TranscendentalNakamaye.Pending.MemberRestrictTowerIso TranscendentalNakamaye.Pending.CompanionRebase
  TranscendentalNakamaye.Pending.NonmonomialOrderRegime
  TranscendentalNakamaye.Pending.StepOneValue TranscendentalNakamaye.Pending.StepOneNearby
  TranscendentalNakamaye.Pending.StepOneValueMasked TranscendentalNakamaye.Pending.StepOneCompare
  TranscendentalNakamaye.Pending.StepOneTangentChange TranscendentalNakamaye.Pending.StepOneCanonicalTail
  TranscendentalNakamaye.Pending.StepOneUSC TranscendentalNakamaye.Pending.StepOneAdmissibleTop
  TranscendentalNakamaye.Pending.StepOneSpecialDrop TranscendentalNakamaye.Pending.StepOneAdmissible
  TranscendentalNakamaye.Pending.StepOneEmptyPrefix TranscendentalNakamaye.Pending.StepOneRepresentative
  TranscendentalNakamaye.Pending.StepOneRestrictOpen TranscendentalNakamaye.Pending.StepOneTowerIso
  TranscendentalNakamaye.Pending.StepOneBridge TranscendentalNakamaye.Pending.StepOneWellFounded
  TranscendentalNakamaye.Pending.StepOnePhase TranscendentalNakamaye.Pending.MaxOrderValue

transport_ext_to_seq
  TranscendentalNakamaye.Pending.ResolutionInvariantExt.isAdmissibleCentre_maxLocus
  TranscendentalNakamaye.Pending.ResolutionInvariantExt.isGeoTestTower_of_isCanonical
  TranscendentalNakamaye.Pending.ResolutionInvariantExt.isInvDomain_of_isCanonical
  TranscendentalNakamaye.Pending.ResolutionInvariantExt.isCanonical_restrict
  TranscendentalNakamaye.Pending.ResolutionInvariantExt.isCanonical_of_isTowerIso
  TranscendentalNakamaye.Pending.ResolutionInvariantExt.isCanonical_append_iff

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace TranscendentalNakamaye.Pending.StepOneSeq

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
open TranscendentalNakamaye.Pending.MarkedIdeals TranscendentalNakamaye.Pending.MarkedIdeals.MarkedIdeal
  TranscendentalNakamaye.Pending.BlowupTowers TranscendentalNakamaye.Pending.BlowupTowerTransforms
  TranscendentalNakamaye.Pending.MaxOrderValue TranscendentalNakamaye.Pending.ResolutionInvariantSeq
  TranscendentalNakamaye.Pending.StepOneWellFounded
open TranscendentalNakamaye.Pending.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open TranscendentalNakamaye.Pending.ResolutionDriver (maxLocus IsCanonicalSegment)
open TranscendentalNakamaye.Pending.HomogenizedIdealAlong (IsMaximalOrderAlong)

noncomputable section

variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ] {X : CMfd.{u} n}

/-- **The new Step 1 value extends the old one**: for an invariant `R` of the old structure, the masked Step 1 value of
`ofExt R` is that of `R`. -/
theorem stepOneInvM_ofExt (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    Seq.StepOneValueMasked.stepOneInvM (ResolutionInvariant.ofExt R) 𝔍 T y = StepOneValueMasked.stepOneInvM R 𝔍 T y :=
  rfl

/-- **The masked Step 1 value of a lower invariant of the new structure is a value function for the marked ideals of
maximal order** (`hir:step-one-seq`; `0 < n`): properties (1)--(7), (4') along its canonical segments, for every marked ideal
of the domain in dimension `≤ k` of maximal order along its submanifold. -/
theorem isMaxOrderValue_stepOneInvM (R : ResolutionInvariant.{u, v} n (k - 1) Λ) (hn : 0 < n) :
    IsMaxOrderValue n k (fun {X} 𝔍 {Y} T y => Seq.StepOneValueMasked.stepOneInvM (X := X) R 𝔍 (Y := Y) T y) :=
  Seq.MaxOrderValue.isMaxOrderValue_stepOneInvM R hn

/-- **The value drops along canonical segments** (the hypothesis of the well-founded driver), for the new structure. -/
theorem stepDrop_stepOneInvM (R : ResolutionInvariant.{u, v} n (k - 1) Λ) {𝔍 : MarkedIdeal n X} (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) :
    StepDrop 𝔍 (Seq.StepOneValueMasked.stepOneInvM R 𝔍) :=
  Seq.StepOneWellFounded.stepDrop_stepOneInvM R 𝔍 h hmax hn

/-- **The maximum locus is an admissible centre** along a canonical segment, for the new structure. -/
theorem isAdmissibleCentre_maxLocus_stepOneInvM (R : ResolutionInvariant.{u, v} n (k - 1) Λ) {𝔍 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hcan : IsCanonical 𝔍 (Seq.StepOneValueMasked.stepOneInvM R 𝔍) T) :
    (geoTransformAlong 𝔍 T).IsAdmissibleCentre
      (maxLocus (Seq.StepOneValueMasked.stepOneInvM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) :=
  Seq.StepOneWellFounded.isAdmissibleCentre_maxLocus_stepOneInvM R 𝔍 h hmax hn T hcan

/-- **Well-founded lower values resolve the marked ideals of maximal order** over a compact base by a canonical segment of the
Step 1 value, for the new structure. -/
theorem exists_isGeoResolution_stepOneInvM [CompactSpace X] [WellFoundedLT Λ] (R : ResolutionInvariant.{u, v} n (k - 1) Λ)
    {𝔍 : MarkedIdeal n X} (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonicalSegment 𝔍 (Seq.StepOneValueMasked.stepOneInvM R 𝔍) T ∧ IsGeoResolution 𝔍 T :=
  Seq.StepOneWellFounded.exists_isGeoResolution_stepOneInvM R 𝔍 h hmax hn

end

end TranscendentalNakamaye.Pending.StepOneSeq
