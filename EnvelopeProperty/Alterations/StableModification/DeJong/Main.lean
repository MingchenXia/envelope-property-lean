import EnvelopeProperty.Alterations.StableModification.DeJong.BaseStep
import EnvelopeProperty.Alterations.StableModification.DeJong.Fibration
import EnvelopeProperty.Alterations.StableModification.DeJong.Induction
import EnvelopeProperty.Alterations.StableModification.Perfection.Global
import EnvelopeProperty.Alterations.StableModification.Flattening.Main
import EnvelopeProperty.Alterations.StableModification.Resolution.GlobalResolution

/-!
# De Jong's Theorem 4.1 over algebraically closed fields from Temkin's theorem

The base step `baseStep : BaseStep k` (de Jong 4.22 with Temkin) is a theorem, so the induction
`deJongAlterationTheorem_of_producers` reduces `DeJongAlterationTheorem k` for algebraically
closed `k` to the input propositions of `Interface.lean` (and, in characteristic `p`,
`Fibration.lean`):

* `PurelyInseparableSmoothing k` (proved: `Perfection.purelyInseparableSmoothing`),
* `FlatteningAfterGEAlteration k` (weak de Jong 2.19; proved:
  `Flattening.flatteningAfterGEAlteration`),
* `TemkinStableModification k` (Temkin's Theorems 1.1 and 1.5, in the form used by the base step),
* `SemistableResolution k` (de Jong 4.23–4.28 with 3.1–3.5 and the 2.4 strictification; proved:
  `Resolution.Global.semistableResolution`).

These are `def … : Prop` statements, not axioms; the theorems below take them as explicit
hypotheses. `deJongAlterationTheorem_of_flattening_stableModification_resolution` uses the
smoothing theorem, `deJongAlterationTheorem_of_stableModification_resolution` also the
flattening theorem, and `deJongAlterationTheorem_of_stableModification` also the resolution
theorem, so that its only hypothesis is `TemkinStableModification k`.
-/

namespace Alterations.StableModification.DeJong

universe u

variable {k : Type u} [Field k]

/-- De Jong 4.1 over an algebraically closed field from the four input propositions. -/
theorem deJongAlterationTheorem_of_remaining [IsAlgClosed k]
    (hPL : PurelyInseparableSmoothing k) (hFLAT : FlatteningAfterGEAlteration k)
    (hTSM : TemkinStableModification k) (hEND : SemistableResolution k) :
    DeJongAlterationTheorem k :=
  deJongAlterationTheorem_of_producers (temkinReadyFibration_of_purelyInseparableSmoothing hPL)
    hFLAT hTSM hEND baseStep

/-- De Jong 4.1 over an algebraically closed field of characteristic zero from the three
remaining input propositions. -/
theorem deJongAlterationTheorem_of_remaining_charZero [IsAlgClosed k] [CharZero k]
    (hFLAT : FlatteningAfterGEAlteration k) (hTSM : TemkinStableModification k)
    (hEND : SemistableResolution k) : DeJongAlterationTheorem k :=
  deJongAlterationTheorem_of_producers temkinReadyFibration_of_charZero hFLAT hTSM hEND baseStep

/-- De Jong 4.1 over an algebraically closed field from three of the input propositions; the
purely inseparable smoothing is `Perfection.purelyInseparableSmoothing`. -/
theorem deJongAlterationTheorem_of_flattening_stableModification_resolution [IsAlgClosed k]
    (hFLAT : FlatteningAfterGEAlteration k) (hTSM : TemkinStableModification k)
    (hEND : SemistableResolution k) : DeJongAlterationTheorem k :=
  deJongAlterationTheorem_of_producers (Perfection.temkinReadyFibration k) hFLAT hTSM hEND baseStep

/-- De Jong 4.1 over an algebraically closed field from Temkin's stable modification and the
semistable resolution; the smoothing and the flattening are proved. -/
theorem deJongAlterationTheorem_of_stableModification_resolution [IsAlgClosed k]
    (hTSM : TemkinStableModification k) (hEND : SemistableResolution k) :
    DeJongAlterationTheorem k :=
  deJongAlterationTheorem_of_flattening_stableModification_resolution
    (Flattening.flatteningAfterGEAlteration k) hTSM hEND

/-- De Jong 4.1 over an algebraically closed field from Temkin's stable modification alone; the
smoothing, the flattening and the semistable resolution are proved. -/
theorem deJongAlterationTheorem_of_stableModification [IsAlgClosed k]
    (hTSM : TemkinStableModification k) : DeJongAlterationTheorem k :=
  deJongAlterationTheorem_of_stableModification_resolution hTSM
    (Resolution.Global.semistableResolution k)

end Alterations.StableModification.DeJong
