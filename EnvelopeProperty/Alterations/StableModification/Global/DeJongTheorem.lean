/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.Alterations.StableModification.Global.Main
import EnvelopeProperty.Alterations.StableModification.DeJong.Main

/-!
# De Jong's alteration theorem from the four remaining inputs of Temkin's route

`Global.temkinStableModification` proves `DeJong.TemkinStableModification k` from four named
hypotheses: existence and uniqueness of stable modifications over valuation rings
(`ValuationStableExistence`, `ValuationStableUniqueness`), spreading of numerical
stability to an open neighbourhood (`StableOpenNbhd k`,, Temkin Lemma 5.1(ii)), and
projectivity of the stable modification (`StableModificationProjectivity k`, Temkin Thm 1.1). Together with `DeJong.deJongAlterationTheorem_of_stableModification` this gives de Jong's
alteration theorem from the same four inputs.
-/

namespace Alterations.StableModification.Global

universe u

/-- **De Jong's alteration theorem** from the four remaining inputs of Temkin's route. -/
theorem deJongAlterationTheorem {k : Type u} [Field k] [IsAlgClosed k]
    (hE : ValuationStableExistence.{u}) (hU : ValuationStableUniqueness.{u})
    (hO : StableOpenNbhd k) (hP : StableModificationProjectivity k) :
    DeJongAlterationTheorem k :=
  DeJong.deJongAlterationTheorem_of_stableModification (temkinStableModification hE hU hO hP)

end Alterations.StableModification.Global
