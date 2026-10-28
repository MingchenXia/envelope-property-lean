/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.SchemeGenericFieldGraph
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Actual canonical function-field maps through the prescribed dense open

The whole original morphism from `Spec X.functionField` is retained by the
native open-immersion lift; dominance is derived, not supplied.

Blueprint: `dense-open-generic-field-lift.tex`.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace EnvelopeProperty.DenseOpenGenericFieldLift

universe u

variable {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) (hU : Dense (U : Set X))

private local instance functionFieldSpecSubsingleton : Subsingleton (Spec X.functionField) := by
  change Subsingleton (PrimeSpectrum X.functionField)
  infer_instance

include hU in
private theorem generic_mem : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU.nonempty)

/-- The original native field-valued point factors through the SAME prescribed dense open. -/
def lift : Spec X.functionField ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (X.fromSpecStalk (genericPoint X)) (by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨genericPoint X, generic_mem U hU⟩, ?_⟩
    change genericPoint X = (X.fromSpecStalk (genericPoint X)) z
    rw [Subsingleton.elim z (IsLocalRing.closedPoint X.functionField),
      Scheme.fromSpecStalk_closedPoint])

/-- Equality of the ENTIRE actual original canonical function-field morphism. -/
theorem lift_inclusion : lift U hU ≫ U.ι = X.fromSpecStalk (genericPoint X) :=
  IsOpenImmersion.lift_fac _ _ _

private theorem canonical_dense : DenseRange (X.fromSpecStalk (genericPoint X)) := by
  have hs : ({genericPoint X} : Set X) ⊆ Set.range (X.fromSpecStalk (genericPoint X)) := by
    exact Set.singleton_subset_iff.mpr
      ⟨IsLocalRing.closedPoint X.functionField, Scheme.fromSpecStalk_closedPoint⟩
  intro x
  apply closure_mono hs
  rw [(genericPoint_spec X).def]
  trivial

/-- Dominance of the actual native open lift is internally derived. -/
theorem lift_isDominant : IsDominant (lift U hU) := by
  constructor
  change Dense (Set.range (lift U hU))
  apply U.ι.isOpenEmbedding.isInducing.dense_iff.mpr
  intro x
  rw [← Set.range_comp]
  change U.ι x ∈ closure (Set.range (lift U hU ≫ U.ι))
  rw [lift_inclusion, canonical_dense.closure_range]
  trivial

end EnvelopeProperty.DenseOpenGenericFieldLift
