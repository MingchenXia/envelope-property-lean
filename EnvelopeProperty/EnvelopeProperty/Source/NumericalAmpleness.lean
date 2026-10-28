import EnvelopeProperty.AlgGeom.NativeNumericalPSHComparisonContinuationKleiman

/-! # Ampleness is numerical (Kleiman)

Let `p : X ⟶ Spec k` be projective with `X` integral. An invertible sheaf `T` whose numerical
class lies in the ample cone `Amp(X) ⊆ N¹(X)_ℝ` (positive real combinations of ample classes)
is ample (`Variety.isAmple_of_lineClass_mem_ampleCone`). This is Kleiman's criterion in the form
of Lazarsfeld, *Positivity in algebraic geometry I*, Theorem 1.4.23 and Corollary 1.4.10, used
in FHX `fhx-envelope-20261028:lem:finite-class-promotion` ("`P_i` is ample") and implicit in BJ22's
`Amp(X)` (`bj22-trivval`, conventions).

The proof is `NativeNumericalFubiniStudy.numericalAmplenessCriterion`: write
`[T] = ∑ cᵢ [Aᵢ]` with `Aᵢ` ample and `cᵢ > 0`, choose rationals `cᵢ / 2 < qᵢ < cᵢ` and an ample
`B` with `∑ qᵢ [Aᵢ] = d⁻¹ [B]`; then `N = T^{⊗d} ⊗ B^∨` has the nef class `d ∑ (cᵢ - qᵢ) [Aᵢ]`, so
`N ⊗ B ≅ T^{⊗d}` is ample by "nef plus ample is ample"
(`SeshadriAmplenessCriterionNefAmple.isAmple_tensor_nef`), and so is `T`. This file states the
criterion in the source-facing namespace `EnvelopeProperty.Variety`, with its converse.
-/

open AlgebraicGeometry CategoryTheory Scheme.Modules

noncomputable section

universe u

namespace EnvelopeProperty.Variety

open NativeRealNumericalClasses

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]

/-- **Kleiman's criterion: ampleness is numerical** (`thm:var-numerical-ampleness`): on an
integral projective scheme, an invertible sheaf whose numerical class lies in the ample cone is
ample. -/
theorem isAmple_of_lineClass_mem_ampleCone [IsIntegral X] (T : X.Modules) (hT : IsInvertible T)
    (h : lineClass p T hT ∈ ampleCone p) : SchemeLineAmpleness.IsAmple p T :=
  NativeNumericalFubiniStudy.numericalAmplenessCriterion p T hT h

/-- On an integral projective scheme, an invertible sheaf is ample if and only if its numerical
class lies in the ample cone. -/
theorem isAmple_iff_lineClass_mem_ampleCone [IsIntegral X] (T : X.Modules)
    (hT : IsInvertible T) : SchemeLineAmpleness.IsAmple p T ↔ lineClass p T hT ∈ ampleCone p :=
  ⟨fun h => ampleLineClass_mem_ampleCone p T h, isAmple_of_lineClass_mem_ampleCone p T hT⟩

/-- Ampleness depends only on the numerical class. -/
theorem isAmple_of_lineClass_eq [IsIntegral X] {T T' : X.Modules}
    (hT : SchemeLineAmpleness.IsAmple p T) (hT' : IsInvertible T')
    (h : lineClass p T hT.isInvertible = lineClass p T' hT') :
    SchemeLineAmpleness.IsAmple p T' := by
  refine isAmple_of_lineClass_mem_ampleCone p T' hT' ?_
  rw [← h]
  exact ampleLineClass_mem_ampleCone p T hT

end EnvelopeProperty.Variety
