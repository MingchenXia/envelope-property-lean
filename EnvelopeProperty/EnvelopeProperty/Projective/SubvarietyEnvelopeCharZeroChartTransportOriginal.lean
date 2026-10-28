/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroChartTransport
import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsNativeCharts
import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsOriginal

/-!
# The actual original multiplier family supplies its original chart estimates

The scheme, sequence, affine open, whole chart section isomorphism,
smoothness and nonvanishing are the actual internally proved original
ones. Only the original smooth-chart hypothesis and obstacle lower bound
are supplied by the caller, together with a genuine original chart DVR.
-/

open scoped NNReal ENNReal Topology Polynomial

noncomputable section

namespace EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

variable {k : Type u} [Field k] [CharZero k] {M : ℕ} (X : ProjSubvariety k M)

/-- The genuine original whole multiplier sequence satisfies the actual
scheme divisorial estimate in the same original old chart coordinates.
Every native family, source, smoothness and nonvanishing datum is derived.
The discrepancy is fixed before all multiplier indices, including zero. -/
theorem exists_originalMultiplier_chart_order_bound (hs : X.HasSmoothCharts)
    (d : ℕ) (φ : X.an → ℝ) {C : ℝ} (hC : ∀ v, C ≤ φ v)
    (j : X.ChartIdx) (V : BirationalDVR k (X.ChartRing j.1)) :
    letI : Smooth (familyAbsoluteStructure X) :=
      Char0.MultiplierFamilySmoothness.familyAbsoluteStructure_smooth X hs
    let eA := familyChartSectionsEquiv X j.1 j.2
    ∃ D : ℝ, 0 ≤ D ∧ ∀ m : ℕ, ∀ a : ℝ, 0 < a → ∃ q : ℕ, 0 < q ∧
      ∀ s ∈ (schemeMultiplierSequence X d φ hC m).ideal (familyChartAffineOpen X j.1),
        ((-a : ℝ) : EReal) * (V.ord (eA s) : EReal) ≤
          (((m : ℝ) / q : ℝ) : EReal) *
            (((-a : ℝ) : EReal) *
              (Char0.dvrIdealOrder
                ((((schemeIdeal X d φ q).ideal (familyChartAffineOpen X j.1)).map eA.toRingHom).map
                  V.toRing.toRingHom) : EReal)) + ((a * D : ℝ) : EReal) := by
  let _ : Smooth (familyAbsoluteStructure X) :=
    Char0.MultiplierFamilySmoothness.familyAbsoluteStructure_smooth X hs
  let _ : Nonempty (familyChartAffineOpen X j.1).1 := by
    change Nonempty (familyChartOpen X j.1)
    exact familyChartOpen_nonempty X j.1 j.2
  exact Char0.exists_schemeAsymptoticMultiplierIdeal_chart_order_bound (A := X.ChartRing j.1)
      (familyAbsoluteStructure X)
      (schemeIdeal_mul_le X d φ)
      (fun q _hq => schemeIdeal_generic_stalk_ne_bot X d φ hC q)
      (familyChartAffineOpen X j.1) (familyChartSectionsEquiv X j.1 j.2) V

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
