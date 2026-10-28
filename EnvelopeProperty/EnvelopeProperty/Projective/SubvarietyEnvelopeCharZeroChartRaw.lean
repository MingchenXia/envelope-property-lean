/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroChartTransportOriginal
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroChartTransportGenerators
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroChartTestsOrders
import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsNativeIdealChart

/-!
# Actual original multiplier cone discrepancy at genuine original chart points

The scheme multiplier estimate, literal original chart maps and canonical
homogeneous representative supply the raw cone estimate internally. No
raw valuation approximation, comparison certificate, or generating family
is an input. The original trivial point is among these actual chart points
through the separately proved parameter-adic chart construction.
-/

open scoped NNReal ENNReal Topology Polynomial

noncomputable section

namespace EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ProjBerk (phiIdeal)

universe u

variable {k : Type u} [Field k] [CharZero k] {M : ℕ} (X : ProjSubvariety k M)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine original multiplier cone ideals satisfy the raw chart
discrepancy estimate. The constant is fixed before every multiplier index,
including zero; all source maps, members, ideals and generators are actual
internally proved original ones. -/
theorem exists_originalMultiplierConeIdeal_chart_le_obstacle_all
    (hs : X.HasSmoothCharts) (d : ℕ) (φ : X.an → ℝ)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) (j : X.ChartIdx)
    (V : BirationalDVR k (X.ChartRing j.1)) (b : ℕ) (hb : 0 < b)
    (htorus : ∀ F : X.ChartRing j.1, V.ord F = F.support.inf fun ℓ =>
      V.ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, ∃ q : ℕ, 0 < q ∧
      X.coneIdealPotential (originalMultiplierConeIdeal X hs d φ hC m)
          (X.chartDivPoint j.1 V b) ≤
        (((m : ℝ) / q : ℝ) : EReal) *
          phiIdeal (X.obstacleIdeal d φ q) (X.chartDivPoint j.1 V b).1 + (A : EReal) := by
  let _ : Smooth (familyAbsoluteStructure X) :=
    Char0.MultiplierFamilySmoothness.familyAbsoluteStructure_smooth X hs
  let _ := (familyAbsoluteStructure X).sectionsAlgebra (familyChartOpen X j.1)
  let _ : Nonempty (familyChartAffineOpen X j.1).1 := by
    change Nonempty (familyChartOpen X j.1)
    exact familyChartOpen_nonempty X j.1 j.2
  obtain ⟨D, hD, hbound⟩ := exists_originalMultiplier_chart_order_bound X hs d φ hC j V
  let a : ℝ := (b : ℝ)⁻¹
  have ha : 0 < a := inv_pos.mpr (Nat.cast_pos.mpr hb)
  refine ⟨a * D, mul_nonneg ha.le hD, fun m => ?_⟩
  obtain ⟨q, hq, hqbound⟩ := hbound m a ha
  let K := schemeMultiplierSequence X d φ hC m
  obtain ⟨G, hGhom, hGspan, hGrep⟩ := exists_finset_coneIdeal_homogeneous_generators X K
  have hGspan' :
      (Ideal.span (G : Set (MvPolynomial (Fin (M + 1)) k)[X])).map X.coneMk =
        originalMultiplierConeIdeal X hs d φ hC m := by
    exact hGspan
  have hGsat : originalMultiplierConeIdeal X hs d φ hC m ≤ X.saturation
      ((Ideal.span (G : Set (MvPolynomial (Fin (M + 1)) k)[X])).map X.coneMk) := by
    rw [hGspan']
    exact le_saturation _
  have hneQ : (schemeIdeal X d φ q).ideal (familyChartAffineOpen X j.1) ≠ ⊥ :=
    Char0.affineIdeal_ne_bot_of_generic_stalk_ne_bot (schemeIdeal X d φ q)
      (schemeIdeal_generic_stalk_ne_bot X d φ hC q) (familyChartAffineOpen X j.1)
  have hneMap : ((X.obstacleIdeal d φ q).map
      (Polynomial.mapRingHom (X.quotDehom j.1).toRingHom)).map V.toRing.toRingHom ≠ ⊥ := by
    rw [← schemeIdeal_chart_map X d φ q j.1 j.2]
    apply (Ideal.map_eq_bot_iff_of_injective V.toRing_injective).mp.mt
    exact (Ideal.map_eq_bot_iff_of_injective
      (familyChartSectionsEquiv X j.1 j.2).injective).mp.mt hneQ
  have hJlower := chartTest_dvrIdealOrder_le_phiIdeal_obstacleIdeal j V b hb htorus hneMap
  refine ⟨q, hq, coneIdealPotential_chartTest_le_of_generator_orders j V b hb htorus
    (originalMultiplierConeIdeal X hs d φ hC m) G hGhom hGspan'.le hGsat ?_⟩
  intro F hF
  have hmem := familyChartSectionsEquiv_symm_dehom_mem X K j.1 j.2
    (parameterEquiv F) (hGrep F hF).1
  simp only [AlgEquiv.symm_apply_apply] at hmem
  have h := hqbound ((familyChartSectionsEquiv X j.1 j.2).symm
    (F.map (X.quotDehom j.1).toRingHom)) hmem
  rw [schemeIdeal_chart_map X d φ q j.1 j.2] at h
  calc -(((b : ℝ)⁻¹ : ℝ) : EReal) *
        (V.ord (F.map (X.quotDehom j.1).toRingHom) : EReal)
      ≤ (((m : ℝ) / q : ℝ) : EReal) *
          (-(((b : ℝ)⁻¹ : ℝ) : EReal) *
            (Char0.dvrIdealOrder (((X.obstacleIdeal d φ q).map
              (Polynomial.mapRingHom (X.quotDehom j.1).toRingHom)).map V.toRing.toRingHom) :
                EReal)) + ((a * D : ℝ) : EReal) := by
        simpa [a] using h
    _ ≤ (((m : ℝ) / q : ℝ) : EReal) *
        phiIdeal (X.obstacleIdeal d φ q) (X.chartDivPoint j.1 V b).1 + ((a * D : ℝ) : EReal) :=
      add_le_add (ProjBerk.ereal_coe_mul_monotone
        (div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg q)) hJlower) le_rfl

/-- The same actual raw estimate in the positive-index interface consumed
by the proved original polynomial envelope assembly. -/
theorem exists_originalMultiplierConeIdeal_chart_le_obstacle
    (hs : X.HasSmoothCharts) (d : ℕ) (φ : X.an → ℝ)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) (j : X.ChartIdx)
    (V : BirationalDVR k (X.ChartRing j.1)) (b : ℕ) (hb : 0 < b)
    (htorus : ∀ F : X.ChartRing j.1, V.ord F = F.support.inf fun ℓ =>
      V.ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, 0 < m → ∃ q : ℕ, 0 < q ∧
      X.coneIdealPotential (originalMultiplierConeIdeal X hs d φ hC m)
          (X.chartDivPoint j.1 V b) ≤
        (((m : ℝ) / q : ℝ) : EReal) *
          phiIdeal (X.obstacleIdeal d φ q) (X.chartDivPoint j.1 V b).1 + (A : EReal) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_originalMultiplierConeIdeal_chart_le_obstacle_all X hs d φ hC j V b hb htorus
  exact ⟨A, hA, fun m _hm => hbound m⟩

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
