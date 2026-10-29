import EnvelopeProperty.AlgGeom.NativeNumericalAmpleFamilyOpenness

/-! # Actual finite positive geometric ample-line representatives -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.NativeRealNumericalClasses
open NativeClosedCurveDegrees
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) [IsProjective p]

private def positiveAmpleSumCone : ConvexCone ℝ (Space p) where
  carrier := {θ | ∃ n : ℕ, 0 < n ∧ ∃ A : Fin n → X.Modules,
    ∃ hA : ∀ i, SchemeLineAmpleness.IsAmple p (A i), ∃ a : Fin n → ℝ,
      (∀ i, 0 < a i) ∧ θ = lineFamilyMap p A (fun i => (hA i).isInvertible) a}
  smul_mem' := by
    intro r hr θ hθ
    obtain ⟨n, hn, A, hA, a, ha, hθ⟩ := hθ
    refine ⟨n, hn, A, hA, r • a, fun i => mul_pos hr (ha i), ?_⟩
    rw [hθ]
    exact ((lineFamilyMap p A (fun i => (hA i).isInvertible)).map_smul r a).symm
  add_mem' := by
    intro θ hθ η hη
    obtain ⟨n, hn, A, hA, a, ha, hθ⟩ := hθ
    obtain ⟨m, hm, B, hB, b, hb, hη⟩ := hη
    let D : Fin (n + m) → X.Modules := Fin.addCases A B
    have hD : ∀ i, SchemeLineAmpleness.IsAmple p (D i) := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [D, Fin.addCases_left] using hA j
      · simpa only [D, Fin.addCases_right] using hB j
    let d : Fin (n + m) → ℝ := Fin.addCases a b
    have hd : ∀ i, 0 < d i := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [d, Fin.addCases_left] using ha j
      · simpa only [d, Fin.addCases_right] using hb j
    refine ⟨n + m, by omega, D, hD, d, hd, ?_⟩
    rw [hθ, hη]
    simp only [lineFamilyMap_apply, Fin.sum_univ_add, D, d, Fin.addCases_left, Fin.addCases_right]

/-- Every class of the SAME actual ample cone has internally produced NONEMPTY finite
original geometrically ample lines with strictly positive original real coefficients. -/
theorem exists_positive_ample_line_sum (θ : Space p) (hθ : θ ∈ ampleCone p) :
    ∃ n : ℕ, 0 < n ∧ ∃ A : Fin n → X.Modules,
      ∃ hA : ∀ i, SchemeLineAmpleness.IsAmple p (A i), ∃ a : Fin n → ℝ,
        (∀ i, 0 < a i) ∧ θ = lineFamilyMap p A (fun i => (hA i).isInvertible) a := by
  have h : ampleCone p ≤ positiveAmpleSumCone p := by
    apply ConvexCone.hull_min
    rintro _ ⟨A, hA, rfl⟩
    refine ⟨1, by omega, fun _ => A, fun _ => hA, fun _ => 1, fun _ => by norm_num, ?_⟩
    simp [lineFamilyMap_apply]
  exact h hθ

private def strictDegreeCone : ConvexCone ℝ (Space p) where
  carrier := {θ | ∀ C : ClosedIntegralCurve X, 0 < curveDegree p C θ}
  smul_mem' r hr θ hθ C := by
    rw [(curveDegree p C).map_smul, smul_eq_mul]
    exact mul_pos hr (hθ C)
  add_mem' θ hθ η hη C := by
    rw [map_add]
    exact add_pos (hθ C) (hη C)

/-- EVERY original closed curve has strictly positive genuine full Euler degree on
EVERY class of the ENTIRE same intrinsic ample cone. -/
theorem curveDegree_ampleCone_pos (θ : Space p) (hθ : θ ∈ ampleCone p)
    (C : ClosedIntegralCurve X) : 0 < curveDegree p C θ := by
  have h : ampleCone p ≤ strictDegreeCone p := by
    apply ConvexCone.hull_min
    rintro _ ⟨A, hA, rfl⟩
    exact curveDegree_ampleLineClass_pos p A hA
  exact h hθ C

end EnvelopeProperty.NativeRealNumericalClasses
