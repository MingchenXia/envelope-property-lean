import EnvelopeProperty.AlgGeom.NativeNumericalNefCone
import EnvelopeProperty.AlgGeom.CurveAmpleLineDegrees

/-! # Strict true-curve positivity of SAME original geometric ample numerical classes -/

open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u v
namespace EnvelopeProperty.NativeRealNumericalClasses
open NativeClosedCurveDegrees
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]

/-- Every original geometric ample line has strictly positive TRUE full original degree
on EVERY same original actual closed integral curve, in the genuine numerical quotient. -/
theorem curveDegree_ampleLineClass_pos (L : X.Modules) (hA : SchemeLineAmpleness.IsAmple p L)
    (C : ClosedIntegralCurve X) : 0 < curveDegree p C (lineClass p L hA.isInvertible) := by
  let : IsProper (C.structureMorphism p) := (C.projectiveFactorization p).isProper
  let : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace (C.structureMorphism p)
  rw [curveDegree_lineClass]
  exact_mod_cast CurveAmpleLineDegrees.degree_pos_on_closedIntegralCurve p L hA C

/-- Original geometric ampleness DERIVES actual closed-curve nefness, no numerical premise. -/
theorem ampleLineClass_mem_nefCone (L : X.Modules) (hA : SchemeLineAmpleness.IsAmple p L) :
    lineClass p L hA.isInvertible ∈ nefCone p :=
  fun C => (curveDegree_ampleLineClass_pos p L hA C).le

/-- Any SAME original actual curve detects nonvanishing of an original ample numerical class. -/
theorem ampleLineClass_ne_zero_of_curve (L : X.Modules) (hA : SchemeLineAmpleness.IsAmple p L)
    (C : ClosedIntegralCurve X) : lineClass p L hA.isInvertible ≠ 0 := by
  intro h
  have hp := curveDegree_ampleLineClass_pos p L hA C
  rw [h, map_zero] at hp
  exact lt_irrefl _ hp

/-- Positive real combinations of actual original ample lines retain TRUE strict curve positivity. -/
theorem curveDegree_positive_ample_sum {ι : Type v} [Fintype ι] [Nonempty ι]
    (L : ι → X.Modules) (hA : ∀ i, SchemeLineAmpleness.IsAmple p (L i))
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (C : ClosedIntegralCurve X) :
    0 < curveDegree p C (∑ i, a i • lineClass p (L i) (hA i).isInvertible) := by
  simp only [map_sum, (curveDegree p C).map_smul, smul_eq_mul]
  exact Finset.sum_pos (fun i _ => mul_pos (ha i) (curveDegree_ampleLineClass_pos p (L i) (hA i) C))
    Finset.univ_nonempty

/-- Every nonempty positive original ample combination is genuinely nef on the SAME quotient. -/
theorem positive_ample_sum_mem_nefCone {ι : Type v} [Fintype ι] [Nonempty ι]
    (L : ι → X.Modules) (hA : ∀ i, SchemeLineAmpleness.IsAmple p (L i))
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    (∑ i, a i • lineClass p (L i) (hA i).isInvertible) ∈ nefCone p :=
  fun C => (curveDegree_positive_ample_sum p L hA a ha C).le

end EnvelopeProperty.NativeRealNumericalClasses
