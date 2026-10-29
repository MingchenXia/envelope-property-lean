/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeValuedPoints

/-! # Original native section logarithms on their actual support opens -/
open scoped NNReal ENNReal Topology
open Topology CategoryTheory AlgebraicGeometry Classical
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeValuedPoint
variable {X Y : Scheme.{u}}

/-- The ORIGINAL section log on its true support-open locus, negative infinity elsewhere. -/
def sectionLogAbs (V : X.Opens) (a : Γ(X, V)) (y : SchemeValuedPoint X) : EReal :=
  if hy : y.point ∈ V then ENNReal.log (eval y V hy a : ℝ≥0∞) else ⊥

/-- EVERY original support-point value is the genuine extended logarithm. -/
theorem sectionLogAbs_of_mem (V : X.Opens) (a : Γ(X, V)) (y : SchemeValuedPoint X)
    (hy : y.point ∈ V) : sectionLogAbs V a y = ENNReal.log (eval y V hy a : ℝ≥0∞) := by
  simp only [sectionLogAbs, dif_pos hy]

/-- Off the actual original support locus the defined function is negative infinity. -/
theorem sectionLogAbs_of_notMem (V : X.Opens) (a : Γ(X, V)) (y : SchemeValuedPoint X)
    (hy : y.point ∉ V) : sectionLogAbs V a y = ⊥ := by
  simp only [sectionLogAbs, dif_neg hy]

/-- Whole genuine presheaf section restriction preserves the original log at EVERY smaller-support point. -/
theorem sectionLogAbs_restrict (V W : X.Opens) (i : W ≤ V) (a : Γ(X, V))
    (y : SchemeValuedPoint X) (hy : y.point ∈ W) :
    sectionLogAbs W (X.presheaf.map (homOfLE i).op a) y = sectionLogAbs V a y := by
  rw [sectionLogAbs_of_mem W _ y hy, sectionLogAbs_of_mem V a y (i hy), eval_restrict]

/-- A TRUE whole scheme map pulls back the ENTIRE original section-log function, including off support. -/
theorem sectionLogAbs_map (g : X ⟶ Y) (V : Y.Opens) (a : Γ(Y, V))
    (y : SchemeValuedPoint X) :
    sectionLogAbs V a (map g y) = sectionLogAbs (g ⁻¹ᵁ V) (g.app V a) y := by
  by_cases hy : g y.point ∈ V
  · have hy' : y.point ∈ g ⁻¹ᵁ V := hy
    rw [sectionLogAbs_of_mem V a (map g y) hy,
      sectionLogAbs_of_mem (g ⁻¹ᵁ V) _ y hy', eval_map]
  · have hy' : y.point ∉ g ⁻¹ᵁ V := hy
    rw [sectionLogAbs_of_notMem V a (map g y) hy,
      sectionLogAbs_of_notMem (g ⁻¹ᵁ V) _ y hy']

/-- The SAME original section log is continuous on its true support open, including genuine zeros. -/
theorem continuousOn_sectionLogAbs (V : X.Opens) (a : Γ(X, V)) :
    ContinuousOn (sectionLogAbs V a) {y : SchemeValuedPoint X | y.point ∈ V} := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun y : {y : SchemeValuedPoint X // y.point ∈ V} => sectionLogAbs V a y.1)
  have he : (fun y : {y : SchemeValuedPoint X // y.point ∈ V} => sectionLogAbs V a y.1) =
      fun y => ENNReal.log (eval y.1 V y.2 a : ℝ≥0∞) :=
    funext (fun y => sectionLogAbs_of_mem V a y.1 y.2)
  rw [he]
  exact ENNReal.continuous_log.comp (ENNReal.continuous_coe.comp (continuous_eval V a))

/-- A genuine ORIGINAL section unit has its finite real log at EVERY actual support point. -/
theorem sectionLogAbs_unit_eq_coe_log (V : X.Opens) (a : Γ(X, V)ˣ)
    (y : SchemeValuedPoint X) (hy : y.point ∈ V) :
    sectionLogAbs V (a : Γ(X, V)) y = ((Real.log (eval y V hy (a : Γ(X, V)) : ℝ) : ℝ) : EReal) := by
  rw [sectionLogAbs_of_mem V _ y hy]
  apply ENNReal.log_of_nnreal
  intro hz
  have hn := (eval_eq_zero_iff y V hy (a : Γ(X, V))).mp hz
  rw [X.basicOpen_of_isUnit a.isUnit] at hn
  exact hn hy

end EnvelopeProperty.Berkovich.SchemeValuedPoint
