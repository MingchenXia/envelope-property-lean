import EnvelopeProperty.AlgGeom.NativeNumericalLineFamilyMaps
import Mathlib.Geometry.Convex.Cone.Basic

/-! # The genuine closed-original-curve nef inequalities in the SAME real numerical quotient -/

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
noncomputable section
universe u v
namespace EnvelopeProperty.NativeRealNumericalClasses
open NativeClosedCurveDegrees
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]

/-- Actual original closed-curve nef inequalities, on the SAME true real numerical quotient. -/
def nefCone : ConvexCone ℝ (Space p) where
  carrier := {θ | ∀ C : ClosedIntegralCurve X, 0 ≤ curveDegree p C θ}
  smul_mem' _ hr _ h C := by
    rw [(curveDegree p C).map_smul, smul_eq_mul]
    exact mul_nonneg hr.le (h C)
  add_mem' _ hθ _ hη C := by
    rw [map_add]
    exact add_nonneg (hθ C) (hη C)

/-- Nef membership retains ALL true original closed-curve tests, no desired positivity certificate. -/
theorem mem_nefCone (θ : Space p) : θ ∈ nefCone p ↔
    ∀ C : ClosedIntegralCurve X, 0 ≤ curveDegree p C θ := Iff.rfl

/-- The genuine closed-curve nef cone actually contains zero. -/
theorem nefCone_pointed : (nefCone p).Pointed := by
  intro C
  rw [map_zero]

/-- The SAME original quotient kills exactly the simultaneous zero degrees, so the nef cone is salient. -/
theorem nefCone_salient : (nefCone p).Salient := by
  intro θ hθ hne hn
  apply hne
  apply ext
  intro C
  have hp := hθ C
  have hm := hn C
  rw [map_neg] at hm
  simpa only [map_zero] using le_antisymm (neg_nonneg.mp hm) hp

/-- Genuine original nef inequalities are preserved by EVERY nonnegative original real scalar. -/
theorem nefCone_smul_nonneg {θ : Space p} (hθ : θ ∈ nefCone p) {r : ℝ} (hr : 0 ≤ r) :
    r • θ ∈ nefCone p := by
  intro C
  rw [(curveDegree p C).map_smul, smul_eq_mul]
  exact mul_nonneg hr (hθ C)

/-- Actual original line nef membership uses the TRUE full Euler degree on every SAME original curve. -/
theorem lineClass_mem_nefCone_iff (L : X.Modules) (hL : IsInvertible L) :
    lineClass p L hL ∈ nefCone p ↔
      ∀ C : ClosedIntegralCurve X,
        letI : IsProper (C.structureMorphism p) := (C.projectiveFactorization p).isProper
        letI : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace (C.structureMorphism p)
        0 ≤ (CurveLineDegrees.degree (C.structureMorphism p)
          ((Scheme.Modules.pullback C.inclusion).obj L) : ℝ) := by
  simp only [mem_nefCone, curveDegree_lineClass]

/-- The exact inverse image on the ENTIRE actual finite line-family coefficient space is the TRUE degree inequalities. -/
theorem lineFamilyMap_mem_nefCone_iff {ι : Type v} [Fintype ι]
    (L : ι → X.Modules) (hL : ∀ i, IsInvertible (L i)) (a : ι → ℝ) :
    lineFamilyMap p L hL a ∈ nefCone p ↔
      ∀ C : ClosedIntegralCurve X,
        ∑ i, a i * curveDegree p C (lineClass p (L i) (hL i)) ≥ 0 := by
  simp only [mem_nefCone, curveDegree_lineFamilyMap]

end EnvelopeProperty.NativeRealNumericalClasses
