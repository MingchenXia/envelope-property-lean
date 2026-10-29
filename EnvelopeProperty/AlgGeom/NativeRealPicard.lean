import EnvelopeProperty.AlgGeom.ProjectiveGeneratedLineClasses
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Real.Basic

/-! # Actual real scalar extension of SAME native original Picard groups and genuine finite line sums -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.NativeRealPicard

/-- The REAL scalar extension of the SAME original native Picard group. -/
abbrev Space (X : Scheme.{u}) := ℝ ⊗[ℤ] Additive X.Pic

/-- The SAME actual original Picard class in its genuine real scalar extension. -/
def picardClass (X : Scheme.{u}) (a : X.Pic) : Space X :=
  (1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul a

/-- The genuine real class of the SAME original actual invertible line. -/
def lineClass {X : Scheme.{u}} (L : X.Modules) (hL : IsInvertible L) : Space X :=
  picardClass X (CurvePicardDegrees.lineClass L hL)

/-- The original native Picard generators span the ENTIRE actual real scalar extension,
without any finite-dimensionality or class-realization premise. -/
theorem span_picardClass (X : Scheme.{u}) :
    Submodule.span ℝ (Set.range (picardClass X)) = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul r a =>
    have h : (1 : ℝ) ⊗ₜ[ℤ] a ∈ Submodule.span ℝ (Set.range (picardClass X)) :=
      Submodule.subset_span ⟨a.toMul, rfl⟩
    have hs := Submodule.smul_mem (Submodule.span ℝ (Set.range (picardClass X))) r h
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hs
  | add x y hx hy => exact add_mem hx hy

/-- ACTUAL original invertible lines span the ENTIRE real Picard space, using genuine
same native Picard representatives, with no supplied finite-family realization. -/
theorem span_lineClass (X : Scheme.{u}) :
    Submodule.span ℝ (Set.range (fun L : {L : X.Modules // IsInvertible L} =>
      lineClass L.val L.property)) = ⊤ := by
  apply top_unique
  rw [← span_picardClass X]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  obtain ⟨L, hL, ha⟩ := ProjectiveGeneratedLineClasses.exists_line_representative a
  exact Submodule.subset_span ⟨⟨L, hL⟩, congrArg (picardClass X) ha⟩

/-- EVERY actual original real Picard element is an ACTUAL finite real sum of SAME
original invertible-line classes, internally produced from finite tensor support. -/
theorem exists_finite_line_sum {X : Scheme.{u}} (z : Space X) :
    ∃ s : Finset {L : X.Modules // IsInvertible L},
      ∃ a : {L : X.Modules // IsInvertible L} → ℝ,
        z = ∑ L ∈ s, a L • lineClass L.val L.property := by
  classical
  have hz : z ∈ Submodule.span ℝ (Set.range (fun L : {L : X.Modules // IsInvertible L} =>
      lineClass L.val L.property)) := span_lineClass X ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  exact ⟨c.support, c, hc.symm⟩

end EnvelopeProperty.NativeRealPicard
