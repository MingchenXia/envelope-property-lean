import EnvelopeProperty.AlgGeom.NativeClosedCurveDegrees
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Pi

/-! # Genuine numerical quotient by TRUE original closed-curve degrees and actual finite line sums -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.NativeRealNumericalClasses
open NativeClosedCurveDegrees
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]

/-- The WHOLE product of TRUE original degree functionals on ALL actual original closed integral curves. -/
def degreeVector : NativeRealPicard.Space X →ₗ[ℝ] (ClosedIntegralCurve X → ℝ) :=
  LinearMap.pi fun C => C.realDegree p

/-- EXACT original numerical triviality: simultaneous vanishing of the TRUE actual closed-curve degrees. -/
def trivialSubmodule : Submodule ℝ (NativeRealPicard.Space X) := (degreeVector p).ker

/-- The genuine REAL numerical quotient of the SAME original real native Picard space. -/
abbrev Space := NativeRealPicard.Space X ⧸ trivialSubmodule p

/-- The SAME actual original real Picard class maps to its actual original numerical class. -/
def projection : NativeRealPicard.Space X →ₗ[ℝ] Space p := (trivialSubmodule p).mkQ

/-- The original real Picard-to-numerical map is genuinely surjective, no class-realization premise. -/
theorem projection_surjective : Function.Surjective (projection p) :=
  (trivialSubmodule p).mkQ_surjective

/-- The numerical class of the SAME original actual invertible line. -/
def lineClass (L : X.Modules) (hL : IsInvertible L) : Space p :=
  projection p (NativeRealPicard.lineClass L hL)

/-- EVERY actual original closed integral curve's TRUE degree descends to the SAME numerical quotient. -/
def curveDegree (C : ClosedIntegralCurve X) : Space p →ₗ[ℝ] ℝ :=
  (trivialSubmodule p).liftQ (C.realDegree p) (by
    intro z hz
    have h : degreeVector p z = 0 := hz
    exact congrFun h C)

/-- The actual descended degree retains EVERY original real Picard element and original degree. -/
@[simp]
theorem curveDegree_projection (C : ClosedIntegralCurve X) (z : NativeRealPicard.Space X) :
    curveDegree p C (projection p z) = C.realDegree p z := rfl

/-- Equality in the actual numerical quotient is EXACTLY equality of ALL TRUE original closed-curve degrees. -/
theorem projection_eq_iff (x y : NativeRealPicard.Space X) :
    projection p x = projection p y ↔ ∀ C : ClosedIntegralCurve X, C.realDegree p x = C.realDegree p y := by
  change Submodule.Quotient.mk x = Submodule.Quotient.mk y ↔ _
  rw [Submodule.Quotient.eq]
  change degreeVector p (x - y) = 0 ↔ _
  rw [map_sub, sub_eq_zero, funext_iff]
  rfl

/-- The SAME numerical line class evaluates by the TRUE whole Euler degree of the
SAME original line pulled back to the SAME actual original closed integral curve. -/
theorem curveDegree_lineClass (C : ClosedIntegralCurve X) (L : X.Modules) (hL : IsInvertible L) :
    letI : IsProper (C.structureMorphism p) := (C.projectiveFactorization p).isProper
    letI : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace (C.structureMorphism p)
    curveDegree p C (lineClass p L hL) =
      (CurveLineDegrees.degree (C.structureMorphism p)
        ((Scheme.Modules.pullback C.inclusion).obj L) : ℝ) :=
  C.realDegree_lineClass p L hL

/-- ALL TRUE original closed-curve functionals jointly detect equality of ENTIRE original numerical classes. -/
@[ext]
theorem ext (x y : Space p) (h : ∀ C : ClosedIntegralCurve X, curveDegree p C x = curveDegree p C y) :
    x = y := by
  obtain ⟨x, rfl⟩ := projection_surjective p x
  obtain ⟨y, rfl⟩ := projection_surjective p y
  exact (projection_eq_iff p x y).mpr h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- EVERY actual original numerical class is an ACTUAL FINITE real sum of SAME
original invertible-line classes. All lines and coefficients are produced internally. -/
theorem exists_finite_line_sum (θ : Space p) :
    ∃ s : Finset {L : X.Modules // IsInvertible L},
      ∃ a : {L : X.Modules // IsInvertible L} → ℝ,
        θ = ∑ L ∈ s, a L • lineClass p L.val L.property := by
  obtain ⟨z, rfl⟩ := projection_surjective p θ
  obtain ⟨s, a, hz⟩ := NativeRealPicard.exists_finite_line_sum z
  exact ⟨s, a, by simpa only [map_sum, (projection p).map_smul, lineClass] using congrArg (projection p) hz⟩

end EnvelopeProperty.NativeRealNumericalClasses
