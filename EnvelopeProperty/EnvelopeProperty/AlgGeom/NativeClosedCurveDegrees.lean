import EnvelopeProperty.AlgGeom.NativeRealPicard
import EnvelopeProperty.AlgGeom.ProjectiveFactorizationRingIso

/-! # TRUE closed-original-curve degree tests on SAME original real native Picard space -/

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.NativeClosedCurveDegrees

/-- EXACT original integral closed one-dimensional curves in the SAME original scheme.
All fields are ordinary original geometric curve data, no degree/class comparison certificate. -/
structure ClosedIntegralCurve (X : Scheme.{u}) where
  carrier : Scheme.{u}
  integral : IsIntegral carrier
  inclusion : carrier ⟶ X
  closed : IsClosedImmersion inclusion
  dimension : topologicalKrullDim carrier = 1

namespace ClosedIntegralCurve
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  (C : ClosedIntegralCurve X)

/-- The SAME actual original curve's whole original coefficient projection. -/
def structureMorphism : C.carrier ⟶ Spec (.of k) := C.inclusion ≫ p

/-- The SAME original curve projection has true finite polynomial projectivity,
derived from actual original closed immersion and original native projectivity. -/
theorem projectiveFactorization [IsProjective p] :
    IsProjectiveFactorization (C.structureMorphism p) :=
  (ProjectiveFactorizationRingIso.of_isProjective p).comp_isClosedImmersion C.inclusion C.closed

/-- The true full original curve degree on the SAME actual native original Picard group. -/
def picardDegree [IsProjective p] : X.Pic →* Multiplicative ℤ := by
  let : IsIntegral C.carrier := C.integral
  exact CurvePicardDegrees.curveDegreeHom (C.structureMorphism p) (C.projectiveFactorization p)
    (le_of_eq C.dimension) C.inclusion

/-- Every original invertible line is evaluated by the TRUE whole Euler degree of its
SAME actual original pullback to this SAME actual original closed integral curve. -/
theorem picardDegree_lineClass [IsProjective p] (L : X.Modules) (hL : IsInvertible L) :
    letI : IsProper (C.structureMorphism p) := (C.projectiveFactorization p).isProper
    letI : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace (C.structureMorphism p)
    Multiplicative.toAdd (C.picardDegree p (CurvePicardDegrees.lineClass L hL)) =
      CurveLineDegrees.degree (C.structureMorphism p) ((Scheme.Modules.pullback C.inclusion).obj L) := by
  let : IsIntegral C.carrier := C.integral
  exact CurvePicardDegrees.curveDegreeHom_lineClass (C.structureMorphism p)
    (C.projectiveFactorization p) (le_of_eq C.dimension) C.inclusion L hL

/-- The SAME true original integer degree on the associated additive native Picard group. -/
def additiveDegree [IsProjective p] : Additive X.Pic →+ ℤ where
  toFun a := Multiplicative.toAdd (C.picardDegree p a.toMul)
  map_zero' := by
    change Multiplicative.toAdd (C.picardDegree p 1) = 0
    rw [map_one]
    rfl
  map_add' a b := by
    change Multiplicative.toAdd (C.picardDegree p (a.toMul * b.toMul)) = _
    rw [map_mul]
    rfl

/-- The actual original integer curve degree extends to the SAME real Picard scalar extension. -/
def realDegree [IsProjective p] : NativeRealPicard.Space X →ₗ[ℝ] ℝ :=
  (((Int.castAddHom ℝ).comp (C.additiveDegree p)).toIntLinearMap).liftBaseChange ℝ

/-- The genuine real-linear extension retains EVERY original pure tensor and TRUE curve degree. -/
@[simp]
theorem realDegree_tmul [IsProjective p] (r : ℝ) (a : Additive X.Pic) :
    C.realDegree p (r ⊗ₜ[ℤ] a) = r * (C.additiveDegree p a : ℝ) := rfl

/-- The actual real functional evaluates SAME original invertible lines by their TRUE
whole Euler degree on the SAME actual original closed curve, with no numerical comparison premise. -/
theorem realDegree_lineClass [IsProjective p] (L : X.Modules) (hL : IsInvertible L) :
    letI : IsProper (C.structureMorphism p) := (C.projectiveFactorization p).isProper
    letI : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace (C.structureMorphism p)
    C.realDegree p (NativeRealPicard.lineClass L hL) =
      (CurveLineDegrees.degree (C.structureMorphism p)
        ((Scheme.Modules.pullback C.inclusion).obj L) : ℝ) := by
  rw [NativeRealPicard.lineClass, NativeRealPicard.picardClass, realDegree_tmul, one_mul]
  exact congrArg (fun d : ℤ => (d : ℝ)) (C.picardDegree_lineClass p L hL)

end ClosedIntegralCurve
end EnvelopeProperty.NativeClosedCurveDegrees
