import EnvelopeProperty.AlgGeom.ProjectiveEmbeddingNontrivialLine
import EnvelopeProperty.AlgGeom.SchemeAmpleClosedRestriction
import EnvelopeProperty.AlgGeom.CurveLineZeroSections
import EnvelopeProperty.AlgGeom.NativeClosedCurveDegrees

/-! # Strict TRUE full Euler curve degree from the SAME original geometric ample line -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.CurveAmpleLineDegrees
open CurveLineDegrees CanonicalGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory

/-- True full original curve degree scales by EVERY actual original
sheafified tensor exponent, from whole tensor additivity. -/
theorem degree_tensorPower {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules) (hL : IsInvertible L) (r : ℕ) :
    letI : IsProper p := hp.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    degree p (bundleTensorPower L r) = (r : ℤ) * degree p L := by
  let : IsProper p := hp.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  induction r with
  | zero => exact (degree_unit p).trans (zero_mul _).symm
  | succ r ih =>
    calc
      degree p (bundleTensorPower L (r + 1)) =
          degree p (bundleTensorPower L r ⊗ L) :=
        (degree_eq_of_iso p (ModularCurves.monoidalTensorObjIso (bundleTensorPower L r) L)).symm
      _ = degree p (bundleTensorPower L r) + degree p L :=
        degree_tensor p hp hdim _ L (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) hL
      _ = ((r + 1 : ℕ) : ℤ) * degree p L := by rw [ih]; push_cast; ring

/-- The SAME actual geometric very-ample line has strictly positive TRUE
full Euler degree on the SAME original positive-dimensional integral curve. -/
theorem degree_pos_of_isVeryAmple {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) (L : X.Modules) (h : SchemeLineAmpleness.IsVeryAmple p L)
    (hdim : topologicalKrullDim X ≤ 1) (hpos : 0 < topologicalKrullDim X) :
    letI : IsProper p := h.isProjectiveFactorization.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    0 < degree p L := by
  let hp := h.isProjectiveFactorization
  let : IsProper p := hp.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have hL := h.isInvertible
  have hnot := ProjectiveEmbeddingNontrivialLine.nontrivial_of_isVeryAmple p L h hpos
  obtain ⟨n, i, _hi, _hp, ⟨e⟩⟩ := h
  let G := (ClosedProjectiveGlobalGeneration.pullback_generatingSections i
    (ProjectiveTwistGlobalGeneration.generatingSections (R := k) (0 : Fin (n + 1)) 1)).ofEpi e.hom
  exact CurveLineZeroSections.degree_pos_of_generatingSections_of_nontrivial p hp hdim L hL G hnot

/-- A genuine original geometric ample line has strictly positive TRUE
full Euler curve degree; the positive actual power and its degree are derived. -/
theorem degree_pos_of_isAmple {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) (L : X.Modules) (h : SchemeLineAmpleness.IsAmple p L)
    (hdim : topologicalKrullDim X ≤ 1) (hpos : 0 < topologicalKrullDim X) :
    letI : IsProper p := h.isProjectiveFactorization.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    0 < degree p L := by
  let hp := h.isProjectiveFactorization
  let : IsProper p := hp.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨r, hr, hV⟩ := h.2
  have hv := degree_pos_of_isVeryAmple p (bundleTensorPower L r) hV hdim hpos
  rw [degree_tensorPower p hp hdim L h.isInvertible r] at hv
  exact (mul_pos_iff_of_pos_left (show (0 : ℤ) < r from Nat.cast_pos.mpr hr)).mp hv

/-- EVERY actual original closed integral curve tests a SAME geometric
ample line by strictly positive TRUE full original Euler degree. -/
theorem degree_pos_on_closedIntegralCurve {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p] (L : X.Modules)
    (h : SchemeLineAmpleness.IsAmple p L) (C : NativeClosedCurveDegrees.ClosedIntegralCurve X) :
    letI : IsProper (C.structureMorphism p) := (C.projectiveFactorization p).isProper
    letI : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace (C.structureMorphism p)
    0 < degree (C.structureMorphism p) ((Scheme.Modules.pullback C.inclusion).obj L) := by
  let : IsIntegral C.carrier := C.integral
  let : IsClosedImmersion C.inclusion := C.closed
  have hA := SchemeAmpleClosedRestriction.ample_pullback h C.inclusion
  exact degree_pos_of_isAmple (C.structureMorphism p) _ hA (le_of_eq C.dimension)
    (by rw [C.dimension]; norm_num)
end EnvelopeProperty.CurveAmpleLineDegrees
