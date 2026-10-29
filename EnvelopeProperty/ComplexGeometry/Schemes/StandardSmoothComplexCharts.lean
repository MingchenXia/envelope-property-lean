import EnvelopeProperty.ComplexGeometry.Schemes.SmoothCanonicalCharts
import EnvelopeProperty.ComplexGeometry.Schemes.AffineComplexPoints
import EnvelopeProperty.ComplexGeometry.Schemes.AnalyticZeroFiberChart
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Analytic coordinates from actual standard-smooth presentations

The coordinate carrier is the literal zero locus of the genuine presentation
relations. Its Jacobian is evaluated at an actual complex algebra point.
The implicit-function theorem must construct the analytic inverse; no manifold
atlas or implicit-function certificate is assumed.
-/

open Algebra MvPolynomial
open scoped Topology

set_option backward.isDefEq.respectTransparency false

namespace ComplexSchemes

noncomputable section

variable {A B I J : Type*} [CommRing A] [Algebra ℂ A]
  [CommRing B] [Algebra ℂ B]

/-- An actual algebra isomorphism transports the genuine evaluation topology. -/
def complexPointAlgEquivHomeomorph (e : A ≃ₐ[ℂ] B) :
    ComplexAlgebraPoint A ≃ₜ ComplexAlgebraPoint B where
  toFun p := p.comp e.symm.toAlgHom
  invFun p := p.comp e.toAlgHom
  left_inv p := by
    ext a
    simp
  right_inv p := by
    ext b
    simp
  continuous_toFun := complexPoint_pullback_continuous e.symm.toAlgHom
  continuous_invFun := complexPoint_pullback_continuous e.toAlgHom

/-- The presentation ideal has the same literal zero locus as its actual relations. -/
theorem presentationZeroLocus_iff (P : Presentation ℂ A I J) (z : I → ℂ) :
    z ∈ complexPolynomialZeroLocus P.ker ↔
      ∀ j, MvPolynomial.eval z (P.relation j) = 0 := by
  constructor
  · intro hz j
    exact hz (P.relation j) (P.relation_mem_ker j)
  · intro hz q hq
    have hle : P.ker ≤ RingHom.ker (MvPolynomial.eval z) := by
      rw [← P.span_range_relation_eq_ker, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hz j
    exact hle hq

/-- Genuine points of the presented algebra are its actual polynomial zero locus. -/
def presentationComplexPointHomeomorph (P : Presentation ℂ A I J) :
    ComplexAlgebraPoint A ≃ₜ complexPolynomialZeroLocus P.ker :=
  (complexPointAlgEquivHomeomorph (P.quotientEquiv.restrictScalars ℂ).symm).trans
    (quotientComplexPointHomeomorph P.ker)

/-- These coordinates are evaluations of the actual presentation generators. -/
@[simp]
theorem presentationComplexPointHomeomorph_coordinates
    (P : Presentation ℂ A I J) (p : ComplexAlgebraPoint A) (i : I) :
    (presentationComplexPointHomeomorph P p).val i = p (P.val i) := by
  change p (P.quotientEquiv (Ideal.Quotient.mk P.ker (MvPolynomial.X i))) = _
  rw [P.quotientEquiv_mk, Generators.algebraMap_apply, MvPolynomial.aeval_X]

variable [Fintype I]

/-- The actual polynomial differential, expressed by its evaluated partial derivatives. -/
def complexPolynomialDifferential (q : MvPolynomial I ℂ) (z : I → ℂ) :
    (I → ℂ) →L[ℂ] ℂ :=
  ∑ i, MvPolynomial.eval z (MvPolynomial.pderiv i q) •
    (ContinuousLinearMap.proj i : (I → ℂ) →L[ℂ] ℂ)

@[simp]
theorem complexPolynomialDifferential_C (c : ℂ) (z : I → ℂ) :
    complexPolynomialDifferential (MvPolynomial.C c) z = 0 := by
  ext v
  simp [complexPolynomialDifferential]

@[simp]
theorem complexPolynomialDifferential_X (i : I) (z : I → ℂ) :
    complexPolynomialDifferential (MvPolynomial.X i) z = ContinuousLinearMap.proj i := by
  classical
  ext v
  simp only [complexPolynomialDifferential, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  simp [MvPolynomial.pderiv_X, Pi.single_apply]

theorem complexPolynomialDifferential_add (p q : MvPolynomial I ℂ) (z : I → ℂ) :
    complexPolynomialDifferential (p + q) z =
      complexPolynomialDifferential p z + complexPolynomialDifferential q z := by
  ext v
  simp [complexPolynomialDifferential, add_mul, Finset.sum_add_distrib]

theorem complexPolynomialDifferential_mul (p q : MvPolynomial I ℂ) (z : I → ℂ) :
    complexPolynomialDifferential (p * q) z =
      MvPolynomial.eval z q • complexPolynomialDifferential p z +
        MvPolynomial.eval z p • complexPolynomialDifferential q z := by
  ext v
  simp only [complexPolynomialDifferential, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply,
    add_apply, smul_eq_mul, MvPolynomial.pderiv_mul,
    map_add, map_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

/-- Polynomial evaluation has exactly the differential computed from actual partials. -/
theorem complexPolynomial_hasFDerivAt (q : MvPolynomial I ℂ) (z : I → ℂ) :
    HasFDerivAt (fun w => MvPolynomial.eval w q) (complexPolynomialDifferential q z) z := by
  induction q using MvPolynomial.induction_on with
  | C c => simpa using hasFDerivAt_const (𝕜 := ℂ) c z
  | add p q hp hq =>
      convert! hp.add hq using 1
      · ext w
        simp
      · exact complexPolynomialDifferential_add p q z
  | mul_X p i hp =>
      convert! hp.mul (hasFDerivAt_apply (𝕜 := ℂ) i z) using 1
      · ext w
        simp
      · simp [complexPolynomialDifferential_mul, add_comm]

/-- Analyticity upgrades the exact polynomial differential to a strict derivative. -/
theorem complexPolynomial_hasStrictFDerivAt (q : MvPolynomial I ℂ) (z : I → ℂ) :
    HasStrictFDerivAt (fun w => MvPolynomial.eval w q)
      (complexPolynomialDifferential q z) z := by
  have h := (AnalyticOnNhd.eval_mvPolynomial q z (Set.mem_univ z)).hasStrictFDerivAt
  rw [(complexPolynomial_hasFDerivAt q z).fderiv] at h
  exact h

omit [Fintype I] in
/-- Polynomial evaluation at an actual point equals the genuine algebra evaluation. -/
theorem presentationPolynomial_eval (P : Presentation ℂ A I J)
    (p : ComplexAlgebraPoint A) (q : MvPolynomial I ℂ) :
    MvPolynomial.eval (fun i => p (P.val i)) q = p (MvPolynomial.aeval P.val q) := by
  have h : p.comp (MvPolynomial.aeval P.val) =
      MvPolynomial.aeval (fun i => p (P.val i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact (congrArg (fun f => f q) h).symm

variable [Fintype J]

/-- The vector consists of the actual presentation relations, with no replacement equations. -/
def presentationRelationVector (P : Presentation ℂ A I J) (z : I → ℂ) : J → ℂ :=
  fun j => MvPolynomial.eval z (P.relation j)

omit [Fintype I] [Fintype J] in
/-- Actual complex points satisfy every component of the relation vector. -/
theorem presentationRelationVector_point (P : Presentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    presentationRelationVector P (fun i => p (P.val i)) = 0 := by
  ext j
  simp [presentationRelationVector, presentationPolynomial_eval]

/-- The vector derivative is assembled from the proved polynomial partials. -/
def presentationRelationDifferential (P : Presentation ℂ A I J) (z : I → ℂ) :
    (I → ℂ) →L[ℂ] (J → ℂ) :=
  ContinuousLinearMap.pi (fun j => complexPolynomialDifferential (P.relation j) z)

omit [Fintype J] in
theorem presentationRelationVector_hasStrictFDerivAt
    (P : Presentation ℂ A I J) (z : I → ℂ) :
    HasStrictFDerivAt (presentationRelationVector P)
      (presentationRelationDifferential P z) z :=
  hasStrictFDerivAt_pi.mpr (fun j => complexPolynomial_hasStrictFDerivAt (P.relation j) z)

variable [DecidableEq J]

/-- Selected derivative rows index equations, hence transpose the native presentation matrix. -/
def presentationSelectedJacobian (P : PreSubmersivePresentation ℂ A I J) (z : I → ℂ) :
    Matrix J J ℂ :=
  ((MvPolynomial.eval z).mapMatrix P.jacobiMatrix).transpose

omit [Fintype I] in
@[simp]
theorem presentationSelectedJacobian_apply
    (P : PreSubmersivePresentation ℂ A I J) (z : I → ℂ) (j i : J) :
    presentationSelectedJacobian P z j i =
      MvPolynomial.eval z (MvPolynomial.pderiv (P.map i) (P.relation j)) := by
  simp [presentationSelectedJacobian, PreSubmersivePresentation.jacobiMatrix_apply]

omit [Fintype I] in
/-- The determinant is the actual Jacobian evaluated at the genuine complex point. -/
theorem presentationSelectedJacobian_det
    (P : PreSubmersivePresentation ℂ A I J) (p : ComplexAlgebraPoint A) :
    (presentationSelectedJacobian P (fun i => p (P.val i))).det = p P.jacobian := by
  rw [P.jacobian_eq_jacobiMatrix_det, Generators.algebraMap_apply,
    ← presentationPolynomial_eval]
  simp [presentationSelectedJacobian, RingHom.map_det]

omit [Fintype I] in
/-- The submersive unit condition derives invertibility at every actual complex point. -/
theorem submersiveSelectedJacobian_det_isUnit
    (P : SubmersivePresentation ℂ A I J) (p : ComplexAlgebraPoint A) :
    IsUnit (presentationSelectedJacobian P.toPreSubmersivePresentation
      (fun i => p (P.val i))).det := by
  rw [presentationSelectedJacobian_det]
  exact P.jacobian_isUnit.map p.toMonoidHom

omit [Fintype I] in
/-- The selected Jacobian defines its genuine finite-dimensional linear derivative. -/
def presentationSelectedLinearMap
    (P : PreSubmersivePresentation ℂ A I J) (z : I → ℂ) :
    (J → ℂ) →ₗ[ℂ] (J → ℂ) :=
  Matrix.toLin' (presentationSelectedJacobian P z)

omit [Fintype I] in
/-- The actual selected linear derivative has the same unit determinant. -/
theorem submersiveSelectedLinearMap_det_isUnit
    (P : SubmersivePresentation ℂ A I J) (p : ComplexAlgebraPoint A) :
    IsUnit ((LinearMap.toMatrix (Pi.basisFun ℂ J) (Pi.basisFun ℂ J))
      (presentationSelectedLinearMap P.toPreSubmersivePresentation
        (fun i => p (P.val i)))).det := by
  simpa [presentationSelectedLinearMap, LinearMap.toMatrix_eq_toMatrix'] using
    submersiveSelectedJacobian_det_isUnit P p

omit [Fintype I] in
/-- Smoothness constructs a genuine continuous linear equivalence for the selected block. -/
def submersiveSelectedLinearEquiv (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) : (J → ℂ) ≃L[ℂ] (J → ℂ) :=
  (LinearEquiv.ofIsUnitDet (submersiveSelectedLinearMap_det_isUnit P p)).toContinuousLinearEquiv

omit [Fintype I] in
@[simp]
theorem submersiveSelectedLinearEquiv_apply (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) (v : J → ℂ) :
    submersiveSelectedLinearEquiv P p v =
      presentationSelectedLinearMap P.toPreSubmersivePresentation
        (fun i => p (P.val i)) v :=
  rfl

/-- The actual free-coordinate complement and selected coordinates partition all variables. -/
def submersiveCoordinateIndexEquiv (P : SubmersivePresentation ℂ A I J) :
    Fin P.dimension ⊕ J ≃ I := by
  classical
  exact (Equiv.sumComm _ _).trans
    ((Equiv.sumCongr (Equiv.ofInjective P.map P.map_inj)
      (submersiveFreeIndexEquiv P).symm).trans
        (Equiv.Set.sumCompl (Set.range P.map)))

omit [DecidableEq J] in
@[simp]
theorem submersiveCoordinateIndexEquiv_free (P : SubmersivePresentation ℂ A I J)
    (i : Fin P.dimension) :
    submersiveCoordinateIndexEquiv P (Sum.inl i) =
      ((submersiveFreeIndexEquiv P).symm i).val :=
  rfl

omit [DecidableEq J] in
@[simp]
theorem submersiveCoordinateIndexEquiv_selected (P : SubmersivePresentation ℂ A I J)
    (j : J) : submersiveCoordinateIndexEquiv P (Sum.inr j) = P.map j :=
  rfl

/-- This genuine continuous linear coordinate change separates free and selected variables. -/
def submersiveCoordinateEquiv (P : SubmersivePresentation ℂ A I J) :
    ((Fin P.dimension → ℂ) × (J → ℂ)) ≃L[ℂ] (I → ℂ) :=
  ((LinearEquiv.sumArrowLequivProdArrow (Fin P.dimension) J ℂ ℂ).symm.trans
    (LinearEquiv.funCongrLeft ℂ ℂ (submersiveCoordinateIndexEquiv P).symm)).toContinuousLinearEquiv

omit [DecidableEq J] in
@[simp]
theorem submersiveCoordinateEquiv_apply_index (P : SubmersivePresentation ℂ A I J)
    (u : (Fin P.dimension → ℂ) × (J → ℂ)) (i : Fin P.dimension ⊕ J) :
    submersiveCoordinateEquiv P u (submersiveCoordinateIndexEquiv P i) =
      Sum.elim u.1 u.2 i := by
  simp [submersiveCoordinateEquiv, LinearEquiv.funCongrLeft]
  rfl

omit [DecidableEq J] in
@[simp]
theorem submersiveCoordinateEquiv_symm_free (P : SubmersivePresentation ℂ A I J)
    (z : I → ℂ) (i : Fin P.dimension) :
    ((submersiveCoordinateEquiv P).symm z).1 i =
      z ((submersiveFreeIndexEquiv P).symm i).val :=
  rfl

omit [DecidableEq J] in
@[simp]
theorem submersiveCoordinateEquiv_symm_selected (P : SubmersivePresentation ℂ A I J)
    (z : I → ℂ) (j : J) :
    ((submersiveCoordinateEquiv P).symm z).2 j = z (P.map j) :=
  rfl

/-- Actual relation equations in the genuine selected/free product coordinates. -/
def submersiveProductRelations (P : SubmersivePresentation ℂ A I J)
    (u : (Fin P.dimension → ℂ) × (J → ℂ)) : J → ℂ :=
  presentationRelationVector P.toPresentation (submersiveCoordinateEquiv P u)

/-- The actual relation derivative composed with the genuine coordinate change. -/
def submersiveProductDifferential (P : SubmersivePresentation ℂ A I J) (z : I → ℂ) :
    ((Fin P.dimension → ℂ) × (J → ℂ)) →L[ℂ] (J → ℂ) :=
  (presentationRelationDifferential P.toPresentation z).comp
    (submersiveCoordinateEquiv P).toContinuousLinearMap

omit [DecidableEq J] in
theorem submersiveProductRelations_hasStrictFDerivAt
    (P : SubmersivePresentation ℂ A I J) (u : (Fin P.dimension → ℂ) × (J → ℂ)) :
    HasStrictFDerivAt (submersiveProductRelations P)
      (submersiveProductDifferential P (submersiveCoordinateEquiv P u)) u :=
  (presentationRelationVector_hasStrictFDerivAt P.toPresentation
    (submersiveCoordinateEquiv P u)).comp u
      (submersiveCoordinateEquiv P).hasStrictFDerivAt

/-- The selected product derivative is exactly the genuine unit-Jacobian equivalence. -/
theorem submersiveProductDifferential_selected
    (P : SubmersivePresentation ℂ A I J) (p : ComplexAlgebraPoint A) :
    (submersiveProductDifferential P (fun i => p (P.val i))).comp
      (ContinuousLinearMap.inr ℂ (Fin P.dimension → ℂ) (J → ℂ)) =
        (submersiveSelectedLinearEquiv P p).toContinuousLinearMap := by
  classical
  ext v j
  simp only [submersiveProductDifferential, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, presentationRelationDifferential,
    ContinuousLinearMap.pi_apply, complexPolynomialDifferential,
    sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    ContinuousLinearEquiv.coe_coe, submersiveSelectedLinearEquiv_apply,
    presentationSelectedLinearMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  change (∑ i : I, MvPolynomial.eval (fun i => p (P.val i))
      (MvPolynomial.pderiv i (P.relation j)) * submersiveCoordinateEquiv P (0, v) i) =
    ∑ i : J, presentationSelectedJacobian P.toPreSubmersivePresentation
      (fun i => p (P.val i)) j i * v i
  rw [← Equiv.sum_comp (submersiveCoordinateIndexEquiv P)]
  simp [Fintype.sum_sum_type]

/-- Invertibility is derived from the actual presentation Jacobian, without an analytic premise. -/
theorem submersiveProductDifferential_selected_isInvertible
    (P : SubmersivePresentation ℂ A I J) (p : ComplexAlgebraPoint A) :
    ((submersiveProductDifferential P (fun i => p (P.val i))).comp
      (ContinuousLinearMap.inr ℂ (Fin P.dimension → ℂ) (J → ℂ))).IsInvertible := by
  rw [submersiveProductDifferential_selected]
  exact ⟨submersiveSelectedLinearEquiv P p, rfl⟩

/-- Product coordinates of the actual complex algebra point. -/
def submersiveProductPoint (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) : (Fin P.dimension → ℂ) × (J → ℂ) :=
  (submersiveCoordinateEquiv P).symm (fun i => p (P.val i))

omit [DecidableEq J] in
@[simp]
theorem submersiveProductPoint_coordinates (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    submersiveCoordinateEquiv P (submersiveProductPoint P p) =
      fun i => p (P.val i) :=
  (submersiveCoordinateEquiv P).apply_symm_apply _

omit [DecidableEq J] in
@[simp]
theorem submersiveProductRelations_point (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    submersiveProductRelations P (submersiveProductPoint P p) = 0 := by
  simpa [submersiveProductRelations] using
    presentationRelationVector_point P.toPresentation p

/-- The native implicit-function data are constructed entirely from the actual presentation. -/
def submersiveImplicitFunctionData (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    ImplicitFunctionData ℂ ((Fin P.dimension → ℂ) × (J → ℂ))
      (J → ℂ) (Fin P.dimension → ℂ) :=
  (submersiveProductRelations_hasStrictFDerivAt P (submersiveProductPoint P p)).implicitFunctionDataOfProdDomain (by
      simpa using submersiveProductDifferential_selected_isInvertible P p)

/-- The genuine ambient inverse-function chart has literal relations and free coordinates. -/
def submersiveAmbientChart (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    OpenPartialHomeomorph ((Fin P.dimension → ℂ) × (J → ℂ))
      ((J → ℂ) × (Fin P.dimension → ℂ)) :=
  (submersiveImplicitFunctionData P p).toOpenPartialHomeomorph

@[simp]
theorem submersiveAmbientChart_apply (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) (u : (Fin P.dimension → ℂ) × (J → ℂ)) :
    submersiveAmbientChart P p u = (submersiveProductRelations P u, u.1) :=
  rfl

/-- The actual point belongs to the source of the constructed ambient chart. -/
theorem submersiveAmbientChart_point_mem_source (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    submersiveProductPoint P p ∈ (submersiveAmbientChart P p).source :=
  (submersiveImplicitFunctionData P p).pt_mem_toOpenPartialHomeomorph_source

/-- The chosen actual point lies in the literal zero-equation fiber of its ambient chart. -/
theorem submersiveAmbientChart_point_zero (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    (submersiveAmbientChart P p (submersiveProductPoint P p)).1 = 0 :=
  submersiveProductRelations_point P p

/-- The genuine target contains the zero-equation slice at the actual free coordinates. -/
theorem submersiveAmbientChart_point_mem_target (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    (0, (submersiveProductPoint P p).1) ∈ (submersiveAmbientChart P p).target := by
  simpa using (submersiveAmbientChart P p).map_source
    (submersiveAmbientChart_point_mem_source P p)

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The genuine presentation ideal zero locus is exactly the actual relation-vector fiber. -/
theorem presentationRelationVector_zero_iff (P : Presentation ℂ A I J) (z : I → ℂ) :
    z ∈ complexPolynomialZeroLocus P.ker ↔ presentationRelationVector P z = 0 := by
  simp only [funext_iff, presentationRelationVector, Pi.zero_apply]
  exact presentationZeroLocus_iff P z

/-- The actual algebra points are the genuine zero fiber in selected/free product coordinates. -/
def submersiveComplexPointProductHomeomorph (P : SubmersivePresentation ℂ A I J) :
    ComplexAlgebraPoint A ≃ₜ
      {u : (Fin P.dimension → ℂ) × (J → ℂ) // submersiveProductRelations P u = 0} :=
  (presentationComplexPointHomeomorph P.toPresentation).trans
    ((submersiveCoordinateEquiv P).symm.toHomeomorph.subtype (fun z => by
      change z ∈ complexPolynomialZeroLocus P.ker ↔
        presentationRelationVector P.toPresentation
          (submersiveCoordinateEquiv P ((submersiveCoordinateEquiv P).symm z)) = 0
      rw [(submersiveCoordinateEquiv P).apply_symm_apply]
      exact presentationRelationVector_zero_iff P.toPresentation z))

omit [DecidableEq J] in
@[simp]
theorem submersiveComplexPointProductHomeomorph_apply
    (P : SubmersivePresentation ℂ A I J) (p : ComplexAlgebraPoint A) :
    (submersiveComplexPointProductHomeomorph P p).val = submersiveProductPoint P p := by
  apply (submersiveCoordinateEquiv P).injective
  ext i
  simp [submersiveComplexPointProductHomeomorph, submersiveProductPoint]

/-- The actual ambient equation zero fiber is the genuine algebra-point carrier. -/
def submersiveComplexPointZeroFiberHomeomorph (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    ComplexAlgebraPoint A ≃ₜ
      {u : (Fin P.dimension → ℂ) × (J → ℂ) // (submersiveAmbientChart P p u).1 = 0} :=
  submersiveComplexPointProductHomeomorph P

/-- The actual implicit chart on the zero fiber is transported to the actual algebra points. -/
def submersiveComplexPointChart (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    OpenPartialHomeomorph (ComplexAlgebraPoint A) (Fin P.dimension → ℂ) :=
  (submersiveComplexPointZeroFiberHomeomorph P p).toOpenPartialHomeomorph.trans
    (zeroFiberOpenPartialHomeomorph (submersiveAmbientChart P p)
      (submersiveProductPoint P p) (submersiveAmbientChart_point_mem_source P p)
        (submersiveAmbientChart_point_zero P p))

/-- The genuine point belongs to the source of its actual implicit zero-fiber chart. -/
theorem submersiveComplexPointChart_point_mem_source (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) : p ∈ (submersiveComplexPointChart P p).source := by
  simp [submersiveComplexPointChart, submersiveComplexPointZeroFiberHomeomorph,
    submersiveAmbientChart_point_mem_source]

/-- The forward map on its actual source reads the literal free coordinate generators. -/
theorem submersiveComplexPointChart_apply (P : SubmersivePresentation ℂ A I J)
    (p q : ComplexAlgebraPoint A) (hq : q ∈ (submersiveComplexPointChart P p).source)
    (i : Fin P.dimension) :
    submersiveComplexPointChart P p q i = q (P.val ((submersiveFreeIndexEquiv P).symm i)) := by
  have hz : (submersiveComplexPointZeroFiberHomeomorph P p q).val ∈
      (submersiveAmbientChart P p).source := by
    simpa [submersiveComplexPointChart] using hq
  have h := zeroFiberOpenPartialHomeomorph_apply (submersiveAmbientChart P p)
    (submersiveProductPoint P p) (submersiveAmbientChart_point_mem_source P p)
      (submersiveAmbientChart_point_zero P p) (submersiveComplexPointZeroFiberHomeomorph P p q) hz
  calc
    submersiveComplexPointChart P p q i =
        (submersiveAmbientChart P p (submersiveComplexPointZeroFiberHomeomorph P p q).val).2 i :=
      congrFun h i
    _ = q (P.val ((submersiveFreeIndexEquiv P).symm i)) := by
      simp [submersiveComplexPointZeroFiberHomeomorph, submersiveProductPoint]

omit [DecidableEq J] in
/-- Every actual relation is analytic after the genuine linear coordinate change. -/
theorem submersiveProductRelations_analyticAt (P : SubmersivePresentation ℂ A I J)
    (u : (Fin P.dimension → ℂ) × (J → ℂ)) :
    AnalyticAt ℂ (submersiveProductRelations P) u :=
  AnalyticAt.pi (fun j =>
    AnalyticOnNhd.eval_continuousLinearMap (submersiveCoordinateEquiv P).toContinuousLinearMap
      (P.relation j) u (Set.mem_univ u))

/-- The actual ambient chart is analytic at every point in its ambient domain. -/
theorem submersiveAmbientChart_analyticAt (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) (u : (Fin P.dimension → ℂ) × (J → ℂ)) :
    AnalyticAt ℂ (submersiveAmbientChart P p) u :=
  (submersiveProductRelations_analyticAt P u).prod
    ((ContinuousLinearMap.fst ℂ (Fin P.dimension → ℂ) (J → ℂ)).analyticAt u)

/-- The analytic inverse theorem applies to the genuinely constructed ambient chart. -/
theorem submersiveAmbientChart_symm_analyticAt (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    AnalyticAt ℂ (submersiveAmbientChart P p).symm
      (0, (submersiveProductPoint P p).1) := by
  have hinv : (fderiv ℂ (submersiveAmbientChart P p) (submersiveProductPoint P p)).IsInvertible :=
    (submersiveImplicitFunctionData P p).isInvertible_fderiv_prodFun
  obtain ⟨e, he⟩ := hinv
  have h := (submersiveAmbientChart P p).analyticAt_symm'
    (submersiveAmbientChart_point_mem_source P p)
    (submersiveAmbientChart_analyticAt P p (submersiveProductPoint P p)) he.symm
  simpa using h

/-- A canonical actual open neighborhood on which the ambient inverse is analytic. -/
def submersiveAnalyticInverseNeighborhood (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    TopologicalSpace.Opens ((J → ℂ) × (Fin P.dimension → ℂ)) :=
  ⟨interior {y | AnalyticAt ℂ (submersiveAmbientChart P p).symm y}, isOpen_interior⟩

/-- Inverse analyticity near the actual point proves it lies in that actual open neighborhood. -/
theorem submersiveAnalyticInverseNeighborhood_point (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    (0, (submersiveProductPoint P p).1) ∈ submersiveAnalyticInverseNeighborhood P p := by
  exact mem_interior_iff_mem_nhds.mpr
    (submersiveAmbientChart_symm_analyticAt P p).eventually_analyticAt

/-- Every point in the chosen open neighborhood has the actual analytic ambient inverse. -/
theorem submersiveAnalyticInverseNeighborhood_analyticAt
    (P : SubmersivePresentation ℂ A I J) (p : ComplexAlgebraPoint A)
    {y : (J → ℂ) × (Fin P.dimension → ℂ)}
    (hy : y ∈ submersiveAnalyticInverseNeighborhood P p) :
    AnalyticAt ℂ (submersiveAmbientChart P p).symm y :=
  (interior_subset (s := {z : (J → ℂ) × (Fin P.dimension → ℂ) |
    AnalyticAt ℂ (submersiveAmbientChart P p).symm z})) hy

/-- The actual free-parameter neighborhood is the zero slice of inverse analyticity. -/
def submersiveAnalyticParameterNeighborhood (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) : TopologicalSpace.Opens (Fin P.dimension → ℂ) :=
  ⟨(fun t => ((0 : J → ℂ), t)) ⁻¹' submersiveAnalyticInverseNeighborhood P p,
    (submersiveAnalyticInverseNeighborhood P p).2.preimage
      (continuous_const.prodMk continuous_id)⟩

theorem submersiveAnalyticParameterNeighborhood_point (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    (submersiveProductPoint P p).1 ∈ submersiveAnalyticParameterNeighborhood P p :=
  submersiveAnalyticInverseNeighborhood_point P p

/-- The actual chart at its chosen point reads its actual free product coordinates. -/
@[simp]
theorem submersiveComplexPointChart_point (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    submersiveComplexPointChart P p p = (submersiveProductPoint P p).1 := by
  ext i
  simpa [submersiveProductPoint] using submersiveComplexPointChart_apply P p p
    (submersiveComplexPointChart_point_mem_source P p) i

/-- Shrink the genuine chart target to the actual open neighborhood of inverse analyticity. -/
def submersiveAnalyticComplexPointChart (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    OpenPartialHomeomorph (ComplexAlgebraPoint A) (Fin P.dimension → ℂ) :=
  ((submersiveComplexPointChart P p).symm.restr
    (submersiveAnalyticParameterNeighborhood P p)).symm

theorem submersiveAnalyticComplexPointChart_point_mem_source
    (P : SubmersivePresentation ℂ A I J) (p : ComplexAlgebraPoint A) :
    p ∈ (submersiveAnalyticComplexPointChart P p).source := by
  change p ∈ (submersiveComplexPointChart P p).source ∧
    submersiveComplexPointChart P p p ∈
      interior (submersiveAnalyticParameterNeighborhood P p : Set (Fin P.dimension → ℂ))
  constructor
  · exact submersiveComplexPointChart_point_mem_source P p
  · apply mem_interior_iff_mem_nhds.mpr
    apply (submersiveAnalyticParameterNeighborhood P p).2.mem_nhds
    rw [submersiveComplexPointChart_point]
    exact submersiveAnalyticParameterNeighborhood_point P p

/-- Its actual target lies in the genuine ambient inverse's analytic zero slice. -/
theorem submersiveAnalyticComplexPointChart_target_subset
    (P : SubmersivePresentation ℂ A I J) (p : ComplexAlgebraPoint A) :
    (submersiveAnalyticComplexPointChart P p).target ⊆
      submersiveAnalyticParameterNeighborhood P p := by
  simp only [submersiveAnalyticComplexPointChart, OpenPartialHomeomorph.symm_target,
    OpenPartialHomeomorph.restr_source]
  exact fun _ ht => (interior_subset
    (s := (submersiveAnalyticParameterNeighborhood P p : Set (Fin P.dimension → ℂ)))) ht.2

/-- The unshrunk target is the actual zero slice of the ambient target. -/
@[simp]
theorem submersiveComplexPointChart_target (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    (submersiveComplexPointChart P p).target =
      (fun t => ((0 : J → ℂ), t)) ⁻¹' (submersiveAmbientChart P p).target := by
  simp [submersiveComplexPointChart]

/-- Inverse coordinates in the genuine presentation are the actual ambient inverse. -/
theorem submersiveComplexPointChart_symm_product (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) {t : Fin P.dimension → ℂ}
    (ht : t ∈ (submersiveComplexPointChart P p).target) :
    (submersiveComplexPointProductHomeomorph P
      ((submersiveComplexPointChart P p).symm t)).val =
        (submersiveAmbientChart P p).symm (0, t) := by
  have hm : ((0 : J → ℂ), t) ∈ (submersiveAmbientChart P p).target := by
    simpa only [submersiveComplexPointChart_target, Set.mem_preimage] using ht
  change (submersiveComplexPointZeroFiberHomeomorph P p
    ((submersiveComplexPointZeroFiberHomeomorph P p).symm
      ((zeroFiberOpenPartialHomeomorph (submersiveAmbientChart P p)
        (submersiveProductPoint P p) (submersiveAmbientChart_point_mem_source P p)
        (submersiveAmbientChart_point_zero P p)).symm t))).val = _
  rw [(submersiveComplexPointZeroFiberHomeomorph P p).apply_symm_apply]
  exact zeroFiberOpenPartialHomeomorph_symm_apply (submersiveAmbientChart P p)
    (submersiveProductPoint P p) (submersiveAmbientChart_point_mem_source P p)
    (submersiveAmbientChart_point_zero P p) t hm

omit [DecidableEq J] in
/-- Applying the actual coordinate equivalence recovers every literal generator evaluation. -/
theorem submersiveComplexPointProductHomeomorph_coordinates
    (P : SubmersivePresentation ℂ A I J) (q : ComplexAlgebraPoint A) (i : I) :
    submersiveCoordinateEquiv P (submersiveComplexPointProductHomeomorph P q).val i =
      q (P.val i) := by
  rw [submersiveComplexPointProductHomeomorph_apply]
  simp [submersiveProductPoint]

/-- Every algebra element evaluates as its actual presentation polynomial on the inverse chart. -/
theorem submersiveComplexPointChart_symm_eval (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) (a : A) {t : Fin P.dimension → ℂ}
    (ht : t ∈ (submersiveComplexPointChart P p).target) :
    (submersiveComplexPointChart P p).symm t a =
      MvPolynomial.eval
        (submersiveCoordinateEquiv P ((submersiveAmbientChart P p).symm (0, t)))
        (P.σ a) := by
  rw [← submersiveComplexPointChart_symm_product P p ht]
  have hc : submersiveCoordinateEquiv P
      (submersiveComplexPointProductHomeomorph P
        ((submersiveComplexPointChart P p).symm t)).val =
      fun i => (submersiveComplexPointChart P p).symm t (P.val i) :=
    funext (submersiveComplexPointProductHomeomorph_coordinates P _)
  rw [hc, presentationPolynomial_eval, P.aeval_val_σ]

/-- Target restriction preserves the actual inverse map. -/
@[simp]
theorem submersiveAnalyticComplexPointChart_symm (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) :
    ⇑(submersiveAnalyticComplexPointChart P p).symm = ⇑(submersiveComplexPointChart P p).symm := by
  ext t
  rfl

/-- The analytic chart retains only points of the actual unshrunk target. -/
theorem submersiveAnalyticComplexPointChart_target_subset_original
    (P : SubmersivePresentation ℂ A I J) (p : ComplexAlgebraPoint A) :
    (submersiveAnalyticComplexPointChart P p).target ⊆ (submersiveComplexPointChart P p).target :=
  fun _ ht => ht.1

/-- Target restriction retains only the genuine original source points. -/
theorem submersiveAnalyticComplexPointChart_source_subset_original
    (P : SubmersivePresentation ℂ A I J) (p : ComplexAlgebraPoint A) :
    (submersiveAnalyticComplexPointChart P p).source ⊆ (submersiveComplexPointChart P p).source :=
  fun _ hq => hq.1

/-- The actual analytic chart reads the literal free generators on its genuine source. -/
theorem submersiveAnalyticComplexPointChart_apply (P : SubmersivePresentation ℂ A I J)
    (p q : ComplexAlgebraPoint A) (hq : q ∈ (submersiveAnalyticComplexPointChart P p).source)
    (i : Fin P.dimension) :
    submersiveAnalyticComplexPointChart P p q i = q (P.val ((submersiveFreeIndexEquiv P).symm i)) :=
  submersiveComplexPointChart_apply P p q
    (submersiveAnalyticComplexPointChart_source_subset_original P p hq) i

/-- Every actual algebra element is analytic in the inverse coordinates throughout the actual target. -/
theorem submersiveAnalyticComplexPointChart_symm_eval_analyticOnNhd
    (P : SubmersivePresentation ℂ A I J) (p : ComplexAlgebraPoint A) (a : A) :
    AnalyticOnNhd ℂ (fun t => (submersiveAnalyticComplexPointChart P p).symm t a)
      (submersiveAnalyticComplexPointChart P p).target := by
  intro t ht
  have hi : AnalyticAt ℂ (submersiveAmbientChart P p).symm ((0 : J → ℂ), t) :=
    submersiveAnalyticInverseNeighborhood_analyticAt P p
      (submersiveAnalyticComplexPointChart_target_subset P p ht)
  have hz : AnalyticAt ℂ (fun s : Fin P.dimension → ℂ => ((0 : J → ℂ), s)) t :=
    analyticAt_const.prod analyticAt_id
  have hp : AnalyticAt ℂ
      (fun u => MvPolynomial.eval (submersiveCoordinateEquiv P u) (P.σ a))
      ((submersiveAmbientChart P p).symm (0, t)) :=
    AnalyticOnNhd.eval_continuousLinearMap (submersiveCoordinateEquiv P).toContinuousLinearMap
      (P.σ a) _ (Set.mem_univ _)
  apply ((hp.comp hi).comp hz).congr
  filter_upwards [(submersiveAnalyticComplexPointChart P p).open_target.mem_nhds ht] with s hs
  change MvPolynomial.eval
      (submersiveCoordinateEquiv P ((submersiveAmbientChart P p).symm (0, s))) (P.σ a) = _
  rw [submersiveAnalyticComplexPointChart_symm]
  exact (submersiveComplexPointChart_symm_eval P p a
    (submersiveAnalyticComplexPointChart_target_subset_original P p hs)).symm

end

end ComplexSchemes
