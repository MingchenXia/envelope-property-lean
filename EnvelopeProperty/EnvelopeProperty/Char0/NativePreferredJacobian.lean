import EnvelopeProperty.Char0.NativeCoefficientComposition

/-! # The whole original Jacobian ideal of the actual default-chart scheme map -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativePreferredJacobian

open CategoryTheory AlgebraicGeometry BingWangEntropy Filter
open TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open SGPT.Okounkov NativeSchemeJacobian NativeSchemeJacobianGenerator
open NativeCoefficientComposition AnalyticEtaleJacobian AnalyticJacobianGenerator
open HolomorphicGermJacobian HironakaHolomorphicJetChartInvariance
open scoped Topology

section Target
variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (q : SchemeComplexPoint f)
local instance preferredTargetAffineAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f n q) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n q).val.map ≫ f)
local instance preferredTargetOriginalAction : Algebra R (SchemeCoordinateAffineRing f n q) :=
  (targetAlgebraMap f n q).toAlgebra

/-- The literal original target coordinate evaluations in the actual preferred centered target chart. -/
def targetCoordinateRepresentative (t : Fin n → R) (z : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 (fun i => schemeCoordinateRegularRepresentative f n q
    (targetAlgebraMap f n q (t i)) (schemeCoordinateModelEquiv n z))

/-- Actual near-origin holomorphy is manufactured from the original target regular functions. -/
theorem targetCoordinateRepresentative_holomorphic (t : Fin n → R) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (targetCoordinateRepresentative f n q t) z := by
  have hi (i : Fin n) : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (fun w => targetCoordinateRepresentative f n q t w i) z :=
    eventually_differentiableAt_comp_clm (schemeCoordinateModelEquiv n).toContinuousLinearMap
      (schemeCoordinateRegularRepresentative_holomorphic f n q (targetAlgebraMap f n q (t i)))
  filter_upwards [Filter.eventually_all.mpr hi] with z hz
  exact (differentiableAt_piLp 2).mpr hz

/-- ENTIRE target coefficient germs are the actual components of the literal target vector. -/
theorem targetCoordinateRepresentative_component (t : Fin n → R) (i : Fin n) :
    ((schemeCoordinateModelRegularAlgHom f n q (targetAlgebraMap f n q (t i)) :
      HolGerm (ComplexModel n)) : Germ (𝓝 (0 : ComplexModel n)) ℂ) =
        (fun z => targetCoordinateRepresentative f n q t z i) := by
  change ((schemeCoordinateModelGermEquiv n
    (HolGerm.mk (schemeCoordinateRegularRepresentative f n q (targetAlgebraMap f n q (t i)))
      (schemeCoordinateRegularRepresentative_holomorphic f n q (targetAlgebraMap f n q (t i)))) :
        HolGerm (ComplexModel n)) : Germ (𝓝 (0 : ComplexModel n)) ℂ) = _
  rw [schemeCoordinateModelGermEquiv, HolGerm.comapEquiv_mk]
  rfl

/-- The actual original target-coordinate complex Jacobian as a whole holomorphic germ. -/
def targetCoordinateJacobian (t : Fin n → R) : HolGerm (ComplexModel n) :=
  jacobianGerm (targetCoordinateRepresentative f n q t)
    (targetCoordinateRepresentative_holomorphic f n q t)

/-- Its entire determinant is exactly the original target-coefficient analytic Jacobian. -/
theorem targetCoordinateJacobian_eq (t : Fin n → R) :
    targetCoordinateJacobian f n q t =
      analyticSourceJacobian (schemeCoordinateModelRegularAlgHom f n q) t := by
  symm
  exact analyticSourceJacobian_eq_jacobianGerm _ t _ _
    (targetCoordinateRepresentative_component f n q t)

/-- Actual original target etale coordinates internally derive the actual target Jacobian unit. -/
theorem targetCoordinateJacobian_isUnit (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale) :
    IsUnit (targetCoordinateJacobian f n q t) := by
  let := affinePointFieldAlgebra f
  let : IsScalarTower ℂ R (SchemeCoordinateAffineRing f n q) :=
    IsScalarTower.of_algebraMap_eq fun c => ((targetAlgebraMap f n q).commutes c).symm
  have hs : Spec.map (CommRingCat.ofHom
      (algebraMap R (SchemeCoordinateAffineRing f n q))) =
      (standardSmoothComplexAffineChart f n q).val.map :=
    affineSchemeOverAlgebraMap_spec _ _ _ rfl
  have hA : (algebraMap R (SchemeCoordinateAffineRing f n q)).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)
      (φ := CommRingCat.ofHom (algebraMap R (SchemeCoordinateAffineRing f n q)))).mp
        (by rw [hs]; infer_instance)
  rw [targetCoordinateJacobian_eq]
  exact AnalyticEtaleJacobian.coordinateJacobian_isUnit
    (schemeCoordinateModelRegularAlgHom f n q)
    (standardSmoothComplexChartFreeGenerator f n q) (schemeCoordinatePolynomialMap_etale f n q)
    (fun i => standardSmoothComplexAlgebraPoint f n q (standardSmoothComplexChartFreeGenerator f n q i))
    (schemeCoordinateModelRegularAlgHom_freeGenerator f n q)
    (fun i => algebraMap R (SchemeCoordinateAffineRing f n q) (t i))
    (etale_aeval_algebraMap t ht hA)
end Target

variable {R : Type} [CommRing R] {Y : Scheme}
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Y ⟶ Spec (.of R)) (n : ℕ)
  [SmoothOfRelativeDimension n (π ≫ f)] [SmoothOfRelativeDimension n f]
  [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] [IsSeparated f] [QuasiCompact f]
  (p : SchemeComplexPoint (π ≫ f))
local instance preferredSourceAffineAlgebra : Algebra ℂ (SchemeCoordinateAffineRing (π ≫ f) n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart (π ≫ f) n p).val.map ≫ (π ≫ f))
local instance preferredSourceOriginalAction : Algebra R (SchemeCoordinateAffineRing (π ≫ f) n p) :=
  (sourceAlgebraMap f π n p).toAlgebra
local instance preferredImageAffineAlgebra :
    Algebra ℂ (SchemeCoordinateAffineRing f n (schemeComplexPointMap (π ≫ f) f π rfl p)) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n
    (schemeComplexPointMap (π ≫ f) f π rfl p)).val.map ≫ f)

/-- The complex-Jacobian germ of the SAME original default centered scheme-morphism coordinate map. -/
def preferredJacobian : HolGerm (ComplexModel n) :=
  jacobianGerm (schemeMorphismCenteredCoordinateMap f π n n p)
    (schemeMorphismCenteredCoordinateMap_holomorphic f π n n p)

/-- The original source coefficient Jacobian has the WHOLE actual default-coordinate chain-rule factorization. -/
theorem sourceCoordinateJacobian_comp (t : Fin n → R) :
    sourceCoordinateJacobian f π n p t =
      compAlgHom (schemeMorphismCenteredCoordinateMap f π n n p)
        (schemeMorphismCenteredCoordinateMap_holomorphic f π n n p)
        (schemeMorphismCenteredCoordinateMap_zero f π n n p)
        (targetCoordinateJacobian f n (schemeComplexPointMap (π ≫ f) f π rfl p) t) *
      preferredJacobian f π n p := by
  let F := schemeMorphismCenteredCoordinateMap f π n n p
  let G := targetCoordinateRepresentative f n (schemeComplexPointMap (π ≫ f) f π rfl p) t
  have hF := schemeMorphismCenteredCoordinateMap_holomorphic f π n n p
  have hF0 := schemeMorphismCenteredCoordinateMap_zero f π n n p
  have hG := targetCoordinateRepresentative_holomorphic f n (schemeComplexPointMap (π ≫ f) f π rfl p) t
  have htF : Tendsto F (𝓝 0) (𝓝 0) := by simpa only [hF0] using hF.self_of_nhds.continuousAt.tendsto
  have hComp : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G ∘ F) z := by
    filter_upwards [hF, htF.eventually hG] with z hf hg
    exact hg.comp z hf
  have he : analyticSourceJacobian (schemeCoordinateModelRegularAlgHom (π ≫ f) n p) t =
      jacobianGerm (G ∘ F) hComp := by
    apply analyticSourceJacobian_eq_jacobianGerm
    intro i
    change ((schemeCoordinateModelRegularAlgHom (π ≫ f) n p (sourceAlgebraMap f π n p (t i)) :
      HolGerm (ComplexModel n)) : Germ (𝓝 (0 : ComplexModel n)) ℂ) = _
    rw [originalCoefficient_comp f π n p n (t i)]
    change ((schemeCoordinateModelRegularAlgHom f n (schemeComplexPointMap (π ≫ f) f π rfl p)
      (targetAlgebraMap f n (schemeComplexPointMap (π ≫ f) f π rfl p) (t i)) :
        HolGerm (ComplexModel n)) : Germ (𝓝 (0 : ComplexModel n)) ℂ).compTendsto F htF = _
    rw [targetCoordinateRepresentative_component]
    rfl
  rw [sourceCoordinateJacobian_eq, he]
  exact jacobianGerm_comp F G hF hF0 hG

/-- The WHOLE native analytic Jacobian ideal is generated by the literal default-chart complex Jacobian. -/
theorem jacobianIdeal_eq_span_preferred (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale) :
    analyticSourceJacobianIdeal (R := R) (schemeCoordinateModelRegularAlgHom (π ≫ f) n p) =
      Ideal.span {preferredJacobian f π n p} := by
  rw [jacobianIdeal_eq_span_sourceCoordinateJacobian f π n p t ht, sourceCoordinateJacobian_comp]
  exact Ideal.span_singleton_mul_left_unit
    ((targetCoordinateJacobian_isUnit f n (schemeComplexPointMap (π ≫ f) f π rfl p) t ht).map
      (compAlgHom (schemeMorphismCenteredCoordinateMap f π n n p)
        (schemeMorphismCenteredCoordinateMap_holomorphic f π n n p)
        (schemeMorphismCenteredCoordinateMap_zero f π n n p)).toRingHom) _

/-- Extension of the WHOLE original algebraic Jacobian ideal is the actual default-coordinate Jacobian ideal. -/
theorem algebraicJacobianIdeal_map_eq_span_preferred (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale)
    (v : Fin n → SchemeCoordinateAffineRing (π ≫ f) n p)
    (hv : (MvPolynomial.aeval (R := ℂ) v).toRingHom.Etale) :
    (affineRelativeJacobianIdeal (R := R) (etaleDifferentialBasis v hv)).map
      (schemeCoordinateModelRegularAlgHom (π ≫ f) n p).toRingHom =
        Ideal.span {preferredJacobian f π n p} := by
  rw [← NativeSchemeJacobian.jacobianIdeal_eq_map f π n p v hv]
  exact jacobianIdeal_eq_span_preferred f π n p t ht

end EnvelopeProperty.Char0.NativePreferredJacobian
