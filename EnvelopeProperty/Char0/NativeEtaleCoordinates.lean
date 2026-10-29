import EnvelopeProperty.Char0.NativePreferredJacobian
import EnvelopeProperty.ComplexGeometry.Pluripotential.LocalHolomorphicInverse

/-! # Actual local holomorphic coordinates from original algebraic etale coordinates -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace EnvelopeProperty.Char0.NativeEtaleCoordinates

open CategoryTheory AlgebraicGeometry ComplexSchemes Filter
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HolomorphicGerms NativePreferredJacobian NativeCoefficientComposition
open HolomorphicGermJacobian HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
open scoped Topology

variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f)

local instance etalePreferredAffineAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- The original affine coefficients in the actual preferred centered holomorphic chart. -/
def coefficientGerm : R →+* HolGerm (ComplexModel n) := by
  let := affinePointFieldAlgebra f
  exact (schemeCoordinateModelRegularAlgHom f n p).toRingHom.comp (targetAlgebraMap f n p).toRingHom

/-- The original coefficient germ has exactly the value of the original actual scheme point. -/
theorem coefficientGerm_eval (r : R) :
    HolGerm.eval (coefficientGerm f n p r) = (Spec.preimage p.val).hom r := by
  change HolGerm.eval (schemeCoordinateModelGermEquiv n
    (schemeCoordinateRegularGerm f n p (targetAlgebraMap f n p r))) = _
  rw [schemeCoordinateModelGermEquiv_eval, schemeCoordinateRegularGerm_eval]
  change affineSchemePointEquivOfStructure
    ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    (standardSmoothComplexChartPoint f n p) (targetAlgebraMap f n p r) = _
  rw [affineSchemePointEquivOfStructure_apply]
  have he := congrArg Spec.preimage (standardSmoothComplexChartPoint_fac f n p)
  rw [Spec.preimage_comp] at he
  have hr := congrArg (fun a : CommRingCat.of R ⟶ CommRingCat.of ℂ => a r) he
  change (Spec.preimage (standardSmoothComplexChartPoint f n p).val).hom
    ((Spec.preimage (standardSmoothComplexAffineChart f n p).val.map).hom r) = _ at hr
  exact hr

/-- The literal original coefficient map is the SAME original stalk map in the actual centered model. -/
theorem coefficientGerm_stalk (r : R) :
    coefficientGerm f n p r = schemeCoordinateModelGermEquiv n
      (schemeCoordinateStalkRegularGerm f n p
        ((Spec (.of R)).presheaf.germ ⊤ (schemeComplexPointImage f p) trivial
          ((Scheme.ΓSpecIso (.of R)).inv r))) := by
  rw [← schemeCoordinateStalkEquiv_global f n p ((Scheme.ΓSpecIso (.of R)).inv r),
    schemeCoordinateStalkRegularGerm_regular]
  change schemeCoordinateModelRegularAlgHom f n p (targetAlgebraMap f n p r) =
    schemeCoordinateModelRegularAlgHom f n p
      (schemeCoordinateGlobalCoefficient f n p ((Scheme.ΓSpecIso (.of R)).inv r))
  rw [targetAlgebraMap_eq_globalCoefficient]

/-- The literal original coordinate evaluations, centered at their actual values. -/
def centeredRepresentative (t : Fin n → R) (z : ComplexModel n) : ComplexModel n :=
  targetCoordinateRepresentative f n p t z - targetCoordinateRepresentative f n p t 0

/-- The actual centered coordinate map fixes the original origin. -/
theorem centeredRepresentative_zero (t : Fin n → R) :
    centeredRepresentative f n p t 0 = 0 := sub_self _

/-- Holomorphy of the literal centered original coordinate map is internally derived. -/
theorem centeredRepresentative_holomorphic (t : Fin n → R) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (centeredRepresentative f n p t) z :=
  (targetCoordinateRepresentative_holomorphic f n p t).mono fun _ hz => hz.sub_const _

/-- The whole actual component is the original coefficient germ minus its actual scalar value. -/
theorem centeredRepresentative_component (t : Fin n → R) (i : Fin n) :
    (((coefficientGerm f n p (t i) - HolGerm.constHom
      (HolGerm.eval (coefficientGerm f n p (t i)))) : HolGerm (ComplexModel n)) :
        Germ (𝓝 (0 : ComplexModel n)) ℂ) =
      (fun z => centeredRepresentative f n p t z i) := by
  have he : HolGerm.eval (coefficientGerm f n p (t i)) =
      targetCoordinateRepresentative f n p t 0 i := by
    change Germ.valueRingHom ((coefficientGerm f n p (t i) : HolGerm (ComplexModel n)) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) = _
    rw [show ((coefficientGerm f n p (t i) : HolGerm (ComplexModel n)) :
        Germ (𝓝 (0 : ComplexModel n)) ℂ) =
      (fun z => targetCoordinateRepresentative f n p t z i) from
        targetCoordinateRepresentative_component f n p t i]
    rfl
  change ((coefficientGerm f n p (t i) : HolGerm (ComplexModel n)) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) -
    ((fun _ : ComplexModel n => HolGerm.eval (coefficientGerm f n p (t i))) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) = _
  rw [show ((coefficientGerm f n p (t i) : HolGerm (ComplexModel n)) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) =
    (fun z => targetCoordinateRepresentative f n p t z i) from
      targetCoordinateRepresentative_component f n p t i, he]
  rfl

/-- Genuine original algebraic etaleness gives the actual invertible centered differential. -/
theorem centeredRepresentative_fderiv_bijective (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale) :
    Function.Bijective (fderiv ℂ (centeredRepresentative f n p t) 0) := by
  have hunit := targetCoordinateJacobian_isUnit f n p t ht
  have he : HolGerm.eval (targetCoordinateJacobian f n p t) =
      DivisorialChangeOfVariables.complexJacobian (targetCoordinateRepresentative f n p t) 0 := by
    change Germ.valueRingHom ((targetCoordinateJacobian f n p t : HolGerm (ComplexModel n)) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) = _
    rw [show ((targetCoordinateJacobian f n p t : HolGerm (ComplexModel n)) :
        Germ (𝓝 (0 : ComplexModel n)) ℂ) =
      (DivisorialChangeOfVariables.complexJacobian (targetCoordinateRepresentative f n p t) :
        Germ (𝓝 (0 : ComplexModel n)) ℂ) from jacobianGerm_source _ _]
    rfl
  have hdet : (fderiv ℂ (centeredRepresentative f n p t) 0).toLinearMap.det ≠ 0 := by
    change (fderiv ℂ (fun z => targetCoordinateRepresentative f n p t z -
      targetCoordinateRepresentative f n p t 0) 0).toLinearMap.det ≠ 0
    rw [fderiv_sub_const]
    change DivisorialChangeOfVariables.complexJacobian (targetCoordinateRepresentative f n p t) 0 ≠ 0
    rw [← he]
    exact (HolGerm.isUnit_iff_eval_ne_zero _).mp hunit
  have hinj : Function.Injective (fderiv ℂ (centeredRepresentative f n p t) 0) := by
    apply LinearMap.ker_eq_bot.mp
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  exact ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩

/-- The actual original algebraic etale tuple manufactures genuine local holomorphic inverse
coordinates, inside every prescribed open neighborhood of the original center. -/
theorem exists_localCoordinates (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale)
    (N : Set (ComplexModel n)) (hN : IsOpen N) (h0N : 0 ∈ N) :
    ∃ Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n),
      Φ.source ⊆ N ∧ Φ.toFun = centeredRepresentative f n p t ∧ Φ.toFun 0 = 0 := by
  obtain ⟨U, hU, hUo, h0U⟩ := mem_nhds_iff.mp
    (centeredRepresentative_holomorphic f n p t)
  obtain ⟨Φ, hΦ, hfun, _⟩ := exists_localHolomorphicEquivAt (hUo.inter hN)
    ⟨h0U, h0N⟩ (fun z hz => (hU hz.1).differentiableWithinAt)
    (centeredRepresentative_fderiv_bijective f n p t ht).injective
  exact ⟨Φ, fun _ hz => (hΦ hz).2, hfun, by rw [hfun, centeredRepresentative_zero]⟩

/-- The chosen actual local inverse coordinates retain the literal original centered map. -/
def localCoordinates (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale) :
    LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n) :=
  Classical.choose (exists_localCoordinates f n p t ht Set.univ isOpen_univ (Set.mem_univ _))

/-- The actual chosen forward map is the original centered coefficient vector. -/
theorem localCoordinates_toFun (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale) :
    (localCoordinates f n p t ht).toFun = centeredRepresentative f n p t :=
  (Classical.choose_spec
    (exists_localCoordinates f n p t ht Set.univ isOpen_univ (Set.mem_univ _))).2.1

/-- The actual local coordinate equivalence fixes the original origin. -/
theorem localCoordinates_zero (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale) :
    (localCoordinates f n p t ht).toFun 0 = 0 :=
  (Classical.choose_spec
    (exists_localCoordinates f n p t ht Set.univ isOpen_univ (Set.mem_univ _))).2.2

/-- The original actual etale tuple gives an equivalence of the ENTIRE holomorphic germ algebras. -/
def coordinateGermEquiv (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale) :
    HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) :=
  localGermAlgEquiv (localCoordinates f n p t ht) (localCoordinates_zero f n p t ht)

/-- The same original coefficient map sends original complex scalars to their literal constants. -/
theorem coefficientGerm_scalar (c : ℂ) :
    letI := affinePointFieldAlgebra f
    coefficientGerm f n p (algebraMap ℂ R c) = HolGerm.constHom c := by
  let := affinePointFieldAlgebra f
  change schemeCoordinateModelRegularAlgHom f n p
    (targetAlgebraMap f n p (algebraMap ℂ R c)) = _
  rw [(targetAlgebraMap f n p).commutes, (schemeCoordinateModelRegularAlgHom f n p).commutes]
  rfl

/-- The original algebraic coordinate centered at its actual original complex residue value. -/
def centeredOriginal (t : Fin n → R) (i : Fin n) : R :=
  letI := affinePointFieldAlgebra f
  t i - algebraMap ℂ R (HolGerm.eval (coefficientGerm f n p (t i)))

/-- Original centering commutes with the actual entire coefficient map. -/
theorem coefficientGerm_centeredOriginal (t : Fin n → R) (i : Fin n) :
    coefficientGerm f n p (centeredOriginal f n p t i) =
      coefficientGerm f n p (t i) - HolGerm.constHom
        (HolGerm.eval (coefficientGerm f n p (t i))) := by
  let := affinePointFieldAlgebra f
  change coefficientGerm f n p (t i - algebraMap ℂ R _) = _
  rw [map_sub, coefficientGerm_scalar]

/-- Every actual coordinate germ is sent to the SAME centered original algebraic coefficient. -/
theorem coordinateGermEquiv_coordinate (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale) (i : Fin n) :
    coordinateGermEquiv f n p t ht (coordinateGerm i) =
      coefficientGerm f n p (centeredOriginal f n p t i) := by
  rw [coefficientGerm_centeredOriginal]
  apply Subtype.ext
  change ((fun z => (localCoordinates f n p t ht).toFun z i) :
    Germ (𝓝 (0 : ComplexModel n)) ℂ) = _
  rw [localCoordinates_toFun]
  exact (centeredRepresentative_component f n p t i).symm

/-- An original coordinate equation through the actual original point needs no centering correction. -/
theorem coordinateGermEquiv_coordinate_of_eval_zero (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale) (i : Fin n)
    (hi : HolGerm.eval (coefficientGerm f n p (t i)) = 0) :
    coordinateGermEquiv f n p t ht (coordinateGerm i) = coefficientGerm f n p (t i) := by
  rw [coordinateGermEquiv_coordinate, coefficientGerm_centeredOriginal, hi, map_zero, sub_zero]

/-- Entire monomial germs are retained, including every actual original algebraic coefficient. -/
theorem coordinateGermEquiv_monomial (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale) (e : Fin n → ℕ) :
    coordinateGermEquiv f n p t ht (∏ i, (coordinateGerm i) ^ e i) =
      coefficientGerm f n p (∏ i, (centeredOriginal f n p t i) ^ e i) := by
  rw [map_prod, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_pow, map_pow, coordinateGermEquiv_coordinate]

/-- The WHOLE original centered monomial ideal extends to the actual coordinate ideal,
with arbitrary holomorphic coefficients rather than selected algebraic test germs. -/
theorem map_centered_monomial_ideal {κ : Type*} (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale) (e : κ → Fin n → ℕ) :
    (Ideal.span (Set.range fun a => ∏ i, (centeredOriginal f n p t i) ^ e a i)).map
        (coefficientGerm f n p) =
      (Ideal.span (Set.range fun a => ∏ i, (coordinateGerm i) ^ e a i)).map
        (coordinateGermEquiv f n p t ht).toRingHom := by
  rw [Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  exact (coordinateGermEquiv_monomial f n p t ht (e a)).symm

/-- Active original component equations with zero center value give their WHOLE actual monomial ideal. -/
theorem map_active_monomial_ideal {κ : Type*} [Fintype κ] (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale)
    (c : κ → Fin n) (a : κ → ℕ)
    (hc : ∀ i, HolGerm.eval (coefficientGerm f n p (t (c i))) = 0) :
    (Ideal.span {∏ i, t (c i) ^ a i}).map (coefficientGerm f n p) =
      (Ideal.span {∏ i, (coordinateGerm (c i)) ^ a i}).map
        (coordinateGermEquiv f n p t ht).toRingHom := by
  have he : coordinateGermEquiv f n p t ht (∏ i, (coordinateGerm (c i)) ^ a i) =
      coefficientGerm f n p (∏ i, t (c i) ^ a i) := by
    rw [map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [map_pow, map_pow, coordinateGermEquiv_coordinate_of_eval_zero f n p t ht (c i) (hc i)]
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
  exact congrArg (fun g => Ideal.span {g}) he.symm

end EnvelopeProperty.Char0.NativeEtaleCoordinates
