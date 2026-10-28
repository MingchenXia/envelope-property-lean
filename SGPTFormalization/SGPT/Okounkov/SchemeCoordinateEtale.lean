import SGPT.Okounkov.SchemeCoordinatePolynomialGerm
import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# The SAME chosen free-coordinate polynomial map is etale

We specialize the native standard-smooth polynomial factorization to the
already chosen actual presentation and free-index equivalence. The actual
coefficient map is identified on generators before transporting the same
relations and original selected Jacobian. No new etale map is chosen.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Algebra BingWangEntropy RingHom

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f)

local instance etaleCoordinateAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- The SAME original chosen-coordinate polynomial map is actually etale.
The native presentation factorization is used with the actual already fixed
presentation, so no existentially chosen coordinate map is substituted. -/
theorem schemeCoordinatePolynomialMap_etale :
    (schemeCoordinatePolynomialMap f n p).toRingHom.Etale := by
  classical
  let r := (standardSmoothComplexChartPresentation f n p).1
  let P := (standardSmoothComplexChartPresentation f n p).2
  let B := MvPolynomial (Fin n) ℂ
  let e₀ : Fin r ⊕ Fin n ≃ Fin (n + r) :=
    ((Equiv.ofInjective _ P.map_inj).sumCongr
      (standardSmoothComplexChartFreeIndexEquiv f n p).symm).trans (Equiv.Set.sumCompl _)
  let e : MvPolynomial (Fin r) B ≃ₐ[ℂ] P.Ring :=
    (MvPolynomial.sumAlgEquiv ℂ _ _).symm.trans (MvPolynomial.renameEquiv _ e₀)
  let φ := e.toAlgHom.comp (IsScalarTower.toAlgHom ℂ B _)
  let ψ : B →ₐ[ℂ] SchemeCoordinateAffineRing f n p :=
    (IsScalarTower.toAlgHom ℂ P.Ring _).comp φ
  have hψ : ψ = schemeCoordinatePolynomialMap f n p := by
    ext i
    simp [ψ, φ, e, e₀, B, MvPolynomial.algebraMap_eq,
      schemeCoordinatePolynomialMap,
      standardSmoothComplexChartFreeGenerator]
    rfl
  algebraize [φ.toRingHom, (algebraMap P.Ring (SchemeCoordinateAffineRing f n p)).comp φ.toRingHom]
  have := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have : IsScalarTower ℂ B (SchemeCoordinateAffineRing f n p) := .to₁₂₄ _ _ P.Ring _
  have hActual : algebraMap B (SchemeCoordinateAffineRing f n p) =
      (schemeCoordinatePolynomialMap f n p).toRingHom :=
    congrArg AlgHom.toRingHom hψ
  have H : (MvPolynomial.aeval fun x =>
      (algebraMap P.Ring (SchemeCoordinateAffineRing f n p)) (e (MvPolynomial.X x))).toRingHom =
        (algebraMap P.Ring (SchemeCoordinateAffineRing f n p)).comp e.toRingHom := by
    ext
    · simp [e, B, IsScalarTower.algebraMap_eq ℂ B (SchemeCoordinateAffineRing f n p)]
    · simp [e, B, @RingHom.algebraMap_toAlgebra B (SchemeCoordinateAffineRing f n p), φ]
    · simp [e, B]
  let P' : Algebra.PreSubmersivePresentation B (SchemeCoordinateAffineRing f n p)
      (Fin r) (Fin r) :=
    { toGenerators := .ofSurjective (algebraMap _ _ <| e <| .X ·) <| by
        convert! P.algebraMap_surjective.comp e.surjective
        exact congr($H)
      relation := e.symm ∘ P.relation
      span_range_relation_eq_ker := by
        rw [Set.range_comp, ← AlgEquiv.coe_ringEquiv e.symm, AlgEquiv.symm_toRingEquiv,
          ← Ideal.map_span, P.span_range_relation_eq_ker, Ideal.map_symm]
        exact congr(RingHom.ker $H).symm
      map := id
      map_inj := Function.injective_id }
  let P' : Algebra.SubmersivePresentation B (SchemeCoordinateAffineRing f n p)
      (Fin r) (Fin r) :=
    { __ := P'
      jacobian_isUnit := by
        convert! P.jacobian_isUnit using 1
        simp_rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, map_det]
        congr 1
        ext i j
        trans algebraMap P.Ring (SchemeCoordinateAffineRing f n p)
          (e ((e.symm (P.relation j)).pderiv i))
        · simpa [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, P',
            Algebra.Generators.ofSurjective] using congr($H _)
        suffices e ((e.symm (P.relation j)).pderiv i) = (P.relation j).pderiv (P.map i) by
          simp [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, this]
        simp [e, B]
        rw [← MvPolynomial.pderiv_rename (R := ℂ) e₀.injective]
        simpa only [MvPolynomial.renameEquiv_symm, MvPolynomial.renameEquiv_apply,
          show e₀ (Sum.inl i) = P.map i from rfl] using
          congrArg (MvPolynomial.pderiv (e₀ (Sum.inl i)))
            ((MvPolynomial.renameEquiv ℂ e₀).apply_symm_apply (P.relation j)) }
  rw [← hActual]
  exact etale_algebraMap.mpr (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr
    ⟨_, _, _, inferInstance, P', by simp [Algebra.Presentation.dimension]⟩)

end SGPT.Okounkov
