import EnvelopeProperty.ComplexGeometry.Schemes.AlgebraicAnalyticTransitions
import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAnalyticClosedEmbedding

/-!
# The native affine differential of a closed immersion

Surjectivity of the actual complex algebra map lifts literal source chart
generators to actual ambient regular functions. Their evaluations construct a
holomorphic local coordinate retraction and prove derivative injectivity.
-/

open Algebra CategoryTheory AlgebraicGeometry
open scoped Topology

set_option backward.isDefEq.respectTransparency false

namespace ComplexSchemes

noncomputable section

variable {A B I J I' J' : Type*} [CommRing A] [Algebra ℂ A]
  [CommRing B] [Algebra ℂ B] [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype I'] [Fintype J'] [DecidableEq J']

/-- Actual lifts of the literal source free generators define a coordinate retraction. -/
def submersiveAnalyticTransitionLocalRetraction (P : SubmersivePresentation ℂ A I J)
    (Q : SubmersivePresentation ℂ B I' J') (g : B →ₐ[ℂ] A)
    (hg : Function.Surjective g) (q : ComplexAlgebraPoint B) :
    (Fin Q.dimension → ℂ) → (Fin P.dimension → ℂ) :=
  fun u i => (submersiveAnalyticComplexPointChart Q q).symm u
    (hg (P.val ((submersiveFreeIndexEquiv P).symm i))).choose

omit [DecidableEq J] in
/-- Each lifted ambient regular function is analytic in the actual inverse target chart. -/
theorem submersiveAnalyticTransitionLocalRetraction_analyticOnNhd
    (P : SubmersivePresentation ℂ A I J) (Q : SubmersivePresentation ℂ B I' J')
    (g : B →ₐ[ℂ] A) (hg : Function.Surjective g) (q : ComplexAlgebraPoint B) :
    AnalyticOnNhd ℂ (submersiveAnalyticTransitionLocalRetraction P Q g hg q)
      (submersiveAnalyticComplexPointChart Q q).target := by
  intro u hu
  apply AnalyticAt.pi
  intro i
  exact submersiveAnalyticComplexPointChart_symm_eval_analyticOnNhd Q q
    (hg (P.val ((submersiveFreeIndexEquiv P).symm i))).choose u hu

/-- The derived coordinate retraction is a genuine left inverse on the actual open overlap. -/
theorem submersiveAnalyticTransitionLocalRetraction_leftInverse
    (P : SubmersivePresentation ℂ A I J) (Q : SubmersivePresentation ℂ B I' J')
    (g : B →ₐ[ℂ] A) (hg : Function.Surjective g)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B)
    {t : Fin P.dimension → ℂ} (ht : t ∈ submersiveAnalyticTransitionDomain P Q g p q) :
    submersiveAnalyticTransitionLocalRetraction P Q g hg q
      (submersiveAnalyticTransition P Q g p q t) = t := by
  ext i
  change (submersiveAnalyticComplexPointChart Q q).symm
      (submersiveAnalyticComplexPointChart Q q
        (((submersiveAnalyticComplexPointChart P p).symm t).comp g))
      (hg (P.val ((submersiveFreeIndexEquiv P).symm i))).choose = t i
  rw [(submersiveAnalyticComplexPointChart Q q).left_inv ht.2]
  change (submersiveAnalyticComplexPointChart P p).symm t
    (g (hg (P.val ((submersiveFreeIndexEquiv P).symm i))).choose) = t i
  rw [(hg (P.val ((submersiveFreeIndexEquiv P).symm i))).choose_spec]
  rw [← submersiveAnalyticComplexPointChart_apply P p _
    ((submersiveAnalyticComplexPointChart P p).map_target ht.1) i]
  exact congrArg (fun u => u i) ((submersiveAnalyticComplexPointChart P p).right_inv ht.1)

/-- The complex chain rule differentiates the actual local retraction identity. -/
theorem submersiveAnalyticTransition_fderiv_leftInverse
    (P : SubmersivePresentation ℂ A I J) (Q : SubmersivePresentation ℂ B I' J')
    (g : B →ₐ[ℂ] A) (hg : Function.Surjective g)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B)
    {t : Fin P.dimension → ℂ} (ht : t ∈ submersiveAnalyticTransitionDomain P Q g p q) :
    (fderiv ℂ (submersiveAnalyticTransitionLocalRetraction P Q g hg q)
      (submersiveAnalyticTransition P Q g p q t)).comp
        (fderiv ℂ (submersiveAnalyticTransition P Q g p q) t) =
      ContinuousLinearMap.id ℂ (Fin P.dimension → ℂ) := by
  have hT := (submersiveAnalyticTransition_analyticOnNhd P Q g p q t ht).differentiableAt
  have htarget : submersiveAnalyticTransition P Q g p q t ∈
      (submersiveAnalyticComplexPointChart Q q).target :=
    (submersiveAnalyticComplexPointChart Q q).map_source ht.2
  have hH := (submersiveAnalyticTransitionLocalRetraction_analyticOnNhd P Q g hg q
    _ htarget).differentiableAt
  have hcomp := hH.hasFDerivAt.comp t hT.hasFDerivAt
  have heq : (fun s => submersiveAnalyticTransitionLocalRetraction P Q g hg q
      (submersiveAnalyticTransition P Q g p q s)) =ᶠ[𝓝 t] id := by
    filter_upwards [(submersiveAnalyticTransitionDomain_isOpen P Q g p q).mem_nhds ht]
      with s hs
    exact submersiveAnalyticTransitionLocalRetraction_leftInverse P Q g hg p q hs
  exact (hcomp.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id t)

/-- The true derivative of an affine closed-immersion coordinate map is injective. -/
theorem submersiveAnalyticTransition_fderiv_injective
    (P : SubmersivePresentation ℂ A I J) (Q : SubmersivePresentation ℂ B I' J')
    (g : B →ₐ[ℂ] A) (hg : Function.Surjective g)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B)
    {t : Fin P.dimension → ℂ} (ht : t ∈ submersiveAnalyticTransitionDomain P Q g p q) :
    Function.Injective (fderiv ℂ (submersiveAnalyticTransition P Q g p q) t) := by
  intro v w hvw
  have hv := congrArg (fun L : (Fin P.dimension → ℂ) →L[ℂ] (Fin P.dimension → ℂ) => L v)
    (submersiveAnalyticTransition_fderiv_leftInverse P Q g hg p q ht)
  have hw := congrArg (fun L : (Fin P.dimension → ℂ) →L[ℂ] (Fin P.dimension → ℂ) => L w)
    (submersiveAnalyticTransition_fderiv_leftInverse P Q g hg p q ht)
  change _ = v at hv
  change _ = w at hw
  exact hv.symm.trans ((congrArg
    (fderiv ℂ (submersiveAnalyticTransitionLocalRetraction P Q g hg q)
      (submersiveAnalyticTransition P Q g p q t)) hvw).trans hw)

end

section NativeAffine

variable {A B : CommRingCat} {I J I' J' : Type*}
  [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype I'] [Fintype J'] [DecidableEq J']

/-- Actual affine closed immersions supply surjectivity and hence the native complex immersion. -/
theorem affineClosedImmersionSubmersiveAnalyticTransition_fderiv_injective
    (f : Spec B ⟶ Spec (.of ℂ)) (f' : Spec A ⟶ Spec (.of ℂ))
    (h : Spec A ⟶ Spec B) [IsClosedImmersion h] (hh : h ≫ f = f') :
    let _ := affinePointFieldAlgebra f
    let _ := affinePointFieldAlgebra f'
    ∀ (P : SubmersivePresentation ℂ A I J) (Q : SubmersivePresentation ℂ B I' J')
      (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) (t : Fin P.dimension → ℂ),
      t ∈ submersiveAnalyticTransitionDomain P Q (affineSchemeOverAlgebraMap f f' h hh) p q →
      Function.Injective
        (fderiv ℂ (submersiveAnalyticTransition P Q (affineSchemeOverAlgebraMap f f' h hh) p q) t) := by
  let := affinePointFieldAlgebra f
  let := affinePointFieldAlgebra f'
  dsimp only
  intro P Q p q t ht
  exact submersiveAnalyticTransition_fderiv_injective P Q (affineSchemeOverAlgebraMap f f' h hh)
    (affineClosedImmersion_preimage_surjective h) p q ht

end NativeAffine

end ComplexSchemes
