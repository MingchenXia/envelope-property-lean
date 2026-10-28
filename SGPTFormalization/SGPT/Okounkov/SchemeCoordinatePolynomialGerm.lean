import SGPT.Okounkov.SchemeCoordinateRegularGerm
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
# Faithfulness of the actual free-coordinate polynomial subalgebra

The actual manufactured free generators are read back as literal coordinates
by the actual inverse chart. Existing analytic uniqueness and polynomial
extensionality prove faithfulness on this polynomial subalgebra. This does
not assert injectivity on the entire algebraic local stalk.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry BingWangEntropy Filter
open TranscendentalNakamaye.Pending
open scoped Topology

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f)

local instance polynomialCoordinateTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

local instance polynomialCoordinateAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- The polynomial map uses the actual internally chosen free generators. -/
def schemeCoordinatePolynomialMap :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] SchemeCoordinateAffineRing f n p :=
  MvPolynomial.aeval (standardSmoothComplexChartFreeGenerator f n p)

/-- Its actual composite with the previously manufactured germ map. -/
def schemeCoordinatePolynomialGerm : MvPolynomial (Fin n) ℂ →+* HolGerm (Fin n → ℂ) :=
  (schemeCoordinateRegularGerm f n p).comp (schemeCoordinatePolynomialMap f n p).toRingHom

private theorem schemeCoordinate_eventually_target :
    ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),
      z + schemeCoordinateCenter f n p ∈ (schemeAnalyticCoordinateChart f n p).target := by
  have hT : Tendsto (fun z : Fin n → ℂ => z + schemeCoordinateCenter f n p)
      (𝓝 0) (𝓝 (schemeCoordinateCenter f n p)) := by
    simpa only [zero_add] using
      (continuous_add_const (schemeCoordinateCenter f n p)).tendsto (0 : Fin n → ℂ)
  exact hT.eventually ((schemeAnalyticCoordinateChart f n p).open_target.mem_nhds
    ((schemeAnalyticCoordinateChart f n p).map_source
      (schemeAnalyticCoordinateChart_point_mem_source f n p)))

/-- Every actual polynomial has its literal translated coordinate representative. -/
theorem schemeCoordinatePolynomialGerm_representative (Q : MvPolynomial (Fin n) ℂ) :
    (fun z => schemeCoordinateRegularRepresentative f n p (schemeCoordinatePolynomialMap f n p Q) z)
      =ᶠ[𝓝 (0 : Fin n → ℂ)]
        (fun z => MvPolynomial.eval (z + schemeCoordinateCenter f n p) Q) := by
  filter_upwards [schemeCoordinate_eventually_target f n p] with z hz
  have h : (schemeAnalyticCoordinateChartInverseAlgebraPoint f n p
      (z + schemeCoordinateCenter f n p)).comp (schemeCoordinatePolynomialMap f n p) =
        MvPolynomial.aeval (z + schemeCoordinateCenter f n p) := by
    ext i
    simp only [AlgHom.comp_apply, schemeCoordinatePolynomialMap, MvPolynomial.aeval_X]
    exact schemeAnalyticCoordinateChart_inverse_freeGenerator f n p
      (z + schemeCoordinateCenter f n p) hz i
  exact congrArg (fun g : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ => g Q) h

/-- Analytic uniqueness and genuine polynomial extensionality prove that the
actual polynomial-coordinate composite is injective, including `n = 0`. -/
theorem schemeCoordinatePolynomialGerm_injective :
    Function.Injective (schemeCoordinatePolynomialGerm f n p) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro Q hQ
  have hzero : (fun z => schemeCoordinateRegularRepresentative f n p
      (schemeCoordinatePolynomialMap f n p Q) z) =ᶠ[𝓝 (0 : Fin n → ℂ)] 0 :=
    Germ.coe_eq.mp (congrArg Subtype.val hQ)
  have hpoly : (fun z => MvPolynomial.eval (z + schemeCoordinateCenter f n p) Q)
      =ᶠ[𝓝 (0 : Fin n → ℂ)] 0 :=
    (schemeCoordinatePolynomialGerm_representative f n p Q).symm.trans hzero
  have hAnalytic : AnalyticOnNhd ℂ
      (fun z : Fin n → ℂ => MvPolynomial.eval (z + schemeCoordinateCenter f n p) Q)
      Set.univ := by
    intro z _
    exact AnalyticAt.aeval_mvPolynomial
      (f := fun w : Fin n → ℂ => w + schemeCoordinateCenter f n p)
      (fun i => ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt z).add
        analyticAt_const) Q
  have hAll := hAnalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ (0 : Fin n → ℂ)) hpoly
  apply MvPolynomial.funext
  intro t
  simpa only [sub_add_cancel, Pi.zero_apply, map_zero] using
    hAll (Set.mem_univ (t - schemeCoordinateCenter f n p))

/-- Faithfulness of the actual germ composite forces faithfulness of the
actual polynomial map into the SAME original affine coordinate ring. -/
theorem schemeCoordinatePolynomialMap_injective :
    Function.Injective (schemeCoordinatePolynomialMap f n p) := by
  intro Q R hQR
  exact schemeCoordinatePolynomialGerm_injective f n p
    (congrArg (schemeCoordinateRegularGerm f n p) hQR)

/-- Algebraic independence of the actual free generators is a conclusion. -/
theorem schemeCoordinateFreeGenerators_algebraicIndependent :
    AlgebraicIndependent ℂ (standardSmoothComplexChartFreeGenerator f n p) :=
  algebraicIndependent_iff_injective_aeval.mpr (schemeCoordinatePolynomialMap_injective f n p)

/-- A genuine algebraic regular function centered at the actual point. -/
def schemeCoordinateCenteredFreeGenerator (i : Fin n) : SchemeCoordinateAffineRing f n p :=
  standardSmoothComplexChartFreeGenerator f n p i -
    algebraMap ℂ (SchemeCoordinateAffineRing f n p)
      (standardSmoothComplexAlgebraPoint f n p (standardSmoothComplexChartFreeGenerator f n p i))

/-- Actual centered algebraic free generators map to literal coordinate germs. -/
theorem schemeCoordinateCenteredFreeGenerator_germ (i : Fin n) :
    schemeCoordinateRegularGerm f n p (schemeCoordinateCenteredFreeGenerator f n p i) =
      HolGerm.mk (fun z : Fin n → ℂ => z i)
        (Eventually.of_forall fun _ =>
          (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).differentiableAt) := by
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  filter_upwards [schemeCoordinate_eventually_target f n p] with z hz
  dsimp only [schemeCoordinateRegularRepresentative, schemeCoordinateCenteredFreeGenerator]
  rw [map_sub, AlgHom.commutes,
    schemeAnalyticCoordinateChart_inverse_freeGenerator f n p
      (z + schemeCoordinateCenter f n p) hz i]
  have hcenter : schemeCoordinateCenter f n p i =
      standardSmoothComplexAlgebraPoint f n p (standardSmoothComplexChartFreeGenerator f n p i) :=
    congrFun (schemeAnalyticCoordinateChart_point f n p) i
  simp only [Pi.add_apply, hcenter, Algebra.algebraMap_self_apply, add_sub_cancel_right]

end SGPT.Okounkov
