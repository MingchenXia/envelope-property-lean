import BingWangEntropy.SchemeAnalyticCoordinates
import TranscendentalNakamaye.Pending.HolomorphicGermRing
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Actual affine regular functions in a chosen scheme coordinate germ

Native smoothness manufactures the actual standard-smooth neighborhood and
its actual inverse algebra evaluations. We take their literal centered germs
in the product coordinate space. No global TN manifold or injectivity claim
is made here.
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

/-- The actual internally chosen affine coordinate ring at the actual point. -/
abbrev SchemeCoordinateAffineRing := (standardSmoothComplexAffineChart f n p).val.ring

local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f

local instance : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- The center is the actual coordinate vector of the original scheme point. -/
def schemeCoordinateCenter : Fin n → ℂ := schemeAnalyticCoordinateChart f n p p

/-- A literal inverse evaluation, centered at the actual original point. -/
def schemeCoordinateRegularRepresentative (a : SchemeCoordinateAffineRing f n p)
    (z : Fin n → ℂ) : ℂ :=
  schemeAnalyticCoordinateChartInverseAlgebraPoint f n p (z + schemeCoordinateCenter f n p) a

/-- Genuine inverse evaluation analyticity supplies the neighborhood germ. -/
theorem schemeCoordinateRegularRepresentative_holomorphic
    (a : SchemeCoordinateAffineRing f n p) :
    ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),
      DifferentiableAt ℂ (schemeCoordinateRegularRepresentative f n p a) z := by
  let e := schemeAnalyticCoordinateChart f n p
  have ht : schemeCoordinateCenter f n p ∈ e.target :=
    e.map_source (schemeAnalyticCoordinateChart_point_mem_source f n p)
  have hT : Tendsto (fun z : Fin n → ℂ => z + schemeCoordinateCenter f n p)
      (𝓝 0) (𝓝 (schemeCoordinateCenter f n p)) := by
    simpa only [zero_add] using
      (continuous_add_const (schemeCoordinateCenter f n p)).tendsto (0 : Fin n → ℂ)
  filter_upwards [hT.eventually (e.open_target.mem_nhds ht)] with z hz
  have ha : AnalyticAt ℂ
      (fun t : Fin n → ℂ => schemeAnalyticCoordinateChartInverseAlgebraPoint f n p t a)
      (z + schemeCoordinateCenter f n p) :=
    schemeAnalyticCoordinateChart_inverse_eval_analyticOnNhd f n p a
      (z + schemeCoordinateCenter f n p) hz
  exact DifferentiableAt.comp (𝕜 := ℂ)
    (f := fun w : Fin n → ℂ => w + schemeCoordinateCenter f n p)
    (g := fun t : Fin n → ℂ => schemeAnalyticCoordinateChartInverseAlgebraPoint f n p t a)
    z ha.differentiableAt
    (differentiableAt_id.add_const (schemeCoordinateCenter f n p))

/-- Every actual regular function gives its actual chosen-coordinate germ;
all ring laws come from the same actual inverse algebra point. -/
def schemeCoordinateRegularGerm :
    SchemeCoordinateAffineRing f n p →+* HolGerm (Fin n → ℂ) where
  toFun a := HolGerm.mk (schemeCoordinateRegularRepresentative f n p a)
    (schemeCoordinateRegularRepresentative_holomorphic f n p a)
  map_one' := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z => map_one
      (schemeAnalyticCoordinateChartInverseAlgebraPoint f n p
        (z + schemeCoordinateCenter f n p))
  map_mul' a b := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z => map_mul
      (schemeAnalyticCoordinateChartInverseAlgebraPoint f n p
        (z + schemeCoordinateCenter f n p)) a b
  map_zero' := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z => map_zero
      (schemeAnalyticCoordinateChartInverseAlgebraPoint f n p
        (z + schemeCoordinateCenter f n p))
  map_add' a b := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z => map_add
      (schemeAnalyticCoordinateChartInverseAlgebraPoint f n p
        (z + schemeCoordinateCenter f n p)) a b

/-- Whole germ evaluation recovers the literal original affine algebra point. -/
theorem schemeCoordinateRegularGerm_eval (a : SchemeCoordinateAffineRing f n p) :
    HolGerm.eval (schemeCoordinateRegularGerm f n p a) =
      standardSmoothComplexAlgebraPoint f n p a := by
  change schemeAnalyticCoordinateChartInverseAlgebraPoint f n p
    (0 + schemeCoordinateCenter f n p) a = _
  rw [zero_add, schemeCoordinateCenter,
    schemeAnalyticCoordinateChartInverseAlgebraPoint_apply f n p p
      (schemeAnalyticCoordinateChart_point_mem_source f n p),
    standardSmoothComplexPointOpenChart_point]

/-- The actual structural scalar is sent to the actual constant germ. -/
theorem schemeCoordinateRegularGerm_scalar (c : ℂ) :
    schemeCoordinateRegularGerm f n p (algebraMap ℂ (SchemeCoordinateAffineRing f n p) c) =
      HolGerm.constHom c := by
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall fun z =>
    (schemeAnalyticCoordinateChartInverseAlgebraPoint f n p
      (z + schemeCoordinateCenter f n p)).commutes c

/-- On the actual source, the representative is the evaluation at the SAME
original scheme point's actual affine lift. -/
theorem schemeCoordinateRegularRepresentative_source
    (a : SchemeCoordinateAffineRing f n p) (q : SchemeComplexPoint f)
    (hq : q ∈ (schemeAnalyticCoordinateChart f n p).source) :
    schemeCoordinateRegularRepresentative f n p a
      (schemeAnalyticCoordinateChart f n p q - schemeCoordinateCenter f n p) =
        standardSmoothComplexPointOpenChart f n p q a := by
  simp only [schemeCoordinateRegularRepresentative, sub_add_cancel]
  rw [schemeAnalyticCoordinateChartInverseAlgebraPoint_apply f n p q hq]

end SGPT.Okounkov
