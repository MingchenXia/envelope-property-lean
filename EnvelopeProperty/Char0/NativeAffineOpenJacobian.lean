import EnvelopeProperty.Char0.NativePreferredJacobian
import EnvelopeProperty.ComplexGeometry.Germs.SchemeNativeOpenJacobian

/-! # The SAME original Jacobian under actual source affine-open restriction

The source chart transition is the actual original open immersion, whose
Jacobian is proved a unit. The determinant chain rule retains that unit;
only the WHOLE principal ideals agree after the actual whole-germ pullback.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativeAffineOpenJacobian

open CategoryTheory AlgebraicGeometry ComplexSchemes Filter
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HolomorphicGerms HolomorphicGerms.NativeOpenJacobian NativePreferredJacobian
open HironakaHolomorphicJetChartInvariance HolomorphicGermJacobian
open scoped Topology Manifold ContDiff

variable {R B : Type} [CommRing R] [CommRing B] {Y : Scheme}
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Y ⟶ Spec (.of R))
  (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (n : ℕ)
  [SmoothOfRelativeDimension n (π ≫ f)] [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)]

local instance affineOpenBaseAffine : IsAffineHom f := isAffineHom_of_isAffine f
local instance affineOpenSourceAffine : IsAffineHom ((j ≫ π) ≫ f) := isAffineHom_of_isAffine _

private instance affineOpenSourceSmooth : SmoothOfRelativeDimension n ((j ≫ π) ≫ f) := by
  rw [Category.assoc]
  exact (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp (f := j) (n := 0) (m := n) (π ≫ f))

local instance affineOpenSourceTopology : TopologicalSpace (SchemeComplexPoint ((j ≫ π) ≫ f)) :=
  schemeAnalyticPointTopology _
local instance affineOpenTargetTopology : TopologicalSpace (SchemeComplexPoint (π ≫ f)) :=
  schemeAnalyticPointTopology _
local instance affineOpenSourceCharts : ChartedSpace (ComplexModel n)
    (SchemeComplexPoint ((j ≫ π) ≫ f)) := schemeAnalyticComplexChartedSpace _ n
local instance affineOpenTargetCharts : ChartedSpace (ComplexModel n)
    (SchemeComplexPoint (π ≫ f)) := schemeAnalyticComplexChartedSpace _ n
local instance affineOpenSourceManifold : IsComplexManifold n
    (SchemeComplexPoint ((j ≫ π) ≫ f)) := schemeAnalyticComplex_isComplexManifold _ n
local instance affineOpenTargetManifold : IsComplexManifold n
    (SchemeComplexPoint (π ≫ f)) := schemeAnalyticComplex_isComplexManifold _ n

/-- The literal SAME original open immersion on actual points, with structural associativity proved. -/
def affineOpenPointMap : SchemeComplexPoint ((j ≫ π) ≫ f) → SchemeComplexPoint (π ≫ f) :=
  schemeComplexPointMap ((j ≫ π) ≫ f) (π ≫ f) j (Category.assoc j π f)

omit [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] in
private theorem affineOpenPointMap_holomorphic :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (affineOpenPointMap f π j) :=
  schemeComplexPointMap_contMDiff_of_structure (π ≫ f) ((j ≫ π) ≫ f) j (Category.assoc j π f) n ∞

/-- Actual whole-germ pullback in the SAME original source charts. -/
def affineOpenGermPullback (q : SchemeComplexPoint ((j ≫ π) ≫ f)) :
    HolGerm (ComplexModel n) →ₐ[ℂ] HolGerm (ComplexModel n) :=
  compAlgHom (NativeHolGerm.centeredCoordinateMap (affineOpenPointMap f π j) q)
    (NativeHolGerm.centeredCoordinateMap_holomorphic _ (affineOpenPointMap_holomorphic f π j n) q)
    (NativeHolGerm.centeredCoordinateMap_zero _ q)

/-- The actual source-open centered complex Jacobian, retained as a whole holomorphic germ. -/
def affineOpenJacobian (q : SchemeComplexPoint ((j ≫ π) ≫ f)) : HolGerm (ComplexModel n) :=
  jacobianGerm (NativeHolGerm.centeredCoordinateMap (affineOpenPointMap f π j) q)
    (NativeHolGerm.centeredCoordinateMap_holomorphic _ (affineOpenPointMap_holomorphic f π j n) q)

/-- The original open immersion internally gives the UNIT chart Jacobian. -/
theorem affineOpenJacobian_isUnit (q : SchemeComplexPoint ((j ≫ π) ≫ f)) :
    IsUnit (affineOpenJacobian f π j n q) :=
  schemeOpenImmersion_jacobianGerm_isUnit (π ≫ f) ((j ≫ π) ≫ f) j
    (Category.assoc j π f) n q

variable [SmoothOfRelativeDimension n f]

local instance affineOpenBaseTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance affineOpenBaseCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f n
local instance affineOpenBaseManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticComplex_isComplexManifold f n

/-- The actual determinant chain rule retains the genuine source-chart UNIT factor.
The SAME original global morphism and its literal affine restriction are used. -/
theorem preferredJacobian_affineOpen_chain_rule (q : SchemeComplexPoint ((j ≫ π) ≫ f)) :
    preferredJacobian f (j ≫ π) n q =
      affineOpenGermPullback f π j n q
        (preferredJacobian f π n (affineOpenPointMap f π j q)) *
      affineOpenJacobian f π j n q := by
  let b := affineOpenPointMap f π j
  let c := schemeComplexPointMap (π ≫ f) f π rfl
  have hb := affineOpenPointMap_holomorphic f π j n
  have hc := schemeComplexPointMap_contMDiff f π n n ∞
  have he : schemeComplexPointMap ((j ≫ π) ≫ f) f (j ≫ π) rfl = c ∘ b := by
    funext x
    apply Subtype.ext
    exact (Category.assoc x.val j π).symm
  simpa only [← he, preferredJacobian, schemeMorphismCenteredCoordinateMap,
    affineOpenGermPullback, affineOpenJacobian, b, c] using
    centeredCoordinateMap_jacobianGerm_comp b c hb hc q

/-- The WHOLE restricted default-Jacobian ideal is the pullback of the WHOLE global
SAME-morphism default-Jacobian ideal. Actual chart Jacobians are only asserted equal up to UNIT. -/
theorem span_preferredJacobian_affineOpen (q : SchemeComplexPoint ((j ≫ π) ≫ f)) :
    Ideal.span {preferredJacobian f (j ≫ π) n q} =
      (Ideal.span {preferredJacobian f π n (affineOpenPointMap f π j q)}).map
        (affineOpenGermPullback f π j n q).toRingHom := by
  rw [preferredJacobian_affineOpen_chain_rule, Ideal.map_span, Set.image_singleton]
  exact Ideal.span_singleton_mul_right_unit (affineOpenJacobian_isUnit f π j n q) _

end EnvelopeProperty.Char0.NativeAffineOpenJacobian
