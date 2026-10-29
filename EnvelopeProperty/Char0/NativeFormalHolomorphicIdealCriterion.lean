import EnvelopeProperty.Char0.NativeEtaleCoordinates
import EnvelopeProperty.ComplexGeometry.Germs.SchemeAffineNativeFormal

/-! # Whole original analytic ideal membership reflected by the actual native Taylor map -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry ComplexSchemes HolomorphicGerms
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HironakaActualFormalCoordinatePowerDivision HironakaActualTaylorCoordinateNaturality
  HironakaActualCoefficientPresentationCentrePower
open scoped Topology

noncomputable section

namespace EnvelopeProperty.Char0.NativeFormalHolomorphicIdealCriterion

section Coefficients

variable {B : Type} [CommRing B] (f : Spec (.of B) ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance coefficientTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance coefficientCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f n
local instance coefficientManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticComplex_isComplexManifold f n

/-- EVERY original affine coefficient has precisely the Taylor series of its
SAME actual preferred holomorphic coefficient germ, via its actual original stalk. -/
theorem taylor_coefficientGerm (p : SchemeComplexPoint f) (b : B) :
    actualUnshiftedTaylorAlgHom n (NativeEtaleCoordinates.coefficientGerm f n p b) =
      schemeAffineNativeFormal f n p b := by
  rw [NativeEtaleCoordinates.coefficientGerm_stalk]
  change _ = actualUnshiftedTaylorAlgHom n
    ((NativeHolGerm.chartEquiv p) ((NativeHolGerm.chartEquiv p).symm _))
  rw [RingEquiv.apply_symm_apply]
  rfl

end Coefficients

section Morphism

variable {R B : Type} [CommRing R] [CommRing B]
    (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Spec (.of B) ⟶ Spec (.of R))
    (n m : ℕ) [SmoothOfRelativeDimension n (π ≫ f)] [SmoothOfRelativeDimension m f]
    [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] [IsSeparated f] [QuasiCompact f]

local instance sourceTopology : TopologicalSpace (SchemeComplexPoint (π ≫ f)) :=
  schemeAnalyticPointTopology (π ≫ f)
local instance targetTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance sourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint (π ≫ f)) :=
  schemeAnalyticComplexChartedSpace (π ≫ f) n
local instance targetCharts : ChartedSpace (ComplexModel m) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f m
local instance sourceManifold : IsComplexManifold n (SchemeComplexPoint (π ≫ f)) :=
  schemeAnalyticComplex_isComplexManifold (π ≫ f) n
local instance targetManifold : IsComplexManifold m (SchemeComplexPoint f) :=
  schemeAnalyticComplex_isComplexManifold f m

/-- The literal formal pullback of Taylor(g), times the SAME original j, lies in
the whole original formal ideal exactly when the actual whole analytic product
lies in the whole original analytic ideal. No comparison certificate is an input. -/
theorem formalPullback_taylor_mul_mem_iff (p : SchemeComplexPoint (π ≫ f))
    (I : Ideal B) (j : B)
    (g : NativeHolGerm m (SchemeComplexPoint f)
      (schemeComplexPointMap (π ≫ f) f π rfl p)) :
    schemeMorphismFormalPullback f π n m p
        (NativeHolGerm.taylor (schemeComplexPointMap (π ≫ f) f π rfl p) g) *
      schemeAffineNativeFormal (π ≫ f) n p j ∈ I.map (schemeAffineNativeFormal (π ≫ f) n p) ↔
    NativeHolGerm.chartEquiv p (schemeMorphismNativeGermPullback f π n m p g) *
      NativeEtaleCoordinates.coefficientGerm (π ≫ f) n p j ∈
        I.map (NativeEtaleCoordinates.coefficientGerm (π ≫ f) n p) := by
  let H := HolGerm (ComplexModel n)
  let F := MvPowerSeries (Fin n) ℂ
  let τ : H →+* F := (actualUnshiftedTaylorAlgHom n).toRingHom
  let γ := NativeEtaleCoordinates.coefficientGerm (π ≫ f) n p
  let a : H := NativeHolGerm.chartEquiv p (schemeMorphismNativeGermPullback f π n m p g)
  have hγ : τ.comp γ = schemeAffineNativeFormal (π ≫ f) n p :=
    RingHom.ext (taylor_coefficientGerm (π ≫ f) n p)
  have ha : τ a = schemeMorphismFormalPullback f π n m p
      (NativeHolGerm.taylor (schemeComplexPointMap (π ≫ f) f π rfl p) g) :=
    schemeNativeTaylor_naturality f π n m p g
  have he : a * γ j ∈ I.map γ ↔ τ (a * γ j) ∈ (I.map γ).map τ := by
    let : Algebra H F := τ.toAlgebra
    let : Module.FaithfullyFlat H F := actualUnshiftedTaylor_faithfullyFlat n
    change a * γ j ∈ I.map γ ↔ a * γ j ∈
      (((I.map γ).map (algebraMap H F)).comap (algebraMap H F))
    rw [Ideal.comap_map_eq_self_of_faithfullyFlat]
  rw [Ideal.map_map, hγ, map_mul, ha,
    show τ (γ j) = schemeAffineNativeFormal (π ≫ f) n p j from RingHom.congr_fun hγ j] at he
  exact he.symm

end Morphism

end EnvelopeProperty.Char0.NativeFormalHolomorphicIdealCriterion
