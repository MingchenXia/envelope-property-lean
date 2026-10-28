import EnvelopeProperty.Char0.NativeSchemeJacobianGenerator
import SGPT.Okounkov.SchemeNativeMorphismCoordinates
import SGPT.Okounkov.SchemeCoordinateGlobalGerm

/-! # Whole original coefficients in the actual default coordinate composition -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativeCoefficientComposition

open CategoryTheory AlgebraicGeometry BingWangEntropy Filter
open TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open SGPT.Okounkov NativeSchemeJacobian NativeSchemeJacobianGenerator
open scoped Topology Manifold ContDiff

/-- The exact original affine coefficient is read through the canonical global-sections isomorphism. -/
theorem affineMap_coefficient {A B : CommRingCat} (a : Spec A ⟶ Spec B) (r : B) :
    (Spec.preimage a).hom r = (Scheme.ΓSpecIso A).hom
      (a.appTop ((Scheme.ΓSpecIso B).inv r)) := by
  have hn := Scheme.ΓSpecIso_naturality (Spec.preimage a)
  rw [Spec.map_preimage] at hn
  have he := congrArg (fun ψ => ψ ((Scheme.ΓSpecIso B).inv r)) hn
  simpa only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] using he.symm

section Target
variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ Spec (.of ℂ)) (m : ℕ)
  [SmoothOfRelativeDimension m f] (q : SchemeComplexPoint f)
local instance targetCoefficientAffineAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f m q) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f m q).val.map ≫ f)

/-- The literal original target coefficient map into its actual preferred affine chart. -/
def targetAlgebraMap :
    letI := affinePointFieldAlgebra f
    R →ₐ[ℂ] SchemeCoordinateAffineRing f m q :=
  affineSchemeOverAlgebraMap f
    ((standardSmoothComplexAffineChart f m q).val.map ≫ f)
    (standardSmoothComplexAffineChart f m q).val.map rfl

/-- Original target coefficients are exactly the coefficients of their canonical original global sections. -/
theorem targetAlgebraMap_eq_globalCoefficient (r : R) :
    targetAlgebraMap f m q r =
      schemeCoordinateGlobalCoefficient f m q ((Scheme.ΓSpecIso (.of R)).inv r) := by
  exact affineMap_coefficient (standardSmoothComplexAffineChart f m q).val.map r
end Target

section Global
variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
  (p : SchemeComplexPoint f)
local instance globalCoefficientPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance globalCoefficientPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance globalCoefficientPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
local instance globalCoefficientAffineAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- Every original global section retains its ENTIRE actual preferred-chart germ. -/
theorem modelGlobalGerm (r : Γ(X, ⊤)) :
    NativeHolGerm.chartEquiv p (schemeNativeStalkGerm f n p
      (X.presheaf.germ ⊤ (schemeComplexPointImage f p) trivial r)) =
        schemeCoordinateModelRegularAlgHom f n p (schemeCoordinateGlobalCoefficient f n p r) := by
  rw [← schemeCoordinateStalkEquiv_global f n p r,
    schemeNativeStalkGerm_regular, schemeNativeRegularGerm_chart]
  rfl
end Global

section Naturality
variable {X Y : Scheme} (f : Y ⟶ Spec (.of ℂ)) (h : X ⟶ Y)
  (n m : ℕ) [SmoothOfRelativeDimension n (h ≫ f)] [SmoothOfRelativeDimension m f]
  [IsSeparated (h ≫ f)] [QuasiCompact (h ≫ f)] [IsSeparated f] [QuasiCompact f]

local instance globalNaturalitySourceTopology : TopologicalSpace (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticPointTopology (h ≫ f)
local instance globalNaturalityTargetTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance globalNaturalitySourceCharts :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticTNChartedSpace (h ≫ f) n
local instance globalNaturalityTargetCharts : ChartedSpace (ComplexModel m) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f m
local instance globalNaturalitySourceManifold : IsComplexManifold n (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticTN_isComplexManifold (h ≫ f) n
local instance globalNaturalityTargetManifold : IsComplexManifold m (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f m


variable (p : SchemeComplexPoint (h ≫ f))
local instance globalNaturalitySourceAffineAlgebra : Algebra ℂ (SchemeCoordinateAffineRing (h ≫ f) n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart (h ≫ f) n p).val.map ≫ (h ≫ f))
local instance globalNaturalityTargetAffineAlgebra :
    Algebra ℂ (SchemeCoordinateAffineRing f m (schemeComplexPointMap (h ≫ f) f h rfl p)) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f m
    (schemeComplexPointMap (h ≫ f) f h rfl p)).val.map ≫ f)

/-- Every original global section has the actual whole default-coordinate composition readback. -/
theorem modelGlobalGerm_naturality (r : Γ(Y, ⊤)) :
    schemeCoordinateModelRegularAlgHom (h ≫ f) n p
      (schemeCoordinateGlobalCoefficient (h ≫ f) n p (h.appTop r)) =
      HironakaHolomorphicJetChartInvariance.compAlgHom
        (schemeMorphismCenteredCoordinateMap f h n m p)
        (schemeMorphismCenteredCoordinateMap_holomorphic f h n m p)
        (schemeMorphismCenteredCoordinateMap_zero f h n m p)
        (schemeCoordinateModelRegularAlgHom f m (schemeComplexPointMap (h ≫ f) f h rfl p)
          (schemeCoordinateGlobalCoefficient f m (schemeComplexPointMap (h ≫ f) f h rfl p) r)) := by
  rw [← modelGlobalGerm (h ≫ f) n p (h.appTop r),
    ← modelGlobalGerm f m (schemeComplexPointMap (h ≫ f) f h rfl p) r]
  have hs := schemeNativeStalkGerm_naturality_chart f h n m p
    (Y.presheaf.germ ⊤ (schemeComplexPointImage f (schemeComplexPointMap (h ≫ f) f h rfl p)) trivial r)
  erw [h.germ_stalkMap_apply] at hs
  simpa using hs

end Naturality

variable {R : Type} [CommRing R] {Y : Scheme}
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Y ⟶ Spec (.of R)) (n : ℕ)
  [SmoothOfRelativeDimension n (π ≫ f)] (p : SchemeComplexPoint (π ≫ f))
local instance sourceCoefficientAffineAlgebra :
    Algebra ℂ (SchemeCoordinateAffineRing (π ≫ f) n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart (π ≫ f) n p).val.map ≫ (π ≫ f))

/-- The literal original coefficient map is exactly the actual coefficient of original global pullback. -/
theorem sourceAlgebraMap_eq_globalCoefficient (r : R) :
    sourceAlgebraMap f π n p r =
      schemeCoordinateGlobalCoefficient (π ≫ f) n p
        (π.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) := by
  let c := (standardSmoothComplexAffineChart (π ≫ f) n p).val.map
  change (Spec.preimage (c ≫ π)).hom r =
    (Scheme.ΓSpecIso _).hom (c.appTop (π.appTop ((Scheme.ΓSpecIso (.of R)).inv r)))
  rw [affineMap_coefficient, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

variable (m : ℕ) [SmoothOfRelativeDimension m f]
  [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] [IsSeparated f] [QuasiCompact f]
local instance coefficientCompositionTargetAffineAlgebra :
    Algebra ℂ (SchemeCoordinateAffineRing f m (schemeComplexPointMap (π ≫ f) f π rfl p)) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f m
    (schemeComplexPointMap (π ≫ f) f π rfl p)).val.map ≫ f)

/-- EVERY original affine target function has its exact WHOLE default-coordinate composition identity. -/
theorem originalCoefficient_comp (r : R) :
    schemeCoordinateModelRegularAlgHom (π ≫ f) n p (sourceAlgebraMap f π n p r) =
      HironakaHolomorphicJetChartInvariance.compAlgHom
        (schemeMorphismCenteredCoordinateMap f π n m p)
        (schemeMorphismCenteredCoordinateMap_holomorphic f π n m p)
        (schemeMorphismCenteredCoordinateMap_zero f π n m p)
        (schemeCoordinateModelRegularAlgHom f m (schemeComplexPointMap (π ≫ f) f π rfl p)
          (targetAlgebraMap f m (schemeComplexPointMap (π ≫ f) f π rfl p) r)) := by
  rw [sourceAlgebraMap_eq_globalCoefficient, targetAlgebraMap_eq_globalCoefficient]
  exact modelGlobalGerm_naturality f π n m p ((Scheme.ΓSpecIso (.of R)).inv r)

end EnvelopeProperty.Char0.NativeCoefficientComposition
