import EnvelopeProperty.Char0.NativeBPMultiplierGermTransform
import EnvelopeProperty.Char0.NativeSNCGeometryApplication
import EnvelopeProperty.Char0.NativeCoefficientComposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EnvelopeProperty.Char0.NativeSNCOriginalGenerators
open CategoryTheory AlgebraicGeometry BingWangEntropy Filter
open TranscendentalNakamaye TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open SGPT.Okounkov NativeSchemeJacobian NativeCoefficientComposition NativeEtaleCoordinates
open TranscendentalNakamaye.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

variable {R : Type} [CommRing R] {Y : Scheme}
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Y ⟶ Spec (.of R)) (n : ℕ)
  [SmoothOfRelativeDimension n (π ≫ f)] [SmoothOfRelativeDimension n f]
  [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] [IsSeparated f] [QuasiCompact f]
local instance sourceTopology : TopologicalSpace (SchemeComplexPoint (π ≫ f)) := schemeAnalyticPointTopology _
local instance targetTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology _
local instance sourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint (π ≫ f)) := schemeAnalyticTNChartedSpace _ n
local instance targetCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace _ n
local instance sourceManifold : IsComplexManifold n (SchemeComplexPoint (π ≫ f)) := schemeAnalyticTN_isComplexManifold _ n
local instance targetManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold _ n
local instance sourceAffineAlgebra (p : SchemeComplexPoint (π ≫ f)) :
    Algebra ℂ (SchemeCoordinateAffineRing (π ≫ f) n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart (π ≫ f) n p).val.map ≫ (π ≫ f))

/-- Literal original coefficient pulled through the actual original morphism and default chart. -/
def centeredOriginalFunction (p : SchemeComplexPoint (π ≫ f)) (r : R) : ComplexModel n → ℂ :=
  fun z => NativeAffineIdealWeight.originalFunction f r
    (schemeComplexPointMap (π ≫ f) f π rfl
      ((complexChartAt (n := n) p).val.symm (z + (complexChartAt (n := n) p).val p)))

private theorem originalFunction_pullback_germ (p : SchemeComplexPoint (π ≫ f)) (r : R) :
    schemeMorphismNativeGermPullback f π n n p
      (NativeAffineIdealWeight.nativeMap f n (schemeComplexPointMap (π ≫ f) f π rfl p) r) =
    schemeNativeStalkGerm (π ≫ f) n p
      (Y.presheaf.germ ⊤ (schemeComplexPointImage (π ≫ f) p) trivial
        (π.appTop ((Scheme.ΓSpecIso (.of R)).inv r))) := by
  simp only [NativeAffineIdealWeight.nativeMap, RingHom.comp_apply]
  rw [← schemeNativeStalkGerm_naturality f π n n p]
  erw [π.germ_stalkMap_apply]
  rfl

private theorem centeredOriginalFunction_coe (p : SchemeComplexPoint (π ≫ f)) (r : R) :
    ((schemeCoordinateModelRegularAlgHom (π ≫ f) n p (sourceAlgebraMap f π n p r) :
      HolGerm (ComplexModel n)) : Germ (𝓝 (0 : ComplexModel n)) ℂ) =
      centeredOriginalFunction f π n p r := by
  rw [sourceAlgebraMap_eq_globalCoefficient, ← modelGlobalGerm,
    ← originalFunction_pullback_germ f π n p r, NativeAffineIdealWeight.nativeMap_apply]
  rfl

private theorem holomorphic_of_coe_eq {m : ℕ} (g : HolGerm (ComplexModel m))
    (F : ComplexModel m → ℂ) (he : (g : Germ (𝓝 (0 : ComplexModel m)) ℂ) = F) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ F z := by
  obtain ⟨G, hG, hGe⟩ := g.property
  have heq : G =ᶠ[𝓝 (0 : ComplexModel m)] F := Germ.coe_eq.mp (hGe.trans he)
  filter_upwards [hG, eventually_eventually_nhds.mpr heq] with z hz hzeq
  exact (Filter.EventuallyEq.differentiableAt_iff (show G =ᶠ[𝓝 z] F from hzeq)).mp hz

/-- The actual original coefficient in the actual original centered source chart is holomorphic. -/
theorem centeredOriginalFunction_holomorphic (p : SchemeComplexPoint (π ≫ f)) (r : R) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (centeredOriginalFunction f π n p r) z :=
  holomorphic_of_coe_eq _ _ (centeredOriginalFunction_coe f π n p r)

/-- ENTIRE literal source-function germ equals the original source coefficient germ. -/
theorem centeredOriginalFunction_germ (p : SchemeComplexPoint (π ≫ f)) (r : R) :
    HolGerm.mk (centeredOriginalFunction f π n p r)
      (centeredOriginalFunction_holomorphic f π n p r) =
      schemeCoordinateModelRegularAlgHom (π ≫ f) n p (sourceAlgebraMap f π n p r) := by
  apply Subtype.ext
  exact (centeredOriginalFunction_coe f π n p r).symm

/-- The WHOLE actual original pulled ideal is the span of its original tuple after any real coefficient map. -/
theorem map_pullback_ideal_eq_span {H : Type*} [CommRing H]
    (I : Ideal R) {s : ℕ} (a : Fin s → R) (ha : Ideal.span (Set.range a) = I)
    (U : Y.affineOpens) (γ : Γ(Y, U.1) →+* H) :
    (((specIdealSheaf I).comap π).ideal U).map γ =
      Ideal.span (Set.range fun i => γ (sectionsHom π U.1 (a i))) := by
  rw [ideal_comap_specIdealSheaf, ← ha, Ideal.map_map, Ideal.map_span, ← Set.range_comp']
  rfl

section AffineSource
variable {B : Type} [CommRing B]
  (g : Spec (.of B) ⟶ Spec (.of R)) [SmoothOfRelativeDimension n (g ≫ f)]

/-- The actual original restricted affine coefficient is the WHOLE literal source-function germ. -/
theorem centeredOriginalFunction_germ_affine (q : SchemeComplexPoint (g ≫ f)) (r : R) :
    HolGerm.mk (centeredOriginalFunction f g n q r)
      (centeredOriginalFunction_holomorphic f g n q r) =
        coefficientGerm (g ≫ f) n q ((Spec.preimage g).hom r) := by
  rw [centeredOriginalFunction_germ]
  change schemeCoordinateModelRegularAlgHom (g ≫ f) n q (sourceAlgebraMap f g n q r) =
    schemeCoordinateModelRegularAlgHom (g ≫ f) n q
      (targetAlgebraMap (g ≫ f) n q ((Spec.preimage g).hom r))
  congr 1
  change (Spec.preimage ((standardSmoothComplexAffineChart (g ≫ f) n q).val.map ≫ g)).hom r =
    (Spec.preimage (standardSmoothComplexAffineChart (g ≫ f) n q).val.map).hom
      ((Spec.preimage g).hom r)
  rw [Spec.preimage_comp]
  rfl
end AffineSource

omit [SmoothOfRelativeDimension n f] [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)]
  [IsSeparated f] [QuasiCompact f] in
private theorem restrictedSmooth (U : Y.affineOpens) :
    SmoothOfRelativeDimension n ((U.2.fromSpec ≫ π) ≫ f) := by
  rw [Category.assoc]
  exact (Nat.zero_add n) ▸
    (smoothOfRelativeDimension_comp (f := U.2.fromSpec) (n := 0) (m := n) (π ≫ f))

omit [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] in
/-- On EVERY original affine source open, the WHOLE original pulled ideal is exactly the
span of the actual original tuple pulled by the SAME restricted original morphism. -/
theorem map_pullback_ideal_eq_centered_span
    (I : Ideal R) {s : ℕ} (a : Fin s → R) (ha : Ideal.span (Set.range a) = I)
    (U : Y.affineOpens) (q : SchemeComplexPoint ((U.2.fromSpec ≫ π) ≫ f)) :
    letI := restrictedSmooth f π n U
    (((specIdealSheaf I).comap π).ideal U).map
      (coefficientGerm ((U.2.fromSpec ≫ π) ≫ f) n q) =
        Ideal.span (Set.range fun i => HolGerm.mk
          (centeredOriginalFunction f (U.2.fromSpec ≫ π) n q (a i))
          (centeredOriginalFunction_holomorphic f (U.2.fromSpec ≫ π) n q (a i))) := by
  let := restrictedSmooth f π n U
  rw [map_pullback_ideal_eq_span π I a ha U]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  rw [centeredOriginalFunction_germ_affine]
  congr 1
  have he : (Spec.preimage (U.2.fromSpec ≫ π)).hom = sectionsHom π U.1 := by
    rw [fromSpec_comp_eq_specMap_sectionsHom, Spec.preimage_map]
    rfl
  exact congrArg (fun h : R →+* Γ(Y, U.1) => h (a i)) he.symm

end EnvelopeProperty.Char0.NativeSNCOriginalGenerators
