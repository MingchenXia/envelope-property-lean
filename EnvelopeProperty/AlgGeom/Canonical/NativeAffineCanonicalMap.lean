import EnvelopeProperty.AlgGeom.Canonical.OpenImmersionSheafUnits
import EnvelopeProperty.AlgGeom.Canonical.AffineCanonicalSheafImage

/-! # Entire canonical differential on the SAME original affine schemes -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

namespace EnvelopeProperty.CanonicalGeometry

universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : X ⟶ Spec (.of K)) (g : Y ⟶ X)

/-- The ENTIRE original native affine differential, between BOTH SAME
actual units, is precisely the ENTIRE actual raw scalar-extension map. -/
theorem nativeAffineCanonicalDifferential_unit (n : ℕ) [SmoothOfRelativeDimension n f] :
    letI : (exteriorCotangentSheaf f n).IsQuasicoherent :=
      (canonicalLineSheaf_isInvertible f n).isQuasicoherent
    (ModuleCat.extendScalars g.appTop.hom).map
        ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤)) ≫
      (Scheme.Modules.affinePullbackΓIso g (exteriorCotangentSheaf f n)).hom ≫
      (exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤) =
    exteriorCotangentRawBaseChangeMorphism f g n ≫
      (exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op ⊤) := by
  let : (exteriorCotangentSheaf f n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(X, ⊤) Γ(Y, g ⁻¹ᵁ ⊤) := (g.app ⊤).hom.toAlgebra
  apply ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).homEquiv _ _).injective
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro z
  change (exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤)
      ((Scheme.Modules.affinePullbackΓIso g (exteriorCotangentSheaf f n)).hom
        ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, ⊤)]
          (exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z)) =
    (exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op ⊤)
      (exteriorCotangentMorphismBaseChange f g ⊤ n ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, ⊤)] z))
  refine (exteriorCotangentSheafPullbackMap_affine_one_tmul f g n z).trans ?_
  apply congrArg ((exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op ⊤))
  change exteriorCotangentMorphismComponent f g n (.op ⊤) z =
    exteriorCotangentMorphismBaseChange f g ⊤ n ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, ⊤)] z)
  rw [exteriorCotangentMorphismBaseChange, LinearMap.liftBaseChange_one_tmul]
  rfl

private def nativeAffineCanonicalUnitIso {I : Type v} [LinearOrder I]
    (b : letI := affineChartAlgebra f ⊤
      Module.Basis I Γ(X, ⊤) (KaehlerDifferential K Γ(X, ⊤))) (n : ℕ) :
    (exteriorCotangentPresheaf f n).obj (.op ⊤) ≅
      (exteriorCotangentSheaf f n).val.obj (.op ⊤) :=
  (LinearEquiv.ofBijective
    ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤)).hom
    (affineChartExteriorSheafificationMap_bijective f (isAffineOpen_top X) b n)).toModuleIso

/-- The actual whole original sheaf map expressed with the actual original
raw units and genuine native pullback on the SAME arbitrary affine schemes. -/
def nativeAffineCanonicalDifferential (n : ℕ) [SmoothOfRelativeDimension n f]
    {I : Type v} {J : Type w} [LinearOrder I] [LinearOrder J]
    (bX : letI := affineChartAlgebra f ⊤
      Module.Basis I Γ(X, ⊤) (KaehlerDifferential K Γ(X, ⊤)))
    (bY : letI := affineChartAlgebra (g ≫ f) ⊤
      Module.Basis J Γ(Y, ⊤) (KaehlerDifferential K Γ(Y, ⊤))) :=
  letI : (exteriorCotangentSheaf f n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  ((ModuleCat.extendScalars g.appTop.hom).map (nativeAffineCanonicalUnitIso f bX n).hom ≫
    (Scheme.Modules.affinePullbackΓIso g (exteriorCotangentSheaf f n)).hom ≫
    (exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤)) ≫
      (nativeAffineCanonicalUnitIso (g ≫ f) bY n).inv

set_option backward.isDefEq.respectTransparency true in
/-- Equality of ENTIRE original actual sheaf and raw differential maps on
arbitrary original affine schemes, retaining the SAME original ring map. -/
theorem nativeAffineCanonicalDifferential_eq_rawBaseChange
    (n : ℕ) [SmoothOfRelativeDimension n f]
    {I : Type v} {J : Type w} [LinearOrder I] [LinearOrder J]
    (bX : letI := affineChartAlgebra f ⊤
      Module.Basis I Γ(X, ⊤) (KaehlerDifferential K Γ(X, ⊤)))
    (bY : letI := affineChartAlgebra (g ≫ f) ⊤
      Module.Basis J Γ(Y, ⊤) (KaehlerDifferential K Γ(Y, ⊤))) :
    nativeAffineCanonicalDifferential f g n bX bY = exteriorCotangentRawBaseChangeMorphism f g n := by
  unfold nativeAffineCanonicalDifferential
  apply (nativeAffineCanonicalUnitIso (g ≫ f) bY n).comp_inv_eq.mpr
  exact nativeAffineCanonicalDifferential_unit f g n

/-- The full original actual sheaf-derived range equals the SAME intrinsic
image of the differentials of ALL original source functions. -/
theorem range_nativeAffineCanonicalDifferential
    (n : ℕ) [SmoothOfRelativeDimension n f]
    {I : Type v} {J : Type w} [LinearOrder I] [LinearOrder J]
    (bX : letI := affineChartAlgebra f ⊤
      Module.Basis I Γ(X, ⊤) (KaehlerDifferential K Γ(X, ⊤)))
    (bY : letI := affineChartAlgebra (g ≫ f) ⊤
      Module.Basis J Γ(Y, ⊤) (KaehlerDifferential K Γ(Y, ⊤))) :
    LinearMap.range (nativeAffineCanonicalDifferential f g n bX bY).hom =
      exteriorCotangentRawImage f g n := by
  rw [nativeAffineCanonicalDifferential_eq_rawBaseChange]
  exact range_exteriorCotangentRawBaseChangeMorphism f g n

/-- The actual original standard-smooth WHOLE affine coordinate rings
internally derive BOTH differential bases for the SAME actual sheaf map. -/
def standardSmoothNativeAffineCanonicalDifferential (n : ℕ) [SmoothOfRelativeDimension n f]
    (hX : RingHom.IsStandardSmoothOfRelativeDimension n
      ((schemeConstantPresheafMap f).app (.op ⊤)).hom)
    (hY : RingHom.IsStandardSmoothOfRelativeDimension n
      ((schemeConstantPresheafMap (g ≫ f)).app (.op ⊤)).hom) :=
  letI := affineChartAlgebra f ⊤
  letI := affineChartAlgebra (g ≫ f) ⊤
  letI : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, ⊤) := hX
  letI : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(Y, ⊤) := hY
  nativeAffineCanonicalDifferential f g n
    (standardSmoothDifferentialBasis K Γ(X, ⊤) n)
    (standardSmoothDifferentialBasis K Γ(Y, ⊤) n)

/-- The ORIGINAL standard-smooth affine chart map has the entire intrinsic
all-original-source-functions image, with BOTH bases internally derived. -/
theorem range_standardSmoothNativeAffineCanonicalDifferential
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (hX : RingHom.IsStandardSmoothOfRelativeDimension n
      ((schemeConstantPresheafMap f).app (.op ⊤)).hom)
    (hY : RingHom.IsStandardSmoothOfRelativeDimension n
      ((schemeConstantPresheafMap (g ≫ f)).app (.op ⊤)).hom) :
    LinearMap.range (standardSmoothNativeAffineCanonicalDifferential f g n hX hY).hom =
      exteriorCotangentRawImage f g n := by
  let := affineChartAlgebra f ⊤
  let := affineChartAlgebra (g ≫ f) ⊤
  let : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, ⊤) := hX
  let : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(Y, ⊤) := hY
  exact range_nativeAffineCanonicalDifferential f g n
    (standardSmoothDifferentialBasis K Γ(X, ⊤) n)
    (standardSmoothDifferentialBasis K Γ(Y, ⊤) n)

end
end EnvelopeProperty.CanonicalGeometry
