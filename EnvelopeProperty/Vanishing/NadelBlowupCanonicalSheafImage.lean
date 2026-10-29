import EnvelopeProperty.AlgGeom.Canonical.AffineCanonicalIdealImage
import EnvelopeProperty.AlgGeom.IntegralLineImageModules

/-! # Actual full canonical-image ideal for the native whole sheaf morphism -/

open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalSheafImage
open CanonicalGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)]

/-- The actual WHOLE native canonical differential has exactly the genuine
original all-source-functions Jacobian ideal as its actual affine ideal image.
No image, factorization or canonical-line comparison is supplied. -/
theorem framedImage_ideal_top
    (bX : letI := affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(X, ⊤) (KaehlerDifferential k Γ(X, ⊤)))
    (bY : letI := affineChartAlgebra (g ≫ f) ⊤
      Module.Basis (Fin n) Γ(Y, ⊤) (KaehlerDifferential k Γ(Y, ⊤))) :
    letI := affineChartAlgebra (g ≫ f) ⊤
    letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
    letI : ((pullback g).obj (canonicalLineSheaf f n)).IsQuasicoherent :=
      ((canonicalLineSheaf_isInvertible f n).pullback g).isQuasicoherent
    letI : ((pullback g).obj (exteriorCotangentSheaf f n)).IsQuasicoherent :=
      ((canonicalLineSheaf_isInvertible f n).pullback g).isQuasicoherent
    (QuasicoherentImageIdeal.imageIdeal _
      (exteriorCotangentSheafPullbackMap f g n ≫ (affineCanonicalFrameIso (g ≫ f) n bY).hom)).ideal
        ⟨⊤, isAffineOpen_top Y⟩ = Char0.affineRelativeJacobianIdeal (R := Γ(X, ⊤)) bY := by
  let := affineChartAlgebra f ⊤
  let := affineChartAlgebra (g ≫ f) ⊤
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let M := (pullback g).obj (canonicalLineSheaf f n)
  let : (canonicalLineSheaf f n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  let : M.IsQuasicoherent := ((canonicalLineSheaf_isInvertible f n).pullback g).isQuasicoherent
  let : ((pullback g).obj (exteriorCotangentSheaf f n)).IsQuasicoherent :=
    ((canonicalLineSheaf_isInvertible f n).pullback g).isQuasicoherent
  let α : M ⟶ unitObj Y :=
    exteriorCotangentSheafPullbackMap f g n ≫ (affineCanonicalFrameIso (g ≫ f) n bY).hom
  let uX := (exteriorSheafificationMap (cotangentPresheaf f) n).app (op ⊤)
  let eX := (LinearEquiv.ofBijective uX.hom
    (affineChartExteriorSheafificationMap_bijective f (isAffineOpen_top X) bX n)).toModuleIso
  let e := (ModuleCat.extendScalars g.appTop.hom).mapIso eX ≪≫
    affinePullbackΓIso g (canonicalLineSheaf f n)
  have he : Function.Surjective e.hom := (ConcreteCategory.bijective_of_isIso e.hom).2
  let c := (affineCanonicalTrivialization bY).toLinearMap.comp
    (exteriorCotangentRawBaseChangeMorphism f g n).hom
  let a : Γ(M, ⊤) →ₗ[Γ(Y, ⊤)] Γ(Y, ⊤) := (α.val.app (op ⊤)).hom
  have hc : a.comp e.hom.hom = c := by
    apply LinearMap.ext
    intro z
    have hunit := ConcreteCategory.congr_hom (nativeAffineCanonicalDifferential_unit f g n) z
    change (exteriorCotangentSheafPullbackMap f g n).app ⊤ (e.hom z) =
      (exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (op ⊤)
        (exteriorCotangentRawBaseChangeMorphism f g n z) at hunit
    exact (congrArg ((affineCanonicalFrameIso (g ≫ f) n bY).hom.app ⊤) hunit).trans
      (affineCanonicalFrameIso_hom_unit (g ≫ f) n bY _)
  have hr : LinearMap.range c =
      (Char0.affineRelativeJacobianIdeal (R := Γ(X, ⊤)) bY : Submodule Γ(Y, ⊤) Γ(Y, ⊤)) := by
    rw [LinearMap.range_comp, range_exteriorCotangentRawBaseChangeMorphism]
    change (Char0.affineCanonicalDifferentialImage (k := k) (R := Γ(X, ⊤)) (A := Γ(Y, ⊤)) n).map
      (affineCanonicalTrivialization bY).toLinearMap = _
    rw [affineCanonicalTrivialization_eq_differentialVolumeEquiv]
    exact Char0.map_affineCanonicalDifferentialImage bY
  change LinearMap.range a = _
  calc
    _ = LinearMap.range (a.comp e.hom.hom) := by
      rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr he, Submodule.map_top]
    _ = _ := by rw [hc]; exact hr

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalSheafImage
