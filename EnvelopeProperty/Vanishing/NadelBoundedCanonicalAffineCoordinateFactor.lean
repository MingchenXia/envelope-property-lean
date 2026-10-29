import EnvelopeProperty.Vanishing.NadelBoundedCanonicalFramedFactorCore
import EnvelopeProperty.Vanishing.NadelBoundedCanonicalOrdinaryDivisibilityCore

/-! # The actual affine canonical factor from original ordinary divisibility -/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineCoordinateFactor
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry Scheme.Modules
open NadelGlobalCanonicalTrace NadelBoundedCanonicalSourceFrame NadelCanonicalMixed.Split
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
local infixr:80 " ≫ₛ " => CategoryStruct.comp (obj := Scheme)

run_cmd
  for (source,short,original) in [
      (`EnvelopeProperty.Vanishing.NadelBoundedCanonicalFramedFactorCore,
        `originalFramedSquareFactor,
        `EnvelopeProperty.Vanishing.NadelBoundedCanonicalFramedFactorCore.originalFramedSquareFactor),
      (`EnvelopeProperty.Vanishing.NadelBoundedCanonicalOrdinaryDivisibilityCore,
        `ordinaryDivisibility_rawCoordinateBound,
        `EnvelopeProperty.Vanishing.NadelBoundedCanonicalOrdinaryDivisibilityCore.ordinaryDivisibility_rawCoordinateBound),
      (`EnvelopeProperty.Vanishing.NadelBoundedCanonicalOrdinaryCoordinateImageCore,
        `originalFrame_rawCoordinate,
        `EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineCoordinateFactor.originalFrame_rawCoordinate),
      (`EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineNaturality,
        `originalAffineCoordinateImage,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeAffineCoordinateImage)] do
    let name := Lean.mkPrivateNameCore source original
    unless (← Lean.getEnv).contains name do throwError "missing checked original canonical computation {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      {scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls}

private theorem exists_actual_affine_factor
    {K : Type u} [Field K] (A B : Type u) [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B) (d : ℕ)
    [SmoothOfRelativeDimension d (affineStructuralMap K (.of B))]
    (a : MvPolynomial (Fin d) K →ₐ[K] A) (ha : a.toRingHom.FormallyEtale)
    (J : (Spec (.of B)).IdealSheafData) (r : B)
    (hr : (Scheme.ΓSpecIso (.of B)).inv r ∈ J.ideal ⟨⊤, isAffineOpen_top (Spec (.of B))⟩)
    (hraw : ∃ w : affineCanonicalModule K B d,
      exteriorPower.ιMulti B d
        (fun j => KaehlerDifferential.D K B (φ (originalCoordinates a j))) = r • w) :
    let p : Scheme.Hom (Spec (.of B)) (Spec (.of A)) := Spec.map (CommRingCat.ofHom φ.toRingHom)
    let ΩA := exteriorCotangentSheaf (K := K) (X := Spec (.of A)) (affineStructuralMap K (.of A)) d
    let ΩB := exteriorCotangentSheaf (K := K) (X := Spec (.of B)) (affineStructuralMap K (.of B)) d
    ∃ θ : (pullback p).obj ΩA ⟶ Scheme.Modules.tensorObj (X := Spec (.of B)) ΩB J.toModules,
      θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap (X := Spec (.of B)) ΩB J.toModules J.toModulesInclusion =
        exteriorCotangentSheafPullbackMap (K := K) (X := Spec (.of A)) (Y := Spec (.of B)) (affineStructuralMap K (.of A)) p d ≫
          eqToHom (congrArg (fun q => exteriorCotangentSheaf (K := K) (X := Spec (.of B)) q d)
            (affineAlgebraMap_structuralSquare K (.of A) (.of B) φ)) := by
  let f : Scheme.Hom (Spec (.of A)) (Spec (.of K)) := affineStructuralMap K (.of A)
  let p : Scheme.Hom (Spec (.of B)) (Spec (.of A)) := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let fB : Scheme.Hom (Spec (.of B)) (Spec (.of K)) := affineStructuralMap K (.of B)
  let h : p ≫ₛ f = fB := affineAlgebraMap_structuralSquare K (.of A) (.of B) φ
  let e := baseCanonicalSheafFrame a ha
  let sX : Fin d → Γ(Spec (.of A), ⊤) := fun j =>
    affineCoordinateMap (.of A) (op ⊤) (originalCoordinates a j)
  let sY : Fin d → Γ(Spec (.of B), ⊤) := fun j =>
    affineCoordinateMap (.of B) (op ⊤) (φ (originalCoordinates a j))
  have hsource := originalFrame_rawCoordinate a ha
  have hcoordinates (j : Fin d) : p.app ⊤ (sX j) = sY j :=
    originalAffineCoordinateImage (.of A) (.of B) (CommRingCat.ofHom φ.toRingHom) (originalCoordinates a j)
  have hbound := ordinaryDivisibility_rawCoordinateBound K B d
    (fun j => φ (originalCoordinates a j)) r hraw
  exact originalFramedSquareFactor (K := K) (X := Spec (.of A)) (Y := Spec (.of B))
    f p fB h d e (canonicalLineSheaf_isInvertible (k := K) (X := Spec (.of B)) fB d)
    sX sY hsource hcoordinates J ((Scheme.ΓSpecIso (.of B)).inv r) hr hbound

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineCoordinateFactor
