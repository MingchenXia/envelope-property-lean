import EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineCoordinateFactor

/-! # Preserve the original bundled coefficient morphism in the affine factor -/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineHomFactor
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

private theorem originalHom_structuralSquare
    (K : Type u) [Field K] (A B : CommRingCat.{u})
    [Algebra K A] [Algebra K B] (ψ : A ⟶ B)
    (hfield : ∀ t : K, ψ.hom (algebraMap K A t) = algebraMap K B t) :
    Spec.map ψ ≫ₛ affineStructuralMap K A = affineStructuralMap K B := by
  change Spec.map ψ ≫ₛ Spec.map (CommRingCat.ofHom (algebraMap K A)) =
    Spec.map (CommRingCat.ofHom (algebraMap K B))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact hfield

private theorem exists_actual_affineHom_factor
    {K : Type u} [Field K] (A B : CommRingCat.{u})
    [Algebra K A] [Algebra K B] (ψ : A ⟶ B)
    (hfield : ∀ t : K, ψ.hom (algebraMap K A t) = algebraMap K B t)
    (d : ℕ) [SmoothOfRelativeDimension d (affineStructuralMap K B)]
    (a : MvPolynomial (Fin d) K →ₐ[K] A) (ha : a.toRingHom.FormallyEtale)
    (J : (Spec B).IdealSheafData) (r : B)
    (hr : (Scheme.ΓSpecIso B).inv r ∈ J.ideal ⟨⊤, isAffineOpen_top (Spec B)⟩)
    (hraw : ∃ w : affineCanonicalModule K B d,
      exteriorPower.ιMulti B d
        (fun j => KaehlerDifferential.D K B (ψ.hom (originalCoordinates a j))) = r • w) :
    let p : Scheme.Hom (Spec B) (Spec A) := Spec.map ψ
    let ΩA := exteriorCotangentSheaf (K := K) (X := Spec A) (affineStructuralMap K A) d
    let ΩB := exteriorCotangentSheaf (K := K) (X := Spec B) (affineStructuralMap K B) d
    ∃ θ : (pullback p).obj ΩA ⟶ Scheme.Modules.tensorObj (X := Spec B) ΩB J.toModules,
      θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap (X := Spec B) ΩB J.toModules J.toModulesInclusion =
        exteriorCotangentSheafPullbackMap (K := K) (X := Spec A) (Y := Spec B)
          (affineStructuralMap K A) p d ≫
            eqToHom (congrArg (fun q => exteriorCotangentSheaf (K := K) (X := Spec B) q d)
              (originalHom_structuralSquare K A B ψ hfield)) := by
  rcases A with ⟨A⟩
  rcases B with ⟨B⟩
  let f : Scheme.Hom (Spec (.of A)) (Spec (.of K)) := affineStructuralMap K (.of A)
  let p : Scheme.Hom (Spec (.of B)) (Spec (.of A)) := Spec.map ψ
  let fB : Scheme.Hom (Spec (.of B)) (Spec (.of K)) := affineStructuralMap K (.of B)
  let h : p ≫ₛ f = fB := originalHom_structuralSquare K (.of A) (.of B) ψ hfield
  let e := baseCanonicalSheafFrame a ha
  let sX : Fin d → Γ(Spec (.of A), ⊤) := fun j =>
    affineCoordinateMap (.of A) (op ⊤) (originalCoordinates a j)
  let sY : Fin d → Γ(Spec (.of B), ⊤) := fun j =>
    affineCoordinateMap (.of B) (op ⊤) (ψ.hom (originalCoordinates a j))
  have hsource := originalFrame_rawCoordinate a ha
  have hcoordinates (j : Fin d) : p.app ⊤ (sX j) = sY j :=
    originalAffineCoordinateImage (.of A) (.of B) ψ (originalCoordinates a j)
  have hbound := ordinaryDivisibility_rawCoordinateBound K B d
    (fun j => ψ.hom (originalCoordinates a j)) r hraw
  exact originalFramedSquareFactor (K := K) (X := Spec (.of A)) (Y := Spec (.of B))
    f p fB h d e (canonicalLineSheaf_isInvertible (k := K) (X := Spec (.of B)) fB d)
    sX sY hsource hcoordinates J ((Scheme.ΓSpecIso (.of B)).inv r) hr hbound

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineHomFactor
