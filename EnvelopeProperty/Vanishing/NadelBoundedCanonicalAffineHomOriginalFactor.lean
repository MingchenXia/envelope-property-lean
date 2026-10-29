import EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineHomFactor

/-! # The original affine canonical factor, with all field transport internal -/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineHomOriginalFactor
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry Scheme.Modules
open NadelGlobalCanonicalTrace NadelCanonicalMixed.Split
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
local infixr:80 " ≫ₛ " => CategoryStruct.comp (obj := Scheme)

run_cmd
  let source := `EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineHomFactor
  for (short,original) in [
      (`originalNormalizedFactor,
        `EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineHomFactor.exists_actual_affineHom_factor),
      (`originalHomSquare,
        `EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineHomFactor.originalHom_structuralSquare)] do
    let name := Lean.mkPrivateNameCore source original
    unless (← Lean.getEnv).contains name do throwError "missing checked original coefficient factor"
    Lean.Elab.Command.modifyScope fun scope =>
      {scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls}

private theorem originalFactor_of_normalized
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (p : Y ⟶ X)
    (fY : Y ⟶ Spec (.of K)) (h : p ≫ₛ f = fY) (d : ℕ)
    (J : Y.IdealSheafData)
    (hnorm : ∃ θ : (pullback p).obj (exteriorCotangentSheaf (K := K) (X := X) f d) ⟶
        Scheme.Modules.tensorObj (exteriorCotangentSheaf (K := K) (X := Y) fY d) J.toModules,
      θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap
        (exteriorCotangentSheaf (K := K) (X := Y) fY d) J.toModules J.toModulesInclusion =
          exteriorCotangentSheafPullbackMap (K := K) (X := X) (Y := Y) f p d ≫
            eqToHom (congrArg (fun q => exteriorCotangentSheaf (K := K) (X := Y) q d) h)) :
    ∃ θ : (pullback p).obj (exteriorCotangentSheaf (K := K) (X := X) f d) ⟶
        Scheme.Modules.tensorObj (exteriorCotangentSheaf (K := K) (X := Y) (p ≫ₛ f) d) J.toModules,
      θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap
        (exteriorCotangentSheaf (K := K) (X := Y) (p ≫ₛ f) d) J.toModules J.toModulesInclusion =
          exteriorCotangentSheafPullbackMap (K := K) (X := X) (Y := Y) f p d := by
  cases h
  simpa only [eqToHom_refl, Category.comp_id] using hnorm

private theorem exists_actual_affineHom_original_factor
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
    let ΩB := exteriorCotangentSheaf (K := K) (X := Spec B) (p ≫ₛ affineStructuralMap K A) d
    ∃ θ : (pullback p).obj ΩA ⟶ Scheme.Modules.tensorObj (X := Spec B) ΩB J.toModules,
      θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap (X := Spec B) ΩB J.toModules J.toModulesInclusion =
        exteriorCotangentSheafPullbackMap (K := K) (X := Spec A) (Y := Spec B)
          (affineStructuralMap K A) p d := by
  have hn := originalNormalizedFactor (K := K) A B ψ hfield d a ha J r hr hraw
  exact originalFactor_of_normalized (K := K) (X := Spec A) (Y := Spec B)
    (affineStructuralMap K A) (Spec.map ψ) (affineStructuralMap K B)
    (originalHomSquare K A B ψ hfield) d J hn

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineHomOriginalFactor
