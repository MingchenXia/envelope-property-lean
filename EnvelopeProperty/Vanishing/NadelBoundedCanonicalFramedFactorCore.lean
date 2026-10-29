import EnvelopeProperty.Vanishing.NadelBoundedCanonicalFramedSquareCore
import EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineFactor

/-! # Factor the original framed canonical square before affine specialization -/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalFramedFactorCore
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry Scheme.Modules
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

run_cmd
  for (source, short, original) in [
      (`EnvelopeProperty.Vanishing.NadelBoundedCanonicalFramedSquareCore,
        `originalFramedSquareCoordinateImage,
        `EnvelopeProperty.Vanishing.NadelBoundedCanonicalFramedSquareCore.originalFramedSquareCoordinateImage),
      (`EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore,
        `originalRawWedge,
        `EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore.rawWedge)] do
    let name := Lean.mkPrivateNameCore source original
    unless (← Lean.getEnv).contains name do throwError "missing checked original framed square {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      {scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls}

private theorem originalFramedSquareFactor
    {K : Type u} [Field K] {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ X)
    (fY : Y ⟶ Spec (.of K)) (h : g ≫ f = fY) (n : ℕ)
    (e : exteriorCotangentSheaf (K := K) (X := X) f n ≅ unitObj X)
    (hB : IsInvertible (exteriorCotangentSheaf (K := K) (X := Y) fY n))
    (zX : Fin n → Γ(X, ⊤)) (zY : Fin n → Γ(Y, ⊤))
    (hsource : e.inv.app ⊤ (1 : Γ(X, ⊤)) = originalRawWedge (K := K) (X := X) f n zX)
    (hcoordinates : ∀ j, g.app ⊤ (zX j) = zY j)
    (J : Y.IdealSheafData) (r : Γ(Y, ⊤))
    (hr : r ∈ J.ideal ⟨⊤, isAffineOpen_top Y⟩)
    (hraw : ∃ w : Γ(exteriorCotangentSheaf (K := K) (X := Y) fY n, ⊤),
      originalRawWedge (K := K) (X := Y) fY n zY = r • w) :
    ∃ θ : (pullback g).obj (exteriorCotangentSheaf (K := K) (X := X) f n) ⟶
        Scheme.Modules.tensorObj (exteriorCotangentSheaf (K := K) (X := Y) fY n) J.toModules,
      θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap
        (exteriorCotangentSheaf (K := K) (X := Y) fY n) J.toModules J.toModulesInclusion =
        exteriorCotangentSheafPullbackMap (K := K) (X := X) (Y := Y) f g n ≫
          eqToHom (congrArg (fun q => exteriorCotangentSheaf (K := K) (X := Y) q n) h) := by
  cases h
  let E := (pullback g).mapIso e ≪≫ pullbackUnitIso g
  let δ := exteriorCotangentSheafPullbackMap (K := K) (X := X) (Y := Y) f g n ≫
    eqToHom (congrArg (fun q => exteriorCotangentSheaf (K := K) (X := Y) q n) (rfl : g ≫ f = g ≫ f))
  apply NadelBoundedCanonicalAffineFactor.exists_factor_of_frame_image
    (X := Y) (A := (pullback g).obj (exteriorCotangentSheaf (K := K) (X := X) f n))
    (B := exteriorCotangentSheaf (K := K) (X := Y) (g ≫ f) n) E hB J δ r hr
  obtain ⟨w, hw⟩ := hraw
  refine ⟨w, ?_⟩
  have hs := originalFramedSquareCoordinateImage (K := K) (X := X) (Y := Y)
    f g (g ≫ f) rfl n e zX zY hsource hcoordinates
  exact hs.trans hw

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalFramedFactorCore
