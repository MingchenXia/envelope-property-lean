import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineNaturality

/-! # Original coordinate differentials in an abstract field square

This private bridge composes actual sheaf differential naturality and
field-square transport before any affine scheme is instantiated.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

run_cmd
  let source := `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineNaturality
  for (short, original) in [
      (`originalSchemeCoordinateSection,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeSchemeCoordinateSection),
      (`originalExteriorTransportCoordinateSection,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeExteriorTransportCoordinateSection)] do
    let name := Lean.mkPrivateNameCore source original
    unless (← Lean.getEnv).contains name do throwError "missing original coordinate law {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      {scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls}

private def rawWedge {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (n : ℕ) (z : Fin n → Γ(X, ⊤)) :=
  exteriorSheafSection (cotangentPresheaf f) n ⊤
    (fun j => (cotangentPresheafDerivation f).d (z j))

private theorem originalSquareCoordinateImage
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ X)
    (fY : Y ⟶ Spec (.of K)) (h : g ≫ f = fY) (n : ℕ)
    (zX : Fin n → Γ(X, ⊤)) (zY : Fin n → Γ(Y, ⊤))
    (hcoordinates : ∀ j, g.app ⊤ (zX j) = zY j) :
    ((eqToHom (congrArg (fun q => exteriorCotangentSheaf q n) h)).val.app (op ⊤)).hom.toFun
      (((exteriorCotangentSheafMorphism f g n).val.app (op ⊤)).hom.toFun
        (rawWedge f n zX)) = rawWedge fY n zY := by
  cases h
  have h₁ := originalSchemeCoordinateSection f g n zX
  have h₂ := congrArg (rawWedge (g ≫ f) n) (funext hcoordinates)
  exact h₁.trans h₂

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore
