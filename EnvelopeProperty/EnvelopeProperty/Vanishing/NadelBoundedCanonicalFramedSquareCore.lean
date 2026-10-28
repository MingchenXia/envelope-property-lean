import EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore
import EnvelopeProperty.Berkovich.SchemeFramedSectionPullback

/-! # Original source-frame values in an abstract canonical field square

All frames and sheaf maps are original. The affine ring realization is
postponed until after the whole frame/differential formula is checked.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalFramedSquareCore
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry Scheme.Modules
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

run_cmd
  let core := `EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore
  let name := Lean.mkPrivateNameCore core
    `EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore.rawWedge
  unless (← Lean.getEnv).contains name do throwError "missing checked original wedge"
  Lean.Elab.Command.modifyScope fun scope =>
    {scope with openDecls := Lean.OpenDecl.explicit `originalRawWedge name :: scope.openDecls}
  let source := `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineNaturality
  let name := Lean.mkPrivateNameCore source
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeSchemeCoordinateSection
  unless (← Lean.getEnv).contains name do throwError "missing checked original sheaf differential"
  Lean.Elab.Command.modifyScope fun scope =>
    {scope with openDecls := Lean.OpenDecl.explicit `originalSchemeCoordinateSection name :: scope.openDecls}
  let source := `EnvelopeProperty.Berkovich.SchemeFramedSectionPullback
  let name := Lean.mkPrivateNameCore source
    `EnvelopeProperty.Berkovich.SchemeFramedSectionPullback.nativeUnit_hom
  unless (← Lean.getEnv).contains name do throwError "missing checked native pullback unit"
  Lean.Elab.Command.modifyScope fun scope =>
    {scope with openDecls := Lean.OpenDecl.explicit `originalNativeUnitHom name :: scope.openDecls}

private theorem originalFramedSquareCoordinateImage
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ X)
    (fY : Y ⟶ Spec (.of K)) (h : g ≫ f = fY) (n : ℕ)
    (e : exteriorCotangentSheaf f n ≅ unitObj X)
    (zX : Fin n → Γ(X, ⊤)) (zY : Fin n → Γ(Y, ⊤))
    (hsource : e.inv.app ⊤ (1 : Γ(X, ⊤)) = originalRawWedge f n zX)
    (hcoordinates : ∀ j, g.app ⊤ (zX j) = zY j) :
    let E := (pullback g).mapIso e ≪≫ pullbackUnitIso g
    ((eqToHom (congrArg (fun q => exteriorCotangentSheaf q n) h)).val.app (op ⊤)).hom.toFun
      ((exteriorCotangentSheafPullbackMap f g n).app ⊤
        (E.inv.app ⊤ (1 : Γ(Y, ⊤)))) = originalRawWedge fY n zY := by
  cases h
  let M := exteriorCotangentSheaf f n
  let s := e.inv.app ⊤ (1 : Γ(X, ⊤))
  let E := (pullback g).mapIso e ≪≫ pullbackUnitIso g
  let δ := exteriorCotangentSheafPullbackMap f g n
  have hp : E.inv.app ⊤ (1 : Γ(Y, ⊤)) = affinePullbackUnitTop g M s :=
    (originalNativeUnitHom g e.inv).symm
  have hu : affinePullbackUnitTop g M s =
      ((pullbackPushforwardAdjunction g).unit.app M).val.app (op ⊤) s := by
    change ((pullback g).obj M).presheaf.map (𝟙 (op (⊤ : Y.Opens))) _ = _
    exact congr($(((pullback g).obj M).presheaf.map_id (op ⊤)).hom
      (((pullbackPushforwardAdjunction g).unit.app M).val.app (op ⊤) s))
  have hd := congr($(exteriorCotangentSheafPullbackMap_unit f g n).val.app (op ⊤) |>.hom s)
  have h₁ := congrArg (fun t => δ.app ⊤ t) hp
  have h₂ := congrArg (fun t => δ.app ⊤ t) hu
  have h₃ := congrArg
    (((exteriorCotangentSheafMorphism f g n).val.app (op ⊤)).hom.toFun) hsource
  have h₄ := originalSchemeCoordinateSection f g n zX
  have h₅ := congrArg (originalRawWedge (g ≫ f) n) (funext hcoordinates)
  exact h₁.trans (h₂.trans (hd.trans (h₃.trans (h₄.trans h₅))))

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalFramedSquareCore
