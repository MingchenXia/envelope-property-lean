import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCounit

/-! # The full coefficient law of the original canonical constructor

The intermediate canonical modules are inferred from the original native
maps themselves. They are never reconstructed from new ring annotations.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  let mod := `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCounit
  let original :=
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeRingEquivSectionsIso
  let name := Lean.mkPrivateNameCore mod original
  unless (← Lean.getEnv).contains name do
    throwError "missing original frozen canonical constructor {name}"
  Lean.Elab.Command.modifyScope fun scope =>
    { scope with openDecls :=
      Lean.OpenDecl.explicit `frozenNativeRingEquivSectionsIso name :: scope.openDecls }

private def outerCoefficientIso
    {S C P : CommRingCat.{u}}
    (α : S →+* C) (β : S →+* P) (ρ : C →+* P)
    {M : ModuleCat C} {Q N : ModuleCat P}
    (E : M ≅ (ModuleCat.restrictScalars ρ).obj Q) (T : Q ≅ N)
    (hs : β = ρ.comp α) :
    (ModuleCat.restrictScalars α).obj M ≅ (ModuleCat.restrictScalars β).obj N :=
  (ModuleCat.restrictScalars α).mapIso E ≪≫
    (ModuleCat.restrictScalarsComp'App α ρ β hs Q).symm ≪≫
    (ModuleCat.restrictScalars β).mapIso T

private theorem outerCoefficientIso_smul
    {S C P : CommRingCat.{u}}
    (α : S →+* C) (β : S →+* P) (ρ : C →+* P)
    {M : ModuleCat C} {Q N : ModuleCat P}
    (E : M ≅ (ModuleCat.restrictScalars ρ).obj Q) (T : Q ≅ N)
    (hs : β = ρ.comp α) (c : C) (w : M) :
    (outerCoefficientIso α β ρ E T hs).hom (c • w) =
      ρ c • (show N from (outerCoefficientIso α β ρ E T hs).hom w) := by
  change T.hom (E.hom (c • w)) = ρ c • T.hom (E.hom w)
  have h := E.hom.hom.map_smul c w
  have ht := congrArg T.hom.hom.toFun h
  exact ht.trans (T.hom.hom.map_smul (ρ c) (E.hom w))


private theorem nativeOriginalConstructor_smul
    {K : Type u} [Field K] {S C P : CommRingCat.{u}} [Algebra K P]
    (α : S →+* C) (β : S →+* P)
    (f : Spec C ⟶ Spec (.of K)) (d : ℕ) [SmoothOfRelativeDimension d f]
    (e : C ≃+* P) (hs : β = e.toRingHom.comp α)
    (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ f = affineStructuralMap K P)
    (c : C)
    (w : (moduleSpecΓFunctor (R := C)).obj (exteriorCotangentSheaf (K := K) f d)) :
    (frozenNativeRingEquivSectionsIso (K := K) α β f d e hs he).hom (c • w) =
      e.toRingHom c •
        (show (moduleSpecΓFunctor (R := P)).obj
          (exteriorCotangentSheaf (K := K) (affineStructuralMap K P) d) from
            (frozenNativeRingEquivSectionsIso (K := K) α β f d e hs he).hom w) := by
  let E := nativeEquivSectionsIso f e d
  let T := (moduleSpecΓFunctor (R := P)).mapIso
    (eqToIso (congrArg (fun z => exteriorCotangentSheaf (K := K) z d) he))
  have hIso : frozenNativeRingEquivSectionsIso (K := K) α β f d e hs he =
      outerCoefficientIso α β e.toRingHom E T hs := by
    rfl
  rw [hIso]
  exact outerCoefficientIso_smul α β e.toRingHom E T hs c w


end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
