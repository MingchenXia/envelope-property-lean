module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk

/-! # The original scheme-module stalk maps are linear for the native stalk action -/

@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace EnvelopeProperty.SchemeModuleStalkLinearity

/-- Expose Mathlib's SAME native stalk action through the usual scheme-module
presheaf notation. The value is exactly the existing native instance. -/
instance nativeStalkModule {X : Scheme.{u}} (M : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) M.val x

/-- The actual additive stalk map preserves the EXISTING native structure-stalk action.
No auxiliary module action, coefficient comparison or scalar certificate is supplied. -/
theorem stalkMap_smul {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (x : X) (r : X.presheaf.stalk x) (m : M.presheaf.stalk x) :
    (((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f) (r • m) : N.presheaf.stalk x) =
      @SMul.smul (X.presheaf.stalk x) (N.presheaf.stalk x) _
        r (((Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f) m : N.presheaf.stalk x) := by
  let g : M.presheaf ⟶ N.presheaf := (Scheme.Modules.toPresheaf X).map f
  change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map g (r • m) : N.presheaf.stalk x) =
    @SMul.smul (X.presheaf.stalk x) (N.presheaf.stalk x) _
      r ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map g m : N.presheaf.stalk x)
  obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hxV, b, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
  let aV := X.presheaf.map (homOfLE hVU).op a
  have ha : X.presheaf.germ V x hxV aV = X.presheaf.germ U x hxU a :=
    X.presheaf.germ_res_apply (homOfLE hVU) x hxV a
  erw [← ha, ← PresheafOfModules.germ_smul (R := X.presheaf) M.val x V hxV aV b,
    TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change N.presheaf.germ V x hxV ((f.val.app (op V)).hom (aV • b)) =
    X.presheaf.germ V x hxV aV • N.presheaf.germ V x hxV ((f.val.app (op V)).hom b)
  exact (congrArg (fun t : Γ(N, V) => N.presheaf.germ V x hxV t)
    ((f.val.app (op V)).hom.map_smul aV b)).trans
      (PresheafOfModules.germ_smul (R := X.presheaf) N.val x V hxV aV
        ((f.val.app (op V)).hom b))

/-- Bundle precisely the SAME actual stalk map, retaining the original native action. -/
def stalkMapLinear {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (x : X) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x where
  toFun := ((Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f)
  map_add' := map_add _
  map_smul' := stalkMap_smul f x

/-- The bundled map is literally the original additive stalk map on every original element. -/
@[simp] theorem stalkMapLinear_apply {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (x : X) (m : M.presheaf.stalk x) :
    stalkMapLinear f x m = ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f) m := rfl

end EnvelopeProperty.SchemeModuleStalkLinearity
