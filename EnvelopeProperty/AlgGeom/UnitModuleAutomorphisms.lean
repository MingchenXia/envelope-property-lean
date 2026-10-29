/-
Copyright (c) 2026. All rights reserved.
-/
import ModularCurves.Picard.UnitPullback

/-! # Actual structure-module automorphisms are original global unit scalars -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}}

/-- EVERY actual whole structure-module endomorphism is actual scalar
multiplication by its ORIGINAL top-open value on the original unit section. -/
theorem unitHom_eq_globalScalar (a : unitObj X ⟶ unitObj X) :
    a = ModularCurves.unitEndomorphismOfTopSection
      ((a.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) := by
  apply SheafOfModules.hom_ext
  ext U
  change (a.val.app U).hom (1 : Γ(X, U.unop)) =
    1 * X.presheaf.map (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op
      ((a.val.app (op ⊤)).hom (1 : Γ(X, ⊤)))
  rw [one_mul]
  have hn := congrArg (fun q => q.hom (1 : Γ(X, ⊤)))
    (a.val.naturality (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op)
  change (a.val.app U).hom
      (X.presheaf.map (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op (1 : Γ(X, ⊤))) =
    X.presheaf.map (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op
      ((a.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) at hn
  simpa only [map_one] using hn

/-- EVERY actual original whole structure-module automorphism is the
actual scalar automorphism of a genuine ORIGINAL global unit. -/
theorem unitIso_eq_globalUnit (e : unitObj X ≅ unitObj X) :
    ∃ u : Γ(X, (⊤ : X.Opens))ˣ, e = ModularCurves.unitAutomorphismOfTopUnit u := by
  let r : Γ(X, ⊤) := (e.hom.val.app (op ⊤)).hom (1 : Γ(X, ⊤))
  have : IsIso (e.hom.val.app (op ⊤)) :=
    inferInstanceAs (IsIso ((SheafOfModules.evaluation _ (op ⊤)).map e.hom))
  have he := (ConcreteCategory.isIso_iff_bijective (e.hom.val.app (op ⊤))).mp inferInstance
  have hr : IsUnit r := by
    apply IsUnit.isUnit_iff_mulRight_bijective.mpr
    have hmul : (fun x : Γ(X, ⊤) => x * r) = (e.hom.val.app (op ⊤)).hom := by
      funext x
      have hx := ((e.hom.val.app (op ⊤)).hom).map_smul x (1 : Γ(X, ⊤))
      simpa only [smul_eq_mul, mul_one, r] using hx.symm
    rw [hmul]
    exact he
  obtain ⟨u, hu⟩ := hr
  refine ⟨u, ?_⟩
  apply Iso.ext
  rw [ModularCurves.unitAutomorphismOfTopUnit_hom, hu]
  simpa only [r] using unitHom_eq_globalScalar e.hom

end AlgebraicGeometry.Scheme.Modules
