import EnvelopeProperty.AlgGeom.AffineModuleFlatBaseChange
import ModularCurves.ForMathlib.SchemeModuleBaseCechBasic

/-! # Literal original scalar-linear section modules on every original open -/
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.SchemeScalarModulePresheaf

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (p : X ⟶ Spec (.of R)) (M : X.Modules)

/-- Actual sections on the original open, with its literal original R action. -/
abbrev openSections (U : X.Opens) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars
    (((p.appLE ⊤ U (by simp)).hom).comp (Scheme.ΓSpecIso (.of R)).inv.hom)).obj
      (ModuleCat.of Γ(X, U) Γ(M, U))

private def restriction {U V : X.Opens} (h : V ≤ U) :
    openSections p M U ⟶ openSections p M V := by
  let : Module R Γ(M, U) := (openSections p M U).isModule
  let : Module R Γ(M, V) := (openSections p M V).isModule
  exact ModuleCat.ofHom
    { toFun := M.presheaf.map (homOfLE h).op
      map_add' := (M.presheaf.map (homOfLE h).op).hom.map_add
      map_smul' := fun r m => by
        change M.presheaf.map (homOfLE h).op
          ((p.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (.of R)).inv r)) • m) = _
        rw [M.map_smul]
        apply congrArg (fun a => a • M.presheaf.map (homOfLE h).op m)
        exact ConcreteCategory.congr_hom
          (p.appLE_map (by simp) (homOfLE h).op)
          ((Scheme.ΓSpecIso (.of R)).inv r) }

/-- The original entire section presheaf, retaining every scalar and restriction. -/
def presheaf : X.Opensᵒᵖ ⥤ ModuleCat.{u} R where
  obj U := openSections p M U.unop
  map h := restriction p M h.unop.le
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact ConcreteCategory.congr_hom (M.presheaf.map_id U) m
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact ConcreteCategory.congr_hom (M.presheaf.map_comp f g) m

private theorem presheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (presheaf p M) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget (ModuleCat.{u} R))]
  convert (Presheaf.isSheaf_iff_isSheaf_forget _ _
    (CategoryTheory.forget AddCommGrpCat.{u})).mp (Scheme.Modules.isSheaf M) using 1
  rfl

/-- The genuine sheaf of the SAME original scalar-linear open-section modules. -/
def sheaf : TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of X) :=
  ⟨presheaf p M, presheaf_isSheaf p M⟩

/-- At the actual top open, the SAME section module has exactly the
original global coefficient action used in affine module base change. -/
def topSectionsIso : (sheaf p M).obj.obj (op ⊤) ≅
    AffineModuleFlatBaseChange.sections p M := by
  refine ModuleCat.isoMk (Iso.refl _) ?_
  intro r
  ext (m : Γ(M, ⊤))
  change (p.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) • m =
    (p.appLE ⊤ ⊤ (by simp) ((Scheme.ΓSpecIso (.of R)).inv r)) • m
  erw [← Scheme.Hom.app_eq_appLE]

/-- The top comparison retains every actual original section unchanged. -/
theorem topSectionsIso_apply (m : Γ(M, ⊤)) : (topSectionsIso p M).hom m = m := rfl

end EnvelopeProperty.SchemeScalarModulePresheaf
