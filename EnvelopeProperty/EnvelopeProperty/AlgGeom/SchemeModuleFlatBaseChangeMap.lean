import EnvelopeProperty.AlgGeom.SchemeScalarModulePresheaf
import EnvelopeProperty.AlgGeom.FiniteCechFlatBaseChange

/-! # The canonical scalar-extension section comparison on every original open -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleFlatBaseChangeMap

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}} (p : X ⟶ Spec (.of R))

private theorem coefficientSquare {Y : Scheme.{u}}
    (g : Y ⟶ X) (q : Y ⟶ Spec (.of S))
    (h : g ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) (U : X.Opens) :
    (Scheme.ΓSpecIso (.of R)).inv ≫ p.appLE ⊤ U (by simp) ≫ g.app U =
      CommRingCat.ofHom (algebraMap R S) ≫ (Scheme.ΓSpecIso (.of S)).inv ≫
        q.appLE ⊤ (g ⁻¹ᵁ U) (by simp) := by
  let t := Spec.map (CommRingCat.ofHom (algebraMap R S))
  have h₁ : p.appLE ⊤ U (by simp) ≫ g.app U =
      (g ≫ p).appLE ⊤ (g ⁻¹ᵁ U) (by simp) := by
    erw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  rw [h₁, h]
  have h₂ := Scheme.Hom.appLE_comp_appLE q t ⊤ ⊤ (g ⁻¹ᵁ U) (by simp) (by simp)
  erw [← h₂, ← Scheme.Hom.app_eq_appLE]
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ q.appLE ⊤ (g ⁻¹ᵁ U) (by simp))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R S))).symm

/-- The actual original pullback unit is linear for the literal original
R actions on every original open and its original inverse image. -/
def unitMap (M : X.Modules) (U : X.Opens) :
    SchemeScalarModulePresheaf.openSections p M U →ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        (SchemeScalarModulePresheaf.openSections
          (FlatGlobalSections.structureMap (S := S) p)
          ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M)
          ((FlatGlobalSections.firstProjection (S := S) p) ⁻¹ᵁ U)) := by
  let g := FlatGlobalSections.firstProjection (S := S) p
  let q := FlatGlobalSections.structureMap (S := S) p
  let N := (Scheme.Modules.pullback g).obj M
  let u := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M
  let : Module R Γ(M, U) := (SchemeScalarModulePresheaf.openSections p M U).isModule
  let : Module R Γ(N, g ⁻¹ᵁ U) :=
    ((ModuleCat.restrictScalars (algebraMap R S)).obj
      (SchemeScalarModulePresheaf.openSections q N (g ⁻¹ᵁ U))).isModule
  let u₀ : Γ(M, U) → Γ(N, g ⁻¹ᵁ U) := u.app U
  exact
    { toFun := u₀
      map_add' := (u.app U).hom.map_add
      map_smul' := fun r m => by
        change u₀ (p.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (.of R)).inv r) • m) =
          (q.appLE ⊤ (g ⁻¹ᵁ U) (by simp)
            ((Scheme.ΓSpecIso (.of S)).inv (algebraMap R S r))) • u₀ m
        calc
          u₀ (p.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (.of R)).inv r) • m) =
              (g.app U (p.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (.of R)).inv r))) • u₀ m :=
            (u.val.app (op U)).hom.map_smul _ _
          _ = _ := congrArg (fun a => a • u₀ m)
            (ConcreteCategory.congr_hom (coefficientSquare p g q pullback.condition U) r) }

private def extendMap {P : ModuleCat.{u} R} {Q : ModuleCat.{u} S}
    (a : P →ₗ[R] (ModuleCat.restrictScalars (algebraMap R S)).obj Q) :
    (FiniteCechFlatBaseChange.tensorFunctor (R := R) (S := S)).obj P ⟶ Q := by
  let : Module R Q := Module.compHom _ (algebraMap R S)
  let : IsScalarTower R S Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let a' : P →ₗ[R] Q := a
  exact ModuleCat.ofHom (AlgebraTensorModule.lift
    ((LinearMap.id : S →ₗ[S] S).smulRight a'))

private theorem extendMap_tmul {P : ModuleCat.{u} R} {Q : ModuleCat.{u} S}
    (a : P →ₗ[R] (ModuleCat.restrictScalars (algebraMap R S)).obj Q) (s : S) (m : P) :
    extendMap a (s ⊗ₜ[R] m) = s • (a m : Q) := rfl

/-- The actual whole scalar-extension section map at the SAME original open. -/
def sectionComparison (M : X.Modules) (U : X.Opens) :
    (FiniteCechFlatBaseChange.tensorFunctor (R := R) (S := S)).obj
        (SchemeScalarModulePresheaf.openSections p M U) ⟶
      SchemeScalarModulePresheaf.openSections
        (FlatGlobalSections.structureMap (S := S) p)
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M)
        ((FlatGlobalSections.firstProjection (S := S) p) ⁻¹ᵁ U) :=
  extendMap (unitMap p M U)

/-- The original whole unit map retains every actual original unit section. -/
theorem unitMap_apply (M : X.Modules) (U : X.Opens) (m : Γ(M, U)) :
    unitMap (S := S) p M U m =
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (FlatGlobalSections.firstProjection (S := S) p)).unit.app M).val.app (op U) m := rfl

/-- Every pure tensor retains the original coefficient and actual unit section. -/
theorem sectionComparison_tmul (M : X.Modules) (U : X.Opens)
    (s : S) (m : SchemeScalarModulePresheaf.openSections p M U) :
    sectionComparison (S := S) p M U (s ⊗ₜ[R] m) =
      s • (unitMap (S := S) p M U m :
        SchemeScalarModulePresheaf.openSections
          (FlatGlobalSections.structureMap (S := S) p)
          ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M)
          ((FlatGlobalSections.firstProjection (S := S) p) ⁻¹ᵁ U)) := rfl

/-- The genuine sheaf of original pulled-module sections on inverse-image opens. -/
def targetSheaf (M : X.Modules) :
    TopCat.Sheaf (ModuleCat.{u} S) (TopCat.of X) :=
  (TopCat.Sheaf.pushforward (ModuleCat.{u} S)
    (FlatGlobalSections.firstProjection (S := S) p).base).obj
      (SchemeScalarModulePresheaf.sheaf (FlatGlobalSections.structureMap (S := S) p)
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M))

private def extendNat {C : Type u} [Category.{u} C]
    (F : C ⥤ ModuleCat.{u} R) (G : C ⥤ ModuleCat.{u} S)
    (a : F ⟶ G ⋙ ModuleCat.restrictScalars (algebraMap R S)) :
    F ⋙ FiniteCechFlatBaseChange.tensorFunctor (R := R) (S := S) ⟶ G where
  app c := extendMap (a.app c).hom
  naturality c d f := by
    let : Module R (G.obj d) := Module.compHom _ (algebraMap R S)
    let : IsScalarTower R S (G.obj d) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    apply ModuleCat.hom_ext
    apply AlgebraTensorModule.ext
    intro s m
    change extendMap (a.app d).hom (s ⊗ₜ[R] F.map f m) =
      G.map f (extendMap (a.app c).hom (s ⊗ₜ[R] m))
    erw [extendMap_tmul, extendMap_tmul]
    have hn : (a.app d).hom (F.map f m) = G.map f ((a.app c).hom m) :=
      ConcreteCategory.congr_hom (a.naturality f) m
    exact (congrArg (fun x : G.obj d => s • x) hn).trans
      ((G.map f).hom.map_smul s ((a.app c).hom m : G.obj c)).symm

/-- The actual whole original module unit is natural on the original
scalar-linear section presheaves and their original inverse-image opens. -/
def unitComparison (M : X.Modules) :
    (SchemeScalarModulePresheaf.sheaf p M).obj ⟶
      (targetSheaf (S := S) p M).obj ⋙ ModuleCat.restrictScalars (algebraMap R S) where
  app U := by
    change SchemeScalarModulePresheaf.openSections p M U.unop ⟶
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        (SchemeScalarModulePresheaf.openSections
          (FlatGlobalSections.structureMap (S := S) p)
          ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M)
          ((FlatGlobalSections.firstProjection (S := S) p) ⁻¹ᵁ U.unop))
    exact ModuleCat.ofHom
      (X := SchemeScalarModulePresheaf.openSections p M U.unop)
      (Y := (ModuleCat.restrictScalars (algebraMap R S)).obj
        (SchemeScalarModulePresheaf.openSections
          (FlatGlobalSections.structureMap (S := S) p)
          ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M)
          ((FlatGlobalSections.firstProjection (S := S) p) ⁻¹ᵁ U.unop)))
      (unitMap (S := S) p M U.unop)
  naturality U V h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact PresheafOfModules.naturality_apply
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (FlatGlobalSections.firstProjection (S := S) p)).unit.app M).val h m

/-- The canonical natural scalar-extension comparison, constructed from
the ACTUAL original pullback adjunction unit on EVERY original open. -/
def comparison (M : X.Modules) :
    (SchemeScalarModulePresheaf.sheaf p M).obj ⋙
        FiniteCechFlatBaseChange.tensorFunctor (R := R) (S := S) ⟶
      (targetSheaf (S := S) p M).obj :=
  extendNat _ _ (unitComparison (S := S) p M)

/-- The canonical natural transformation has the SAME entire original
section component, without any matching premise. -/
theorem comparison_app (M : X.Modules) (U : X.Opens) :
    (comparison (S := S) p M).app (op U) = sectionComparison (S := S) p M U := rfl

/-- EVERY pure tensor in the genuine whole natural comparison retains
the original coefficient and the actual original pullback-unit section. -/
theorem comparison_tmul (M : X.Modules) (U : X.Opens)
    (s : S) (m : SchemeScalarModulePresheaf.openSections p M U) :
    (comparison (S := S) p M).app (op U) (s ⊗ₜ[R] m) =
      s • (unitMap (S := S) p M U m :
        SchemeScalarModulePresheaf.openSections
          (FlatGlobalSections.structureMap (S := S) p)
          ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M)
          ((FlatGlobalSections.firstProjection (S := S) p) ⁻¹ᵁ U)) := rfl

end EnvelopeProperty.SchemeModuleFlatBaseChangeMap
