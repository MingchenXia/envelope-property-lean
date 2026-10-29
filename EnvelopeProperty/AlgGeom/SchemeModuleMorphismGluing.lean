/-
Copyright (c) 2026 Envelope Property contributors and Bing Wang Entropy contributors.
Released under Apache 2.0 license as described in the file LICENSE.
The Mathlib-only morphism gluing proofs adapt the sibling
ComplexGeometry/Schemes/BundleMorphismGluing.lean source; no sibling interface is imported.
-/
import EnvelopeProperty.AlgGeom.ModuleHomSheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Gluing morphisms and isomorphisms of sheaves of modules -/
open CategoryTheory Opposite AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleMorphismGluing
variable {X : Scheme.{u}}

/-- Morphisms between the restrictions of two sheaves of modules to an open. -/
abbrev bundleHomSections (L N : X.Modules) (U : X.Opens) : Type u :=
  L.over U ⟶ N.over U

/-- Restriction of a morphism of modules along an inclusion of opens, using the comparison
isomorphisms `SheafOfModules.overFunctorMap`. -/
def bundleHomRestriction (L N : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (α : bundleHomSections L N V) : bundleHomSections L N U :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app L).inv ≫
    (SheafOfModules.overMap X.ringCatSheaf i).map α ≫
    ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app N).hom

/-- The components of a restricted morphism are those of the original morphism. -/
theorem bundleHomRestriction_app (L N : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (α : bundleHomSections L N V) (W : (Over U)ᵒᵖ) (x : (L.over U).val.obj W) :
    (bundleHomRestriction L N i α).val.app W x =
      α.val.app ((Over.map i).op.obj W) x := by
  rfl

private def additiveHom (L N : X.Modules) :=
  (ModuleHomSheaf.ambientHom X.ringCatSheaf L N).obj

private def underlyingHom (L N : X.Modules) (U : X.Opens)
    (α : bundleHomSections L N U) := ModuleHomSheaf.toAmbient X.ringCatSheaf L N U α

private def linearHomEquiv (L N : X.Modules) (U : X.Opens) :=
  ModuleHomSheaf.localHomEquiv X.ringCatSheaf L N U

/-- The presheaf of types `U ↦ Hom(L|_U, N|_U)`. -/
def bundleHomTypePresheaf (L N : X.Modules) : X.Opensᵒᵖ ⥤ Type u where
  obj U := bundleHomSections L N U.unop
  map i := ↾(bundleHomRestriction L N i.unop)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro α
    apply (linearHomEquiv L N U.unop).injective
    apply Subtype.ext
    change (additiveHom L N).map (𝟙 U) (underlyingHom L N U.unop α) =
      underlyingHom L N U.unop α
    exact ConcreteCategory.congr_hom ((additiveHom L N).map_id U) _
  map_comp {U V W} i j := by
    apply ConcreteCategory.hom_ext
    intro α
    apply (linearHomEquiv L N W.unop).injective
    apply Subtype.ext
    change (additiveHom L N).map (i ≫ j) (underlyingHom L N U.unop α) =
      (additiveHom L N).map j ((additiveHom L N).map i (underlyingHom L N U.unop α))
    exact ConcreteCategory.congr_hom ((additiveHom L N).map_comp i j) _

private def linearHomIso (L N : X.Modules) :
    bundleHomTypePresheaf L N ≅ (ModuleHomSheaf.localHomSheaf X.ringCatSheaf L N).obj :=
  NatIso.ofComponents (fun U => (linearHomEquiv L N U.unop).toIso) (fun i => by
    apply ConcreteCategory.hom_ext
    intro α
    apply Subtype.ext
    exact ModuleHomSheaf.ambientHom_map_toAmbient X.ringCatSheaf L N i α)

/-- The presheaf `U ↦ Hom(L|_U, N|_U)` is a sheaf. -/
theorem bundleHomTypePresheaf_isSheaf (L N : X.Modules) :
    Presheaf.IsSheaf (_root_.Opens.grothendieckTopology X) (bundleHomTypePresheaf L N) :=
  (Presheaf.isSheaf_of_iso_iff (linearHomIso L N)).2
    (ModuleHomSheaf.localHomSheaf X.ringCatSheaf L N).property

/-- The sheaf of types `U ↦ Hom(L|_U, N|_U)`. -/
def bundleHomTypeSheaf (L N : X.Modules) : TopCat.Sheaf (Type u) X :=
  ⟨bundleHomTypePresheaf L N, bundleHomTypePresheaf_isSheaf L N⟩

/-- Morphisms of the restrictions to `⊤` are the morphisms `L ⟶ N`. -/
def bundleHomTopEquiv (L N : X.Modules) : bundleHomSections L N ⊤ ≃ (L ⟶ N) where
  toFun α :=
    { val :=
      { app := fun U ↦ α.val.app (.op (Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top))))
        naturality := fun {U V} i ↦ by
          exact α.val.naturality
            (Over.homMk i.unop :
              Over.mk (homOfLE (show V.unop ≤ ⊤ from le_top)) ⟶
                Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top))).op } }
  invFun α := (SheafOfModules.overFunctor X.ringCatSheaf ⊤).map α
  left_inv α := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    ext x
    rfl
  right_inv α := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    rfl

/-- Restriction of the global morphism attached to a morphism over `⊤` is its restriction. -/
theorem bundleHomTopEquiv_restrict (L N : X.Modules) (α : bundleHomSections L N ⊤)
    (U : X.Opens) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).map (bundleHomTopEquiv L N α) =
      bundleHomRestriction L N (homOfLE (show U ≤ ⊤ from le_top)) α := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  rfl

private theorem cover_top {ι : Type*} (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) : (⊤ : X.Opens) ≤ iSup U := by
  intro x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr (hc x)

set_option backward.isDefEq.respectTransparency false in
/-- Compatible morphisms of modules on an open cover glue uniquely. -/
theorem bundleHom_existsUnique {ι : Type*} (L N : X.Modules) (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) (α : ∀ i, bundleHomSections L N (U i))
    (ha : ∀ i j, bundleHomRestriction L N (TopologicalSpace.Opens.infLELeft (U i) (U j)) (α i) =
      bundleHomRestriction L N (TopologicalSpace.Opens.infLERight (U i) (U j)) (α j)) :
    ∃! f : L ⟶ N, ∀ i, (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map f = α i := by
  obtain ⟨f, hf, hu⟩ := (bundleHomTypeSheaf L N).existsUnique_gluing' U ⊤
    (fun i ↦ homOfLE (show U i ≤ ⊤ from le_top)) (cover_top U hc) α (by
      intro i j
      exact ha i j)
  refine ⟨bundleHomTopEquiv L N f, ?_, ?_⟩
  · intro i
    rw [bundleHomTopEquiv_restrict]
    exact hf i
  · intro g hg
    apply (bundleHomTopEquiv L N).symm.injective
    rw [Equiv.symm_apply_apply]
    apply hu
    intro i
    exact (bundleHomTopEquiv_restrict L N ((bundleHomTopEquiv L N).symm g) (U i)).symm.trans
      (by simpa using hg i)

/-- The morphism of modules glued from compatible local morphisms. -/
def bundleGlueHom {ι : Type*} (L N : X.Modules) (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) (α : ∀ i, bundleHomSections L N (U i))
    (ha : ∀ i j, bundleHomRestriction L N (TopologicalSpace.Opens.infLELeft (U i) (U j)) (α i) =
      bundleHomRestriction L N (TopologicalSpace.Opens.infLERight (U i) (U j)) (α j)) : L ⟶ N :=
  (bundleHom_existsUnique L N U hc α ha).choose

/-- The glued morphism restricts to the prescribed local morphisms. -/
theorem bundleGlueHom_restrict {ι : Type*} (L N : X.Modules) (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) (α : ∀ i, bundleHomSections L N (U i))
    (ha : ∀ i j, bundleHomRestriction L N (TopologicalSpace.Opens.infLELeft (U i) (U j)) (α i) =
      bundleHomRestriction L N (TopologicalSpace.Opens.infLERight (U i) (U j)) (α j)) (i : ι) :
    (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map (bundleGlueHom L N U hc α ha) = α i :=
  (bundleHom_existsUnique L N U hc α ha).choose_spec.1 i

/-- Morphisms of modules are determined by their restrictions to an open cover. -/
theorem bundleHom_ext {ι : Type*} (L N : X.Modules) (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) {f g : L ⟶ N}
    (h : ∀ i, (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map f =
      (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map g) : f = g := by
  apply (bundleHomTopEquiv L N).symm.injective
  apply (bundleHomTypeSheaf L N).eq_of_locally_eq' U ⊤
    (fun i ↦ homOfLE (show U i ≤ ⊤ from le_top)) (cover_top U hc)
  intro i
  change bundleHomRestriction L N (homOfLE (show U i ≤ ⊤ from le_top))
      ((bundleHomTopEquiv L N).symm f) =
    bundleHomRestriction L N (homOfLE (show U i ≤ ⊤ from le_top))
      ((bundleHomTopEquiv L N).symm g)
  rw [← bundleHomTopEquiv_restrict, ← bundleHomTopEquiv_restrict,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h i

/-- Restriction preserves identities. -/
theorem bundleHomRestriction_id (L : X.Modules) {U V : X.Opens} (i : U ⟶ V) :
    bundleHomRestriction L L i (𝟙 (L.over V)) = 𝟙 (L.over U) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Restriction preserves composition. -/
theorem bundleHomRestriction_comp (L N M : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (α : bundleHomSections L N V) (β : bundleHomSections N M V) :
    bundleHomRestriction L M i (α ≫ β) =
      bundleHomRestriction L N i α ≫ bundleHomRestriction N M i β := by
  simp only [bundleHomRestriction, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- The restriction of an isomorphism of modules along an inclusion of opens. -/
def bundleHomRestrictionIso (L N : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (e : L.over V ≅ N.over V) : L.over U ≅ N.over U :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app L).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf i).mapIso e ≪≫
    ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app N)

/-- Its `hom` is the restriction of the `hom`. -/
theorem bundleHomRestrictionIso_hom (L N : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (e : L.over V ≅ N.over V) :
    (bundleHomRestrictionIso L N i e).hom = bundleHomRestriction L N i e.hom := rfl

/-- Its `inv` is the restriction of the `inv`. -/
theorem bundleHomRestrictionIso_inv (L N : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (e : L.over V ≅ N.over V) :
    (bundleHomRestrictionIso L N i e).inv = bundleHomRestriction N L i e.inv := by
  simp only [bundleHomRestrictionIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    bundleHomRestriction, Category.assoc]

/-- If local isomorphisms agree on overlaps, so do their inverses. -/
theorem bundleLocalIso_inv_compatible {ι : Type*} (L N : X.Modules) (U : ι → X.Opens)
    (e : ∀ i, L.over (U i) ≅ N.over (U i))
    (he : ∀ i j, bundleHomRestriction L N (TopologicalSpace.Opens.infLELeft (U i) (U j)) (e i).hom =
      bundleHomRestriction L N (TopologicalSpace.Opens.infLERight (U i) (U j)) (e j).hom) :
    ∀ i j, bundleHomRestriction N L (TopologicalSpace.Opens.infLELeft (U i) (U j)) (e i).inv =
      bundleHomRestriction N L (TopologicalSpace.Opens.infLERight (U i) (U j)) (e j).inv := by
  intro i j
  rw [← bundleHomRestrictionIso_inv, ← bundleHomRestrictionIso_inv]
  apply congrArg Iso.inv
  apply Iso.ext
  exact he i j

set_option backward.isDefEq.respectTransparency false in
/-- Compatible local isomorphisms glue to a global isomorphism; its inverse is glued from the
local inverses. -/
def bundleGlueIso {ι : Type*} (L N : X.Modules) (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) (e : ∀ i, L.over (U i) ≅ N.over (U i))
    (he : ∀ i j, bundleHomRestriction L N (TopologicalSpace.Opens.infLELeft (U i) (U j)) (e i).hom =
      bundleHomRestriction L N (TopologicalSpace.Opens.infLERight (U i) (U j)) (e j).hom) : L ≅ N where
  hom := bundleGlueHom L N U hc (fun i ↦ (e i).hom) he
  inv := bundleGlueHom N L U hc (fun i ↦ (e i).inv) (bundleLocalIso_inv_compatible L N U e he)
  hom_inv_id := by
    apply bundleHom_ext L L U hc
    intro i
    rw [Functor.map_comp, CategoryTheory.Functor.map_id, bundleGlueHom_restrict, bundleGlueHom_restrict]
    exact (e i).hom_inv_id
  inv_hom_id := by
    apply bundleHom_ext N N U hc
    intro i
    rw [Functor.map_comp, CategoryTheory.Functor.map_id, bundleGlueHom_restrict, bundleGlueHom_restrict]
    exact (e i).inv_hom_id

/-- The glued isomorphism restricts to the prescribed local isomorphisms. -/
theorem bundleGlueIso_restrict {ι : Type*} (L N : X.Modules) (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) (e : ∀ i, L.over (U i) ≅ N.over (U i))
    (he : ∀ i j, bundleHomRestriction L N (TopologicalSpace.Opens.infLELeft (U i) (U j)) (e i).hom =
      bundleHomRestriction L N (TopologicalSpace.Opens.infLERight (U i) (U j)) (e j).hom) (i : ι) :
    (SheafOfModules.overFunctor X.ringCatSheaf (U i)).mapIso (bundleGlueIso L N U hc e he) = e i := by
  apply Iso.ext
  exact bundleGlueHom_restrict L N U hc (fun i ↦ (e i).hom) he i

end EnvelopeProperty.SchemeModuleMorphismGluing
