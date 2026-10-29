import EnvelopeProperty.Cartier.GeometricAffineHomology
import EnvelopeProperty.DI.CechDegreeOneLocalData
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Exact original readback and naturality of affine local module maps -/
noncomputable section
namespace EnvelopeProperty.DI.AffineLocalMapRestriction
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section AffineSheafMaps
variable (R : CommRingCat.{u}) (M N : (Spec R).Modules) [M.IsQuasicoherent]

def specHomOfSections
    (l : (moduleSpecΓFunctor (R := R)).obj M ⟶ (moduleSpecΓFunctor (R := R)).obj N) : M ⟶ N := by
  letI : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact inv M.fromTildeΓ ≫
    ((tilde.adjunction (R := R)).homEquiv ((moduleSpecΓFunctor (R := R)).obj M) N).symm l

theorem specHomOfSections_map
    (l : (moduleSpecΓFunctor (R := R)).obj M ⟶ (moduleSpecΓFunctor (R := R)).obj N) :
    (moduleSpecΓFunctor (R := R)).map (specHomOfSections R M N l) = l := by
  let : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let Γ₀ := moduleSpecΓFunctor (R := R)
  let adj := tilde.adjunction (R := R)
  change Γ₀.map (inv M.fromTildeΓ ≫ (adj.homEquiv (Γ₀.obj M) N).symm l) = l
  rw [Γ₀.map_comp]
  have hu : Γ₀.map (inv M.fromTildeΓ) = adj.unit.app (Γ₀.obj M) := by
    apply (cancel_mono (Γ₀.map M.fromTildeΓ)).1
    rw [← Γ₀.map_comp, IsIso.inv_hom_id, Γ₀.map_id]
    exact (adj.right_triangle_components M).symm
  rw [hu]
  simpa only [adj.homEquiv_unit] using (adj.homEquiv (Γ₀.obj M) N).apply_symm_apply l

theorem specHomOfSections_zero : specHomOfSections R M N 0 = 0 := by
  simp only [specHomOfSections, Adjunction.homAddEquiv_symm_zero, comp_zero]

theorem specHomOfSections_add
    (l l' : (moduleSpecΓFunctor (R := R)).obj M ⟶ (moduleSpecΓFunctor (R := R)).obj N) :
    specHomOfSections R M N (l+l') = specHomOfSections R M N l + specHomOfSections R M N l' := by
  simp only [specHomOfSections, Adjunction.homAddEquiv_symm_add, Preadditive.comp_add]

theorem specHomOfSections_sub
    (l l' : (moduleSpecΓFunctor (R := R)).obj M ⟶ (moduleSpecΓFunctor (R := R)).obj N) :
    specHomOfSections R M N (l-l') = specHomOfSections R M N l - specHomOfSections R M N l' := by
  simp only [specHomOfSections, Adjunction.homAddEquiv_symm_sub, Preadditive.comp_sub]

theorem specMap_ext (a b : M ⟶ N)
    (h : (moduleSpecΓFunctor (R := R)).map a = (moduleSpecΓFunctor (R := R)).map b) : a = b := by
  let : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  apply (cancel_epi M.fromTildeΓ).1
  have ha := Scheme.Modules.fromTildeΓNatTrans.naturality a
  have hb := Scheme.Modules.fromTildeΓNatTrans.naturality b
  change (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map a) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ a at ha
  change (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map b) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ b at hb
  exact ha.symm.trans ((congrArg (fun t => (tilde.functor R).map t ≫ N.fromTildeΓ) h).trans hb)

end AffineSheafMaps

section ActualAffineRestriction
variable {Z : Scheme.{u}} {W : Z.Opens} (hW : IsAffineOpen W) (M N : Z.Modules)
  [((Scheme.Modules.restrictFunctor hW.fromSpec).obj M).IsQuasicoherent]

def affineSpecMap (l : M.val.obj (op W) ⟶ N.val.obj (op W)) :
    (Scheme.Modules.restrictFunctor hW.fromSpec).obj M ⟶
      (Scheme.Modules.restrictFunctor hW.fromSpec).obj N :=
  specHomOfSections Γ(Z,W)
    ((Scheme.Modules.restrictFunctor hW.fromSpec).obj M)
    ((Scheme.Modules.restrictFunctor hW.fromSpec).obj N)
    ((Cartier.GeometricAffineHomology.moduleSectionsIso hW M).hom ≫ l ≫
      (Cartier.GeometricAffineHomology.moduleSectionsIso hW N).inv)

theorem affineSpecMap_sections (l : M.val.obj (op W) ⟶ N.val.obj (op W)) :
    (Cartier.GeometricAffineHomology.moduleSectionsIso hW M).inv ≫
        (moduleSpecΓFunctor (R := Γ(Z,W))).map (affineSpecMap hW M N l) ≫
          (Cartier.GeometricAffineHomology.moduleSectionsIso hW N).hom = l := by
  rw [affineSpecMap, specHomOfSections_map]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

def chartRestrictionIso (P : Z.Modules) :
    P.restrict W.ι ≅
      (Scheme.Modules.restrictFunctor hW.isoSpec.hom).obj (P.restrict hW.fromSpec) :=
  (Scheme.Modules.restrictFunctorCongr hW.isoSpec_hom_fromSpec).symm.app P ≪≫
    (Scheme.Modules.restrictFunctorComp hW.isoSpec.hom hW.fromSpec).app P

def affineLocalMap (l : M.val.obj (op W) ⟶ N.val.obj (op W)) :
    M.restrict W.ι ⟶ N.restrict W.ι :=
  (chartRestrictionIso hW M).hom ≫
    (Scheme.Modules.restrictFunctor hW.isoSpec.hom).map (affineSpecMap hW M N l) ≫
      (chartRestrictionIso hW N).inv

theorem affineLocalMap_zero : affineLocalMap hW M N 0 = 0 := by
  simp only [affineLocalMap, affineSpecMap, comp_zero, zero_comp,
    specHomOfSections_zero, Functor.map_zero]

theorem affineLocalMap_add (l l' : M.val.obj (op W) ⟶ N.val.obj (op W)) :
    affineLocalMap hW M N (l+l') = affineLocalMap hW M N l + affineLocalMap hW M N l' := by
  simp only [affineLocalMap, affineSpecMap, Preadditive.comp_add, Preadditive.add_comp,
    specHomOfSections_add, Functor.map_add]

theorem affineLocalMap_sub (l l' : M.val.obj (op W) ⟶ N.val.obj (op W)) :
    affineLocalMap hW M N (l-l') = affineLocalMap hW M N l - affineLocalMap hW M N l' := by
  simp only [affineLocalMap, affineSpecMap, Preadditive.comp_sub, Preadditive.sub_comp,
    specHomOfSections_sub, Functor.map_sub]

omit [((Scheme.Modules.restrictFunctor hW.fromSpec).obj M).IsQuasicoherent] in
theorem moduleSections_naturality (φ : M ⟶ N) :
    (moduleSpecΓFunctor (R := Γ(Z,W))).map ((Scheme.Modules.restrictFunctor hW.fromSpec).map φ) ≫
      (Cartier.GeometricAffineHomology.moduleSectionsIso hW N).hom =
        (Cartier.GeometricAffineHomology.moduleSectionsIso hW M).hom ≫ φ.val.app (op W) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact (ConcreteCategory.congr_hom
    (φ.mapPresheaf.naturality
      (eqToHom (show hW.fromSpec ''ᵁ (⊤ : (Spec Γ(Z,W)).Opens) = W by simp).symm).op) s).symm

omit [((Scheme.Modules.restrictFunctor hW.fromSpec).obj M).IsQuasicoherent] in
theorem chartRestriction_naturality (φ : M ⟶ N) :
    (Scheme.Modules.restrictFunctor W.ι).map φ ≫ (chartRestrictionIso hW N).hom =
      (chartRestrictionIso hW M).hom ≫
        (Scheme.Modules.restrictFunctor hW.isoSpec.hom).map
          ((Scheme.Modules.restrictFunctor hW.fromSpec).map φ) := by
  exact ((Scheme.Modules.restrictFunctorCongr hW.isoSpec_hom_fromSpec).symm ≪≫
    (Scheme.Modules.restrictFunctorComp hW.isoSpec.hom hW.fromSpec)).hom.naturality φ

theorem affineLocalMap_postcompose (P : Z.Modules)
    (l : M.val.obj (op W) ⟶ N.val.obj (op W)) (φ : N ⟶ P) :
    affineLocalMap hW M P (l ≫ φ.val.app (op W)) =
      affineLocalMap hW M N l ≫ (Scheme.Modules.restrictFunctor W.ι).map φ := by
  have ha : affineSpecMap hW M P (l ≫ φ.val.app (op W)) =
      affineSpecMap hW M N l ≫ (Scheme.Modules.restrictFunctor hW.fromSpec).map φ := by
    apply specMap_ext
    rw [Functor.map_comp]
    rw [affineSpecMap, specHomOfSections_map, affineSpecMap, specHomOfSections_map]
    have hn := moduleSections_naturality hW N P φ
    have hn' := congrArg (fun a =>
      (Cartier.GeometricAffineHomology.moduleSectionsIso hW N).inv ≫ a ≫
        (Cartier.GeometricAffineHomology.moduleSectionsIso hW P).inv) hn
    simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.comp_id] at hn'
    simp only [Category.assoc, hn']
  have hc := chartRestriction_naturality hW N P φ
  have hc' := congrArg (fun a =>
    (chartRestrictionIso hW N).inv ≫ a ≫ (chartRestrictionIso hW P).inv) hc
  simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.comp_id] at hc'
  simp only [affineLocalMap, ha, Functor.map_comp, Category.assoc, hc']

end ActualAffineRestriction

private theorem transport_roundTrip {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (ε : F ⋙ G ≅ 𝟭 C)
    {A B : C} {A' B' : D} (eA : A' ≅ F.obj A) (eB : B' ≅ F.obj B) (φ : A ⟶ B) :
    ((G.mapIso eA) ≪≫ ε.app A).inv ≫
        G.map (eA.hom ≫ F.map φ ≫ eB.inv) ≫
          ((G.mapIso eB) ≪≫ ε.app B).hom = φ := by
  have hA : G.map eA.inv ≫ G.map eA.hom = 𝟙 _ := by
    rw [← Functor.map_comp, eA.inv_hom_id, CategoryTheory.Functor.map_id]
  have hB : G.map eB.inv ≫ G.map eB.hom = 𝟙 _ := by
    rw [← Functor.map_comp, eB.inv_hom_id, CategoryTheory.Functor.map_id]
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hA, reassoc_of% hB]
  change (ε.app A).inv ≫ (F ⋙ G).map φ ≫ (ε.app B).hom = φ
  exact CategoryTheory.NatIso.naturality_1 ε φ

section Readback
variable {Z : Scheme.{u}} {W : Z.Opens} (hW : IsAffineOpen W)

/-- The ORIGINAL inverse-chart restriction round trip, with its ORIGINAL composition/identity units. -/
def specReturn :
    Scheme.Modules.restrictFunctor hW.isoSpec.hom ⋙ Scheme.Modules.restrictFunctor hW.isoSpec.inv ≅
      𝟭 (Spec Γ(Z,W)).Modules :=
  (Scheme.Modules.restrictFunctorComp hW.isoSpec.inv hW.isoSpec.hom).symm ≪≫
    Scheme.Modules.restrictFunctorCongr hW.isoSpec.inv_hom_id ≪≫
      Scheme.Modules.restrictFunctorId

/-- The SAME original W.toScheme restriction, read on the SAME original affine spectrum. -/
def specReadbackIso (P : Z.Modules) :
    (Scheme.Modules.restrictFunctor hW.isoSpec.inv).obj (P.restrict W.ι) ≅ P.restrict hW.fromSpec :=
  (Scheme.Modules.restrictFunctor hW.isoSpec.inv).mapIso (chartRestrictionIso hW P) ≪≫
    (specReturn hW).app (P.restrict hW.fromSpec)

variable (M N : Z.Modules)
  [((Scheme.Modules.restrictFunctor hW.fromSpec).obj M).IsQuasicoherent]

/-- Whole original spectrum readback of the actual original affine-local construction. -/
theorem affineLocalMap_spec_readback (l : M.val.obj (op W) ⟶ N.val.obj (op W)) :
    (specReadbackIso hW M).inv ≫
        (Scheme.Modules.restrictFunctor hW.isoSpec.inv).map (affineLocalMap hW M N l) ≫
          (specReadbackIso hW N).hom = affineSpecMap hW M N l := by
  exact transport_roundTrip
    (Scheme.Modules.restrictFunctor hW.isoSpec.hom)
    (Scheme.Modules.restrictFunctor hW.isoSpec.inv) (specReturn hW)
    (chartRestrictionIso hW M) (chartRestrictionIso hW N) (affineSpecMap hW M N l)

/-- The native original-section readback after inverse-chart restriction and ORIGINAL units. -/
def sectionReadback
    (φ : M.restrict W.ι ⟶ N.restrict W.ι) : M.val.obj (op W) ⟶ N.val.obj (op W) :=
  (Cartier.GeometricAffineHomology.moduleSectionsIso hW M).inv ≫
    (moduleSpecΓFunctor (R := Γ(Z,W))).map
      ((specReadbackIso hW M).inv ≫
        (Scheme.Modules.restrictFunctor hW.isoSpec.inv).map φ ≫
          (specReadbackIso hW N).hom) ≫
      (Cartier.GeometricAffineHomology.moduleSectionsIso hW N).hom

/-- Exact original Γ readback, with no matching map or class certificate. -/
theorem sectionReadback_affineLocalMap (l : M.val.obj (op W) ⟶ N.val.obj (op W)) :
    sectionReadback hW M N (affineLocalMap hW M N l) = l := by
  unfold sectionReadback
  rw [affineLocalMap_spec_readback]
  exact affineSpecMap_sections hW M N l

end Readback

end EnvelopeProperty.DI.AffineLocalMapRestriction
