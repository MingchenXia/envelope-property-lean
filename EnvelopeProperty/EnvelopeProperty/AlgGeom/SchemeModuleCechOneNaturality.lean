import ModularCurves.ForMathlib.AcyclicAffineCechComparison

/-! # Original-map naturality of the existing native degree-one Cech comparison -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u

namespace EnvelopeProperty.SchemeModuleCechOneNaturality

variable {X : TopCat.{u}} {I : Type u} (U : I → Opens X)

private theorem sectionsFunctor_additive (X : TopCat.{u}) :
    (globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

attribute [local instance] sectionsFunctor_additive

private abbrev descent {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :=
  InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F)

private def bicomplexMap {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    cechInjectiveResolutionBicomplex U F ⟶ cechInjectiveResolutionBicomplex U G :=
  ((cechSheafComplexFunctor U).mapHomologicalComplex (.up ℕ)).map (descent f)

private def totalMap {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :=
  HomologicalComplex₂.total.map (bicomplexMap U f) (.up ℕ)

private def sectionsMap {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    cechInjectiveResolutionGlobalSectionsComplex F ⟶
      cechInjectiveResolutionGlobalSectionsComplex G :=
  ((globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).map (descent f)

/-- The entire original native vertical-edge square for the actual injective descent. -/
theorem verticalEdge_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    ((cechComplexFunctor U).map f.hom) ≫ cechInjectiveResolutionVerticalEdge U G =
      cechInjectiveResolutionVerticalEdge U F ≫ totalMap U f := by
  have h := congrArg (cechSheafComplexFunctor U).map
    (InjectiveResolution.desc_commutes_zero f (injectiveResolution G) (injectiveResolution F))
  rw [Functor.map_comp, Functor.map_comp] at h
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, cechInjectiveResolutionVerticalEdge_f,
    Category.assoc]
  change ((cechComplexFunctor U).map f.hom).f n ≫
      (cechInjectiveResolutionAugmentation U G).f n ≫
        (cechInjectiveResolutionBicomplex U G).ιTotal (.up ℕ) 0 n n (zero_add n) = _
  unfold totalMap
  erw [HomologicalComplex₂.ιTotal_map]
  have hn := HomologicalComplex.congr_hom h n
  change (cechInjectiveResolutionAugmentation U F).f n ≫
      ((bicomplexMap U f).f 0).f n =
    ((cechComplexFunctor U).map f.hom).f n ≫
      (cechInjectiveResolutionAugmentation U G).f n at hn
  rw [← Category.assoc, ← hn, Category.assoc]

/-- The entire original native horizontal-edge square for that same actual descent. -/
theorem horizontalEdge_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    sectionsMap f ≫ cechInjectiveResolutionHorizontalEdge U G =
      cechInjectiveResolutionHorizontalEdge U F ≫ totalMap U f := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, cechInjectiveResolutionHorizontalEdge_f,
    Category.assoc]
  unfold totalMap
  erw [HomologicalComplex₂.ιTotal_map]
  have h := cechGlobalSectionsAugmentation_naturality
    (F := (injectiveResolution F).cocomplex.X n) (U := U) ((descent f).f n)
  change (globalSectionsFunctor X).map ((descent f).f n) ≫
      cechGlobalSectionsAugmentation ((injectiveResolution G).cocomplex.X n) U ≫
        (cechInjectiveResolutionBicomplex U G).ιTotal (.up ℕ) n 0 n rfl = _
  rw [← Category.assoc, ← h, Category.assoc]
  rfl

private theorem inverseSquare {C : Type*} [Category* C] {A B D E : C}
    (v : A ⟶ B) (w : D ⟶ E) [IsIso v] [IsIso w]
    (f : A ⟶ D) (g : B ⟶ E) (h : f ≫ w = v ≫ g) :
    inv v ≫ f = g ≫ inv w := by
  apply (cancel_mono w).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [h, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

private def derivedMap {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    ((globalSectionsFunctor X).rightDerived 1).obj F ⟶
      ((globalSectionsFunctor X).rightDerived 1).obj G :=
  ((globalSectionsFunctor X).rightDerived 1).map f

private def derivedIso (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    AddCommGrpCat.of (H F 1) ≅ ((globalSectionsFunctor X).rightDerived 1).obj F :=
  AddEquiv.toAddCommGrpIso
    (X := AddCommGrpCat.of (H F 1))
    (Y := ((globalSectionsFunctor X).rightDerived 1).obj F)
    (H.addEquivRightDerivedGlobalSections F 1)

private theorem sheafComparison_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (hU : ⨆ i, U i = ⊤)
    (hF : ∀ i, Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.restrict AddCommGrpCat (U i).isOpenEmbedding).obj F) 1))
    (hG : ∀ i, Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.restrict AddCommGrpCat (U i).isOpenEmbedding).obj G) 1)) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) 1 ≫
        (cechHomologyOneIso_of_subsingleton_H U G hU hG).hom =
      (cechHomologyOneIso_of_subsingleton_H U F hU hF).hom ≫
        AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map f 1) := by
  let vF := HomologicalComplex.homologyMap (cechInjectiveResolutionVerticalEdge U F) 1
  let vG := HomologicalComplex.homologyMap (cechInjectiveResolutionVerticalEdge U G) 1
  let hF' := HomologicalComplex.homologyMap (cechInjectiveResolutionHorizontalEdge U F) 1
  let hG' := HomologicalComplex.homologyMap (cechInjectiveResolutionHorizontalEdge U G) 1
  let c := HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) 1
  let t := HomologicalComplex.homologyMap (totalMap U f) 1
  let g := HomologicalComplex.homologyMap (sectionsMap f) 1
  let d := derivedMap f
  let eF := derivedIso F
  let eG := derivedIso G
  let : (globalSectionsFunctor X).Additive := sectionsFunctor_additive X
  let rF := ((injectiveResolution F).isoRightDerivedObj
    (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (globalSectionsFunctor X) 1).inv
  let rG := ((injectiveResolution G).isoRightDerivedObj
    (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (globalSectionsFunctor X) 1).inv
  let : QuasiIsoAt (cechInjectiveResolutionHorizontalEdge U F) 1 :=
    cechInjectiveResolutionHorizontalEdge_quasiIsoAt_one U F hU
  let : QuasiIsoAt (cechInjectiveResolutionHorizontalEdge U G) 1 :=
    cechInjectiveResolutionHorizontalEdge_quasiIsoAt_one U G hU
  have hv : c ≫ vG = vF ≫ t := by
    simpa only [HomologicalComplex.homologyMap_comp] using
      congrArg (fun k => HomologicalComplex.homologyMap k 1) (verticalEdge_naturality U f)
  have hh : g ≫ hG' = hF' ≫ t := by
    simpa only [HomologicalComplex.homologyMap_comp] using
      congrArg (fun k => HomologicalComplex.homologyMap k 1) (horizontalEdge_naturality U f)
  have hi : inv hF' ≫ g = t ≫ inv hG' := inverseSquare hF' hG' g t hh
  have hr : rF ≫ d = g ≫ rG :=
    InjectiveResolution.isoRightDerivedObj_inv_naturality
      (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      f (injectiveResolution F)
      (injectiveResolution G) (descent f)
      (InjectiveResolution.desc_commutes_zero f (injectiveResolution G) (injectiveResolution F))
      (globalSectionsFunctor X) 1
  have he : AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map f 1) ≫ eG.hom = eF.hom ≫ d := by
    ext x
    exact H.addEquivRightDerivedGlobalSections_naturality f 1 x
  have hei₀ := inverseSquare eF.hom eG.hom
    (AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map f 1)) d he
  have heF : inv eF.hom = eF.inv := IsIso.inv_eq_of_hom_inv_id eF.hom_inv_id
  have heG : inv eG.hom = eG.inv := IsIso.inv_eq_of_hom_inv_id eG.hom_inv_id
  have hei : eF.inv ≫ AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map f 1) = d ≫ eG.inv := by
    simpa only [heF, heG] using hei₀
  change c ≫ (vG ≫ inv hG' ≫ rG ≫ eG.inv) =
    (vF ≫ inv hF' ≫ rF ≫ eF.inv) ≫ AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map f 1)
  calc
    _ = vF ≫ (t ≫ inv hG') ≫ rG ≫ eG.inv := by simp only [← Category.assoc, hv]
    _ = vF ≫ (inv hF' ≫ g) ≫ rG ≫ eG.inv := by rw [← hi]
    _ = vF ≫ inv hF' ≫ rF ≫ (d ≫ eG.inv) := by
      simpa only [Category.assoc] using
        congrArg (fun k => vF ≫ inv hF' ≫ k ≫ eG.inv) hr.symm
    _ = vF ≫ inv hF' ≫ rF ≫ (eF.inv ≫ AddCommGrpCat.ofHom
        (CategoryTheory.Sheaf.H.map f 1)) := by
      simpa only [Category.assoc] using
        congrArg (fun k => vF ≫ inv hF' ≫ rF ≫ k) hei.symm
    _ = _ := by simp only [Category.assoc]

/-- The existing actual affine-QC degree-one comparison commutes with every original map. -/
theorem affineHOneIso_naturality {Y : Scheme.{u}} {M N : Y.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    {J : Type u} (V : J → Y.Opens) (hV : IsOpenCover V)
    (hVa : ∀ i, IsAffineOpen (V i)) :
    HomologicalComplex.homologyMap
        ((cechComplexFunctor V).map ((Scheme.Modules.toSheaf Y).map f).hom) 1 ≫
      (Scheme.Modules.cechHomologyOneIso_of_affine_openCover N V hV hVa).hom =
    (Scheme.Modules.cechHomologyOneIso_of_affine_openCover M V hV hVa).hom ≫
      AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map ((Scheme.Modules.toSheaf Y).map f) 1) :=
  sheafComparison_naturality V ((Scheme.Modules.toSheaf Y).map f) hV
    (fun i => Scheme.Modules.restrict_subsingleton_H_of_isAffineOpen M (V i) (hVa i) 0)
    (fun i => Scheme.Modules.restrict_subsingleton_H_of_isAffineOpen N (V i) (hVa i) 0)

end EnvelopeProperty.SchemeModuleCechOneNaturality
