import EnvelopeProperty.AlgGeom.InvertibleSectionFamilyImage
import EnvelopeProperty.AlgGeom.SchemeGeneratingSectionsUnit
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent

/-! # Genuine global generation makes the whole original base ideal the unit ideal -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace EnvelopeProperty.GeneratedLineBaseIdealUnit
open Scheme.Modules InvertibleSheafBaseIdeal InvertibleSectionFamilyImage
@[instance_reducible] private noncomputable def originalSchemeMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

attribute [local instance] originalSchemeMonoidal

private theorem tensorIso_refl_right {C : Type*} [Category C] [MonoidalCategory C]
    {A B : C} (e : A ≅ B) (D : C) :
    (e ⊗ᵢ Iso.refl D) = whiskerRightIso e D := by
  apply Iso.ext
  simp [tensorHom_def]

private theorem unit_comparison_evaluation {C : Type*} [Category C] [MonoidalCategory C]
    {A Q : C} (e : A ≅ 𝟙_ C) (D : C) (q : A ⊗ D ⟶ Q) :
    ((e ⊗ᵢ Iso.refl D) ≪≫ λ_ D).hom ≫
      (whiskerRightIso e D ≪≫ λ_ D).inv ≫ q = q := by
  rw [tensorIso_refl_right]
  exact Iso.hom_inv_id_assoc _ _

private theorem map_comp_pairing {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B E : C} {T : D} (a : A ⟶ B) (b : B ⟶ E)
    (q : A ⟶ E) (p : F.obj E ⟶ T) (h : q = a ≫ b) :
    F.map q ≫ p = F.map a ≫ F.map b ≫ p := by
  rw [h, F.map_comp, Category.assoc]

private theorem mapped_injection_comparison {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {I : Type*} (f : I → C) [HasCoproduct f]
    [HasCoproduct fun i => F.obj (f i)] [PreservesColimit (Discrete.functor f) F] (i : I) :
    F.map (Sigma.ι f i) ≫ (PreservesCoproduct.iso F f).hom =
      Sigma.ι (fun i => F.obj (f i)) i := by
  apply (cancel_mono (PreservesCoproduct.iso F f).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, PreservesCoproduct.inv_hom]
  simp [sigmaComparison]

private theorem mapped_injection_composite {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {I : Type*} (f : I → C) [HasCoproduct f]
    [HasCoproduct fun i => F.obj (f i)] [PreservesColimit (Discrete.functor f) F]
    (g : I → D) [HasCoproductsOfShape I D] (e : ∀ i, F.obj (f i) ≅ g i) (i : I) :
    F.map (Sigma.ι f i) ≫ ((PreservesCoproduct.iso F f) ≪≫ Sigma.mapIso e).hom =
      (e i).hom ≫ Sigma.ι g i := by
  rw [Iso.trans_hom, ← Category.assoc, mapped_injection_comparison]
  simp

private theorem summand_diagram {C : Type*} [Category C] {A D Q P T : C}
    (a : A ⟶ D) (b : D ⟶ P) (u : A ≅ Q) (j : Q ⟶ P) (q : P ⟶ T)
    (v : Q ⟶ T) (g : A ⟶ T) (hb : a ≫ b = u.hom ≫ j)
    (hq : j ≫ q = v) (hu : u.hom ≫ v = g) : a ≫ (b ≫ q) = g := by
  rw [← Category.assoc, hb, Category.assoc, hq, hu]

/-- The true original top-open value of an original compatible generating section. -/
def topSection {X : Scheme.{u}} {L : X.Modules} (G : L.GeneratingSections) (i : G.I) :
    Γ(L, ⊤) := (G.s i).val (op ⊤)

/-- This original global section defines the SAME actual free basis generator. -/
theorem sectionHom_topSection {X : Scheme.{u}} {L : X.Modules}
    (G : L.GeneratingSections) (i : G.I) :
    SchemeModuleGlobalSections.sectionHom L (topSection G i) =
      SchemeGeneratingSectionsUnit.generatorHom G i := by
  have hs : ModularCurves.moduleSectionsOfTop L (topSection G i) = G.s i := by
    apply PresheafOfModules.sections_ext
    intro W
    exact PresheafOfModules.sections_property (G.s i)
      (homOfLE (le_top : W.unop ≤ ⊤)).op
  change L.unitHomEquiv.symm (ModularCurves.moduleSectionsOfTop L (topSection G i)) = _
  rw [hs]
  exact (congrArg L.unitHomEquiv.symm
    (congrFun (L.freeHomEquiv.apply_symm_apply G.s).symm i)).trans
      (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply G.π i)

/-- The ENTIRE actual original dual-family evaluation is the true original
free evaluation tensored by the original dual, then the original pairing. -/
theorem familyEvaluation_generators {X : Scheme.{u}} {L : X.Modules}
    (hL : IsInvertible L) (G : L.GeneratingSections) :
    familyEvaluation hL (topSection G) =
      (tensorRight (C := X.Modules) (dualObj L)).map G.π ≫ ModularCurves.dualPairing L := by
  let F := tensorRight (C := X.Modules) (dualObj L)
  let : F.IsEquivalence := SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence _ hL.dual
  apply Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit F (fun _ : G.I => unitObj X)
      (fun i => SheafOfModules.ιFree i) (SheafOfModules.isColimitFreeCofan G.I))
  intro i
  have he : F.map (SheafOfModules.ιFree i) ≫ (freeTensorDualIso hL G.I).hom =
      (unitTensorDualIso L).hom ≫ Sigma.ι (fun _ : G.I => dualObj L) i :=
    mapped_injection_composite F (fun _ : G.I => unitObj X)
      (fun _ : G.I => dualObj L) (fun _ => unitTensorDualIso L) i
  have hs : (unitTensorDualIso L).hom ≫ sectionEvaluation L (topSection G i) =
      F.map (SchemeModuleGlobalSections.sectionHom L (topSection G i)) ≫
        ModularCurves.dualPairing L :=
    unit_comparison_evaluation (C := X.Modules)
      (ModularCurves.monoidalUnitObjIso X).symm (dualObj L)
      (F.map (SchemeModuleGlobalSections.sectionHom L (topSection G i)) ≫
        ModularCurves.dualPairing L)
  have hm : F.map (SchemeModuleGlobalSections.sectionHom L (topSection G i)) ≫
      ModularCurves.dualPairing L =
        F.map (SheafOfModules.ιFree i) ≫ F.map G.π ≫ ModularCurves.dualPairing L :=
    map_comp_pairing F (SheafOfModules.ιFree i) G.π
      (SchemeModuleGlobalSections.sectionHom L (topSection G i))
      (ModularCurves.dualPairing L) (sectionHom_topSection G i)
  exact summand_diagram _ _ (unitTensorDualIso L) _ _ _ _ he
    (Sigma.ι_desc _ i) (hs.trans hm)

/-- Actual source global generation DERIVES epimorphic original dual evaluation. -/
theorem familyEvaluation_generators_epi {X : Scheme.{u}} {L : X.Modules}
    (hL : IsInvertible L) (G : L.GeneratingSections) :
    Epi (familyEvaluation hL (topSection G)) := by
  let : (tensorRight (C := X.Modules) (dualObj L)).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence _ hL.dual
  let : IsIso (ModularCurves.dualPairing L) := by
    change IsIso (ModularCurves.monoidalTensorObjIso L (dualObj L) ≪≫ hL.evaluationIso).hom
    infer_instance
  rw [familyEvaluation_generators]
  change Epi ((tensorRight (C := X.Modules) (dualObj L)).map G.π ≫ ModularCurves.dualPairing L)
  let hF : Functor.PreservesEpimorphisms (tensorRight (C := X.Modules) (dualObj L)) :=
    Functor.preservesEpimorphisms_of_adjunction
      (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence _ hL.dual).toAdjunction
  let : Epi G.π := G.epi
  let : Epi ((tensorRight (C := X.Modules) (dualObj L)).map G.π) :=
    @Functor.map_epi X.Modules _ X.Modules _
      (tensorRight (C := X.Modules) (dualObj L)) hF _ _ G.π G.epi
  infer_instance

/-- Genuine original global generation makes the WHOLE ALL-section base ideal
unit on every actual original affine open, including empty schemes. -/
theorem baseIdeal_eq_top_of_generatingSections {X : Scheme.{u}} {L : X.Modules}
    (hL : IsInvertible L) (G : L.GeneratingSections) : baseIdeal hL = ⊤ := by
  let : ((tensorRight (C := X.Modules) (dualObj L)).obj
    (SheafOfModules.free (R := X.ringCatSheaf) G.I)).IsQuasicoherent :=
    freeTensorDual_isQuasicoherent hL G.I
  let : Epi (familyEvaluation hL (topSection G)) := familyEvaluation_generators_epi hL G
  let : (unitObj X).IsQuasicoherent := (isInvertible_unit (X := X)).isQuasicoherent
  have hi : QuasicoherentImageIdeal.imageIdeal _ (familyEvaluation hL (topSection G)) ≤
      baseIdeal hL := by
    rw [familyEvaluation_imageIdeal]
    exact iSup_le fun i => le_iSup (fun s : Γ(L, ⊤) => sectionIdeal hL s) (topSection G i)
  apply top_le_iff.mp
  intro U a ha
  obtain ⟨s, hs⟩ := Scheme.Modules.isQuasicoherent_app_surjective_of_epi U.1 U.2
    (familyEvaluation hL (topSection G)) a
  exact hi U ⟨s, hs⟩

end EnvelopeProperty.GeneratedLineBaseIdealUnit
