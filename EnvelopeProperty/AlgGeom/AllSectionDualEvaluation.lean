import EnvelopeProperty.AlgGeom.SchemeModulePrincipalEvaluation
import ModularCurves.ForMathlib.SchemeModuleRestrictLimits

/-! # Whole original dual evaluation from the SAME original free evaluation -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace EnvelopeProperty.AllSectionDualEvaluation
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

/-- The ENTIRE actual original dual-family evaluation is the true original
free evaluation tensored by the original dual, then the original pairing. -/
theorem familyEvaluation_all {X : Scheme.{u}} {L : X.Modules}
    (hL : IsInvertible L)  :
    familyEvaluation hL (fun s : Γ(L, ⊤) => s) =
      (tensorRight (C := X.Modules) (dualObj L)).map (SchemeModulePrincipalEvaluation.evaluation L) ≫ ModularCurves.dualPairing L := by
  let F := tensorRight (C := X.Modules) (dualObj L)
  let : F.IsEquivalence := SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence _ hL.dual
  apply Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit F (fun _ : Γ(L, ⊤) => unitObj X)
      (fun i => SheafOfModules.ιFree i) (SheafOfModules.isColimitFreeCofan Γ(L, ⊤)))
  intro i
  have he : F.map (SheafOfModules.ιFree i) ≫ (freeTensorDualIso hL Γ(L, ⊤)).hom =
      (unitTensorDualIso L).hom ≫ Sigma.ι (fun _ : Γ(L, ⊤) => dualObj L) i :=
    mapped_injection_composite F (fun _ : Γ(L, ⊤) => unitObj X)
      (fun _ : Γ(L, ⊤) => dualObj L) (fun _ => unitTensorDualIso L) i
  have hs : (unitTensorDualIso L).hom ≫ sectionEvaluation L i =
      F.map (SchemeModuleGlobalSections.sectionHom L i) ≫
        ModularCurves.dualPairing L :=
    unit_comparison_evaluation (C := X.Modules)
      (ModularCurves.monoidalUnitObjIso X).symm (dualObj L)
      (F.map (SchemeModuleGlobalSections.sectionHom L i) ≫
        ModularCurves.dualPairing L)
  have hm : F.map (SchemeModuleGlobalSections.sectionHom L i) ≫
      ModularCurves.dualPairing L =
        F.map (SheafOfModules.ιFree i) ≫ F.map (SchemeModulePrincipalEvaluation.evaluation L) ≫ ModularCurves.dualPairing L :=
    map_comp_pairing F (SheafOfModules.ιFree i) (SchemeModulePrincipalEvaluation.evaluation L)
      (SchemeModuleGlobalSections.sectionHom L i)
      (ModularCurves.dualPairing L) (SchemeModulePrincipalEvaluation.sectionHom_evaluation L i)
  exact summand_diagram _ _ (unitTensorDualIso L) _ _ _ _ he
    (Sigma.ι_desc _ i) (hs.trans hm)


/-- The true image of ALL original dual evaluations is the SAME whole base ideal. -/
theorem familyEvaluation_imageIdeal {X : Scheme.{u}} {L : X.Modules} (hL : IsInvertible L) :
    let : ((tensorRight (C := X.Modules) (dualObj L)).obj
      (SheafOfModules.free (R := X.ringCatSheaf) Γ(L, ⊤))).IsQuasicoherent :=
        freeTensorDual_isQuasicoherent hL Γ(L, ⊤)
    QuasicoherentImageIdeal.imageIdeal _ (familyEvaluation hL (fun s : Γ(L, ⊤) => s)) =
      baseIdeal hL := by
  let : ((tensorRight (C := X.Modules) (dualObj L)).obj
    (SheafOfModules.free (R := X.ringCatSheaf) Γ(L, ⊤))).IsQuasicoherent :=
      freeTensorDual_isQuasicoherent hL Γ(L, ⊤)
  exact InvertibleSectionFamilyImage.familyEvaluation_imageIdeal hL (fun s : Γ(L, ⊤) => s)

private theorem epi_map_whiskerRight {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    {A B : C} (e : A ⟶ B) (Q : C) [Epi (F.map e)]
    [(tensorRight (C := D) (F.obj Q)).PreservesEpimorphisms] :
    Epi (F.map (e ▷ Q)) := by
  let : Epi ((tensorRight (C := D) (F.obj Q)).map (F.map e)) :=
    Functor.map_epi _ _
  let : Epi ((F.map e) ▷ F.obj Q) := inferInstanceAs
    (Epi ((tensorRight (C := D) (F.obj Q)).map (F.map e)))
  have he := Functor.OplaxMonoidal.δ_natural_left F e Q
  have hh : Epi (Functor.OplaxMonoidal.δ F A Q ≫ (F.map e) ▷ F.obj Q) := by
    infer_instance
  have : Epi (F.map (e ▷ Q) ≫ Functor.OplaxMonoidal.δ F B Q) := he ▸ hh
  exact (epi_comp_iff_of_isIso (F.map (e ▷ Q))
    (Functor.OplaxMonoidal.δ F B Q)).mp this

/-- Actual generation on the SAME principal open DERIVES epimorphic
restriction of the ENTIRE original dual evaluation of ALL original sections. -/
theorem restrict_familyEvaluation_epi {X B : Scheme.{u}} (π : X ⟶ B)
    {L : X.Modules} (hL : IsInvertible L) [CompactSpace X] [X.IsSeparated]
    (r : Γ(B, ⊤)) (G : (L.restrict (π ⁻¹ᵁ B.basicOpen r).ι).GeneratingSections) :
    Epi ((restrictFunctor (π ⁻¹ᵁ B.basicOpen r).ι).map
      (familyEvaluation hL (fun s : Γ(L, ⊤) => s))) := by
  let P := π ⁻¹ᵁ B.basicOpen r
  let F := restrictFunctor P.ι
  let : (Scheme.Modules.pullback P.ι).Monoidal := Scheme.Modules.pullbackMonoidal P.ι
  let : F.Monoidal := Functor.Monoidal.transport (restrictFunctorIsoPullback P.ι).symm
  let : L.IsQuasicoherent := hL.isQuasicoherent
  let : Epi (F.map (SchemeModulePrincipalEvaluation.evaluation L)) :=
    SchemeModulePrincipalEvaluation.restrict_evaluation_epi π L r G
  have hD : IsInvertible (F.obj (dualObj L)) :=
    (hL.dual.pullback P.ι).of_iso ((restrictFunctorIsoPullback P.ι).app (dualObj L))
  let hT : (tensorRight (C := P.toScheme.Modules) (F.obj (dualObj L))).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence _ hD).toAdjunction
  let : IsIso (ModularCurves.dualPairing L) := by
    change IsIso (ModularCurves.monoidalTensorObjIso L (dualObj L) ≪≫ hL.evaluationIso).hom
    infer_instance
  have hE := epi_map_whiskerRight F (SchemeModulePrincipalEvaluation.evaluation L) (dualObj L)
  rw [familyEvaluation_all, F.map_comp]
  let : Epi (F.map ((tensorRight (C := X.Modules) (dualObj L)).map
    (SchemeModulePrincipalEvaluation.evaluation L))) := hE
  infer_instance

end EnvelopeProperty.AllSectionDualEvaluation
