import EnvelopeProperty.Projective.SubvarietyMultiplierConeGeneratorsTensor

/-! # Original included finite generators have exactly the whole ideal image -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierConeGeneratorsEvaluation
open Scheme.Modules SchemeGeneratingSectionsUnit InvertibleSectionFamilyImage
open InvertibleSheafBaseIdeal MultiplierConeGeneratorsTensor
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem sectionHom_topValue {Y : Scheme.{u}} (L : Y.Modules) (f : unitObj Y ⟶ L) :
    SchemeModuleGlobalSections.sectionHom L (f.val.app (.op ⊤) (1 : Γ(Y, ⊤))) = f := by
  apply L.unitHomEquiv.injective
  rw [SchemeModuleGlobalSections.sectionHom, Equiv.apply_symm_apply]
  apply Subtype.ext
  funext U
  change L.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op
    ((L.unitHomEquiv f).val (.op ⊤)) = (L.unitHomEquiv f).val U
  exact (L.unitHomEquiv f).property (homOfLE (le_top : U.unop ≤ ⊤)).op

/-- The same original included generator, as an actual whole original section. -/
def includedSection {Y : Scheme.{u}} (K : Y.IdealSheafData) (L : Y.Modules)
    (G : (K.toModules ⊗ L).GeneratingSections) (a : G.I) : Γ(L, ⊤) :=
  (generatorHom G a ≫ idealTensorInclusion K L).val.app (.op ⊤) (1 : Γ(Y, ⊤))

/-- The actual section-Hom constructor recovers the exact original basis
map, original epimorphic evaluation and original tensor-ideal inclusion. -/
theorem includedSection_sectionHom {Y : Scheme.{u}} (K : Y.IdealSheafData) (L : Y.Modules)
    (G : (K.toModules ⊗ L).GeneratingSections) (a : G.I) :
    SchemeModuleGlobalSections.sectionHom L (includedSection K L G a) =
      generatorHom G a ≫ idealTensorInclusion K L :=
  sectionHom_topValue L _

private theorem map_coproduct_basis {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {ι : Type*} (f : ι → C)
    [HasCoproduct f] [HasCoproduct fun a => F.obj (f a)]
    [PreservesColimit (Discrete.functor f) F] (a : ι) :
    F.map (Sigma.ι f a) ≫ (PreservesCoproduct.iso F f).hom =
      Sigma.ι (fun a => F.obj (f a)) a := by
  apply (cancel_mono (PreservesCoproduct.iso F f).inv).mp
  calc
    _ = F.map (Sigma.ι f a) := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = _ := by rw [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]

private theorem freeTensorDual_basis {Y : Scheme.{u}} (L : Y.Modules) (hL : IsInvertible L)
    (ι : Type u) (a : ι) :
    (tensorRight (C := Y.Modules) (dualObj L)).map (SheafOfModules.ιFree a) ≫
      (freeTensorDualIso hL ι).hom =
      (unitTensorDualIso L).hom ≫ Sigma.ι (fun _ : ι => dualObj L) a := by
  let F := tensorRight (C := Y.Modules) (dualObj L)
  let : F.IsEquivalence := SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence _ hL.dual
  have hb := map_coproduct_basis F (fun _ : ι => unitObj Y) a
  change F.map (SheafOfModules.ιFree a) ≫
      (PreservesCoproduct.iso F (fun _ : ι => unitObj Y)).hom = _ at hb
  change F.map (SheafOfModules.ιFree a) ≫
      (PreservesCoproduct.iso F (fun _ : ι => unitObj Y)).hom ≫
      (Sigma.mapIso (fun _ : ι => unitTensorDualIso L)).hom = _
  rw [← Category.assoc, hb, Sigma.ι_mapIso_hom]

private theorem unitTensorDualIso_eq {Y : Scheme.{u}} (L : Y.Modules) :
    unitTensorDualIso L = SchemeTensorUnitSections.leftUnitIso (dualObj L) := by
  apply Iso.ext
  simp only [unitTensorDualIso, SchemeTensorUnitSections.leftUnitIso,
    Iso.trans_hom, tensorIso_hom, Iso.symm_hom, Iso.refl_hom,
    tensorHom_id, whiskerRightIso_hom]

/-- The native actual family evaluation is literally the right-tensor of
its SAME original free-to-line map followed by the SAME native pairing. -/
theorem familyEvaluation_eq_tensorEvaluation {Y : Scheme.{u}} (L : Y.Modules) (hL : IsInvertible L)
    (ι : Type u) (σ : SheafOfModules.free (R := Y.ringCatSheaf) ι ⟶ L)
    (s : ι → Γ(L, ⊤))
    (hs : ∀ a, SchemeModuleGlobalSections.sectionHom L (s a) = SheafOfModules.ιFree a ≫ σ) :
    familyEvaluation hL s =
      (tensorRight (C := Y.Modules) (dualObj L)).map σ ≫ ModularCurves.dualPairing L := by
  let F := tensorRight (C := Y.Modules) (dualObj L)
  let : F.IsEquivalence := SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence _ hL.dual
  apply Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit F (fun _ : ι => unitObj Y)
      (fun a => SheafOfModules.ιFree a) (SheafOfModules.isColimitFreeCofan ι))
  intro a
  change F.map (SheafOfModules.ιFree a) ≫ familyEvaluation hL s =
    F.map (SheafOfModules.ιFree a) ≫ (F.map σ ≫ ModularCurves.dualPairing L)
  calc
    _ = (unitTensorDualIso L).hom ≫ sectionEvaluation L (s a) := by
      rw [familyEvaluation, ← Category.assoc, freeTensorDual_basis,
        Category.assoc, Sigma.ι_desc]
    _ = F.map (SheafOfModules.ιFree a ≫ σ) ≫ ModularCurves.dualPairing L := by
      rw [unitTensorDualIso_eq, sectionEvaluation]
      change (SchemeTensorUnitSections.leftUnitIso (dualObj L)).hom ≫
        ((SchemeTensorUnitSections.leftUnitIso (dualObj L)).inv ≫
          (SchemeModuleGlobalSections.sectionHom L (s a) ▷ dualObj L) ≫
          ModularCurves.dualPairing L) = _
      rw [Iso.hom_inv_id_assoc, hs a]
      rfl
    _ = _ := by rw [F.map_comp, Category.assoc]

private theorem imageIdeal_eq_of_epi_factor {Y : Scheme.{u}} {A : Y.Modules}
    [A.IsQuasicoherent] (α : A ⟶ unitObj Y) (K : Y.IdealSheafData)
    (p : A ⟶ K.toModules) [Epi p] (hp : p ≫ K.toModulesInclusion = α) :
    QuasicoherentImageIdeal.imageIdeal A α = K := by
  apply le_antisymm
  · exact (QuasicoherentImageFactorization.imageIdeal_le_iff_factor α K).mpr ⟨p, hp⟩
  · let J := QuasicoherentImageIdeal.imageIdeal A α
    let : StrongEpi p := strongEpi_of_epi p
    let F : StrongEpiMonoFactorisation α :=
      { I := K.toModules, m := K.toModulesInclusion, e := p, fac := hp }
    let G : MonoFactorisation α :=
      { I := J.toModules, m := J.toModulesInclusion,
        e := QuasicoherentImageModule.imageFactor α,
        fac := QuasicoherentImageModule.imageFactor_inclusion α }
    let l : K.toModules ⟶ J.toModules := F.toMonoIsImage.lift G
    have hl : l ≫ J.toModulesInclusion = K.toModulesInclusion := F.toMonoIsImage.lift_fac G
    intro U c hc
    let z : Γ(K.toModules, U.1) := (K.toModulesSectionsEquiv U).symm ⟨c, hc⟩
    have hz := (J.toModulesSectionsEquiv U (l.val.app (op U.1) z)).property
    have he := congrArg (fun q : K.toModules ⟶ unitObj Y => q.val.app (op U.1) z) hl
    change (l.val.app (op U.1) z).1 = c at he
    exact he ▸ hz

/-- Genuine original global generators of the actual ideal polarization
have exactly the WHOLE original ideal as their included evaluation image.
No desired image or replacement base-ideal certificate is an input. -/
theorem includedEvaluation_imageIdeal {Y : Scheme.{u}} (K : Y.IdealSheafData) (L : Y.Modules)
    (hL : IsInvertible L) (G : (K.toModules ⊗ L).GeneratingSections) :
    let _ := freeTensorDual_isQuasicoherent hL G.I
    QuasicoherentImageIdeal.imageIdeal _
      (familyEvaluation hL (includedSection K L G)) = K := by
  let _ := freeTensorDual_isQuasicoherent hL G.I
  let q := coefficientEpimorphism K L hL G
  let : Epi q := coefficientEpimorphism_epi K L hL G
  apply imageIdeal_eq_of_epi_factor _ K q
  rw [coefficientEpimorphism_inclusion]
  exact (familyEvaluation_eq_tensorEvaluation L hL G.I
    (G.π ≫ idealTensorInclusion K L) (includedSection K L G) fun a =>
      (includedSection_sectionHom K L G a).trans (Category.assoc _ _ _)).symm

end EnvelopeProperty.ProjSubvariety.MultiplierConeGeneratorsEvaluation
