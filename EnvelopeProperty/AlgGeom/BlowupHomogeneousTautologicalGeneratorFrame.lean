import EnvelopeProperty.AlgGeom.CartierIdealModules
import EnvelopeProperty.AlgGeom.IdealModuleFunctorial
import EnvelopeProperty.AlgGeom.SchemeModuleGlobalSections

/-! # The original regular ideal basis retains its actual included scalar -/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine

private theorem tildeMap_counit_top {A : CommRingCat.{u}}
    (M : (Spec A).Modules)
    (e : ModuleCat.of A A ⟶ AlgebraicGeometry.moduleSpecΓFunctor.obj M) (a : A) :
    (((AlgebraicGeometry.tilde.functor A).map e ≫ M.fromTildeΓ).val.app (.op ⊤))
        ((AlgebraicGeometry.tilde.toOpen (ModuleCat.of A A) ⊤).hom a) = e.hom a := by
  have hmap := AlgebraicGeometry.tilde.toOpen_map_app e ⊤
  have hc := Scheme.Modules.toOpen_fromTildeΓ_app M ⊤
  have h : AlgebraicGeometry.tilde.toOpen (ModuleCat.of A A) ⊤ ≫
      (AlgebraicGeometry.modulesSpecToSheaf.map
        ((AlgebraicGeometry.tilde.functor A).map e ≫ M.fromTildeΓ)).1.app (.op ⊤) = e := by
    change AlgebraicGeometry.tilde.toOpen (ModuleCat.of A A) ⊤ ≫
      ((AlgebraicGeometry.modulesSpecToSheaf.map ((AlgebraicGeometry.tilde.functor A).map e)).1.app (.op ⊤) ≫
        (AlgebraicGeometry.modulesSpecToSheaf.map M.fromTildeΓ).1.app (.op ⊤)) = e
    have hc' : AlgebraicGeometry.tilde.toOpen
        (AlgebraicGeometry.moduleSpecΓFunctor.obj M) ⊤ ≫
        (AlgebraicGeometry.modulesSpecToSheaf.map M.fromTildeΓ).1.app (.op ⊤) = 𝟙 _ :=
      hc.trans ((AlgebraicGeometry.modulesSpecToSheaf.obj M).1.map_id (.op ⊤))
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (AlgebraicGeometry.modulesSpecToSheaf.map M.fromTildeΓ).1.app (.op ⊤)) hmap).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => e ≫ k) hc').trans (Category.comp_id e))))
  exact congrArg (fun f => f.hom a) h

private theorem unit_hom_ext_top {X : Scheme.{u}} {M : X.Modules}
    {f g : Scheme.Modules.unitObj X ⟶ M}
    (h : f.val.app (.op ⊤) (show Γ(X, ⊤) from 1) =
      g.val.app (.op ⊤) (show Γ(X, ⊤) from 1)) : f = g := by
  apply SheafOfModules.hom_ext
  ext V
  let i := (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
  have hf := PresheafOfModules.naturality_apply f.val i (show Γ(X, ⊤) from 1)
  have hg := PresheafOfModules.naturality_apply g.val i (show Γ(X, ⊤) from 1)
  change f.val.app V (X.presheaf.map i (show Γ(X, ⊤) from 1)) =
    M.presheaf.map i (f.val.app (.op ⊤) (show Γ(X, ⊤) from 1)) at hf
  change g.val.app V (X.presheaf.map i (show Γ(X, ⊤) from 1)) =
    M.presheaf.map i (g.val.app (.op ⊤) (show Γ(X, ⊤) from 1)) at hg
  rw [map_one] at hf hg
  exact hf.trans ((congrArg (fun x => M.presheaf.map i x) h).trans hg.symm)

/-- The SAME actual regular-generator basis, followed by the original ideal
inclusion and original affine unit comparison, is multiplication by the SAME
original entire equation in the native spectrum section ring. -/
theorem regularGeneratorModuleIso_inclusion {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (g : Γ(X, U))
    (hg : g ∈ nonZeroDivisors Γ(X, U)) (hI : I.ideal U = Ideal.span {g}) :
    letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    (I.regularGeneratorModuleIso U g hg hI).hom ≫
        (Scheme.Modules.restrictFunctor U.2.fromSpec).map I.toModulesInclusion ≫
        (Scheme.Modules.restrictUnitIso U.2.fromSpec).hom =
      ModularCurves.unitEndomorphismOfTopSection ((Scheme.ΓSpecIso Γ(X, U)).inv.hom g) := by
  letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let A := Γ(X, U)
  let M := I.toModules.restrict U.2.fromSpec
  let e : A ≃ₗ[A] AlgebraicGeometry.moduleSpecΓFunctor.obj M :=
    ((EnvelopeProperty.regularGeneratorModuleEquiv (I.ideal U) g hg hI).trans
      (I.toModulesSectionsEquiv U).symm).trans (I.toModules.topSectionsEquiv U.2)
  have hto : (AlgebraicGeometry.tilde.toOpen (ModuleCat.of A A) ⊤).hom (1 : A) =
      (1 : Γ(Spec A, ⊤)) := by
    change algebraMap A Γ(Spec A, ⊤) 1 = 1
    exact map_one _
  have hk : (I.regularGeneratorModuleIso U g hg hI).hom.val.app (.op ⊤)
      (1 : Γ(Spec A, ⊤)) = e 1 := by
    have ht := tildeMap_counit_top M e.toModuleIso.hom 1
    rw [hto] at ht
    exact ht
  have he : e 1 = (I.toModules.topSectionsEquiv U.2)
      ((I.toModulesSectionsEquiv U).symm
        ⟨g, hI.symm ▸ Ideal.mem_span_singleton_self g⟩) := by
    change (I.toModules.topSectionsEquiv U.2)
      ((I.toModulesSectionsEquiv U).symm
        (EnvelopeProperty.regularGeneratorModuleEquiv (I.ideal U) g hg hI 1)) = _
    congr 2
    apply Subtype.ext
    exact one_mul g
  apply unit_hom_ext_top
  change (Scheme.Modules.restrictUnitIso U.2.fromSpec).hom.val.app (.op ⊤)
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).map I.toModulesInclusion).val.app (.op ⊤)
        ((I.regularGeneratorModuleIso U g hg hI).hom.val.app (.op ⊤)
          (show Γ(Spec A, ⊤) from 1))) = _
  have hvalue := congrArg (fun s : Γ(M, ⊤) =>
    (Scheme.Modules.restrictUnitIso U.2.fromSpec).hom.val.app (.op ⊤)
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).map I.toModulesInclusion).val.app (.op ⊤) s))
    (hk.trans he)
  have hi := Scheme.Modules.fromSpec_appIso_inv U.2 ⊤ (Scheme.Modules.fromSpec_image_top U.2).le g
  have hr : (Spec A).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec A).Opens) ≤ ⊤)).op
      ((Scheme.ΓSpecIso A).inv.hom g) = (Scheme.ΓSpecIso A).inv.hom g := by
    exact congrArg (fun k : Γ(Spec A, ⊤) ⟶ Γ(Spec A, ⊤) =>
      k.hom ((Scheme.ΓSpecIso A).inv.hom g)) ((Spec A).presheaf.map_id (.op ⊤))
  have hi' : (U.2.fromSpec.appIso ⊤).inv.hom ((Scheme.ΓSpecIso A).inv.hom g) =
      X.presheaf.map (homOfLE (Scheme.Modules.fromSpec_image_top U.2).le).op g :=
    (congrArg (fun s : Γ(Spec A, ⊤) => (U.2.fromSpec.appIso ⊤).inv.hom s) hr).symm.trans hi
  have hincl :
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).map I.toModulesInclusion).val.app (.op ⊤))
        ((I.toModules.topSectionsEquiv U.2)
          ((I.toModulesSectionsEquiv U).symm
            ⟨g, hI.symm ▸ Ideal.mem_span_singleton_self g⟩)) =
      X.presheaf.map (homOfLE (Scheme.Modules.fromSpec_image_top U.2).le).op g := by
    rfl
  have hvalue' := hvalue.trans (congrArg (fun s =>
    (Scheme.Modules.restrictUnitIso U.2.fromSpec).hom.val.app (.op ⊤) s) hincl)
  apply hvalue'.trans
  change (U.2.fromSpec.appIso ⊤).hom
      (X.presheaf.map (homOfLE (Scheme.Modules.fromSpec_image_top U.2).le).op g) =
    (ModularCurves.unitEndomorphismOfTopSection ((Scheme.ΓSpecIso A).inv.hom g)).val.app (.op ⊤)
      (show Γ(Spec A, ⊤) from 1)
  have hcancel := congrArg (fun k : Γ(Spec A, ⊤) ⟶
      Γ(Spec A, ⊤) => k.hom ((Scheme.ΓSpecIso A).inv.hom g))
    (U.2.fromSpec.appIso ⊤).inv_hom_id
  have hscalar :
      (ModularCurves.unitEndomorphismOfTopSection ((Scheme.ΓSpecIso A).inv.hom g)).val.app (.op ⊤)
        (show Γ(Spec A, ⊤) from 1) =
      (Scheme.ΓSpecIso A).inv.hom g := by
    change 1 * (Spec A).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec A).Opens) ≤ ⊤)).op ((Scheme.ΓSpecIso A).inv.hom g) = _
    exact (one_mul _).trans hr
  have hpoint := (congrArg (fun s : Γ(X, U.2.fromSpec ''ᵁ (⊤ : (Spec A).Opens)) =>
    (U.2.fromSpec.appIso ⊤).hom.hom s) hi').symm.trans hcancel
  exact hpoint.trans hscalar.symm

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
