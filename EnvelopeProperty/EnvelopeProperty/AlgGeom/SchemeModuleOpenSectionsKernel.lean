import ModularCurves.ForMathlib.SchemeModuleBaseCechZero
import ModularCurves.ForMathlib.SchemeModuleCechRestrict

/-! # Original whole open sections as the SAME actual Cech kernel -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleOpenSectionsKernel

open Scheme.Modules

private theorem postcompose_three {C : Type*} [Category* C] {P Q R S T : C}
    {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ S} {d : P ⟶ S}
    (h : a ≫ b ≫ c = d) (e : S ⟶ T) : a ≫ b ≫ c ≫ e = d ≫ e := by
  simpa only [Category.assoc] using congrArg (fun f => f ≫ e) h

private def componentIso {A : Type u} [CommRing A]
    {C D : CochainComplex (ModuleCat.{u} A) ℕ} (e : C ≅ D) (i : ℕ) :
    C.X i ≅ D.X i where
  hom := e.hom.f i
  inv := e.inv.f i
  hom_inv_id := by
    simp [← HomologicalComplex.comp_f, e.hom_inv_id]
  inv_hom_id := by
    simp [← HomologicalComplex.comp_f, e.inv_hom_id]

private theorem componentIso_comm {A : Type u} [CommRing A]
    {C D : CochainComplex (ModuleCat.{u} A) ℕ} (e : C ≅ D) (i j : ℕ) :
    C.d i j ≫ (componentIso e j).hom = (componentIso e i).hom ≫ D.d i j :=
  (e.hom.comm i j).symm

private def complexKernelIso {A : Type u} [CommRing A]
    {C D : CochainComplex (ModuleCat.{u} A) ℕ} (e : C ≅ D) :
    ModuleCat.of A (LinearMap.ker (C.d 0 1).hom) ≅
      ModuleCat.of A (LinearMap.ker (D.d 0 1).hom) :=
  (ModuleCat.kernelIsoKer (C.d 0 1)).symm ≪≫
    kernel.mapIso (C.d 0 1) (D.d 0 1)
      (componentIso e 0) (componentIso e 1)
      (componentIso_comm e 0 1) ≪≫
    ModuleCat.kernelIsoKer (D.d 0 1)

/-- The actual whole open-section module retains its SAME original base
coefficient action under restriction to the original open scheme. -/
def openSectionsRestrictIso {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    (W : X.Opens) :
    (baseModulePresheaf π M).obj (op W) ≅
      baseSections (W.ι ≫ π) (M.restrict W.ι) :=
  (baseModulePresheaf π M).mapIso (eqToIso W.ι_image_top).op ≪≫
    (baseModulePresheafRestrictAppIso π W.ι M ⊤).symm

private theorem openSectionsRestrictIso_restrict {X S : Scheme.{u}}
    (π : X ⟶ S) (M : X.Modules) (W : X.Opens) (V : W.toScheme.Opens) :
    (openSectionsRestrictIso π M W).hom ≫
        (baseModulePresheaf (W.ι ≫ π) (M.restrict W.ι)).map
          (homOfLE (le_top : V ≤ ⊤)).op ≫
        (baseModulePresheafRestrictAppIso π W.ι M V).hom =
      (baseModulePresheaf π M).map
        (homOfLE (show W.ι ''ᵁ V ≤ W from by
          calc
            W.ι ''ᵁ V ≤ W.ι ''ᵁ ⊤ := W.ι.image_mono le_top
            _ = W := W.ι_image_top)).op := by
  dsimp only [openSectionsRestrictIso, Iso.trans_hom, Iso.symm_hom]
  rw [baseModulePresheafRestrictAppIso_hom_naturality]
  simp only [Category.assoc]
  change (baseModulePresheaf π M).map _ ≫ (baseModulePresheaf π M).map _ =
    (baseModulePresheaf π M).map _
  rw [← Functor.map_comp]
  exact congrArg (baseModulePresheaf π M).map (Subsingleton.elim _ _)

private theorem complexKernelIso_hom_subtype {A : Type u} [CommRing A]
    {C D : CochainComplex (ModuleCat.{u} A) ℕ} (e : C ≅ D) :
    (complexKernelIso e).hom ≫ ModuleCat.ofHom (LinearMap.ker (D.d 0 1).hom).subtype =
      ModuleCat.ofHom (LinearMap.ker (C.d 0 1).hom).subtype ≫ e.hom.f 0 := by
  simp only [complexKernelIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ModuleCat.kernelIsoKer_hom_ker_subtype, kernel.mapIso_hom, kernel.map, kernel.lift_ι]
  rw [← ModuleCat.kernelIsoKer_hom_ker_subtype (C.d 0 1)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

private theorem complexKernelIso_inv_subtype {A : Type u} [CommRing A]
    {C D : CochainComplex (ModuleCat.{u} A) ℕ} (e : C ≅ D) :
    (complexKernelIso e).inv ≫ ModuleCat.ofHom (LinearMap.ker (C.d 0 1).hom).subtype =
      ModuleCat.ofHom (LinearMap.ker (D.d 0 1).hom).subtype ≫ e.inv.f 0 := by
  apply (cancel_epi (complexKernelIso e).hom).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, complexKernelIso_hom_subtype,
    Category.assoc]
  have he : e.hom.f 0 ≫ e.inv.f 0 = 𝟙 (C.X 0) := by
    simp [← HomologicalComplex.comp_f, e.hom_inv_id]
  rw [he, Category.comp_id]

private theorem sheafAugmentation_app_π {A : Type u} [CommRing A]
    {T : TopCat.{u}} (F : TopCat.Sheaf (ModuleCat.{u} A) T)
    {ι : Type u} (U : ι → Opens T) (W : Opens T) (i : Fin 1 → ι) :
    (TopCat.Sheaf.moduleCechAugmentation F U).hom.app (op W) ≫
        (TopCat.Sheaf.moduleCechTermSectionsIso F U 0 W).hom ≫
        Pi.π (fun j : Fin 1 → ι =>
          F.obj.obj (op (W ⊓ ∏ᶜ fun k : Fin 1 => U (j k)))) i =
      F.obj.map (homOfLE (show W ⊓ (∏ᶜ fun k : Fin 1 => U (i k)) ≤ W
        from inf_le_left)).op := by
  erw [TopCat.Sheaf.moduleCechTermSectionsIso_hom_π, ← Category.assoc]
  have haugmentation :
      (TopCat.Sheaf.moduleCechAugmentation F U).hom.app (op W) ≫
          (Pi.π (TopCat.Sheaf.moduleCechTermFactor F U 0) i).hom.app (op W) =
        ((TopCat.Sheaf.toRestrict (ModuleCat A)
          (∏ᶜ fun k : Fin 1 => U (i k))).app F).hom.app (op W) := by
    exact congrArg (fun f => f.hom.app (op W))
      (Pi.lift_π (fun j : Fin 1 → ι =>
        (TopCat.Sheaf.toRestrict (ModuleCat A)
          (∏ᶜ fun k : Fin 1 => U (j k))).app F) i)
  rw [haugmentation]
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  rw [← F.obj.map_comp]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

private theorem augmentation_restrict_factor {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (W : X.Opens)
    (i : Fin 1 → ι) :
    (TopCat.Sheaf.moduleCechAugmentation (baseModuleTopSheaf π M) U).hom.app (op W) ≫
        (baseModuleCechTermAppRestrictIso π M U W 0).hom ≫
        Pi.π (fun j : Fin 1 → ι => baseCechFactor
          (W.ι ≫ π) (M.restrict W.ι) (fun a => W.ι ⁻¹ᵁ U a) 0 j) i =
      (baseModulePresheaf π M).map
        (homOfLE (show W ⊓ (∏ᶜ fun k : Fin 1 => U (i k)) ≤ W
          from inf_le_left)).op ≫
        (baseModuleCechFactorAppRestrictIso π M U W 0 i).hom := by
  have hp := congrArg
    (fun f => (TopCat.Sheaf.moduleCechAugmentation
      (baseModuleTopSheaf π M) U).hom.app (op W) ≫ f)
    (baseModuleCechTermAppRestrictIso_hom_π π M U W 0 i)
  have hq := congrArg
    (fun f => (TopCat.Sheaf.moduleCechAugmentation
      (baseModuleTopSheaf π M) U).hom.app (op W) ≫ f)
    (TopCat.Sheaf.moduleCechTermSectionsIso_hom_π
      (baseModuleTopSheaf π M) U 0 W i)
  have hs := sheafAugmentation_app_π (baseModuleTopSheaf π M) U W i
  have hfactor := hq.symm.trans hs
  exact hp.trans (postcompose_three hfactor
    (baseModuleCechFactorAppRestrictIso π M U W 0 i).hom)

private theorem restriction_to_factor {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (W : X.Opens)
    (i : Fin 1 → ι) :
    (baseModulePresheaf π M).map
        (homOfLE (show W ⊓ (∏ᶜ fun k : Fin 1 => U (i k)) ≤ W
          from inf_le_left)).op ≫
        (baseModuleCechFactorAppRestrictIso π M U W 0 i).hom =
      (openSectionsRestrictIso π M W).hom ≫
        (baseModulePresheaf (W.ι ≫ π) (M.restrict W.ι)).map
          (homOfLE (le_top : (∏ᶜ fun k : Fin 1 => W.ι ⁻¹ᵁ U (i k)) ≤ ⊤)).op := by
  apply (cancel_mono (baseModulePresheafRestrictAppIso π W.ι M
    (∏ᶜ fun k : Fin 1 => W.ι ⁻¹ᵁ U (i k))).hom).1
  erw [Category.assoc, openSectionsRestrictIso_restrict π M W
    (∏ᶜ fun k : Fin 1 => W.ι ⁻¹ᵁ U (i k))]
  dsimp only [baseModuleCechFactorAppRestrictIso, Iso.trans_hom, Iso.symm_hom]
  change ((baseModulePresheaf π M).map _ ≫
      (baseModulePresheaf π M).map _ ≫
      (baseModulePresheafRestrictAppIso π W.ι M
        (∏ᶜ fun k : Fin 1 => W.ι ⁻¹ᵁ U (i k))).inv) ≫
      (baseModulePresheafRestrictAppIso π W.ι M
        (∏ᶜ fun k : Fin 1 => W.ι ⁻¹ᵁ U (i k))).hom =
    (baseModulePresheaf π M).map _
  simp only [Category.assoc]
  change (baseModulePresheaf π M).map _ ≫ (baseModulePresheaf π M).map _ =
    (baseModulePresheaf π M).map _
  rw [← Functor.map_comp]
  exact congrArg (baseModulePresheaf π M).map (Subsingleton.elim _ _)

private theorem augmentation_restrict {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (W : X.Opens) :
    (TopCat.Sheaf.moduleCechAugmentation (baseModuleTopSheaf π M) U).hom.app (op W) ≫
        (baseModuleCechTermAppRestrictIso π M U W 0).hom =
      (openSectionsRestrictIso π M W).hom ≫
        baseCechAugmentation (W.ι ≫ π) (M.restrict W.ι)
          (fun i => W.ι ⁻¹ᵁ U i) := by
  apply Pi.hom_ext
  intro i
  have hp := augmentation_restrict_factor π M U W i
  have hq := restriction_to_factor π M U W i
  have hr := congrArg (fun f => (openSectionsRestrictIso π M W).hom ≫ f)
    (baseCechAugmentation_comp_π (W.ι ≫ π) (M.restrict W.ι)
      (fun a => W.ι ⁻¹ᵁ U a) i)
  exact (Category.assoc _ _ _).trans
    (hp.trans (hq.trans (hr.symm.trans (Category.assoc _ _ _).symm)))

private theorem kernel_transport_augmentation {A : Type u} [CommRing A]
    {C D : CochainComplex (ModuleCat.{u} A) ℕ} (e : C ≅ D)
    {P : ModuleCat.{u} A}
    (r : P ⟶ ModuleCat.of A (LinearMap.ker (D.d 0 1).hom))
    (a : P ⟶ C.X 0)
    (h : r ≫ ModuleCat.ofHom (LinearMap.ker (D.d 0 1).hom).subtype = a ≫ e.hom.f 0) :
    r ≫ (complexKernelIso e).inv ≫
        ModuleCat.ofHom (LinearMap.ker (C.d 0 1).hom).subtype = a := by
  rw [complexKernelIso_inv_subtype, ← Category.assoc, h, Category.assoc]
  have he : e.hom.f 0 ≫ e.inv.f 0 = 𝟙 (C.X 0) := by
    simp [← HomologicalComplex.comp_f, e.hom_inv_id]
  rw [he, Category.comp_id]

private theorem kernel_iso_augmentation {A : Type u} [CommRing A]
    {C D : CochainComplex (ModuleCat.{u} A) ℕ} (e : C ≅ D)
    {P Q : ModuleCat.{u} A} (r : P ≅ Q)
    (b : Q ≅ ModuleCat.of A (LinearMap.ker (D.d 0 1).hom))
    (a : P ⟶ C.X 0)
    (h : r.hom ≫ b.hom ≫ ModuleCat.ofHom (LinearMap.ker (D.d 0 1).hom).subtype =
      a ≫ e.hom.f 0) :
    (r ≪≫ b ≪≫ (complexKernelIso e).symm).hom ≫
        ModuleCat.ofHom (LinearMap.ker (C.d 0 1).hom).subtype = a := by
  have hk := kernel_transport_augmentation e (r.hom ≫ b.hom) a
    ((Category.assoc _ _ _).trans h)
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using hk

private theorem preimage_isOpenCover {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : IsOpenCover U) (W : X.Opens) :
    IsOpenCover (fun i => W.ι ⁻¹ᵁ U i) := by
  change (⨆ i, W.ι ⁻¹ᵁ U i) = ⊤
  apply le_antisymm le_top
  intro x _
  have hx : W.ι x ∈ ⨆ i, U i := by
    rw [show (⨆ i, U i) = ⊤ from hU]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

/-- The original WHOLE section module on ANY actual open is the kernel of
the SAME actual sheaf-level Cech differential evaluated on that original open. -/
def openSectionsKernelIso {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U) (W : X.Opens) :
    (baseModulePresheaf π M).obj (op W) ≅
      ModuleCat.of Γ(S, ⊤) (LinearMap.ker
        ((TopCat.Sheaf.moduleCechSectionsComplex (baseModuleTopSheaf π M) U W).d 0 1).hom) :=
  openSectionsRestrictIso π M W ≪≫
    baseSectionsIsoKernelBaseCechDifferential (W.ι ≫ π) (M.restrict W.ι)
      (fun i => W.ι ⁻¹ᵁ U i) (preimage_isOpenCover U hU W) ≪≫
    (complexKernelIso (baseModuleCechSectionsRestrictComplexIso π M U W)).symm

/-- The WHOLE original open-section kernel identification recovers precisely
the actual sheaf augmentation, including the empty open. -/
@[reassoc]
theorem openSectionsKernelIso_hom_subtype {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (W : X.Opens) :
    (openSectionsKernelIso π M U hU W).hom ≫
        ModuleCat.ofHom (LinearMap.ker
          ((TopCat.Sheaf.moduleCechSectionsComplex (baseModuleTopSheaf π M) U W).d 0 1).hom).subtype =
      (TopCat.Sheaf.moduleCechAugmentation (baseModuleTopSheaf π M) U).hom.app (op W) := by
  apply kernel_iso_augmentation (baseModuleCechSectionsRestrictComplexIso π M U W)
    (openSectionsRestrictIso π M W)
    (baseSectionsIsoKernelBaseCechDifferential (W.ι ≫ π) (M.restrict W.ι)
      (fun i => W.ι ⁻¹ᵁ U i) (preimage_isOpenCover U hU W))
  have hb := congrArg (fun f => (openSectionsRestrictIso π M W).hom ≫ f)
    (baseSectionsIsoKernelBaseCechDifferential_hom_subtype
      (W.ι ≫ π) (M.restrict W.ι) (fun i => W.ι ⁻¹ᵁ U i)
      (preimage_isOpenCover U hU W))
  exact hb.trans (augmentation_restrict π M U W).symm

end EnvelopeProperty.SchemeModuleOpenSectionsKernel
