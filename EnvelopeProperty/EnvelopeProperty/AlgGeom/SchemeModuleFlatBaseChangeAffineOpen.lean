import EnvelopeProperty.AlgGeom.AffineCartesianModuleBaseChange
import EnvelopeProperty.AlgGeom.SchemeScalarModuleOpenRestriction
import EnvelopeProperty.AlgGeom.SchemeModuleFlatBaseChangeMap
import EnvelopeProperty.AlgGeom.SchemeModulePullbackOpenSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct TopologicalSpace
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleFlatBaseChangeAffineOpen

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}} (p : X ⟶ Spec (.of R))

private theorem restrictedSquare (U : X.Opens) :
    IsPullback
      ((FlatGlobalSections.firstProjection (S := S) p).resLE U
        ((FlatGlobalSections.firstProjection (S := S) p) ⁻¹ᵁ U) le_rfl)
      (((FlatGlobalSections.firstProjection (S := S) p) ⁻¹ᵁ U).ι ≫
        FlatGlobalSections.structureMap (S := S) p)
      (U.ι ≫ p) (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let g := FlatGlobalSections.firstProjection (S := S) p
  have h : IsPullback (g.resLE U (g ⁻¹ᵁ U) le_rfl) (g ⁻¹ᵁ U).ι U.ι g := by
    apply IsOpenImmersion.isPullback
    · exact (g.resLE_comp_ι le_rfl).symm
    · simp
  exact h.paste_vert (IsPullback.of_hasPullback p
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))

private theorem unitTopNaturality {A B : Scheme.{u}} (f : A ⟶ B)
    {M : B.Modules} {N : A.Modules} (v : M ⟶ (pushforward f).obj N)
    (W : B.Opens) (hW : W = ⊤)
    (hA : (⊤ : A.Opens) = f ⁻¹ᵁ W) (hTop : (⊤ : A.Opens) = f ⁻¹ᵁ ⊤) :
    v.app W ≫ N.presheaf.map
        (eqToHom hA).op =
      M.presheaf.map (eqToHom hW.symm).op ≫ v.app ⊤ ≫
        N.presheaf.map (eqToHom hTop).op := by
  let v' : M.presheaf ⟶ (Opens.map f.base).op ⋙ N.presheaf := v.mapPresheaf
  change v'.app (op W) ≫ N.presheaf.map (eqToHom hA).op =
    M.presheaf.map (eqToHom hW.symm).op ≫ v'.app (op ⊤) ≫
      N.presheaf.map (eqToHom hTop).op
  have h := v'.naturality (eqToHom hW.symm).op
  have hp := congrArg (fun k : Γ(M, W) ⟶ Γ(N, f ⁻¹ᵁ ⊤) => k ≫
    N.presheaf.map (eqToHom hTop).op) h
  simp only [Category.assoc] at hp
  erw [← N.presheaf.map_comp] at hp
  have hpath : (((Opens.map f.base).map (eqToHom hW.symm)).op ≫
      (eqToHom hTop).op) = (eqToHom hA).op := Subsingleton.elim _ _
  erw [hpath] at hp
  exact hp.symm

private theorem restrictTransport {A : Scheme.{u}} (N : A.Modules) (V : A.Opens) :
    N.presheaf.map (homOfLE (V.ι.image_preimage_le V)).op ≫
      (N.restrict V.ι).presheaf.map (eqToHom V.ι_preimage_self.symm).op =
        N.presheaf.map (eqToHom V.ι_image_top).op := by
  rw [restrict_map N V.ι (eqToHom V.ι_preimage_self.symm)]
  exact (N.presheaf.map_comp _ _).symm.trans
    (congrArg N.presheaf.map (Subsingleton.elim _ _))

private theorem sectionSquareTransport {A B : Scheme.{u}} (f : A ⟶ B)
    (W : B.Opens) (M : B.Modules) (N : A.Modules)
    (P : (f ⁻¹ᵁ W).toScheme.Modules)
    (v : M ⟶ (pushforward f).obj N)
    (ul : M.restrict W.ι ⟶
      (pushforward (f.resLE W (f ⁻¹ᵁ W) le_rfl)).obj P)
    (E : P ⟶ N.restrict (f ⁻¹ᵁ W).ι)
    (ht : (f.resLE W (f ⁻¹ᵁ W) le_rfl) ⁻¹ᵁ (W.ι ⁻¹ᵁ W) =
      (f ⁻¹ᵁ W).ι ⁻¹ᵁ (f ⁻¹ᵁ W))
    (h : M.presheaf.map (homOfLE (W.ι.image_preimage_le W)).op ≫
      ul.app (W.ι ⁻¹ᵁ W) ≫ P.presheaf.map (eqToHom ht.symm).op ≫
        E.app ((f ⁻¹ᵁ W).ι ⁻¹ᵁ (f ⁻¹ᵁ W)) =
      v.app W ≫ N.presheaf.map
        (homOfLE ((f ⁻¹ᵁ W).ι.image_preimage_le (f ⁻¹ᵁ W))).op)
    (m : Γ(M, W)) :
    E.app ⊤
      (P.presheaf.map (eqToHom (show (⊤ : (f ⁻¹ᵁ W).toScheme.Opens) =
          (f.resLE W (f ⁻¹ᵁ W) le_rfl) ⁻¹ᵁ ⊤ by simp)).op
        (ul.app ⊤ (M.presheaf.map (eqToHom W.ι_image_top).op m))) =
      N.presheaf.map (eqToHom (f ⁻¹ᵁ W).ι_image_top).op (v.app W m) := by
  let V := f ⁻¹ᵁ W
  let f' := f.resLE W V le_rfl
  let ul' : (M.restrict W.ι).presheaf ⟶ (Opens.map f'.base).op ⋙ P.presheaf := ul.mapPresheaf
  let E' : P.presheaf ⟶ (N.restrict V.ι).presheaf := E.mapPresheaf
  let v' : M.presheaf ⟶ (Opens.map f.base).op ⋙ N.presheaf := v.mapPresheaf
  let a : Γ(M, W) ⟶ Γ(M.restrict W.ι, W.ι ⁻¹ᵁ W) :=
    M.presheaf.map (homOfLE (W.ι.image_preimage_le W)).op
  let b : Γ(N, V) ⟶ Γ(N.restrict V.ι, V.ι ⁻¹ᵁ V) :=
    N.presheaf.map (homOfLE (V.ι.image_preimage_le V)).op
  let rM : Γ(M, W) ⟶ Γ(M.restrict W.ι, ⊤) :=
    M.presheaf.map (eqToHom W.ι_image_top).op
  let rN : Γ(N, V) ⟶ Γ(N.restrict V.ι, ⊤) :=
    N.presheaf.map (eqToHom V.ι_image_top).op
  change a ≫ ul'.app (op (W.ι ⁻¹ᵁ W)) ≫ P.presheaf.map (eqToHom ht.symm).op ≫
    E'.app (op (V.ι ⁻¹ᵁ V)) = v'.app (op W) ≫ b at h
  change E'.app (op ⊤)
    (P.presheaf.map (eqToHom (show (⊤ : V.toScheme.Opens) = f' ⁻¹ᵁ ⊤ by simp)).op
      (ul'.app (op ⊤) (rM m))) = rN (v'.app (op W) m)
  have hp := congrArg (fun k : Γ(M, W) ⟶ Γ(N.restrict V.ι, V.ι ⁻¹ᵁ V) =>
    k ≫ (N.restrict V.ι).presheaf.map (eqToHom V.ι_preimage_self.symm).op) h
  simp only [Category.assoc] at hp
  erw [← E'.naturality (eqToHom V.ι_preimage_self.symm).op] at hp
  have htotal : (⊤ : V.toScheme.Opens) = f' ⁻¹ᵁ (W.ι ⁻¹ᵁ W) := by
    rw [W.ι_preimage_self]
    simp
  have hcollapse : P.presheaf.map (eqToHom ht.symm).op ≫
      P.presheaf.map (eqToHom V.ι_preimage_self.symm).op =
        P.presheaf.map (eqToHom htotal).op :=
    (P.presheaf.map_comp _ _).symm.trans
      (congrArg P.presheaf.map (Subsingleton.elim _ _))
  erw [← Category.assoc (P.presheaf.map (eqToHom ht.symm).op)
    (P.presheaf.map (eqToHom V.ι_preimage_self.symm).op)
    (E'.app (op ⊤)), hcollapse] at hp
  have hn := unitTopNaturality f' ul (W.ι ⁻¹ᵁ W) W.ι_preimage_self htotal (by simp)
  change ul'.app (op (W.ι ⁻¹ᵁ W)) ≫ P.presheaf.map (eqToHom htotal).op =
    (M.restrict W.ι).presheaf.map (eqToHom W.ι_preimage_self.symm).op ≫
      ul'.app (op ⊤) ≫ P.presheaf.map
        (eqToHom (show (⊤ : V.toScheme.Opens) = f' ⁻¹ᵁ ⊤ by simp)).op at hn
  rw [← Category.assoc (ul'.app (op (W.ι ⁻¹ᵁ W)))
    (P.presheaf.map (eqToHom htotal).op) (E'.app (op ⊤)), hn] at hp
  have ha : a ≫ (M.restrict W.ι).presheaf.map
      (eqToHom W.ι_preimage_self.symm).op = rM := restrictTransport M W
  have hb : b ≫ (N.restrict V.ι).presheaf.map
      (eqToHom V.ι_preimage_self.symm).op = rN := restrictTransport N V
  simp only [Category.assoc] at hp
  rw [← Category.assoc a, ha, hb] at hp
  simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom hp m


private theorem unitTopSquare {Y : Scheme.{u}} (g : Y ⟶ X)
    (U : X.Opens) (M : X.Modules) (m : Γ(M, U)) :
    (SchemeModulePullbackOpenSections.pullbackRestrictIso g U M).hom.app ⊤
      (affinePullbackUnitTop (g.resLE U (g ⁻¹ᵁ U) le_rfl) (M.restrict U.ι)
        (M.presheaf.map (eqToHom U.ι_image_top).op m)) =
      ((Scheme.Modules.pullback g).obj M).presheaf.map (eqToHom (g ⁻¹ᵁ U).ι_image_top).op
        (((pullbackPushforwardAdjunction g).unit.app M).app U m) := by
  have h := congrArg (fun f => f.app U)
    (SchemeModulePullbackOpenSections.unit_square g U M)
  simp only [Hom.comp_app, pushforward_map_app, Functor.comp_map] at h
  simp only [SchemeModulePullbackOpenSections.pushforwardSquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Hom.comp_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app,
    restrictAdjunction_unit_app_app] at h
  erw [Category.id_comp, Category.comp_id] at h
  let V := g ⁻¹ᵁ U
  let g' := g.resLE U V le_rfl
  have ht : g' ⁻¹ᵁ (U.ι ⁻¹ᵁ U) = V.ι ⁻¹ᵁ V := by
    change (g' ≫ U.ι) ⁻¹ᵁ U = (V.ι ≫ g) ⁻¹ᵁ U
    rw [g.resLE_comp_ι le_rfl]
  exact sectionSquareTransport g U M ((Scheme.Modules.pullback g).obj M)
    ((Scheme.Modules.pullback g').obj (M.restrict U.ι))
    ((pullbackPushforwardAdjunction g).unit.app M)
    ((pullbackPushforwardAdjunction g').unit.app (M.restrict U.ι))
    (SchemeModulePullbackOpenSections.pullbackRestrictIso g U M).hom ht h m

private def sectionsNativeIso {A : Type u} [CommRing A] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of A)) (N : Y.Modules) :
    AffineModuleFlatBaseChange.sections q N ≅
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).obj
        (baseSections q N) :=
  (SchemeScalarModulePresheaf.topSectionsIso q N).symm ≪≫
    SchemeScalarModuleOpenRestriction.nativeSectionsIso q N ⊤

private def sectionsIso {A : Type u} [CommRing A] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of A)) {P N : Y.Modules} (e : P ≅ N) :
    AffineModuleFlatBaseChange.sections q P ≅
      AffineModuleFlatBaseChange.sections q N :=
  sectionsNativeIso q P ≪≫
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).mapIso
      (baseSectionsMapIso q e) ≪≫ (sectionsNativeIso q N).symm

private theorem sectionsIso_apply {A : Type u} [CommRing A] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of A)) {P N : Y.Modules} (e : P ≅ N)
    (m : AffineModuleFlatBaseChange.sections q P) :
    (sectionsIso q e).hom m = e.hom.app ⊤ m := rfl

private def affineOpenEquiv (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    S ⊗[R] SchemeScalarModulePresheaf.openSections p M U ≃ₗ[S]
      SchemeScalarModulePresheaf.openSections
        (FlatGlobalSections.structureMap (S := S) p)
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M)
        ((FlatGlobalSections.firstProjection (S := S) p) ⁻¹ᵁ U) := by
  let g := FlatGlobalSections.firstProjection (S := S) p
  let q := FlatGlobalSections.structureMap (S := S) p
  let V := g ⁻¹ᵁ U
  let g' := g.resLE U V le_rfl
  let N := (Scheme.Modules.pullback g).obj M
  let e := SchemeModulePullbackOpenSections.pullbackRestrictIso g U M
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := IsAffine.of_isPullback (restrictedSquare (S := S) p U)
  exact ((SchemeScalarModuleOpenRestriction.openRestrictIso p M U).toLinearEquiv.baseChange R S).trans
    ((AffineCartesianModuleBaseChange.tensorEquiv (U.ι ≫ p) g' (V.ι ≫ q)
      (restrictedSquare (S := S) p U) (M.restrict U.ι)).trans
        ((sectionsIso (V.ι ≫ q) e).toLinearEquiv.trans
          (SchemeScalarModuleOpenRestriction.openRestrictIso q N V).toLinearEquiv.symm))

private theorem tensorComparison {A A' : ModuleCat.{u} R}
    {B C D : ModuleCat.{u} S} (r : A ≅ A') (e : S ⊗[R] A' ≃ₗ[S] B)
    (f : B ≅ C) (t : D ≅ C) (v : A → D) (w : A' → B)
    (he : ∀ (s : S) (m : A'), e (s ⊗ₜ[R] m) = s • w m)
    (hw : ∀ m : A, f.hom (w (r.hom m)) = t.hom (v m)) (s : S) (m : A) :
    (r.toLinearEquiv.baseChange R S).trans
      (e.trans (f.toLinearEquiv.trans t.toLinearEquiv.symm)) (s ⊗ₜ[R] m) = s • v m := by
  apply t.toLinearEquiv.injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    LinearEquiv.apply_symm_apply, he, Iso.toLinearEquiv_apply]
  rw [f.hom.hom.map_smul, t.hom.hom.map_smul]
  exact congrArg (fun z : C => s • z) (hw m)

private theorem tensorComparison_eq {A A' : ModuleCat.{u} R}
    {B C D : ModuleCat.{u} S} (r : A ≅ A') (e : S ⊗[R] A' ≃ₗ[S] B)
    (f : B ≅ C) (t : D ≅ C) (v : A → D) (w : A' → B)
    (L : S ⊗[R] A →ₗ[S] D)
    (he : ∀ (s : S) (m : A'), e (s ⊗ₜ[R] m) = s • w m)
    (hw : ∀ m : A, f.hom (w (r.hom m)) = t.hom (v m))
    (hL : ∀ (s : S) (m : A), L (s ⊗ₜ[R] m) = s • v m) :
    ((r.toLinearEquiv.baseChange R S).trans
      (e.trans (f.toLinearEquiv.trans t.toLinearEquiv.symm))).toLinearMap = L := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => exact (tensorComparison r e f t v w he hw s m).trans (hL s m).symm
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private theorem affineOpenEquiv_eq (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (affineOpenEquiv (S := S) p M U hU).toLinearMap =
      (SchemeModuleFlatBaseChangeMap.sectionComparison (S := S) p M U).hom := by
  let g := FlatGlobalSections.firstProjection (S := S) p
  let q := FlatGlobalSections.structureMap (S := S) p
  let V := g ⁻¹ᵁ U
  let g' := g.resLE U V le_rfl
  let N := (Scheme.Modules.pullback g).obj M
  let e := SchemeModulePullbackOpenSections.pullbackRestrictIso g U M
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := IsAffine.of_isPullback (restrictedSquare (S := S) p U)
  have he := tensorComparison_eq
    (SchemeScalarModuleOpenRestriction.openRestrictIso p M U)
    (AffineCartesianModuleBaseChange.tensorEquiv (U.ι ≫ p) g' (V.ι ≫ q)
      (restrictedSquare (S := S) p U) (M.restrict U.ι))
    (sectionsIso (V.ι ≫ q) e)
    (SchemeScalarModuleOpenRestriction.openRestrictIso q N V)
    (fun m => SchemeModuleFlatBaseChangeMap.unitMap (S := S) p M U m)
    (fun m => affinePullbackUnitTop g' (M.restrict U.ι) m)
    (SchemeModuleFlatBaseChangeMap.sectionComparison (S := S) p M U).hom
    (fun s m => AffineCartesianModuleBaseChange.tensorEquiv_tmul
      (U.ι ≫ p) g' (V.ι ≫ q) (restrictedSquare (S := S) p U) (M.restrict U.ι) s m)
    (fun m => unitTopSquare g U M m)
    (fun s m => SchemeModuleFlatBaseChangeMap.sectionComparison_tmul (S := S) p M U s m)
  dsimp only [affineOpenEquiv]
  dsimp only [g, q, V, g', N, e] at he
  exact he

/-- On every actual original affine open, the SAME canonical whole scalar
extension comparison is an isomorphism. No matching square is an input. -/
theorem isIso_comparison (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso ((SchemeModuleFlatBaseChangeMap.comparison (S := S) p M).app (op U)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective
    (SchemeModuleFlatBaseChangeMap.sectionComparison (S := S) p M U).hom
  rw [← affineOpenEquiv_eq p M U hU]
  exact (affineOpenEquiv (S := S) p M U hU).bijective

end EnvelopeProperty.SchemeModuleFlatBaseChangeAffineOpen
