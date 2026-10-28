import EnvelopeProperty.Berkovich.SchemeGenericLineLocalFramePullback
import EnvelopeProperty.AlgGeom.UnitModuleAutomorphisms

/-! # True proper-model norms of arbitrary original residue-fibre sections pull back -/
open scoped NNReal
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
open SchemeLineSectionEvaluation

private theorem frame_sectionAtOne {B : Scheme.{u}} {N : B.Modules}
    (e : N ≅ Scheme.Modules.unitObj B) (α : Scheme.Modules.unitObj B ⟶ N)
    (r : Γ(B, ⊤)) (h : α ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection r) :
    (e.hom.val.app (op ⊤)).hom (sectionAtOne α) = r := by
  have happ := congrArg sectionAtOne h
  change (e.hom.val.app (op ⊤)).hom (sectionAtOne α) =
    (ModularCurves.unitEndomorphismOfTopSection r).val.app (op ⊤)
      (show Γ(B, ⊤) from 1) at happ
  exact happ.trans (by
    rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
    simp only [homOfLE_refl,op_id,one_mul]
    erw [CategoryTheory.Functor.map_id]
    rfl)

private theorem frameNorm_sectionAtOne {B : Scheme.{u}} {N : B.Modules}
    (e : N ≅ Scheme.Modules.unitObj B) (α : Scheme.Modules.unitObj B ⟶ N)
    (r : Γ(B, ⊤)) (h : α ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection r)
    (norm : Γ(N, (⊤ : B.Opens)) → ℝ≥0) (w : Γ(B, ⊤) → ℝ≥0)
    (hn : ∀ s, norm s = w ((e.hom.val.app (op ⊤)).hom s)) :
    norm (sectionAtOne α) = w r :=
  (hn _).trans (congrArg w (frame_sectionAtOne e α r h))

private theorem exists_frame_scalar {B : Scheme.{u}} {N : B.Modules}
    (e : N ≅ Scheme.Modules.unitObj B) (β : Scheme.Modules.unitObj B ⟶ N) :
    ∃ r : Γ(B, ⊤), β ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection r :=
  ⟨sectionAtOne (β ≫ e.hom), Scheme.Modules.unitHom_eq_globalScalar (β ≫ e.hom)⟩

private theorem pullbackScalar_of_frame {B C : Scheme.{u}} (p : B ⟶ C)
    {A : C.Modules} {N : B.Modules} (a : (Scheme.Modules.pullback p).obj A ≅ N)
    (eA : A ≅ Scheme.Modules.unitObj C) (eN : N ≅ Scheme.Modules.unitObj B)
    (he : a ≪≫ eN = (Scheme.Modules.pullback p).mapIso eA ≪≫ Scheme.Modules.pullbackUnitIso p)
    (β : Scheme.Modules.unitObj C ⟶ A) (r : Γ(C, ⊤))
    (hr : β ≫ eA.hom = ModularCurves.unitEndomorphismOfTopSection r) :
    (pullbackSectionHom p β ≫ a.hom) ≫ eN.hom =
      ModularCurves.unitEndomorphismOfTopSection (p.appTop.hom r) := by
  have heh := congrArg Iso.hom he
  change a.hom ≫ eN.hom = (Scheme.Modules.pullback p).map eA.hom ≫
    (Scheme.Modules.pullbackUnitIso p).hom at heh
  unfold pullbackSectionHom
  rw [Category.assoc,heh]
  change (Scheme.Modules.pullbackUnitIso p).inv ≫
    ((Scheme.Modules.pullback p).map β ≫ (Scheme.Modules.pullback p).map eA.hom) ≫
      (Scheme.Modules.pullbackUnitIso p).hom = _
  rw [← (Scheme.Modules.pullback p).map_comp,hr]
  exact ModularCurves.pullback_unitEndomorphismOfTopSection p r

private theorem localFrameNorm_sectionAtOne
    {T : Type u} [CommRing T] {ν : Valuation T ℝ≥0}
    {Z : Scheme.{u}} {f : Z ⟶ Spec (CommRingCat.of T)} [IsProper f]
    (hb : ∀ t, ν t ≤ 1) (z : RelativeSchemeValuedPoint ν f)
    {L : Z.Modules} (hL : Scheme.Modules.IsInvertible L)
    (V : Z.Opens) (hc : center hb z ∈ V)
    (e : (Scheme.Modules.pullback V.ι).obj L ≅ Scheme.Modules.unitObj V.toScheme)
    (β : Scheme.Modules.unitObj (Spec (CommRingCat.of (Z.residueField z.1.point))) ⟶ genericLineModule z L)
    (r : Γ(Spec (CommRingCat.of (Z.residueField z.1.point)), ⊤))
    (hr : β ≫ (localFrameGenericIso hb z V hc e).hom = ModularCurves.unitEndomorphismOfTopSection r) :
    modelLineNorm hb z hL (sectionAtOne β) =
      z.1.residueVal ((Scheme.ΓSpecIso (CommRingCat.of (Z.residueField z.1.point))).hom.hom r) :=
  frameNorm_sectionAtOne (localFrameGenericIso hb z V hc e) β r hr (modelLineNorm hb z hL)
    (fun a => z.1.residueVal ((Scheme.ΓSpecIso (CommRingCat.of (Z.residueField z.1.point))).hom.hom a))
    (fun s => modelLineNorm_eq_localFrame hb z hL V hc e s)

variable {R S : Type u} [CommRing R] [CommRing S]
variable {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}
variable {X Y : Scheme.{u}}
variable {fX : X ⟶ Spec (CommRingCat.of S)} {fY : Y ⟶ Spec (CommRingCat.of R)}
variable [IsProper fX] [IsProper fY]

private theorem centerPreimageMem
    (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r) (g : X ⟶ Y)
    (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (hbR : ∀ r, v r ≤ 1) (hbS : ∀ s, w s ≤ 1) (y : RelativeSchemeValuedPoint w fX)
    (U : Y.Opens) (hc : center hbR (mapOverBase φ hφ g hg y) ∈ U) :
    center hbS y ∈ g ⁻¹ᵁ U := by
  change g (center hbS y) ∈ U
  rw [center_map_overBase φ hφ g hg hbR hbS y]
  exact hc

private theorem pullbackResidueSectionHom_localScalar
    (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r) (g : X ⟶ Y)
    (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (hbR : ∀ r, v r ≤ 1) (hbS : ∀ s, w s ≤ 1) (y : RelativeSchemeValuedPoint w fX)
    {M : Y.Modules} (U : Y.Opens) (hc : center hbR (mapOverBase φ hφ g hg y) ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (β : Scheme.Modules.unitObj (Spec (CommRingCat.of (Y.residueField (g y.1.point)))) ⟶
      (Scheme.Modules.pullback (Y.fromSpecResidueField (g y.1.point))).obj M)
    (r : Γ(Spec (CommRingCat.of (Y.residueField (g y.1.point))), ⊤))
    (hr : β ≫ (localFrameGenericIso hbR (mapOverBase φ hφ g hg y) U hc e).hom =
      ModularCurves.unitEndomorphismOfTopSection r) :
    SchemeValuedPoint.pullbackResidueSectionHom g y.1.point β ≫
      (localFrameGenericIso hbS y (g ⁻¹ᵁ U) (centerPreimageMem φ hφ g hg hbR hbS y U hc)
        (localPullbackFrame g U e)).hom =
      ModularCurves.unitEndomorphismOfTopSection ((Spec.map (g.residueFieldMap y.1.point)).appTop.hom r) := by
  exact pullbackScalar_of_frame (Spec.map (g.residueFieldMap y.1.point))
    (SchemeValuedPoint.residueModulePullbackIso g y.1.point M)
    (localFrameGenericIso hbR (mapOverBase φ hφ g hg y) U hc e)
    (localFrameGenericIso hbS y (g ⁻¹ᵁ U) (centerPreimageMem φ hφ g hg hbR hbS y U hc)
      (localPullbackFrame g U e))
    (residueModulePullbackIso_localFrame φ hφ g hg hbR hbS y U hc e) β r hr

private theorem residueSpec_value_appTop (g : X ⟶ Y) (y : SchemeValuedPoint X)
    (r : Γ(Spec (CommRingCat.of (Y.residueField (g y.point))), ⊤)) :
    y.residueVal ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.point))).hom.hom
      ((Spec.map (g.residueFieldMap y.point)).appTop.hom r)) =
    (SchemeValuedPoint.map g y).residueVal
      ((Scheme.ΓSpecIso (CommRingCat.of (Y.residueField (g y.point)))).hom.hom r) := by
  have h := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_naturality (g.residueFieldMap y.point))
  exact congrArg y.residueVal h

private theorem modelLineNorm_pullbackResidueSectionHom_eq_localFrame_of_scalar
    (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r) (g : X ⟶ Y)
    (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (hbR : ∀ r, v r ≤ 1) (hbS : ∀ s, w s ≤ 1) (y : RelativeSchemeValuedPoint w fX)
    {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M)
    (U : Y.Opens) (hc : center hbR (mapOverBase φ hφ g hg y) ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (β : Scheme.Modules.unitObj (Spec (CommRingCat.of (Y.residueField (g y.1.point)))) ⟶
      (Scheme.Modules.pullback (Y.fromSpecResidueField (g y.1.point))).obj M)
    (r : Γ(Spec (CommRingCat.of (Y.residueField (g y.1.point))), ⊤))
    (hr : β ≫ (localFrameGenericIso hbR (mapOverBase φ hφ g hg y) U hc e).hom =
      ModularCurves.unitEndomorphismOfTopSection r) :
    modelLineNorm hbS y (hM.pullback g)
      (sectionAtOne (SchemeValuedPoint.pullbackResidueSectionHom g y.1.point β)) =
    modelLineNorm hbR (mapOverBase φ hφ g hg y) hM (sectionAtOne β) := by
  have hnX := localFrameNorm_sectionAtOne hbS y (hM.pullback g) (g ⁻¹ᵁ U)
    (centerPreimageMem φ hφ g hg hbR hbS y U hc) (localPullbackFrame g U e)
    (SchemeValuedPoint.pullbackResidueSectionHom g y.1.point β)
    ((Spec.map (g.residueFieldMap y.1.point)).appTop.hom r)
    (pullbackResidueSectionHom_localScalar φ hφ g hg hbR hbS y U hc e β r hr)
  have hnY := localFrameNorm_sectionAtOne hbR (mapOverBase φ hφ g hg y) hM U hc e β r hr
  exact hnX.trans ((residueSpec_value_appTop g y.1 r).trans hnY.symm)

private theorem modelLineNorm_pullbackResidueSectionHom_eq_localFrame
    (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r) (g : X ⟶ Y)
    (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (hbR : ∀ r, v r ≤ 1) (hbS : ∀ s, w s ≤ 1) (y : RelativeSchemeValuedPoint w fX)
    {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M)
    (U : Y.Opens) (hc : center hbR (mapOverBase φ hφ g hg y) ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (β : Scheme.Modules.unitObj (Spec (CommRingCat.of (Y.residueField (g y.1.point)))) ⟶
      (Scheme.Modules.pullback (Y.fromSpecResidueField (g y.1.point))).obj M) :
    modelLineNorm hbS y (hM.pullback g)
      (sectionAtOne (SchemeValuedPoint.pullbackResidueSectionHom g y.1.point β)) =
    modelLineNorm hbR (mapOverBase φ hφ g hg y) hM (sectionAtOne β) := by
  obtain ⟨r,hr⟩ := exists_frame_scalar
    (localFrameGenericIso hbR (mapOverBase φ hφ g hg y) U hc e) β
  exact modelLineNorm_pullbackResidueSectionHom_eq_localFrame_of_scalar φ hφ g hg hbR hbS y hM U hc e β r hr


/-- The TRUE actual model norm of ANY original generic-fibre section morphism
commutes with its ACTUAL native residue-field pullback, including sections
which do not extend to global model sections. No metric or frame certificate. -/
theorem modelLineNorm_pullbackResidueSectionHom_eq_overBase
    (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r) (g : X ⟶ Y)
    (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (hbR : ∀ r, v r ≤ 1) (hbS : ∀ s, w s ≤ 1) (y : RelativeSchemeValuedPoint w fX)
    {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M)
    (β : Scheme.Modules.unitObj (Spec (CommRingCat.of (Y.residueField (g y.1.point)))) ⟶
      (Scheme.Modules.pullback (Y.fromSpecResidueField (g y.1.point))).obj M) :
    modelLineNorm hbS y (hM.pullback g)
      (sectionAtOne (SchemeValuedPoint.pullbackResidueSectionHom g y.1.point β)) =
    modelLineNorm hbR (mapOverBase φ hφ g hg y) hM (sectionAtOne β) := by
  have hMt := hM
  obtain ⟨ι,U,hU,hframe⟩ := hMt
  have hcov : center hbR (mapOverBase φ hφ g hg y) ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  obtain ⟨e⟩ := hframe i
  exact modelLineNorm_pullbackResidueSectionHom_eq_localFrame φ hφ g hg hbR hbS y hM (U i) hi e β

/-- The whole genuine model norm of EVERY original generic-fibre section is
preserved by the literal original residue-field pullback. No global extension,
flatness or properness of the intervening map is needed. -/
theorem modelLineNorm_pullbackResidueSection_eq_overBase
    (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r) (g : X ⟶ Y)
    (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (hbR : ∀ r, v r ≤ 1) (hbS : ∀ s, w s ≤ 1) (y : RelativeSchemeValuedPoint w fX)
    {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : Γ((Scheme.Modules.pullback (Y.fromSpecResidueField (g y.1.point))).obj M, ⊤)) :
    modelLineNorm hbS y (hM.pullback g) (SchemeValuedPoint.pullbackResidueSection g y.1.point s) =
      modelLineNorm hbR (mapOverBase φ hφ g hg y) hM s := by
  let N := (Scheme.Modules.pullback (Y.fromSpecResidueField (g y.1.point))).obj M
  change modelLineNorm hbS y (hM.pullback g)
    (sectionAtOne (SchemeValuedPoint.pullbackResidueSectionHom g y.1.point (Scheme.Modules.topSectionHom N s))) = _
  have h := modelLineNorm_pullbackResidueSectionHom_eq_overBase φ hφ g hg hbR hbS y hM
    (Scheme.Modules.topSectionHom N s)
  have hs : sectionAtOne (Scheme.Modules.topSectionHom N s) = s :=
    Scheme.Modules.topSectionHom_app_top_apply_one N s
  rw [hs] at h
  exact h

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
