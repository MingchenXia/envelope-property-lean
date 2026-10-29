import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberSectionLifting
import EnvelopeProperty.AlgGeom.GeneratedLineProjectiveTwist
import EnvelopeProperty.AlgGeom.PolynomialDominanceFromCentralFiber
import EnvelopeProperty.AlgGeom.PushforwardUnitSections
import EnvelopeProperty.Berkovich.SchemeLinePullbackSections
import ModularCurves.ForMathlib.SchemeModuleEpiCover
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # The SAME lifted central generators on a genuine principal neighborhood of zero -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberGeneratorNeighborhood
open ProjectiveCentralFiberSectionLifting SchemeLineSectionEvaluation

private theorem sectionHom_atOne {X : Scheme.{u}} (L : X.Modules)
    (α : unitObj X ⟶ L) :
    SchemeModuleGlobalSections.sectionHom L (sectionAtOne α) = α := by
  have hone : topSectionHom (unitObj X) (1 : Γ(X,⊤)) = 𝟙 (unitObj X) :=
    ModularCurves.unitEndomorphismOfTopSection_one
  have h := ModularCurves.topSectionHom_comp (M := unitObj X) (N := L)
    (show Γ(X,⊤) from 1) α
  exact h.symm.trans ((congrArg (fun q : unitObj X ⟶ unitObj X => q ≫ α) hone).trans
    (Category.id_comp α))

private theorem sectionAtOne_pullback {X Z : Scheme.{u}} (g : Z ⟶ X)
    (L : X.Modules) (τ : Γ(L,⊤)) :
    sectionAtOne (pullbackSectionHom g (SchemeModuleGlobalSections.sectionHom L τ)) =
      affinePullbackUnitTop g L τ := by
  let α := pullbackSectionHom g (SchemeModuleGlobalSections.sectionHom L τ)
  have h := pullback_unit_app_top_applyT g L τ
  rw [map_one] at h
  change ((pullbackPushforwardAdjunction g).unit.app L).val.app (op ⊤) τ =
    α.val.app (op (g ⁻¹ᵁ (⊤ : X.Opens))) (1 : Γ(Z,g ⁻¹ᵁ (⊤ : X.Opens))) at h
  unfold affinePullbackUnitTop
  rw [h]
  have hn := PresheafOfModules.naturality_apply α.val
    (eqToHom (show (⊤ : Z.Opens) = g ⁻¹ᵁ (⊤ : X.Opens) by simp)).op
    (1 : Γ(Z,g ⁻¹ᵁ (⊤ : X.Opens)))
  change α.val.app (op ⊤)
    ((Z.presheaf.map
      (eqToHom (show (⊤ : Z.Opens) = g ⁻¹ᵁ (⊤ : X.Opens) by simp)).op).hom
        (1 : Γ(Z,g ⁻¹ᵁ (⊤ : X.Opens)))) = _ at hn
  rw [map_one] at hn
  exact hn

/-- Genuine original section-Hom pullback equals the SAME native adjunction-unit restriction. -/
theorem pullbackSectionHom_sectionHom {X Z : Scheme.{u}} (g : Z ⟶ X)
    (L : X.Modules) (τ : Γ(L,⊤)) :
    pullbackSectionHom g (SchemeModuleGlobalSections.sectionHom L τ) =
      SchemeModuleGlobalSections.sectionHom ((Scheme.Modules.pullback g).obj L)
        (affinePullbackUnitTop g L τ) := by
  have h := sectionHom_atOne ((Scheme.Modules.pullback g).obj L)
    (pullbackSectionHom g (SchemeModuleGlobalSections.sectionHom L τ))
  rw [sectionAtOne_pullback] at h
  exact h.symm

/-- Every point of the ACTUAL central scheme has an ambient neighborhood where
one SAME lifted original generator is a genuine section frame. -/
theorem exists_lifted_generator_frame {Y Z : Scheme.{u}} (j : Z ⟶ Y)
    (L : Y.Modules) (hL : IsInvertible L)
    (G₀ : ((Scheme.Modules.pullback j).obj L).GeneratingSections)
    (τ : G₀.I → Γ(L,⊤))
    (hτ : ∀ a, affinePullbackUnitTop j L (τ a) = (G₀.s a).val (op ⊤)) (x : Z) :
    ∃ W : Y.AffineZariskiSite, j x ∈ W.1 ∧ ∃ a : G₀.I,
      IsIso (pullbackSectionHom W.1.ι (SchemeModuleGlobalSections.sectionHom L (τ a))) := by
  let α := fun a => SchemeModuleGlobalSections.sectionHom L (τ a)
  have hLift (a : G₀.I) : pullbackSectionHom j (α a) =
      SchemeGeneratingSectionsUnit.generatorHom G₀ a := by
    let M := (Scheme.Modules.pullback j).obj L
    have h := congrFun (M.freeHomEquiv.apply_symm_apply G₀.s) a
    change M.unitHomEquiv (SchemeGeneratingSectionsUnit.generatorHom G₀ a) = G₀.s a at h
    have ht := congrArg (fun q => q.val (op (⊤ : Z.Opens))) h
    change sectionAtOne (SchemeGeneratingSectionsUnit.generatorHom G₀ a) = (G₀.s a).val (op ⊤) at ht
    exact (pullbackSectionHom_sectionHom j L (τ a)).trans
      ((congrArg (SchemeModuleGlobalSections.sectionHom M) ((hτ a).trans ht.symm)).trans
        (sectionHom_atOne M (SchemeGeneratingSectionsUnit.generatorHom G₀ a)))
  obtain ⟨U,hxU,⟨e⟩⟩ := GeneratedLineFramedAffineCover.exists_framed_affine L hL (j x)
  let V := j ⁻¹ᵁ U.1
  let E := localPullbackFrame j U.1 e
  let H := SchemeGeneratedLineCoefficients.framedGenerators
    (ClosedProjectiveGlobalGeneration.pullback_generatingSections V.ι G₀) E
  let r := fun a => SchemeLineSectionUnitFrames.frameScalar e (pullbackSectionHom U.1.ι (α a))
  have hscalar (a : G₀.I) :
      pullbackSectionHom V.ι (pullbackSectionHom j (α a)) ≫ E.hom =
        ModularCurves.unitEndomorphismOfTopSection ((j ∣_ U.1).appTop.hom (r a)) := by
    dsimp only [E,localPullbackFrame,Iso.trans_hom,Iso.app_hom]
    rw [← Category.assoc,pullbackSectionHom_comp,
      frameViaFactor_sectionHom_scalar (j ∣_ U.1) U.1.ι (V.ι ≫ j)
        (morphismRestrict_ι j U.1) e (α a) (r a)
        (SchemeLineSectionUnitFrames.frameScalar_identity e (pullbackSectionHom U.1.ι (α a)))]
  have hcoeff (a : G₀.I) : SchemeGeneratorCoefficientOpens.coefficient H a =
      (j ∣_ U.1).appTop.hom (r a) := by
    have hh := hscalar a
    rw [hLift] at hh
    have hc := (GeneratedLineLocalCoefficients.localCoefficient_scalar G₀ V E a).symm.trans hh
    have hv := congrArg sectionAtOne hc
    exact (topSectionHom_app_top_apply_one _ _).symm.trans
      (hv.trans (topSectionHom_app_top_apply_one _ _))
  have hxV : x ∈ V := hxU
  let xV : V.toScheme := ⟨x,hxV⟩
  obtain ⟨a,ha⟩ := SchemeGeneratorCoefficientOpens.exists_mem_basicOpen H xV
  have ha' : xV ∈ V.toScheme.basicOpen ((j ∣_ U.1).appTop.hom (r a)) :=
    Eq.mp (congrArg (fun c : Γ(V.toScheme,⊤) => xV ∈ V.toScheme.basicOpen c) (hcoeff a)) ha
  have ha'' : xV ∈ (j ∣_ U.1) ⁻¹ᵁ U.1.toScheme.basicOpen (r a) :=
    Eq.mpr (congrArg (fun W : V.toScheme.Opens => xV ∈ W)
      (Scheme.preimage_basicOpen_top (j ∣_ U.1) (r a))) ha'
  let c := U.1.topIso.hom.hom (r a)
  let W := Y.basicOpen c
  have hW : IsAffineOpen W := U.2.basicOpen c
  have he : U.1.ι ''ᵁ U.1.toScheme.basicOpen (r a) = W := by
    have h := U.1.ι_image_basicOpen_topIso_inv c
    rw [show U.1.topIso.inv.hom c = r a from U.1.topIso.hom_inv_id_apply (r a)] at h
    exact h
  have hxW : j x ∈ W := by
    rw [← he]
    refine ⟨(j ∣_ U.1) xV,ha'',?_⟩
    exact congrArg (fun f : V.toScheme ⟶ Y => f xV) (morphismRestrict_ι j U.1)
  exact ⟨⟨W,hW⟩,hxW,a,SchemeGeneratorFrameNeighborhoods.section_isIso_on_basicOpen U.1 e
    (α a) (r a) (SchemeLineSectionUnitFrames.frameScalar_identity e (pullbackSectionHom U.1.ι (α a)))⟩

/-- The closed bad locus has a genuine closed image; its complement contains zero. -/
theorem exists_principal_neighborhood_of_fiber_subset {k : Type u} [Field k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsProper p]
    (T : Y.Opens) (hT : Set.range (zeroInclusion p) ⊆ (T : Set Y)) :
    ∃ g : Polynomial k, Polynomial.eval 0 g ≠ 0 ∧
      p ⁻¹ᵁ (PrimeSpectrum.basicOpen g) ≤ T := by
  classical
  let B : Set Y := (T : Set Y)ᶜ
  have hB : IsClosed B := T.isOpen.isClosed_compl
  let V : (Spec (CommRingCat.of (Polynomial k))).Opens :=
    ⟨(p '' B)ᶜ,(p.isClosedMap B hB).isOpen_compl⟩
  let z₀ := zeroMap k (IsLocalRing.closedPoint k)
  have hz₀ : z₀ ∈ V := by
    rintro ⟨y,hy,hpy⟩
    have hyf : y ∈ Set.range (zeroInclusion p) := by
      rw [zeroInclusion,Scheme.Pullback.range_fst]
      exact ⟨IsLocalRing.closedPoint k,hpy.symm⟩
    exact hy (hT hyf)
  obtain ⟨W,⟨g,rfl⟩,hzg,hgV⟩ :=
    Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens hz₀
  refine ⟨g,?_,?_⟩
  · intro hg
    apply hzg
    change (Polynomial.evalRingHom (0 : k)) g ∈ (IsLocalRing.closedPoint k).asIdeal
    change (Polynomial.evalRingHom (0 : k)) g = 0 at hg
    rw [hg]
    exact Ideal.zero_mem _
  · intro y hy
    by_contra hyT
    exact (hgV hy) ⟨y,hyT,rfl⟩

private def tupleMap {X : Scheme.{u}} {ι : Type u} (L : X.Modules) (τ : ι → Γ(L,⊤)) :
    SheafOfModules.free (R := X.ringCatSheaf) ι ⟶ L :=
  L.freeHomEquiv.symm (fun a => ModularCurves.moduleSectionsOfTop L (τ a))

private theorem tupleMap_basis {X : Scheme.{u}} {ι : Type u}
    (L : X.Modules) (τ : ι → Γ(L,⊤)) (a : ι) :
    SheafOfModules.ιFree a ≫ tupleMap L τ = SchemeModuleGlobalSections.sectionHom L (τ a) := by
  apply L.unitHomEquiv.injective
  have h := congrFun (L.freeHomEquiv.apply_symm_apply
    (fun a => ModularCurves.moduleSectionsOfTop L (τ a))) a
  exact h.trans (L.unitHomEquiv.apply_symm_apply _).symm

private theorem tupleMap_epi {X : Scheme.{u}} {ι : Type u}
    (L : X.Modules) (τ : ι → Γ(L,⊤))
    (hcover : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ ∃ a : ι,
      IsIso (pullbackSectionHom W.ι (SchemeModuleGlobalSections.sectionHom L (τ a)))) :
    @Epi (SheafOfModules X.ringCatSheaf) inferInstance _ _ (tupleMap L τ) := by
  let J := {q : X.Opens × ι //
    IsIso (pullbackSectionHom q.1.ι (SchemeModuleGlobalSections.sectionHom L (τ q.2)))}
  let U := fun a : J => a.1.1
  have hcov : ∀ x : X, ∃ (a : J) (y : (U a).toScheme), (U a).ι y = x := by
    intro x
    obtain ⟨W,hx,a,ha⟩ := hcover x
    let j : J := ⟨⟨W,a⟩,ha⟩
    exact ⟨j,⟨x,hx⟩,rfl⟩
  constructor
  intro N f g hfg
  apply SchemeModuleOpenCoverDetection.hom_ext
    (fun a : J => (U a).toScheme) (fun a => (U a).ι) hcov
  intro a
  let F := Scheme.Modules.pullback (U a).ι
  let α := SchemeModuleGlobalSections.sectionHom L (τ a.1.2)
  have hi : IsIso (pullbackSectionHom (U a).ι α) := a.2
  let := hi
  apply (cancel_epi (pullbackSectionHom (U a).ι α)).mp
  have h : α ≫ f = α ≫ g := by
    have hh := congrArg (fun q => SheafOfModules.ιFree a.1.2 ≫ q) hfg
    have hf : α ≫ f = SheafOfModules.ιFree a.1.2 ≫ (tupleMap L τ ≫ f) :=
      (congrArg (fun q : unitObj X ⟶ L => q ≫ f) (tupleMap_basis L τ a.1.2).symm).trans
        (Category.assoc _ _ _)
    have hg : α ≫ g = SheafOfModules.ιFree a.1.2 ≫ (tupleMap L τ ≫ g) :=
      (congrArg (fun q : unitObj X ⟶ L => q ≫ g) (tupleMap_basis L τ a.1.2).symm).trans
        (Category.assoc _ _ _)
    exact hf.trans (hh.trans hg.symm)
  have hh := congrArg F.map h
  have hm : F.map α ≫ F.map f = F.map α ≫ F.map g :=
    (F.map_comp α f).symm.trans (hh.trans (F.map_comp α g))
  have hp := congrArg (fun q => (pullbackUnitIso (U a).ι).inv ≫ q) hm
  change ((pullbackUnitIso (U a).ι).inv ≫ F.map α) ≫ F.map f =
    ((pullbackUnitIso (U a).ι).inv ≫ F.map α) ≫ F.map g
  exact (Category.assoc _ _ _).trans (hp.trans (Category.assoc _ _ _).symm)

private theorem restricted_frame_cover {X Y : Scheme.{u}} (u : X ⟶ Y)
    {ι : Type u} (L : Y.Modules) (τ : ι → Γ(L,⊤))
    (hcover : ∀ x : X, ∃ W : Y.Opens, u x ∈ W ∧ ∃ a : ι,
      IsIso (pullbackSectionHom W.ι (SchemeModuleGlobalSections.sectionHom L (τ a)))) :
    ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ a : ι,
      IsIso (pullbackSectionHom V.ι
        (SchemeModuleGlobalSections.sectionHom ((Scheme.Modules.pullback u).obj L)
          (affinePullbackUnitTop u L (τ a)))) := by
  intro x
  obtain ⟨W,hx,a,ha⟩ := hcover x
  let V := u ⁻¹ᵁ W
  let α := SchemeModuleGlobalSections.sectionHom L (τ a)
  have hf : IsIso (pullbackSectionHom (V.ι ≫ u) α) :=
    SchemeLineSectionFactorization.isIso_pullbackSectionHom_factor
      (u ∣_ W) W.ι (V.ι ≫ u) (morphismRestrict_ι u W) α ha
  let := hf
  have hc : IsIso (pullbackSectionHom V.ι (pullbackSectionHom u α) ≫
      (Scheme.Modules.pullbackComp V.ι u).hom.app L) := by
    rw [pullbackSectionHom_comp]
    infer_instance
  let := hc
  have hs : IsIso (pullbackSectionHom V.ι (pullbackSectionHom u α)) :=
    IsIso.of_isIso_comp_right _ ((Scheme.Modules.pullbackComp V.ι u).hom.app L)
  refine ⟨V,hx,a,?_⟩
  rw [← pullbackSectionHom_sectionHom]
  exact hs

/-- The ORIGINAL finite central generating family lifts with the SAME index and
genuinely generates the SAME original line over an internally derived D(g), g(0) != 0. -/
theorem exists_finite_generators_near_zero {k : Type u} [Field k]
    {Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsDominant p]
    (hp : IsProjectiveFactorization p) (L : Y.Modules) (hL : IsInvertible L)
    (h₀ : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (zeroInclusion p)).obj L).sheaf 1))
    (G₀ : ((Scheme.Modules.pullback (zeroInclusion p)).obj L).GeneratingSections)
    (hG₀ : G₀.IsFiniteType) :
    ∃ g : Polynomial k, Polynomial.eval 0 g ≠ 0 ∧
      ∃ τ : G₀.I → Γ(L,⊤),
        (∀ a, affinePullbackUnitTop (zeroInclusion p) L (τ a) = (G₀.s a).val (op ⊤)) ∧
        let W := p ⁻¹ᵁ PrimeSpectrum.basicOpen g
        ∃ G : ((Scheme.Modules.pullback W.ι).obj L).GeneratingSections,
          G.IsFiniteType ∧ ∃ hI : G.I = G₀.I, ∀ a : G.I,
            SchemeGeneratingSectionsUnit.generatorHom G a =
              pullbackSectionHom W.ι (SchemeModuleGlobalSections.sectionHom L (τ (hI ▸ a))) := by
  classical
  let : IsProper p := hp.isProper
  have hsurj := restriction_surjective_of_hone_zero p hp L hL h₀
  choose τ hτ using fun a : G₀.I => hsurj ((G₀.s a).val (op ⊤))
  let J := {q : Y.Opens × G₀.I //
    IsIso (pullbackSectionHom q.1.ι (SchemeModuleGlobalSections.sectionHom L (τ q.2)))}
  let T : Y.Opens := ⨆ a : J, a.1.1
  have hT : Set.range (zeroInclusion p) ⊆ (T : Set Y) := by
    rintro y ⟨x,rfl⟩
    obtain ⟨U,hx,a,ha⟩ := exists_lifted_generator_frame (zeroInclusion p) L hL G₀ τ hτ x
    exact Opens.mem_iSup.mpr ⟨⟨⟨U.1,a⟩,ha⟩,hx⟩
  obtain ⟨g,hg,hgT⟩ := exists_principal_neighborhood_of_fiber_subset p T hT
  refine ⟨g,hg,τ,hτ,?_⟩
  let W := p ⁻¹ᵁ PrimeSpectrum.basicOpen g
  let Lg := (Scheme.Modules.pullback W.ι).obj L
  let τg := fun a => affinePullbackUnitTop W.ι L (τ a)
  have hcover : ∀ x : W.toScheme, ∃ V : Y.Opens, W.ι x ∈ V ∧ ∃ a : G₀.I,
      IsIso (pullbackSectionHom V.ι (SchemeModuleGlobalSections.sectionHom L (τ a))) := by
    intro x
    have hxT : W.ι x ∈ T := hgT x.2
    obtain ⟨a,ha⟩ := Opens.mem_iSup.mp hxT
    exact ⟨a.1.1,ha,a.1.2,a.2⟩
  have hrestricted := restricted_frame_cover W.ι L τ hcover
  have hEp := tupleMap_epi Lg τg hrestricted
  let G : Lg.GeneratingSections :=
    { I := G₀.I
      s := fun a => ModularCurves.moduleSectionsOfTop Lg (τg a)
      epi := hEp }
  have hG : G.IsFiniteType := ⟨hG₀.finite⟩
  refine ⟨G,hG,rfl,?_⟩
  intro a
  change SheafOfModules.ιFree a ≫ tupleMap Lg τg = _
  exact (tupleMap_basis Lg τg a).trans (pullbackSectionHom_sectionHom W.ι L (τ a)).symm

/-- Genuine near-zero original projective map and WHOLE O(1) pullback of the SAME line,
retaining EVERY original central generator through its SAME actual global lift. -/
theorem exists_projective_morphism_near_zero {k : Type u} [Field k]
    {Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsDominant p]
    (hp : IsProjectiveFactorization p) (L : Y.Modules) (hL : IsInvertible L)
    (h₀ : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (zeroInclusion p)).obj L).sheaf 1))
    (G₀ : ((Scheme.Modules.pullback (zeroInclusion p)).obj L).GeneratingSections)
    (hG₀ : G₀.IsFiniteType) :
    ∃ g : Polynomial k, Polynomial.eval 0 g ≠ 0 ∧
      ∃ τ : G₀.I → Γ(L,⊤),
        (∀ a, affinePullbackUnitTop (zeroInclusion p) L (τ a) = (G₀.s a).val (op ⊤)) ∧
        let B : (Spec (CommRingCat.of (Polynomial k))).Opens := PrimeSpectrum.basicOpen g
        let W := p ⁻¹ᵁ B
        IsIso B.toScheme.toSpecΓ ∧
        ∃ (n : ℕ) (Φ : W.toScheme ⟶ Alterations.projectiveSpace Γ(B.toScheme,⊤) n)
          (c : G₀.I → Fin (n+1))
          (E : (Scheme.Modules.pullback Φ).obj
            (MvPolynomial.coordinateHyperplaneTwist (R := Γ(B.toScheme,⊤)) (0 : Fin (n+1)) 1) ≅
              (Scheme.Modules.pullback W.ι).obj L),
          Φ ≫ Alterations.projectiveSpaceStructure Γ(B.toScheme,⊤) n =
              (p ∣_ B) ≫ B.toScheme.toSpecΓ ∧
          ∀ a : G₀.I, pullbackSectionHom Φ
              (ProjectiveHomogeneousSections.sectionHom (R := Γ(B.toScheme,⊤)) (0 : Fin (n+1)) 1
                (MvPolynomial.X (c a)) (MvPolynomial.isHomogeneous_X _ _)) ≫ E.hom =
            pullbackSectionHom W.ι (SchemeModuleGlobalSections.sectionHom L (τ a)) := by
  classical
  obtain ⟨g,hg,τ,hτ,G,hG,hI,hsection⟩ := exists_finite_generators_near_zero p hp L hL h₀ G₀ hG₀
  let B : (Spec (CommRingCat.of (Polynomial k))).Opens := PrimeSpectrum.basicOpen g
  let W := p ⁻¹ᵁ B
  let : IsAffine B.toScheme := by
    change IsAffineOpen B
    exact IsAffineOpen.Spec_basicOpen (R := CommRingCat.of (Polynomial k)) g
  let : IsProper p := hp.isProper
  let : Surjective p := surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range
  let z₀ := zeroMap k (IsLocalRing.closedPoint k)
  have hz₀ : z₀ ∈ B := by
    change (Polynomial.evalRingHom (0 : k)) g ∉ (IsLocalRing.closedPoint k).asIdeal
    rw [show IsLocalRing.closedPoint k = (⊥ : PrimeSpectrum k) from Subsingleton.elim _ _]
    exact hg
  obtain ⟨y,hy⟩ := p.surjective z₀
  have hyW : y ∈ W := by
    change p y ∈ B
    rw [hy]
    exact hz₀
  let : Nonempty W := ⟨⟨y,hyW⟩⟩
  let : IsIntegral W.toScheme := inferInstance
  let pg : W.toScheme ⟶ Spec (CommRingCat.of Γ(B.toScheme,⊤)) :=
    (p ∣_ B) ≫ B.toScheme.toSpecΓ
  obtain ⟨n,Φ,c,E,hΦ,hcoord⟩ := GeneratedLineProjectiveTwist.exists_projective_morphism
    pg (hL.pullback W.ι) G hG
  let eI : G.I ≃ G₀.I := Equiv.cast hI
  refine ⟨g,hg,τ,hτ,inferInstance,n,Φ,(fun a => c (eI.symm a)),E,hΦ,?_⟩
  intro a
  have h := hsection (eI.symm a)
  have hidx : (hI ▸ eI.symm a) = a := eI.apply_symm_apply a
  rw [hidx] at h
  exact (hcoord (eI.symm a)).trans h

end EnvelopeProperty.ProjectiveCentralFiberGeneratorNeighborhood
