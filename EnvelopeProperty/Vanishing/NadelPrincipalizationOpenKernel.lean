import EnvelopeProperty.Vanishing.NadelPrincipalizationOpenPushforwardMates
import EnvelopeProperty.AlgGeom.PushforwardKernelIdealModule
import EnvelopeProperty.AlgGeom.IdealModuleOpenRestriction

/-! # The entire original pushed-section kernel ideal under actual open base change -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationOpenKernel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem iso_section_zero_iff {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (W : X.Opens) (s : Γ(M, W)) : e.hom.app W s = 0 ↔ s = 0 := by
  constructor
  · intro hs
    have hi := ConcreteCategory.congr_hom
      (congrArg (fun φ => φ.app W) e.hom_inv_id) s
    change e.inv.app W (e.hom.app W s) = s at hi
    exact hi.symm.trans ((congrArg (e.inv.app W) hs).trans (map_zero _))
  · rintro rfl
    exact map_zero _

/-- The native pulled original section vanishes exactly on the original
coefficient corresponding under the actual open-immersion ring isomorphism. -/
theorem pulledSection_zero_iff {X X' : Scheme.{u}} (g : X' ⟶ X) [IsOpenImmersion g]
    {M : X.Modules} (α : unitObj X ⟶ M) (W : X'.Opens) (a : Γ(X', W)) :
    ((pullbackUnitIso g).inv ≫ (pullback g).map α).app W a = 0 ↔
      α.app (g ''ᵁ W) ((g.appIso W).inv.hom a) = 0 := by
  let e := (restrictFunctorIsoPullback g).app M
  let eU := (restrictFunctorIsoPullback g).app (unitObj X)
  have hu : (pullbackUnitIso g).inv ≫ eU.inv = (restrictUnitIso g).inv := by
    apply (cancel_mono (restrictUnitIso g).hom).mp
    have hcoh : eU.inv ≫ (restrictUnitIso g).hom = (pullbackUnitIso g).hom :=
      ModularCurves.restrictFunctorIsoPullback_inv_comp_restrictUnitIsoLow g
    simp only [Category.assoc]
    rw [hcoh]
    simp only [Iso.inv_hom_id]
  have hn : (pullback g).map α ≫ e.inv = eU.inv ≫ (restrictFunctor g).map α :=
    (restrictFunctorIsoPullback g).inv.naturality α
  have hh : ((pullbackUnitIso g).inv ≫ (pullback g).map α) ≫ e.inv =
      (restrictUnitIso g).inv ≫ (restrictFunctor g).map α := by
    rw [Category.assoc, hn, ← Category.assoc, hu]
  have hv := congrArg (fun φ => φ.app W a) hh
  change e.inv.app W (((pullbackUnitIso g).inv ≫ (pullback g).map α).app W a) =
    α.app (g ''ᵁ W) ((g.appIso W).inv.hom a) at hv
  rw [← hv]
  exact (iso_section_zero_iff e.symm W _).symm

private theorem pullback_QC {A B : Scheme.{u}} (j : A ⟶ B) [IsOpenImmersion j]
    (M : B.Modules) [M.IsQuasicoherent] : ((pullback j).obj M).IsQuasicoherent := by
  apply (isQuasicoherent A).prop_of_iso ((restrictFunctorIsoPullback j).app M)
  infer_instance

attribute [local instance] pullback_QC

variable {Y X Y' X' : Scheme.{u}} (p : Y ⟶ X) (p' : Y' ⟶ X')
    (h : Y' ⟶ Y) (g : X' ⟶ X) [IsOpenImmersion h] [IsOpenImmersion g]
    (H : IsPullback p' h g p) [QuasiCompact p] [QuasiCompact p']
    (M : Y.Modules) [M.IsQuasicoherent] (δ : unitObj Y ⟶ M)

include H in
/-- The ENTIRE original geometric pushed-section kernel ideal commutes with
the actual original open Cartesian base change. The original whole sections
and actual ideal comap are retained, without a pushforward-QC premise. -/
private theorem kernel_comap_aux :
    (unitMapPushforwardKernelIdealSheaf p M
      ((pullbackPushforwardAdjunction p).homEquiv _ _ ((pullbackUnitIso p).hom ≫ δ))).comap g =
    unitMapPushforwardKernelIdealSheaf p' ((pullback h).obj M)
      ((pullbackPushforwardAdjunction p').homEquiv _ _
        ((pullbackUnitIso p').hom ≫ (pullbackUnitIso h).inv ≫ (pullback h).map δ)) := by
  let α := (pullbackPushforwardAdjunction p).homEquiv _ _ ((pullbackUnitIso p).hom ≫ δ)
  let β := (pullbackPushforwardAdjunction p').homEquiv _ _
    ((pullbackUnitIso p').hom ≫ (pullbackUnitIso h).inv ≫ (pullback h).map δ)
  let K := unitMapPushforwardKernelIdealSheaf p M α
  let K' := unitMapPushforwardKernelIdealSheaf p' ((pullback h).obj M) β
  apply Scheme.IdealSheafData.ext
  funext U
  ext a
  rw [← (K.comap g).isLocallyMem_iff U a, ← K'.isLocallyMem_iff U a,
    K.isLocallyMem_comap_iff_appIso_inv g U.1 a,
    PushforwardKernelIdealModule.isLocallyMem_iff p M α,
    PushforwardKernelIdealModule.isLocallyMem_iff p' ((pullback h).obj M) β]
  change α.app (g ''ᵁ U.1) ((g.appIso U.1).inv.hom a) = 0 ↔ β.app U.1 a = 0
  have ht := NadelPrincipalizationOpenPushforward.adjointSection_triangle p p' h g H δ
  have hv := congrArg (fun φ => φ.app U.1 a) ht
  change (NadelPrincipalizationOpenPushforward.openIso p p' h g H M).hom.app U.1
      (((pullbackUnitIso g).inv ≫ (pullback g).map α).app U.1 a) = β.app U.1 a at hv
  rw [← hv, iso_section_zero_iff]
  exact (pulledSection_zero_iff g α U.1 a).symm

omit [QuasiCompact p'] in
/-- The same whole ideal base-change formula, with local quasicompactness
itself derived from the actual Cartesian square and the original morphism. -/
theorem kernel_comap :
    letI : QuasiCompact p' := MorphismProperty.of_isPullback H.flip inferInstance
    (unitMapPushforwardKernelIdealSheaf p M
      ((pullbackPushforwardAdjunction p).homEquiv _ _ ((pullbackUnitIso p).hom ≫ δ))).comap g =
    unitMapPushforwardKernelIdealSheaf p' ((pullback h).obj M)
      ((pullbackPushforwardAdjunction p').homEquiv _ _
        ((pullbackUnitIso p').hom ≫ (pullbackUnitIso h).inv ≫ (pullback h).map δ)) := by
  let : QuasiCompact p' := MorphismProperty.of_isPullback H.flip inferInstance
  exact kernel_comap_aux p p' h g H M δ

end EnvelopeProperty.Vanishing.NadelPrincipalizationOpenKernel
