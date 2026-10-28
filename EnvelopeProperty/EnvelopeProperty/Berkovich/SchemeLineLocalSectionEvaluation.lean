import EnvelopeProperty.Berkovich.SchemeLineSectionEvaluation
import ModularCurves.Picard.DualPullback
import EnvelopeProperty.AlgGeom.SchemeModuleGlobalSections

/-! # The original local coefficient evaluates at the original scheme-valued point -/
open scoped NNReal
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace EnvelopeProperty.SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
    simp only [homOfLE_refl, op_id, one_mul]
    erw [CategoryTheory.Functor.map_id]
    rfl)

private theorem frameNorm_sectionAtOne {B : Scheme.{u}} {N : B.Modules}
    (e : N ≅ Scheme.Modules.unitObj B) (α : Scheme.Modules.unitObj B ⟶ N)
    (r : Γ(B, ⊤)) (h : α ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection r)
    (norm : Γ(N, (⊤ : B.Opens)) → ℝ≥0) (w : Γ(B, ⊤) → ℝ≥0)
    (hn : ∀ s, norm s = w ((e.hom.val.app (op ⊤)).hom s)) :
    norm (sectionAtOne α) = w r :=
  (hn _).trans (congrArg w (frame_sectionAtOne e α r h))

/-- Genuine open pullback of an original whole section map equals its native restriction map. -/
theorem pullbackSectionHom_restrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (α : Scheme.Modules.unitObj X ⟶ M) :
    pullbackSectionHom U.ι α ≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app M =
      (Scheme.Modules.restrictUnitIso U.ι).inv ≫ (Scheme.Modules.restrictFunctor U.ι).map α := by
  let c := Scheme.Modules.restrictFunctorIsoPullback U.ι
  have hn := c.inv.naturality α
  have hu := congrArg Iso.inv (show
    (c.symm.app (Scheme.Modules.unitObj X)) ≪≫ Scheme.Modules.restrictUnitIso U.ι =
      Scheme.Modules.pullbackUnitIso U.ι from by
        apply Iso.ext
        exact ModularCurves.restrictFunctorIsoPullback_inv_comp_restrictUnitIsoLow U.ι)
  change (Scheme.Modules.restrictUnitIso U.ι).inv ≫ c.hom.app (Scheme.Modules.unitObj X) =
    (Scheme.Modules.pullbackUnitIso U.ι).inv at hu
  unfold pullbackSectionHom
  rw [Category.assoc, hn, ← Category.assoc, ← hu]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- The original global section has its exact original local-frame scalar,
as a WHOLE native module morphism on the original affine open. -/
theorem sectionHom_localScalar {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme)
    (s : Γ(M, (⊤ : X.Opens))) :
    pullbackSectionHom U.1.ι (SchemeModuleGlobalSections.sectionHom M s) ≫
        (Scheme.Modules.pullbackIsoOfRestrictIso M U.1 e).hom =
      ModularCurves.unitEndomorphismOfTopSection
        (ModularCurves.affineOpenTopSection U (ModularCurves.localTrivializationCoefficient M U e s)) := by
  simp only [Scheme.Modules.pullbackIsoOfRestrictIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  rw [← Category.assoc, pullbackSectionHom_restrict,
    ← SchemeModuleGlobalSections.sectionHom_restrict, SchemeModuleGlobalSections.sectionHom_comp]
  change SchemeModuleGlobalSections.sectionHom (Scheme.Modules.unitObj U.1.toScheme)
      (ModularCurves.localTrivializationTopSection M U e s) = _
  rw [ModularCurves.localTrivializationCoefficient, ModularCurves.affineOpenTopSection_ambientSection]
  rfl
end EnvelopeProperty.SchemeLineSectionEvaluation

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem openTopSection_eq_appLE {X : Scheme.{u}} (U : X.Opens) (c : Γ(X, U)) :
    Scheme.Modules.openTopSection U c =
      (U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom c := by
  rw [Scheme.Modules.openTopSection, Scheme.Opens.ι_appIso, Scheme.Opens.ι_appLE]
  change (X.presheaf.map (eqToHom U.ι_image_top).op).hom c = _
  apply ConcreteCategory.congr_hom
  apply X.presheaf.congr_map
  exact Subsingleton.elim _ _


variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of R)} [IsProper fX]
  (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v fX) {M : X.Modules}

/-- The genuine proper model-line norm of the ORIGINAL whole global section
is the original residue valuation of its ACTUAL original local-frame scalar.
The local equation is a whole module-morphism identity, not a metric certificate. -/
theorem modelLineNorm_fibreSection_eq_localScalar (hM : Scheme.Modules.IsInvertible M)
    (U : X.Opens) (hc : center hb y ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (α : Scheme.Modules.unitObj X ⟶ M) (r : Γ(U.toScheme, ⊤))
    (hr : SchemeLineSectionEvaluation.pullbackSectionHom U.ι α ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection r) :
    modelLineNorm hb y hM (fibreSection y α) =
      y.1.residueVal ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom
        ((localGenericFactor hb y U hc).appTop.hom r)) := by
  have h : SchemeLineSectionEvaluation.pullbackSectionHom
      (X.fromSpecResidueField y.1.point) α ≫ (localFrameGenericIso hb y U hc e).hom =
      ModularCurves.unitEndomorphismOfTopSection
        ((localGenericFactor hb y U hc).appTop.hom r) :=
    SchemeLineSectionEvaluation.frameViaFactor_sectionHom_scalar
      (localGenericFactor hb y U hc) U.ι (X.fromSpecResidueField y.1.point)
      (localGenericFactor_comp hb y U hc) e α r hr
  exact SchemeLineSectionEvaluation.frameNorm_sectionAtOne
    (localFrameGenericIso hb y U hc e)
    (SchemeLineSectionEvaluation.pullbackSectionHom (X.fromSpecResidueField y.1.point) α)
    _ h (modelLineNorm hb y hM)
    (fun z => y.1.residueVal
      ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom z))
    (modelLineNorm_eq_localFrame hb y hM U hc e)


/-- The SAME actual local coefficient pulls back to its original residue-field evaluation. -/
theorem localGenericFactor_openTopSection (U : X.Opens) (hc : center hb y ∈ U)
    (c : Γ(X, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom
      ((localGenericFactor hb y U hc).appTop.hom (Scheme.Modules.openTopSection U c)) =
      X.evaluation U y.1.point (support_mem_of_center_mem hb y U hc) c := by
  rw [openTopSection_eq_appLE]
  let g := localGenericFactor hb y U hc
  have htop : ⊤ ≤ g ⁻¹ᵁ (⊤ : U.toScheme.Opens) := le_top
  have he := Scheme.Hom.appLE_comp_appLE g U.ι U ⊤ ⊤ U.ι_preimage_self.ge htop
  have ht : g.appLE ⊤ ⊤ htop = g.appTop := by simp [Scheme.Hom.appLE]
  have hfun : ∀ h : ⊤ ≤ (g ≫ U.ι) ⁻¹ᵁ U,
      (g ≫ U.ι).appLE U ⊤ h ≫
        (Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom =
      X.evaluation U y.1.point (support_mem_of_center_mem hb y U hc) := by
    dsimp only [g]
    rw [localGenericFactor_comp]
    intro h
    exact SchemeValuedPoint.fromSpecResidueField_appLE_top _ _ _ _
  have hcomp : U.ι.appLE U ⊤ U.ι_preimage_self.ge ≫ g.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom =
      X.evaluation U y.1.point (support_mem_of_center_mem hb y U hc) := by
    rw [← ht, ← Category.assoc, he]
    exact hfun _
  exact congrArg (fun q : Γ(X, U) ⟶ X.residueField y.1.point => q.hom c) hcomp

/-- An original global section's actual model norm is the ORIGINAL scheme-valued
point evaluation of its ORIGINAL whole local frame coefficient. -/
theorem modelLineNorm_fibreSection_eq_localEval {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (U : X.Opens) (hc : center hb y ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (α : Scheme.Modules.unitObj X ⟶ M) (c : Γ(X, U))
    (hr : SchemeLineSectionEvaluation.pullbackSectionHom U.ι α ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection (Scheme.Modules.openTopSection U c)) :
    modelLineNorm hb y hM (fibreSection y α) =
      SchemeValuedPoint.eval y.1 U (support_mem_of_center_mem hb y U hc) c := by
  rw [modelLineNorm_fibreSection_eq_localScalar hb y hM U hc e α _ hr,
    localGenericFactor_openTopSection]
  rfl
end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
