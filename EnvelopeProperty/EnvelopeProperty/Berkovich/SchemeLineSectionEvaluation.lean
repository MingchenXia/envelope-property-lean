import EnvelopeProperty.Berkovich.SchemeLineLocalFrames
import ModularCurves.Picard.UnitPullback
import ModularCurves.Picard.DualPullback.PullbackSection

/-! # Actual whole global line sections evaluated through their original local frames -/

open scoped NNReal
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace EnvelopeProperty.SchemeLineSectionEvaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem factorFrame_unit {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D)
    (f : B ⟶ D) (hg : g ≫ b = f) :
    Scheme.Modules.frameViaFactor g b f hg (Scheme.Modules.pullbackUnitIso b) =
      Scheme.Modules.pullbackUnitIso f := by
  apply Iso.ext
  apply (cancel_epi (Scheme.Modules.frameFactorIso g b f hg
    (Scheme.Modules.unitObj D)).hom).mp
  simp only [Scheme.Modules.frameViaFactor, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.hom_inv_id_assoc]
  have hcongr := ModularCurves.pullbackUnitIso_congrLow hg
  have hcomp := ModularCurves.pullbackUnitIso_compLow g b
  change (Scheme.Modules.pullback g).map (Scheme.Modules.pullbackUnitIso b).hom ≫
      (Scheme.Modules.pullbackUnitIso g).hom =
    (Scheme.Modules.pullbackComp g b).hom.app (Scheme.Modules.unitObj D) ≫
      (Scheme.Modules.pullbackCongr hg).hom.app (Scheme.Modules.unitObj D) ≫
        (Scheme.Modules.pullbackUnitIso f).hom
  rw [show (Scheme.Modules.pullbackCongr hg).hom.app (Scheme.Modules.unitObj D) ≫
      (Scheme.Modules.pullbackUnitIso f).hom = _ from hcongr]
  exact hcomp.symm

variable {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D) (f : B ⟶ D)
  (hg : g ≫ b = f) {M : D.Modules}

/-- The ACTUAL original pullback of a whole original structure-line section,
using the true original unit comparison. -/
def pullbackSectionHom (p : B ⟶ D) (α : Scheme.Modules.unitObj D ⟶ M) :
    Scheme.Modules.unitObj B ⟶ (Scheme.Modules.pullback p).obj M :=
  (Scheme.Modules.pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map α

/-- An ACTUAL local frame applied to the pullback of an ORIGINAL whole global
section is the pullback of that SAME original local frame coefficient. -/
theorem frameViaFactor_sectionHom
    (e : (Scheme.Modules.pullback b).obj M ≅ Scheme.Modules.unitObj C)
    (α : Scheme.Modules.unitObj D ⟶ M) :
    pullbackSectionHom f α ≫ (Scheme.Modules.frameViaFactor g b f hg e).hom =
      (Scheme.Modules.pullbackUnitIso g).inv ≫
        (Scheme.Modules.pullback g).map (pullbackSectionHom b α ≫ e.hom) ≫
          (Scheme.Modules.pullbackUnitIso g).hom := by
  let c := Scheme.Modules.frameFactorIso g b f hg
  have hnat := ((Scheme.Modules.pullbackComp g b) ≪≫
    Scheme.Modules.pullbackCongr hg).hom.naturality α
  simp only [Functor.comp_map] at hnat
  have hnat' : (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback b).map α) ≫
      (c M).hom = (c (Scheme.Modules.unitObj D)).hom ≫ (Scheme.Modules.pullback f).map α := hnat
  have hn : (Scheme.Modules.pullback f).map α ≫ (c M).inv =
      (c (Scheme.Modules.unitObj D)).inv ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback b).map α) := by
    apply (cancel_epi (c (Scheme.Modules.unitObj D)).hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← hnat', Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have huInv := congrArg Iso.inv (factorFrame_unit g b f hg)
  simp only [Scheme.Modules.frameViaFactor, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv] at huInv
  have hu : (Scheme.Modules.pullbackUnitIso f).inv ≫ (c (Scheme.Modules.unitObj D)).inv =
      (Scheme.Modules.pullbackUnitIso g).inv ≫
        (Scheme.Modules.pullback g).map (Scheme.Modules.pullbackUnitIso b).inv := by
    rw [← huInv, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold pullbackSectionHom
  simp only [Scheme.Modules.frameViaFactor, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  change _ = (Scheme.Modules.pullbackUnitIso g).inv ≫
    (Scheme.Modules.pullback g).map (Scheme.Modules.pullbackUnitIso b).inv ≫
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback b).map α) ≫
        (Scheme.Modules.pullback g).map e.hom ≫ (Scheme.Modules.pullbackUnitIso g).hom
  rw [← Category.assoc ((Scheme.Modules.pullback f).map α), hn]
  simp only [← Category.assoc]
  rw [hu]

/-- An ACTUAL original local scalar equation remains the SAME actual scalar
equation on the original residue-field pullback line. -/
theorem frameViaFactor_sectionHom_scalar
    (e : (Scheme.Modules.pullback b).obj M ≅ Scheme.Modules.unitObj C)
    (α : Scheme.Modules.unitObj D ⟶ M) (r : Γ(C, ⊤))
    (hr : pullbackSectionHom b α ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection r) :
    pullbackSectionHom f α ≫ (Scheme.Modules.frameViaFactor g b f hg e).hom =
      ModularCurves.unitEndomorphismOfTopSection (g.appTop.hom r) := by
  rw [frameViaFactor_sectionHom, hr]
  exact ModularCurves.pullback_unitEndomorphismOfTopSection g r

/-- The actual value at one of an original whole structure-line morphism. -/
def sectionAtOne {B : Scheme.{u}} {N : B.Modules}
    (α : Scheme.Modules.unitObj B ⟶ N) : Γ(N, (⊤ : B.Opens)) :=
  α.val.app (op ⊤) (show Γ(B, ⊤) from 1)

private theorem sectionAtOne_comp {B : Scheme.{u}} {N P : B.Modules}
    (α : Scheme.Modules.unitObj B ⟶ N) (β : N ⟶ P) :
    sectionAtOne (α ≫ β) = β.val.app (op ⊤) (sectionAtOne α) := by
  rfl

private theorem unitScalar_apply_one {B : Scheme.{u}} (r : Γ(B, ⊤)) :
    (ModularCurves.unitEndomorphismOfTopSection r).val.app (op ⊤)
      (show Γ(B, ⊤) from 1) = r := by
  rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
  simp only [homOfLE_refl, op_id, one_mul]
  erw [CategoryTheory.Functor.map_id]
  rfl

/-- The exact scalar of the true generic section in an actual transported frame. -/
theorem frameViaFactor_sectionHom_scalar_apply
    (e : (Scheme.Modules.pullback b).obj M ≅ Scheme.Modules.unitObj C)
    (α : Scheme.Modules.unitObj D ⟶ M) (r : Γ(C, ⊤))
    (hr : pullbackSectionHom b α ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection r) :
    (Scheme.Modules.frameViaFactor g b f hg e).hom.val.app (op ⊤)
      (sectionAtOne (pullbackSectionHom f α)) =
      g.appTop.hom r := by
  have h := frameViaFactor_sectionHom_scalar g b f hg e α r hr
  have happ := congrArg (fun q => q.val.app (op ⊤) (show Γ(B, ⊤) from 1)) h
  erw [Scheme.Modules.sheafOfModules_comp_app_apply] at happ
  exact happ.trans (unitScalar_apply_one _)

end EnvelopeProperty.SchemeLineSectionEvaluation

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of R)} [IsProper fX]
  (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v fX) {M : X.Modules}

/-- The actual original generic-fiber section of an original WHOLE global
structure-line morphism, constructed by the native pullback and unit isomorphism. -/
def fibreSection (α : Scheme.Modules.unitObj X ⟶ M) : Γ(genericLineModule y M, ⊤) :=
  SchemeLineSectionEvaluation.sectionAtOne
    (SchemeLineSectionEvaluation.pullbackSectionHom (X.fromSpecResidueField y.1.point) α)


end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
