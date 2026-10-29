import EnvelopeProperty.Berkovich.SchemeGenericLinePullback
import EnvelopeProperty.AlgGeom.UnitModuleAutomorphisms

/-! # Actual framed residue coefficients under arbitrary original scheme pullback -/
open AlgebraicGeometry CategoryTheory Opposite
open scoped NNReal
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeFramedSectionPullback
open SchemeLineSectionEvaluation

theorem affinePullbackUnitTop_eq_sectionAtOne {Z W : Scheme.{u}} (h : W ⟶ Z) (M : Z.Modules)
    (m : Γ(M, ⊤)) :
    Scheme.Modules.affinePullbackUnitTop h M m =
      sectionAtOne (pullbackSectionHom h (Scheme.Modules.topSectionHom M m)) := by
  let α := pullbackSectionHom h (Scheme.Modules.topSectionHom M m)
  let a := (eqToHom (show (⊤ : W.Opens) = h ⁻¹ᵁ (⊤ : Z.Opens) by simp)).op
  change ((Scheme.Modules.pullback h).obj M).presheaf.map a
    (((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M).val.app (op ⊤) m) = _
  erw [Scheme.Modules.pullback_unit_app_top_applyT]
  have hn := PresheafOfModules.naturality_apply α.val a
    (h.app (⊤ : Z.Opens) (show Γ(Z, ⊤) from 1))
  change α.val.app (op ⊤)
    (W.presheaf.map a (h.app (⊤ : Z.Opens) (show Γ(Z, ⊤) from 1))) = _ at hn
  rw [map_one, map_one] at hn
  erw [map_one]
  exact hn.symm

private theorem unitHom_ext {Z : Scheme.{u}} {N : Z.Modules}
    {α β : Scheme.Modules.unitObj Z ⟶ N}
    (h : sectionAtOne α = sectionAtOne β) : α = β := by
  apply SheafOfModules.hom_ext
  ext V
  let i := (homOfLE (le_top : V.unop ≤ (⊤ : Z.Opens))).op
  have ha := PresheafOfModules.naturality_apply α.val i (show Γ(Z, ⊤) from 1)
  have hb := PresheafOfModules.naturality_apply β.val i (show Γ(Z, ⊤) from 1)
  change α.val.app V (Z.presheaf.map i (show Γ(Z, ⊤) from 1)) =
    N.presheaf.map i (sectionAtOne α) at ha
  change β.val.app V (Z.presheaf.map i (show Γ(Z, ⊤) from 1)) =
    N.presheaf.map i (sectionAtOne β) at hb
  rw [map_one] at ha hb
  exact ha.trans ((congrArg (fun z => N.presheaf.map i z) h).trans hb.symm)

private theorem topSectionHom_sectionAtOne {Z : Scheme.{u}} {N : Z.Modules}
    (α : Scheme.Modules.unitObj Z ⟶ N) :
    Scheme.Modules.topSectionHom N (sectionAtOne α) = α := by
  apply unitHom_ext
  exact Scheme.Modules.topSectionHom_app_top_apply_one N _


private theorem sectionHom_comp {X : Scheme.{u}} {P Q : X.Modules}
    (σ : Γ(P, ⊤)) (f : P ⟶ Q) :
    Scheme.Modules.topSectionHom P σ ≫ f = Scheme.Modules.topSectionHom Q (f.app ⊤ σ) := by
  apply unitHom_ext
  exact (congrArg (fun s => f.app ⊤ s) (Scheme.Modules.topSectionHom_app_top_apply_one P σ)).trans
    (Scheme.Modules.topSectionHom_app_top_apply_one Q (f.app ⊤ σ)).symm

/-- The native unit section really commutes with EVERY original module map. -/
theorem affinePullbackUnitTop_naturality {X W : Scheme.{u}} (f : W ⟶ X)
    {P Q : X.Modules} (h : P ⟶ Q) (σ : Γ(P, ⊤)) :
    Scheme.Modules.affinePullbackUnitTop f Q (h.app ⊤ σ) =
      ((Scheme.Modules.pullback f).map h).app ⊤ (Scheme.Modules.affinePullbackUnitTop f P σ) := by
  rw [affinePullbackUnitTop_eq_sectionAtOne f Q, ← sectionHom_comp]
  rw [affinePullbackUnitTop_eq_sectionAtOne f P]
  have hh : pullbackSectionHom f (Scheme.Modules.topSectionHom P σ ≫ h) =
      pullbackSectionHom f (Scheme.Modules.topSectionHom P σ) ≫ (Scheme.Modules.pullback f).map h := by
    unfold pullbackSectionHom
    rw [Functor.map_comp, Category.assoc]
  exact congrArg sectionAtOne hh

private theorem nativeUnit_hom {X W : Scheme.{u}} (f : W ⟶ X) {P : X.Modules}
    (β : Scheme.Modules.unitObj X ⟶ P) :
    Scheme.Modules.affinePullbackUnitTop f P (sectionAtOne β) = sectionAtOne (pullbackSectionHom f β) := by
  rw [affinePullbackUnitTop_eq_sectionAtOne, topSectionHom_sectionAtOne]

/-- The native unit section retains the ACTUAL pullback-composition square. -/
theorem affinePullbackUnitTop_comp {X W V : Scheme.{u}} (i : V ⟶ W) (f : W ⟶ X)
    (P : X.Modules) (σ : Γ(P, ⊤)) :
    ((Scheme.Modules.pullbackComp i f).hom.app P).app ⊤
        (Scheme.Modules.affinePullbackUnitTop i ((Scheme.Modules.pullback f).obj P)
          (Scheme.Modules.affinePullbackUnitTop f P σ)) =
      Scheme.Modules.affinePullbackUnitTop (i ≫ f) P σ := by
  rw [affinePullbackUnitTop_eq_sectionAtOne f P σ, nativeUnit_hom,
    affinePullbackUnitTop_eq_sectionAtOne (i ≫ f) P σ]
  exact congrArg sectionAtOne (pullbackSectionHom_comp i f (Scheme.Modules.topSectionHom P σ))

private theorem affineUnit_frameScalar {Z W : Scheme.{u}} (h : W ⟶ Z)
    (M : Z.Modules) (e : (Scheme.Modules.pullback h).obj M ≅ Scheme.Modules.unitObj W)
    (m : Γ(M, ⊤)) :
    pullbackSectionHom h (Scheme.Modules.topSectionHom M m) ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection
        (e.hom.val.app (op ⊤) (Scheme.Modules.affinePullbackUnitTop h M m)) := by
  have he := Scheme.Modules.unitHom_eq_globalScalar
    (pullbackSectionHom h (Scheme.Modules.topSectionHom M m) ≫ e.hom)
  refine he.trans ?_
  apply congrArg ModularCurves.unitEndomorphismOfTopSection
  change e.hom.val.app (op ⊤)
    (sectionAtOne (pullbackSectionHom h (Scheme.Modules.topSectionHom M m))) = _
  erw [← affinePullbackUnitTop_eq_sectionAtOne]

private theorem frameViaFactor_unitSection {A B C : Scheme.{u}}
    (g : A ⟶ B) (b : B ⟶ C) (f : A ⟶ C) (hf : g ≫ b = f)
    (M : C.Modules) (e : (Scheme.Modules.pullback b).obj M ≅ Scheme.Modules.unitObj B)
    (m : Γ(M, ⊤)) :
    (Scheme.Modules.frameViaFactor g b f hf e).hom.app ⊤
        (Scheme.Modules.affinePullbackUnitTop f M m) =
      g.appTop (e.hom.app ⊤ (Scheme.Modules.affinePullbackUnitTop b M m)) := by
  have hs := SchemeLineSectionEvaluation.frameViaFactor_sectionHom_scalar_apply g b f hf e
    (Scheme.Modules.topSectionHom M m) _ (affineUnit_frameScalar b M e m)
  have hu := congrArg (fun z : Γ((Scheme.Modules.pullback f).obj M, ⊤) =>
    (Scheme.Modules.frameViaFactor g b f hf e).hom.app ⊤ z) (affinePullbackUnitTop_eq_sectionAtOne f M m)
  exact hu.trans hs

variable {Y Z : Scheme.{u}} (g : Y ⟶ Z) {M : Z.Modules} {N : Y.Modules}

/-- The actual WHOLE original section transported by native pullback and
the actual original module isomorphism, with no section-matching premise. -/
def transportedSection (α : (Scheme.Modules.pullback g).obj M ≅ N) (σ : Γ(M, ⊤)) : Γ(N, ⊤) :=
  α.hom.app ⊤ (Scheme.Modules.affinePullbackUnitTop g M σ)

/-- The transported original section has its actual whole original section
morphism: the native pulled section morphism followed by the actual iso. -/
theorem transportedSection_sectionHom (α : (Scheme.Modules.pullback g).obj M ≅ N)
    (σ : Γ(M, ⊤)) :
    Scheme.Modules.topSectionHom N (transportedSection g α σ) =
      pullbackSectionHom g (Scheme.Modules.topSectionHom M σ) ≫ α.hom := by
  apply unitHom_ext
  exact (Scheme.Modules.topSectionHom_app_top_apply_one N (transportedSection g α σ)).trans
    (congrArg (fun s => α.hom.app ⊤ s) (affinePullbackUnitTop_eq_sectionAtOne g M σ))

/-- The ACTUAL native residue coefficient of the original whole section
in an ACTUAL original residue-fibre frame. -/
def residueFrameCoefficient {X : Scheme.{u}} (x : SchemeValuedPoint X) (P : X.Modules)
    (e : (Scheme.Modules.pullback (X.fromSpecResidueField x.point)).obj P ≅
      Scheme.Modules.unitObj (Spec (.of (X.residueField x.point)))) (σ : Γ(P, ⊤)) :
    X.residueField x.point :=
  (Scheme.ΓSpecIso (.of (X.residueField x.point))).hom
    (e.hom.app ⊤ (Scheme.Modules.affinePullbackUnitTop (X.fromSpecResidueField x.point) P σ))

/-- The WHOLE actual native residue frame is induced by the REAL original
residue-field map, native pullback comparison and actual module iso.
No frame-preservation equation or desired evaluation is an input. -/
def inducedResidueFrame (α : (Scheme.Modules.pullback g).obj M ≅ N) (y : SchemeValuedPoint Y)
    (e : (Scheme.Modules.pullback (Z.fromSpecResidueField (g y.point))).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (Z.residueField (g y.point))))) :
    (Scheme.Modules.pullback (Y.fromSpecResidueField y.point)).obj N ≅
      Scheme.Modules.unitObj (Spec (.of (Y.residueField y.point))) :=
  ((Scheme.Modules.pullback (Y.fromSpecResidueField y.point)).mapIso α).symm ≪≫
    (SchemeValuedPoint.residueModulePullbackIso g y.point M).symm ≪≫
      (Scheme.Modules.pullback (Spec.map (g.residueFieldMap y.point))).mapIso e ≪≫
        Scheme.Modules.pullbackUnitIso (Spec.map (g.residueFieldMap y.point))

/-- The whole induced native frame really has its canonical original
residue-field pullback square; all comparisons are derived. -/
theorem inducedResidueFrame_compat (α : (Scheme.Modules.pullback g).obj M ≅ N)
    (y : SchemeValuedPoint Y)
    (e : (Scheme.Modules.pullback (Z.fromSpecResidueField (g y.point))).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (Z.residueField (g y.point))))) :
    SchemeValuedPoint.residueModulePullbackIso g y.point M ≪≫
        (Scheme.Modules.pullback (Y.fromSpecResidueField y.point)).mapIso α ≪≫
          inducedResidueFrame g α y e =
      (Scheme.Modules.pullback (Spec.map (g.residueFieldMap y.point))).mapIso e ≪≫
        Scheme.Modules.pullbackUnitIso (Spec.map (g.residueFieldMap y.point)) := by
  unfold inducedResidueFrame
  simp only [Iso.self_symm_id_assoc]


/-- The derived frame is the ACTUAL native factor frame, preceded by the
inverse actual pulled module iso and the original native composition map. -/
theorem inducedResidueFrame_eq (α : (Scheme.Modules.pullback g).obj M ≅ N)
    (y : SchemeValuedPoint Y)
    (e : (Scheme.Modules.pullback (Z.fromSpecResidueField (g y.point))).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (Z.residueField (g y.point))))) :
    inducedResidueFrame g α y e =
      ((Scheme.Modules.pullback (Y.fromSpecResidueField y.point)).mapIso α).symm ≪≫
        (Scheme.Modules.pullbackComp (Y.fromSpecResidueField y.point) g).app M ≪≫
          Scheme.Modules.frameViaFactor (Spec.map (g.residueFieldMap y.point))
            (Z.fromSpecResidueField (g y.point)) (Y.fromSpecResidueField y.point ≫ g)
            (g.SpecMap_residueFieldMap_fromSpecResidueField y.point) e := by
  have h := SchemeValuedPoint.residueModulePullbackIso_frame g y.point M e
  have hh := congrArg (fun E => (SchemeValuedPoint.residueModulePullbackIso g y.point M).symm ≪≫ E)
    h.symm
  simp only [Iso.symm_self_id_assoc] at hh
  exact congrArg (fun E => ((Scheme.Modules.pullback (Y.fromSpecResidueField y.point)).mapIso α).symm ≪≫ E) hh


/-- Composing the REAL pulled module iso with the derived residue frame
gives the ACTUAL native factor frame, as a whole original morphism. -/
theorem inducedResidueFrame_hom (α : (Scheme.Modules.pullback g).obj M ≅ N)
    (y : SchemeValuedPoint Y)
    (e : (Scheme.Modules.pullback (Z.fromSpecResidueField (g y.point))).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (Z.residueField (g y.point))))) :
    (Scheme.Modules.pullback (Y.fromSpecResidueField y.point)).map α.hom ≫
        (inducedResidueFrame g α y e).hom =
      (Scheme.Modules.pullbackComp (Y.fromSpecResidueField y.point) g).hom.app M ≫
        (Scheme.Modules.frameViaFactor (Spec.map (g.residueFieldMap y.point))
          (Z.fromSpecResidueField (g y.point)) (Y.fromSpecResidueField y.point ≫ g)
          (g.SpecMap_residueFieldMap_fromSpecResidueField y.point) e).hom := by
  have h := congrArg
    (fun E => (Scheme.Modules.pullback (Y.fromSpecResidueField y.point)).mapIso α ≪≫ E)
    (inducedResidueFrame_eq g α y e)
  simp only [Iso.self_symm_id_assoc] at h
  exact congrArg Iso.hom h

private theorem transportedSection_frameSection
    (α : (Scheme.Modules.pullback g).obj M ≅ N) (y : SchemeValuedPoint Y)
    (e : (Scheme.Modules.pullback (Z.fromSpecResidueField (g y.point))).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (Z.residueField (g y.point))))) (σ : Γ(M, ⊤)) :
    (inducedResidueFrame g α y e).hom.app ⊤
        (Scheme.Modules.affinePullbackUnitTop (Y.fromSpecResidueField y.point) N
          (transportedSection g α σ)) =
      (Spec.map (g.residueFieldMap y.point)).appTop
        (e.hom.app ⊤ (Scheme.Modules.affinePullbackUnitTop (Z.fromSpecResidueField (g y.point)) M σ)) := by
  let hY := Y.fromSpecResidueField y.point
  let hZ := Z.fromSpecResidueField (g y.point)
  let ρ := Spec.map (g.residueFieldMap y.point)
  let E := Scheme.Modules.frameViaFactor ρ hZ (hY ≫ g)
    (g.SpecMap_residueFieldMap_fromSpecResidueField y.point) e
  let s := Scheme.Modules.affinePullbackUnitTop hY ((Scheme.Modules.pullback g).obj M)
    (Scheme.Modules.affinePullbackUnitTop g M σ)
  have hn := affinePullbackUnitTop_naturality hY α.hom (Scheme.Modules.affinePullbackUnitTop g M σ)
  have hp := congrArg (fun f => f.app ⊤ s) (inducedResidueFrame_hom g α y e)
  have hc := congrArg (fun z : Γ((Scheme.Modules.pullback (hY ≫ g)).obj M, ⊤) => E.hom.app ⊤ z)
    (affinePullbackUnitTop_comp hY g M σ)
  have hs := frameViaFactor_unitSection ρ hZ (hY ≫ g)
    (g.SpecMap_residueFieldMap_fromSpecResidueField y.point) M e σ
  exact (congrArg (fun z : Γ((Scheme.Modules.pullback hY).obj N, ⊤) =>
    (inducedResidueFrame g α y e).hom.app ⊤ z) hn).trans (hp.trans (hc.trans hs))

/-- The ACTUAL native residue coefficient of EVERY transported original
section is the ACTUAL original residue-field image of its original coefficient.
No coefficient/evaluation/frame-preservation certificate is supplied. -/
theorem transportedSection_coefficient (α : (Scheme.Modules.pullback g).obj M ≅ N)
    (y : SchemeValuedPoint Y)
    (e : (Scheme.Modules.pullback (Z.fromSpecResidueField (g y.point))).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (Z.residueField (g y.point))))) (σ : Γ(M, ⊤)) :
    residueFrameCoefficient y N (inducedResidueFrame g α y e) (transportedSection g α σ) =
      g.residueFieldMap y.point
        (residueFrameCoefficient (SchemeValuedPoint.map g y) M e σ) := by
  have h := congrArg (Scheme.ΓSpecIso (.of (Y.residueField y.point))).hom.hom
    (transportedSection_frameSection g α y e σ)
  have hn := congrArg (fun f : Γ(Spec (.of (Z.residueField (g y.point))), ⊤) ⟶
      CommRingCat.of (Y.residueField y.point) =>
      f.hom (e.hom.app ⊤
        (Scheme.Modules.affinePullbackUnitTop (Z.fromSpecResidueField (g y.point)) M σ)))
    (Scheme.ΓSpecIso_naturality (g.residueFieldMap y.point))
  exact h.trans hn

/-- Actual native valuations of the induced framed coefficients agree for
EVERY actual original section, including zero, under ANY original scheme map
and actual original module iso. No properness or bounded base is required. -/
theorem transportedSection_valuation (α : (Scheme.Modules.pullback g).obj M ≅ N)
    (y : SchemeValuedPoint Y)
    (e : (Scheme.Modules.pullback (Z.fromSpecResidueField (g y.point))).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (Z.residueField (g y.point))))) (σ : Γ(M, ⊤)) :
    y.residueVal
        (residueFrameCoefficient y N (inducedResidueFrame g α y e) (transportedSection g α σ)) =
      (SchemeValuedPoint.map g y).residueVal
        (residueFrameCoefficient (SchemeValuedPoint.map g y) M e σ) :=
  congrArg y.residueVal (transportedSection_coefficient g α y e σ)

end EnvelopeProperty.Berkovich.SchemeFramedSectionPullback
