import EnvelopeProperty.Berkovich.SchemeFramedSectionPullback
import EnvelopeProperty.AlgGeom.SchemeLineFramePullbackCoherence

/-! # Actual original factor frames and native whole-section evaluation -/
open AlgebraicGeometry CategoryTheory Opposite
open scoped NNReal
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeFramedSectionFactor
open SchemeFramedSectionPullback SchemeLineSectionEvaluation

/-- The two actual residue factors agree by the actual monomorphism. -/
theorem residueFactor_unique {Y Z U : Scheme.{u}} (g : Y ⟶ Z) (b : U ⟶ Z) [Mono b]
    (k : Y ⟶ U) (hk : k ≫ b = g) (y : SchemeValuedPoint Y)
    (q : Spec (.of (Z.residueField (g y.point))) ⟶ U)
    (hq : q ≫ b = Z.fromSpecResidueField (g y.point)) :
    Y.fromSpecResidueField y.point ≫ k = Spec.map (g.residueFieldMap y.point) ≫ q := by
  apply (cancel_mono b).mp
  rw [Category.assoc, hk, Category.assoc, hq]
  exact (g.SpecMap_residueFieldMap_fromSpecResidueField y.point).symm

/-- Pullback of the actual factor frame retains its whole native composition comparison. -/
theorem pulledFactorFrame {V Y U Z : Scheme.{u}} (i : V ⟶ Y) (k : Y ⟶ U)
    (b : U ⟶ Z) (g : Y ⟶ Z) (hk : k ≫ b = g) {M : Z.Modules}
    (e : (Scheme.Modules.pullback b).obj M ≅ Scheme.Modules.unitObj U) :
    (Scheme.Modules.pullback i).mapIso (Scheme.Modules.frameViaFactor k b g hk e) ≪≫
        Scheme.Modules.pullbackUnitIso i =
      (Scheme.Modules.pullbackComp i g).app M ≪≫
        Scheme.Modules.frameViaFactor (i ≫ k) b (i ≫ g)
          (by rw [Category.assoc, hk]) e := by
  have hc := Scheme.Modules.frameViaFactor_comp i k b g hk (i ≫ g) rfl e
  have hp := Scheme.Modules.frameFactorIso_pairing i g (i ≫ g) rfl
    (Iso.refl ((Scheme.Modules.pullback (i ≫ g)).obj M))
    (Scheme.Modules.frameViaFactor k b g hk e)
  simpa only [Iso.trans_refl, Iso.refl_trans] using
    hp.symm.trans (congrArg (fun E => (Scheme.Modules.pullbackComp i g).app M ≪≫ E) hc)

/-- The actual source frame from the given local factor and actual module iso. -/
def sourceFrame {Y U Z : Scheme.{u}} (g : Y ⟶ Z) (b : U ⟶ Z) (k : Y ⟶ U)
    (hk : k ≫ b = g) {M : Z.Modules} {N : Y.Modules}
    (α : (Scheme.Modules.pullback g).obj M ≅ N)
    (e : (Scheme.Modules.pullback b).obj M ≅ Scheme.Modules.unitObj U) :
    N ≅ Scheme.Modules.unitObj Y :=
  α.symm ≪≫ Scheme.Modules.frameViaFactor k b g hk e

/-- The actual induced residue frame equals the genuine pulled global source frame. -/
theorem inducedResidueFrame_eq_sourceFrame {Y U Z : Scheme.{u}}
    (g : Y ⟶ Z) (b : U ⟶ Z) [Mono b] (k : Y ⟶ U) (hk : k ≫ b = g)
    {M : Z.Modules} {N : Y.Modules} (α : (Scheme.Modules.pullback g).obj M ≅ N)
    (e : (Scheme.Modules.pullback b).obj M ≅ Scheme.Modules.unitObj U)
    (y : SchemeValuedPoint Y) (q : Spec (.of (Z.residueField (g y.point))) ⟶ U)
    (hq : q ≫ b = Z.fromSpecResidueField (g y.point)) :
    inducedResidueFrame g α y
        (Scheme.Modules.frameViaFactor q b (Z.fromSpecResidueField (g y.point)) hq e) =
      (Scheme.Modules.pullback (Y.fromSpecResidueField y.point)).mapIso
          (sourceFrame g b k hk α e) ≪≫
        Scheme.Modules.pullbackUnitIso (Y.fromSpecResidueField y.point) := by
  rw [inducedResidueFrame_eq]
  rw [Scheme.Modules.frameViaFactor_comp]
  have hqk := residueFactor_unique g b k hk y q hq
  simp only [← hqk]
  rw [← pulledFactorFrame (Y.fromSpecResidueField y.point) k b g hk e]
  apply Iso.ext
  simp only [sourceFrame, Functor.mapIso_trans, Functor.mapIso_symm,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]

/-- Native unit comparison on every original scalar whole section. -/
theorem affinePullbackUnitTop_unit {Y Z : Scheme.{u}} (h : Y ⟶ Z) (a : Γ(Z, ⊤)) :
    (Scheme.Modules.pullbackUnitIso h).hom.app ⊤
        (Scheme.Modules.affinePullbackUnitTop h (Scheme.Modules.unitObj Z) a) = h.appTop a := by
  have hs : Scheme.Modules.topSectionHom (Scheme.Modules.unitObj Z) a =
      ModularCurves.unitEndomorphismOfTopSection a := by
    exact (Scheme.Modules.unitHom_eq_globalScalar _).trans
      (congrArg ModularCurves.unitEndomorphismOfTopSection
        (Scheme.Modules.topSectionHom_app_top_apply_one (Scheme.Modules.unitObj Z) a))
  have hp : pullbackSectionHom h (Scheme.Modules.topSectionHom (Scheme.Modules.unitObj Z) a) ≫
      (Scheme.Modules.pullbackUnitIso h).hom =
        ModularCurves.unitEndomorphismOfTopSection (h.appTop a) := by
    unfold pullbackSectionHom
    rw [hs]
    exact ModularCurves.pullback_unitEndomorphismOfTopSection h a
  have hv := congrArg sectionAtOne hp
  change (Scheme.Modules.pullbackUnitIso h).hom.app ⊤
      (sectionAtOne (pullbackSectionHom h (Scheme.Modules.topSectionHom (Scheme.Modules.unitObj Z) a))) =
        sectionAtOne (ModularCurves.unitEndomorphismOfTopSection (h.appTop a)) at hv
  have hu := congrArg (fun z : Γ((Scheme.Modules.pullback h).obj (Scheme.Modules.unitObj Z), ⊤) =>
    (Scheme.Modules.pullbackUnitIso h).hom.app ⊤ z)
    (affinePullbackUnitTop_eq_sectionAtOne h (Scheme.Modules.unitObj Z) a)
  refine hu.trans (hv.trans ?_)
  unfold sectionAtOne
  rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
  simp only [homOfLE_refl, op_id, one_mul]
  erw [CategoryTheory.Functor.map_id]
  rfl

/-- A true global frame's residue coefficient is the actual native residue evaluation. -/
theorem residueFrameCoefficient_pullbackFrame {Y : Scheme.{u}} (y : SchemeValuedPoint Y)
    {N : Y.Modules} (E : N ≅ Scheme.Modules.unitObj Y) (τ : Γ(N, ⊤)) :
    residueFrameCoefficient y N
        ((Scheme.Modules.pullback (Y.fromSpecResidueField y.point)).mapIso E ≪≫
          Scheme.Modules.pullbackUnitIso (Y.fromSpecResidueField y.point)) τ =
      Y.Γevaluation y.point (E.hom.app ⊤ τ) := by
  let h := Y.fromSpecResidueField y.point
  have hn := affinePullbackUnitTop_naturality h E.hom τ
  have hu := affinePullbackUnitTop_unit h (E.hom.app ⊤ τ)
  have hs : ((Scheme.Modules.pullback h).mapIso E ≪≫ Scheme.Modules.pullbackUnitIso h).hom.app ⊤
        (Scheme.Modules.affinePullbackUnitTop h N τ) = h.appTop (E.hom.app ⊤ τ) :=
    (congrArg (fun z => (Scheme.Modules.pullbackUnitIso h).hom.app ⊤ z) hn).symm.trans hu
  have he := congrArg (fun f : Γ(Y, ⊤) ⟶ CommRingCat.of (Y.residueField y.point) =>
    f.hom (E.hom.app ⊤ τ)) (SchemeValuedPoint.fromSpecResidueField_appTop y.point)
  exact (congrArg (Scheme.ΓSpecIso (.of (Y.residueField y.point))).hom.hom hs).trans he

/-- Actual scalar coefficient evaluation in the original source factor frame. -/
theorem sourceFrame_coefficient {Y U Z : Scheme.{u}}
    (g : Y ⟶ Z) (b : U ⟶ Z) [Mono b] (k : Y ⟶ U) (hk : k ≫ b = g)
    {M : Z.Modules} {N : Y.Modules} (α : (Scheme.Modules.pullback g).obj M ≅ N)
    (e : (Scheme.Modules.pullback b).obj M ≅ Scheme.Modules.unitObj U)
    (y : SchemeValuedPoint Y) (q : Spec (.of (Z.residueField (g y.point))) ⟶ U)
    (hq : q ≫ b = Z.fromSpecResidueField (g y.point)) (σ : Γ(M, ⊤)) :
    Y.Γevaluation y.point ((sourceFrame g b k hk α e).hom.app ⊤ (transportedSection g α σ)) =
      g.residueFieldMap y.point (residueFrameCoefficient (SchemeValuedPoint.map g y) M
        (Scheme.Modules.frameViaFactor q b (Z.fromSpecResidueField (g y.point)) hq e) σ) := by
  have h := transportedSection_coefficient g α y
    (Scheme.Modules.frameViaFactor q b (Z.fromSpecResidueField (g y.point)) hq e) σ
  rw [inducedResidueFrame_eq_sourceFrame, residueFrameCoefficient_pullbackFrame] at h
  exact h

/-- Actual native evaluation of the source frame coefficient preserves the original valuation. -/
theorem sourceFrame_valuation {Y U Z : Scheme.{u}}
    (g : Y ⟶ Z) (b : U ⟶ Z) [Mono b] (k : Y ⟶ U) (hk : k ≫ b = g)
    {M : Z.Modules} {N : Y.Modules} (α : (Scheme.Modules.pullback g).obj M ≅ N)
    (e : (Scheme.Modules.pullback b).obj M ≅ Scheme.Modules.unitObj U)
    (y : SchemeValuedPoint Y) (q : Spec (.of (Z.residueField (g y.point))) ⟶ U)
    (hq : q ≫ b = Z.fromSpecResidueField (g y.point)) (σ : Γ(M, ⊤)) :
    SchemeValuedPoint.eval y ⊤ (by trivial)
        ((sourceFrame g b k hk α e).hom.app ⊤ (transportedSection g α σ)) =
      (SchemeValuedPoint.map g y).residueVal
        (residueFrameCoefficient (SchemeValuedPoint.map g y) M
          (Scheme.Modules.frameViaFactor q b (Z.fromSpecResidueField (g y.point)) hq e) σ) := by
  exact congrArg y.residueVal (sourceFrame_coefficient g b k hk α e y q hq σ)

end EnvelopeProperty.Berkovich.SchemeFramedSectionFactor
