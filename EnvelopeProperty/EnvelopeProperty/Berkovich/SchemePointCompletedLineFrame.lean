import EnvelopeProperty.Berkovich.SchemePointLaurentModuleEvaluation

/-! # Genuine proper-center frames in the original completed point field -/
open AlgebraicGeometry CategoryTheory Opposite
open scoped LaurentPolynomial NNReal Classical
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemePointCompletedLineFrame
open SchemeLineSectionEvaluation

private theorem affineUnit_sectionHom {Z W : Scheme.{u}} (h : W ⟶ Z) (M : Z.Modules)
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
  erw [← affineUnit_sectionHom]

private theorem factorFrameCoefficient {A B : Type u} [CommRing A] [CommRing B]
    {Z : Scheme.{u}} (ψ : A →+* B) (j : Spec (.of A) ⟶ Z) (h : Spec (.of B) ⟶ Z)
    (hc : Spec.map (CommRingCat.ofHom ψ) ≫ j = h) (M : Z.Modules)
    (e : (Scheme.Modules.pullback j).obj M ≅ Scheme.Modules.unitObj (Spec (.of A)))
    (m : Γ(M, ⊤)) :
    (Scheme.ΓSpecIso (.of B)).hom
      ((Scheme.Modules.frameViaFactor (Spec.map (CommRingCat.ofHom ψ)) j h hc e).hom.val.app (op ⊤)
        (Scheme.Modules.affinePullbackUnitTop h M m)) =
      ψ ((Scheme.ΓSpecIso (.of A)).hom
        (e.hom.val.app (op ⊤) (Scheme.Modules.affinePullbackUnitTop j M m))) := by
  let c := Spec.map (CommRingCat.ofHom ψ)
  let α := Scheme.Modules.topSectionHom M m
  let r : Γ(Spec (.of A), ⊤) := e.hom.val.app (op ⊤) (Scheme.Modules.affinePullbackUnitTop j M m)
  have hr := affineUnit_frameScalar j M e m
  have hs := frameViaFactor_sectionHom_scalar_apply c j h hc e α r hr
  have hu := congrArg (fun z : Γ((Scheme.Modules.pullback h).obj M, ⊤) =>
    (Scheme.ΓSpecIso (.of B)).hom ((Scheme.Modules.frameViaFactor c j h hc e).hom.app ⊤ z))
      (affineUnit_sectionHom h M m)
  have hv := congrArg (fun z : Γ(Spec (.of B), ⊤) => (Scheme.ΓSpecIso (.of B)).hom z) hs
  have hn := congrArg (fun k : Γ(Spec (.of A), ⊤) ⟶ CommRingCat.of B => k.hom r)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
  exact hu.trans (hv.trans hn)

private theorem frameFunctional_apply {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (x : RelativeSchemeValuedPoint v p)
    (M : X.Modules)
    (e : (Scheme.Modules.pullback (SchemeValuedPoint.fieldPoint x.1)).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1))))
    (m : AffineModuleFlatBaseChange.sections p M) :
    SchemePointLaurentModuleEvaluation.frameFunctional p x M e m =
      (Scheme.ΓSpecIso (.of (SchemeValuedPoint.H x.1))).hom
        (e.hom.val.app (op ⊤) (Scheme.Modules.affinePullbackUnitTop
          (SchemeValuedPoint.fieldPoint x.1) M m)) := rfl

private theorem nnnormResidue {Z : Scheme.{u}} (z : SchemeValuedPoint Z)
    (a : Z.residueField z.point) : ‖z.residueToH a‖₊ = z.residueVal a :=
  NNReal.eq (SchemeValuedPoint.norm_residueToH z a)

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (x : RelativeSchemeValuedPoint v p)

def completedFrame (M : X.Modules)
    (e : RelativeSchemeValuedPoint.genericLineModule x M ≅
      Scheme.Modules.unitObj (Spec (.of (X.residueField x.1.point)))) :
    (Scheme.Modules.pullback (SchemeValuedPoint.fieldPoint x.1)).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1))) :=
  Scheme.Modules.frameViaFactor
    (Spec.map (CommRingCat.ofHom (SchemeValuedPoint.residueToH x.1)))
    (X.fromSpecResidueField x.1.point) (SchemeValuedPoint.fieldPoint x.1) rfl e

theorem completedFrame_functional (M : X.Modules)
    (e : RelativeSchemeValuedPoint.genericLineModule x M ≅
      Scheme.Modules.unitObj (Spec (.of (X.residueField x.1.point))))
    (m : AffineModuleFlatBaseChange.sections p M) :
    SchemePointLaurentModuleEvaluation.frameFunctional p x M (completedFrame p x M e) m =
      SchemeValuedPoint.residueToH x.1
        ((Scheme.ΓSpecIso (.of (X.residueField x.1.point))).hom
          (e.hom.val.app (op ⊤)
            (Scheme.Modules.affinePullbackUnitTop (X.fromSpecResidueField x.1.point) M m))) := by
  refine (frameFunctional_apply p x M _ m).trans ?_
  exact factorFrameCoefficient (SchemeValuedPoint.residueToH x.1)
    (X.fromSpecResidueField x.1.point) (SchemeValuedPoint.fieldPoint x.1) rfl M e m

variable [IsProper p] (hb : ∀ r, v r ≤ 1)

/-- An actual original local frame at the true proper center gives the
actual completed-point frame via the native original residue embedding. -/
def completedLocalFrame (M : X.Modules) (U : X.Opens)
    (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme) :
    (Scheme.Modules.pullback (SchemeValuedPoint.fieldPoint x.1)).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1))) :=
  completedFrame p x M (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc e)

/-- The completed-frame functional is genuinely the residue embedding of
the original proper-center frame coefficient of EVERY original section. -/
theorem completedLocalFrame_functional (M : X.Modules) (U : X.Opens)
    (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (m : AffineModuleFlatBaseChange.sections p M) :
    SchemePointLaurentModuleEvaluation.frameFunctional p x M (completedFrame p x M (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc e)) m =
      SchemeValuedPoint.residueToH x.1
        ((Scheme.ΓSpecIso (.of (X.residueField x.1.point))).hom
          ((RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc e).hom.val.app (op ⊤)
            (Scheme.Modules.affinePullbackUnitTop (X.fromSpecResidueField x.1.point) M m))) := by
  exact completedFrame_functional p x M
    (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc e) m


/-- The absolute value of the actual proper-center completed-frame
functional equals the TRUE original model line norm of the actual
original native residue pullback-unit section, including zero. -/
theorem completedLocalFrame_nnnorm_eq_modelLineNorm (M : X.Modules)
    (hM : Scheme.Modules.IsInvertible M) (U : X.Opens)
    (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (m : AffineModuleFlatBaseChange.sections p M) :
    ‖SchemePointLaurentModuleEvaluation.frameFunctional p x M
      (completedFrame p x M (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc e)) m‖₊ =
      RelativeSchemeValuedPoint.modelLineNorm hb x hM
        (Scheme.Modules.affinePullbackUnitTop (X.fromSpecResidueField x.1.point) M m) := by
  have hf := completedFrame_functional p x M
    (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc e) m
  have hn := nnnormResidue x.1
    ((Scheme.ΓSpecIso (.of (X.residueField x.1.point))).hom
      ((RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc e).hom.val.app (op ⊤)
        (Scheme.Modules.affinePullbackUnitTop (X.fromSpecResidueField x.1.point) M m)))
  have hm := RelativeSchemeValuedPoint.modelLineNorm_eq_localFrame hb x hM U hc e
    (Scheme.Modules.affinePullbackUnitTop (X.fromSpecResidueField x.1.point) M m)
  exact (congrArg (fun z : SchemeValuedPoint.H x.1 => ‖z‖₊) hf).trans (hn.trans hm.symm)

/-- Genuine original invertibility derives an ACTUAL completed-point frame
whose functional computes the true original model norm for ALL original
sections simultaneously; no frame/norm certificate is supplied. -/
theorem exists_completedFrame_modelLineNorm (M : X.Modules)
    (hM : Scheme.Modules.IsInvertible M) :
    ∃ e : (Scheme.Modules.pullback (SchemeValuedPoint.fieldPoint x.1)).obj M ≅
        Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1))),
      ∀ m : AffineModuleFlatBaseChange.sections p M,
        ‖SchemePointLaurentModuleEvaluation.frameFunctional p x M e m‖₊ =
          RelativeSchemeValuedPoint.modelLineNorm hb x hM
            (Scheme.Modules.affinePullbackUnitTop (X.fromSpecResidueField x.1.point) M m) := by
  have hMt := hM
  obtain ⟨ι, U, hU, hframe⟩ := hMt
  have hc : RelativeSchemeValuedPoint.center hb x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
  obtain ⟨e⟩ := hframe i
  refine ⟨completedFrame p x M (RelativeSchemeValuedPoint.localFrameGenericIso hb x (U i) hi e), ?_⟩
  intro m
  exact completedLocalFrame_nnnorm_eq_modelLineNorm p x hb M hM (U i) hi e m


/-- Actual invertibility constructs a frame whose original Laurent
source evaluations have the weighted TRUE original model-line norms.
The original finite coefficient family precedes ALL points and radii. -/
theorem exists_completedFrame_finite_family_modelNorm [CompactSpace X] [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent] (hM : Scheme.Modules.IsInvertible M)
    (G : Finset (SchemeModuleLaurentCoefficients.pulledSections p M)) :
    ∃ e : (Scheme.Modules.pullback (SchemeValuedPoint.fieldPoint x.1)).obj M ≅
        Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1))),
      ∀ (r : ℝ≥0) (hr : 0 < r),
        G.sup (fun σ =>
          (Spectrum.laurentGauss (NormedField.valuation (K := SchemeValuedPoint.H x.1)) r hr).val
            (SchemePointLaurentModuleEvaluation.sourceCoefficient p x M e σ)) =
          (SchemeModuleLaurentCoefficients.terms p M G).sup
            (fun t => RelativeSchemeValuedPoint.modelLineNorm hb x hM
              (Scheme.Modules.affinePullbackUnitTop (X.fromSpecResidueField x.1.point) M t.1) *
              r ^ t.2) := by
  obtain ⟨e, he⟩ := exists_completedFrame_modelLineNorm p x hb M hM
  refine ⟨e, fun r hr => ?_⟩
  have h := SchemePointLaurentModuleEvaluation.sourceCoefficient_finite_family p x M G e r hr
  refine h.trans ?_
  apply Finset.sup_congr rfl
  intro t _
  exact congrArg (fun a => a * r ^ t.2) (he t.1)

end EnvelopeProperty.Berkovich.SchemePointCompletedLineFrame
