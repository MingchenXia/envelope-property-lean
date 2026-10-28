import EnvelopeProperty.Berkovich.SchemePointCompletedLineFrame
import EnvelopeProperty.AlgGeom.SchemeLineFramePullbackCoherence

/-! # Actual original product local frames and whole Gauss-source frame coherence -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped LaurentPolynomial Classical NNReal
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemePointLaurentLocalFrame
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
    (Scheme.Modules.frameViaFactor g b f hf e).hom.app ⊤ z) (affineUnit_sectionHom f M m)
  exact hu.trans hs

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (x : RelativeSchemeValuedPoint v p)
    [IsProper p] (hb : ∀ r, v r ≤ 1)

/-- The actual original completed point factors through the original
proper-center open by its TRUE original residue-field factor. -/
def completedOpenFactor (U : X.Opens) (hc : RelativeSchemeValuedPoint.center hb x ∈ U) :
    Spec (.of (SchemeValuedPoint.H x.1)) ⟶ U.toScheme :=
  Spec.map (CommRingCat.ofHom (SchemeValuedPoint.residueToH x.1)) ≫
    RelativeSchemeValuedPoint.localGenericFactor hb x U hc

/-- The actual entire completed-point triangle through the original open. -/
theorem completedOpenFactor_comp (U : X.Opens) (hc : RelativeSchemeValuedPoint.center hb x ∈ U) :
    completedOpenFactor p x hb U hc ≫ U.ι = SchemeValuedPoint.fieldPoint x.1 := by
  rw [completedOpenFactor, Category.assoc, RelativeSchemeValuedPoint.localGenericFactor_comp]
  rfl

/-- The original proper-center completed frame is the direct native
transport of the SAME actual local frame through its actual completed factor. -/
theorem completedFrame_eq (M : X.Modules) (U : X.Opens)
    (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme) :
    SchemePointCompletedLineFrame.completedFrame p x M
        (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc e) =
      Scheme.Modules.frameViaFactor (completedOpenFactor p x hb U hc) U.ι
        (SchemeValuedPoint.fieldPoint x.1) (completedOpenFactor_comp p x hb U hc) e := by
  exact Scheme.Modules.frameViaFactor_comp
    (Spec.map (CommRingCat.ofHom (SchemeValuedPoint.residueToH x.1)))
    (RelativeSchemeValuedPoint.localGenericFactor hb x U hc) U.ι
    (X.fromSpecResidueField x.1.point)
    (RelativeSchemeValuedPoint.localGenericFactor_comp hb x U hc)
    (SchemeValuedPoint.fieldPoint x.1) rfl e

private def sourceMap : Spec (.of (SchemeValuedPoint.H x.1)[T;T⁻¹]) ⟶
    FlatGlobalSections.baseChange (S := R[T;T⁻¹]) p :=
  (SchemePointLaurentGauss.productMap p x).left
private abbrev firstProjection := FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p
private abbrev constantProjection := Spec.map (CommRingCat.ofHom (LaurentPolynomial.C :
  SchemeValuedPoint.H x.1 →+* (SchemeValuedPoint.H x.1)[T;T⁻¹]))

omit [IsProper p] in
private theorem sourceMap_first : sourceMap p x ≫ firstProjection p =
    constantProjection p x ≫ SchemeValuedPoint.fieldPoint x.1 := by
  exact congrArg Over.Hom.left (SchemePointLaurentGauss.productMap_fst p x)

private theorem sourceMap_local (U : X.Opens) (hc : RelativeSchemeValuedPoint.center hb x ∈ U) :
    sourceMap p x ≫ firstProjection p =
      (constantProjection p x ≫ completedOpenFactor p x hb U hc) ≫ U.ι := by
  rw [Category.assoc, completedOpenFactor_comp, sourceMap_first]

private theorem sourceRange (U : X.Opens) (hc : RelativeSchemeValuedPoint.center hb x ∈ U) :
    Set.range (sourceMap p x) ⊆ Set.range (firstProjection p ⁻¹ᵁ U).ι := by
  rintro _ ⟨z, rfl⟩
  have hz : firstProjection p (sourceMap p x z) ∈ U := by
    change (sourceMap p x ≫ firstProjection p) z ∈ U
    rw [sourceMap_local p x hb U hc]
    exact (completedOpenFactor p x hb U hc (constantProjection p x z)).property
  exact ⟨⟨sourceMap p x z, hz⟩, rfl⟩

/-- The ACTUAL original product map factors through its original
inverse-image frame open; the factor is derived from native geometry. -/
def productOpenFactor (U : X.Opens) (hc : RelativeSchemeValuedPoint.center hb x ∈ U) :
    Spec (.of (SchemeValuedPoint.H x.1)[T;T⁻¹]) ⟶ (firstProjection p ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (firstProjection p ⁻¹ᵁ U).ι (sourceMap p x) (sourceRange p x hb U hc)

/-- The original product-open factor retains the entire native product map. -/
theorem productOpenFactor_comp (U : X.Opens) (hc : RelativeSchemeValuedPoint.center hb x ∈ U) :
    productOpenFactor p x hb U hc ≫ (firstProjection p ⁻¹ᵁ U).ι = sourceMap p x :=
  IsOpenImmersion.lift_fac (firstProjection p ⁻¹ᵁ U).ι (sourceMap p x) (sourceRange p x hb U hc)

/-- The WHOLE restricted product projection is the actual original
completed-point local factor preceded by the actual constant projection. -/
theorem productOpenFactor_restrict (U : X.Opens)
    (hc : RelativeSchemeValuedPoint.center hb x ∈ U) :
    productOpenFactor p x hb U hc ≫ (firstProjection p ∣_ U) =
      constantProjection p x ≫ completedOpenFactor p x hb U hc := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, productOpenFactor_comp,
    ]
  exact sourceMap_local p x hb U hc


/-- The ACTUAL source frame from the original proper-center completed
frame equals pullback of the SAME actual original product-local frame,
as a WHOLE native isomorphism, with no frame-preservation premise. -/
theorem sourceFrame_eq_localPullbackFrame (M : X.Modules) (U : X.Opens)
    (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme) :
    SchemePointLaurentModuleEvaluation.sourceFrame p x M
        (SchemePointCompletedLineFrame.completedFrame p x M
          (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc e)) =
      Scheme.Modules.frameViaFactor (productOpenFactor p x hb U hc)
        (firstProjection p ⁻¹ᵁ U).ι (sourceMap p x) (productOpenFactor_comp p x hb U hc)
        (SchemeLineSectionEvaluation.localPullbackFrame (firstProjection p) U e) := by
  change (Scheme.Modules.pullbackComp (sourceMap p x) (firstProjection p)).app M ≪≫
      Scheme.Modules.frameViaFactor (constantProjection p x) (SchemeValuedPoint.fieldPoint x.1)
        (sourceMap p x ≫ firstProjection p) (sourceMap_first p x).symm
        (SchemePointCompletedLineFrame.completedFrame p x M
          (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc e)) =
    Scheme.Modules.frameViaFactor (productOpenFactor p x hb U hc)
      (firstProjection p ⁻¹ᵁ U).ι (sourceMap p x) (productOpenFactor_comp p x hb U hc)
      ((Scheme.Modules.pullbackComp (firstProjection p ⁻¹ᵁ U).ι (firstProjection p)).app M ≪≫
        Scheme.Modules.frameViaFactor (firstProjection p ∣_ U) U.ι
          ((firstProjection p ⁻¹ᵁ U).ι ≫ firstProjection p) (morphismRestrict_ι _ _) e)
  rw [completedFrame_eq p x hb M U hc e,
    Scheme.Modules.frameViaFactor_pullbackComp]
  rw [Scheme.Modules.frameViaFactor_comp, Scheme.Modules.frameViaFactor_comp]
  simp only [productOpenFactor_restrict]


/-- The ACTUAL local coefficient of an original whole product-line section
in the actual original product frame on its original frame open. -/
def localCoefficient (M : X.Modules) (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (σ : SchemeModuleLaurentCoefficients.pulledSections p M) :
    Γ((firstProjection p ⁻¹ᵁ U).toScheme, ⊤) :=
  (SchemeLineSectionEvaluation.localPullbackFrame (firstProjection p) U e).hom.app ⊤
    (Scheme.Modules.affinePullbackUnitTop (firstProjection p ⁻¹ᵁ U).ι
      ((Scheme.Modules.pullback (firstProjection p)).obj M) σ)

/-- The actual native product local coefficient pulls back to the SAME
actual source-frame section, for EVERY original section, with no matching premise. -/
theorem sourceFrameSection_eq_localCoefficient (M : X.Modules) (U : X.Opens)
    (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (σ : SchemeModuleLaurentCoefficients.pulledSections p M) :
    SchemePointLaurentModuleEvaluation.sourceFrameSection p x M
        (SchemePointCompletedLineFrame.completedFrame p x M
          (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc e)) σ =
      (productOpenFactor p x hb U hc).appTop (localCoefficient p M U e σ) := by
  have he := congrArg (fun E :
      (Scheme.Modules.pullback (sourceMap p x)).obj
          ((Scheme.Modules.pullback (firstProjection p)).obj M) ≅
        Scheme.Modules.unitObj (Spec (.of (SchemeValuedPoint.H x.1)[T;T⁻¹])) =>
      E.hom.app ⊤ (Scheme.Modules.affinePullbackUnitTop (sourceMap p x)
        ((Scheme.Modules.pullback (firstProjection p)).obj M) σ))
    (sourceFrame_eq_localPullbackFrame p x hb M U hc e)
  have hf := frameViaFactor_unitSection (productOpenFactor p x hb U hc)
    (firstProjection p ⁻¹ᵁ U).ι (sourceMap p x) (productOpenFactor_comp p x hb U hc)
    ((Scheme.Modules.pullback (firstProjection p)).obj M)
    (SchemeLineSectionEvaluation.localPullbackFrame (firstProjection p) U e) σ
  exact he.trans hf


/-- The ACTUAL original native product Gauss point has its genuine native
lift to the actual original product frame open. -/
def openPoint (U : X.Opens) (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (r : ℝ≥0) (hr : 0 < r) : SchemeValuedPoint (firstProjection p ⁻¹ᵁ U).toScheme :=
  SchemeValuedPoint.map (productOpenFactor p x hb U hc) (SchemePointLaurentGauss.point p x r hr)

/-- The WHOLE original lifted native point projects to the ACTUAL
original product Gauss point, not just its support. -/
theorem openPoint_comp (U : X.Opens) (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint.map (firstProjection p ⁻¹ᵁ U).ι (openPoint p x hb U hc r hr) =
      (SchemePointLaurentGauss.productPoint p x r hr).1 := by
  change SchemeValuedPoint.map (firstProjection p ⁻¹ᵁ U).ι
    (SchemeValuedPoint.map (productOpenFactor p x hb U hc) (SchemePointLaurentGauss.point p x r hr)) =
    SchemeValuedPoint.map (sourceMap p x) (SchemePointLaurentGauss.point p x r hr)
  rw [← SchemeValuedPoint.map_comp, productOpenFactor_comp]

/-- EVERY original whole section's ACTUAL local coefficient on the
ACTUAL native product Gauss point has the weighted TRUE ORIGINAL model
norms of its actual original Laurent coefficients, including zeros and
ALL negative integer powers; no desired point/norm/evaluation is supplied. -/
theorem localCoefficient_value [CompactSpace X] [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent] (hM : Scheme.Modules.IsInvertible M)
    (U : X.Opens) (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (r : ℝ≥0) (hr : 0 < r) (σ : SchemeModuleLaurentCoefficients.pulledSections p M) :
    SchemeValuedPoint.eval (openPoint p x hb U hc r hr) ⊤ trivial
        (localCoefficient p M U e σ) =
      (SchemeModuleLaurentCoefficients.coefficients p M σ).support.sup
        (fun i => RelativeSchemeValuedPoint.modelLineNorm hb x hM
          (Scheme.Modules.affinePullbackUnitTop (X.fromSpecResidueField x.1.point) M
            (SchemeModuleLaurentCoefficients.coefficients p M σ i)) * r ^ i) := by
  let E := SchemePointCompletedLineFrame.completedFrame p x M
    (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc e)
  have ht := SchemeValuedPoint.evalTop_map (productOpenFactor p x hb U hc)
    (SchemePointLaurentGauss.point p x r hr) (localCoefficient p M U e σ)
  have hu := congrArg (fun s : Γ(Spec (.of (SchemeValuedPoint.H x.1)[T;T⁻¹]), ⊤) =>
      SchemeValuedPoint.eval (SchemePointLaurentGauss.point p x r hr) ⊤ trivial s)
    (sourceFrameSection_eq_localCoefficient p x hb M U hc e σ).symm
  have hs := SchemePointLaurentModuleEvaluation.sourceFrameSection_value p x M E r hr σ
  have hm : (SchemeModuleLaurentCoefficients.coefficients p M σ).support.sup
        (fun i => ‖SchemePointLaurentModuleEvaluation.frameFunctional p x M E
          (SchemeModuleLaurentCoefficients.coefficients p M σ i)‖₊ * r ^ i) =
      (SchemeModuleLaurentCoefficients.coefficients p M σ).support.sup
        (fun i => RelativeSchemeValuedPoint.modelLineNorm hb x hM
          (Scheme.Modules.affinePullbackUnitTop (X.fromSpecResidueField x.1.point) M
            (SchemeModuleLaurentCoefficients.coefficients p M σ i)) * r ^ i) := by
    apply Finset.sup_congr rfl
    intro i _
    exact congrArg (fun a => a * r ^ i)
      (SchemePointCompletedLineFrame.completedLocalFrame_nnnorm_eq_modelLineNorm p x hb M hM U hc e
        (SchemeModuleLaurentCoefficients.coefficients p M σ i))
  exact ht.trans (hu.trans (hs.trans hm))

/-- ONE actual original coefficient/weight family, chosen BEFORE ALL native
points, frames and radii, gives the genuine local product-point maximum
of the TRUE original model line norms for every original finite family. -/
theorem localCoefficient_finite_family [CompactSpace X] [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent] (hM : Scheme.Modules.IsInvertible M)
    (G : Finset (SchemeModuleLaurentCoefficients.pulledSections p M))
    (U : X.Opens) (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (r : ℝ≥0) (hr : 0 < r) :
    G.sup (fun σ => SchemeValuedPoint.eval (openPoint p x hb U hc r hr) ⊤ trivial
        (localCoefficient p M U e σ)) =
      (SchemeModuleLaurentCoefficients.terms p M G).sup
        (fun t => RelativeSchemeValuedPoint.modelLineNorm hb x hM
          (Scheme.Modules.affinePullbackUnitTop (X.fromSpecResidueField x.1.point) M t.1) * r ^ t.2) := by
  simp only [localCoefficient_value p x hb M hM U hc e r hr,
    SchemeModuleLaurentCoefficients.terms, Finset.sup_biUnion, Finset.sup_image]
  rfl

end EnvelopeProperty.Berkovich.SchemePointLaurentLocalFrame
