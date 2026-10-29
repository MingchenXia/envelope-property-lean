import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureChartGenericFiber
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureChartValues

/-! # Every original local function retains its SAME whole generic section

These are actual ring-section pullbacks along the already proved original
projection square. No trace, function-match, or component certificate is
an input, and original local sections need not extend globally.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} {π : Y ⟶ X} {D : ℕ} (C : WholeFreeChart π D)

private instance source_open : IsOpenImmersion C.sourceMap := C.sourceMap_isOpenImmersion

private def baseImage : X.Opens := C.base.2.fromSpec ''ᵁ ⊤
private def originalSourceOpen : Y.Opens := π ⁻¹ᵁ C.baseImage

private theorem source_preimage_top : C.sourceMap ⁻¹ᵁ C.originalSourceOpen = ⊤ := by
  change C.sourceMap ⁻¹ᵁ (π ⁻¹ᵁ (C.base.2.fromSpec ''ᵁ ⊤)) = ⊤
  rw [← Scheme.Hom.comp_preimage, ← C.isPullback.w, Scheme.Hom.comp_preimage,
    C.base.2.fromSpec.preimage_image_eq, Scheme.Hom.preimage_top]

/-- The actual original chart comparison on EVERY local function is the
actual source chart pullback to its entire original coefficient spectrum. -/
theorem pushforwardIso_top_eq_appLE
    (w : Γ((restrictFunctor C.base.2.fromSpec).obj
      ((pushforward π).obj (unitObj Y)), ⊤)) :
    C.pushforwardIso.hom.app ⊤ w =
      C.sourceMap.appLE C.originalSourceOpen ⊤ C.source_preimage_top.ge
        (show Γ(Y, C.originalSourceOpen) from w) := by
  let h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback C.isPullback ⊤
  have hm : Y.presheaf.map (eqToHom h).op ≫ (C.sourceMap.appIso ⊤).hom =
      C.sourceMap.appLE C.originalSourceOpen ⊤ C.source_preimage_top.ge := by
    rw [Scheme.Hom.appIso_hom']
    exact C.sourceMap.map_appLE _ _
  exact ConcreteCategory.congr_hom hm (show Γ(Y, C.originalSourceOpen) from w)

variable [IsIntegral X] [Nonempty C.base.1]

private theorem generic_preimage_top (U : X.Opens) [Nonempty U] :
    (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U = ⊤ := by
  let : Subsingleton (Spec X.functionField) := by
    change Subsingleton (PrimeSpectrum X.functionField)
    infer_instance
  ext z
  change ((X.fromSpecStalk (genericPoint X)) z ∈ U) ↔ True
  constructor
  · intro _; trivial
  · intro _
    rw [Subsingleton.elim z (IsLocalRing.closedPoint X.functionField),
      Scheme.fromSpecStalk_closedPoint]
    exact genericPoint_mem_nonempty_open U

private theorem generic_source_preimage_top :
    (pullback.fst π (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ C.originalSourceOpen = ⊤ := by
  have hγ : (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ C.baseImage = ⊤ := by
    change (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ (C.base.2.fromSpec ''ᵁ ⊤) = ⊤
    rw [Scheme.Hom.image_top_eq_opensRange, C.base.2.opensRange_fromSpec]
    exact generic_preimage_top C.base.1
  change (pullback.fst π (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ (π ⁻¹ᵁ C.baseImage) = ⊤
  rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
    hγ, Scheme.Hom.preimage_top]

/-- Every ACTUAL original local function pulls to a whole section of the
SAME original generic fiber along its actual first projection. -/
def genericOriginalSection
    (w : Γ((restrictFunctor C.base.2.fromSpec).obj
      ((pushforward π).obj (unitObj Y)), ⊤)) :
    Γ(pullback π (X.fromSpecStalk (genericPoint X)), ⊤) :=
  (pullback.fst π (X.fromSpecStalk (genericPoint X))).appLE C.originalSourceOpen ⊤
    C.generic_source_preimage_top.ge (show Γ(Y, C.originalSourceOpen) from w)

/-- Computing the generic section through the WHOLE chart gives exactly
the SAME actual original first-projection section, on every original w. -/
theorem genericFiberIso_originalSection
    (w : Γ((restrictFunctor C.base.2.fromSpec).obj
      ((pushforward π).obj (unitObj Y)), ⊤)) :
    C.genericFiberIso.inv.appTop
        ((pullback.fst C.scalarMap C.genericBaseMap).appTop (C.pushforwardIso.hom.app ⊤ w)) =
      C.genericOriginalSection w := by
  have hmap : C.genericFiberIso.inv ≫
      (pullback.fst C.scalarMap C.genericBaseMap ≫ C.sourceMap) =
      pullback.fst π (X.fromSpecStalk (genericPoint X)) := by
    rw [← C.genericFiberIso_fst, Iso.inv_hom_id_assoc]
  have hm : C.sourceMap.appLE C.originalSourceOpen ⊤ C.source_preimage_top.ge ≫
        (pullback.fst C.scalarMap C.genericBaseMap).appTop ≫ C.genericFiberIso.inv.appTop =
      (pullback.fst π (X.fromSpecStalk (genericPoint X))).appLE C.originalSourceOpen ⊤
        C.generic_source_preimage_top.ge := by
    simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top,
      Scheme.Hom.appLE_comp_appLE, Category.assoc, hmap]
  exact (congrArg (fun b => C.genericFiberIso.inv.appTop
    ((pullback.fst C.scalarMap C.genericBaseMap).appTop b))
      (C.pushforwardIso_top_eq_appLE w)).trans
    (ConcreteCategory.congr_hom hm (show Γ(Y, C.originalSourceOpen) from w))

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
