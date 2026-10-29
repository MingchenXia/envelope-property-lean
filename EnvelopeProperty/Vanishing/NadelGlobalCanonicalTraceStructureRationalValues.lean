import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureGenericSections
import EnvelopeProperty.AlgGeom.CyclicSectionStructuralUnitOpenSquare

/-! # The actual original rational trace on EVERY original local section

The whole generic-field target is read through actual restriction maps.
The original rational trace is evaluated by its actual sheaf naturality,
not replaced by a chosen matching section map.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules Opposite
open CyclicSectionStructuralUnitNaturality CyclicSectionStructuralUnitOpenSquare
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} [IsIntegral X] {π : Y ⟶ X} {D : ℕ}
    (C : WholeFreeChart π D) [Nonempty C.base.1]

private def baseImage : X.Opens := C.base.2.fromSpec ''ᵁ ⊤

private theorem generic_base_preimage_top :
    (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ C.baseImage = ⊤ := by
  change (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ (C.base.2.fromSpec ''ᵁ ⊤) = ⊤
  rw [← C.genericBaseMap_over_original, Scheme.Hom.comp_preimage,
    C.base.2.fromSpec.preimage_image_eq, Scheme.Hom.preimage_top]

private theorem generic_source_preimage_top :
    (pullback.fst π (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ (π ⁻¹ᵁ C.baseImage) = ⊤ := by
  rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
    C.generic_base_preimage_top, Scheme.Hom.preimage_top]

private def targetRestrictionMap :
    Γ(Spec X.functionField, (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ C.baseImage) ⟶
      Γ(Spec X.functionField, ⊤) :=
  (Spec X.functionField).presheaf.map (eqToHom C.generic_base_preimage_top.symm).op

private instance targetRestrictionMap_isIso : IsIso C.targetRestrictionMap := by
  dsimp only [targetRestrictionMap]
  infer_instance

/-- The actual restricted original generic-field target is read through
the SAME whole-field restriction and native spectrum-section isomorphism. -/
def genericTargetRead
    (w : Γ((restrictFunctor C.base.2.fromSpec).obj
      ((pushforward (X.fromSpecStalk (genericPoint X))).obj (unitObj (Spec X.functionField))), ⊤)) :
    X.functionField :=
  (Scheme.ΓSpecIso X.functionField).hom (C.targetRestrictionMap w)

/-- These ACTUAL original target coefficients detect EVERY original
restricted generic-target section. -/
theorem genericTargetRead_injective : Function.Injective C.genericTargetRead := by
  intro a b h
  apply (ConcreteCategory.bijective_of_isIso C.targetRestrictionMap).injective
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso X.functionField).hom).injective h

private theorem squareSource_top
    (w : Γ((restrictFunctor C.base.2.fromSpec).obj
      ((pushforward π).obj (unitObj Y)), ⊤)) :
    let γ := X.fromSpecStalk (genericPoint X)
    let Z := pullback π γ
    let q := pullback.snd π γ
    (((pushforward q).obj (unitObj Z)).presheaf.map
        (eqToHom C.generic_base_preimage_top.symm).op)
      ((unitSquareMap π q (pullback.fst π γ) γ pullback.condition).app C.baseImage
        (show Γ(Y, π ⁻¹ᵁ C.baseImage) from w)) = C.genericOriginalSection w := by
  let γ := X.fromSpecStalk (genericPoint X)
  let Z := pullback π γ
  let q := pullback.snd π γ
  let g := pullback.fst π γ
  let hsq := congrArg (fun f => f ⁻¹ᵁ C.baseImage)
    (pullback.condition.symm : q ≫ γ = g ≫ π)
  let j := (TopologicalSpace.Opens.map q.base).map (eqToHom C.generic_base_preimage_top.symm)
  have hm : g.app (π ⁻¹ᵁ C.baseImage) ≫ Z.presheaf.map (eqToHom hsq).op ≫
        Z.presheaf.map j.op =
      g.appLE (π ⁻¹ᵁ C.baseImage) ⊤ C.generic_source_preimage_top.ge := by
    rw [Scheme.Hom.appLE, ← Functor.map_comp]
    apply congrArg (fun f => g.app (π ⁻¹ᵁ C.baseImage) ≫ f)
    exact Z.presheaf.congr_map (Subsingleton.elim _ _)
  exact ConcreteCategory.congr_hom hm (show Γ(Y, π ⁻¹ᵁ C.baseImage) from w)

/-- The SAME original rational trace, evaluated on EVERY original local
section, is the native trace of its SAME WHOLE original generic section. -/
theorem genericRationalStructureTrace_chart_top [IsFinite π]
    (w : Γ((restrictFunctor C.base.2.fromSpec).obj
      ((pushforward π).obj (unitObj Y)), ⊤)) :
    let γ := X.fromSpecStalk (genericPoint X)
    let q := pullback.snd π γ
    let _ : Algebra X.functionField Γ(pullback π γ, ⊤) :=
      ((Scheme.ΓSpecIso X.functionField).inv ≫ q.appTop).hom.toAlgebra
    C.genericTargetRead
        (((restrictFunctor C.base.2.fromSpec).map (genericRationalStructureTrace π)).app ⊤ w) =
      Algebra.trace X.functionField Γ(pullback π γ, ⊤) (C.genericOriginalSection w) := by
  let γ := X.fromSpecStalk (genericPoint X)
  let q := pullback.snd π γ
  let g := pullback.fst π γ
  let _ : Algebra X.functionField Γ(pullback π γ, ⊤) :=
    ((Scheme.ΓSpecIso X.functionField).inv ≫ q.appTop).hom.toAlgebra
  have hK : IsField X.functionField :=
    isField_stalk_of_closure_mem_irreducibleComponents X _
      (by simp [irreducibleComponents_eq_singleton])
  let T := fieldStructureTrace X.functionField hK q
  let a := (unitSquareMap π q g γ pullback.condition).app C.baseImage
    (show Γ(Y, π ⁻¹ᵁ C.baseImage) from w)
  let i := (eqToHom C.generic_base_preimage_top.symm).op
  have hn := PresheafOfModules.naturality_apply T.val i a
  have hs := C.squareSource_top w
  have hv : C.genericTargetRead
      (((restrictFunctor C.base.2.fromSpec).map (genericRationalStructureTrace π)).app ⊤ w) =
      (Scheme.ΓSpecIso X.functionField).hom (T.app ⊤ (C.genericOriginalSection w)) :=
    (congrArg (Scheme.ΓSpecIso X.functionField).hom hn.symm).trans
      (congrArg (fun z => (Scheme.ΓSpecIso X.functionField).hom (T.app ⊤ z)) hs)
  exact hv.trans (fieldStructureTrace_top X.functionField hK q (C.genericOriginalSection w))

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
