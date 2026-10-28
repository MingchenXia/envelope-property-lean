import EnvelopeProperty.Berkovich.SchemeLinePullbackSections
import EnvelopeProperty.Berkovich.SchemeCenterBaseChange
import EnvelopeProperty.AlgGeom.UnitModuleAutomorphisms

/-! # Genuine whole section model norms commute with actual scheme pullback -/
open scoped NNReal
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

private theorem openTopSection_surjective {Y : Scheme.{u}} (U : Y.Opens) :
    Function.Surjective (Scheme.Modules.openTopSection U) := by
  let e := Y.presheaf.mapIso (eqToIso U.ι_image_top).op ≪≫ U.ι.appIso ⊤
  intro r
  refine ⟨e.inv.hom r, ?_⟩
  exact congrArg (fun q => q.hom r) e.inv_hom_id

variable {R S : Type u} [CommRing R] [CommRing S]
variable {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}
variable {X Y : Scheme.{u}}
variable {fX : X ⟶ Spec (CommRingCat.of S)} {fY : Y ⟶ Spec (CommRingCat.of R)}
variable [IsProper fX] [IsProper fY]

/-- The TRUE actual model norm of the SAME original globally pulled-back
section equals the original model norm at the SAME original mapped valued
point over compatible bounded bases. All center/frame/section comparisons
are derived; no flatness, properness of g or metric comparison premise. -/
theorem modelLineNorm_pullbackSection_eq_overBase
    (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r) (g : X ⟶ Y)
    (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (hbR : ∀ r, v r ≤ 1) (hbS : ∀ s, w s ≤ 1) (y : RelativeSchemeValuedPoint w fX)
    {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M)
    (α : Scheme.Modules.unitObj Y ⟶ M) :
    modelLineNorm hbS y (hM.pullback g)
        (fibreSection y (SchemeLineSectionEvaluation.pullbackSectionHom g α)) =
      modelLineNorm hbR (mapOverBase φ hφ g hg y) hM
        (fibreSection (mapOverBase φ hφ g hg y) α) := by
  let z := mapOverBase φ hφ g hg y
  have hMtriv := hM
  obtain ⟨ι, U, hU, hframe⟩ := hMtriv
  have hcov : center hbR z ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  obtain ⟨e⟩ := hframe i
  let a := SchemeLineSectionEvaluation.pullbackSectionHom (U i).ι α ≫ e.hom
  let r : Γ((U i).toScheme, ⊤) := (a.val.app (op ⊤)).hom (1 : Γ((U i).toScheme, ⊤))
  obtain ⟨c, hc⟩ := openTopSection_surjective (U i) r
  have hr : SchemeLineSectionEvaluation.pullbackSectionHom (U i).ι α ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection (Scheme.Modules.openTopSection (U i) c) := by
    exact (Scheme.Modules.unitHom_eq_globalScalar a).trans
      (congrArg ModularCurves.unitEndomorphismOfTopSection hc.symm)
  have hy : center hbS y ∈ g ⁻¹ᵁ U i := by
    change g (center hbS y) ∈ U i
    rw [center_map_overBase φ hφ g hg hbR hbS y]
    exact hi
  rw [modelLineNorm_pullbackSection_eq_localEval hbS y g hM (U i) hy e α c hr,
    modelLineNorm_fibreSection_eq_localEval hbR z hM (U i) hi e α c hr]
  exact (SchemeValuedPoint.eval_map g y.1 (U i)
    (support_mem_of_center_mem hbR z (U i) hi) c).symm

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
