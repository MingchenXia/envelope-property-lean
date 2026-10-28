import EnvelopeProperty.AlgGeom.IdealModuleOffSupport
import EnvelopeProperty.Berkovich.CartierGenericUnitSection
import EnvelopeProperty.Berkovich.SchemeModelIdealSupport
import EnvelopeProperty.AlgGeom.SchemeLineSectionFactorization

/-! # Actual generic Cartier sections on their true support opens

All open membership below concerns the underlying support of the native
point. Its proper valuative center is not required to belong to the open.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open scoped NNReal ENNReal
universe u
namespace EnvelopeProperty.NumericalSectionRegauging
open Berkovich Berkovich.RelativeSchemeValuedPoint

/-- The actual original residue morphism through a genuine support neighborhood. -/
def supportResidueFactor {X : Scheme.{u}} (x : X) (V : X.Opens) (hx : x ∈ V) :
    Spec (CommRingCat.of (X.residueField x)) ⟶ V.toScheme :=
  Classical.choose (Scheme.exists_lift_open_of_closedPoint_mem
    (X.fromSpecResidueField x) V (by exact (X.fromSpecResidueField_apply x _).symm ▸ hx))

/-- The support factor has its actual whole original scheme triangle. -/
theorem supportResidueFactor_comp {X : Scheme.{u}} (x : X) (V : X.Opens) (hx : x ∈ V) :
    supportResidueFactor x V hx ≫ V.ι = X.fromSpecResidueField x :=
  Classical.choose_spec (Scheme.exists_lift_open_of_closedPoint_mem
    (X.fromSpecResidueField x) V (by exact (X.fromSpecResidueField_apply x _).symm ▸ hx))

-- These typed names retain the SAME actual maps, while exposing the
-- native unit-object types to ordinary categorical rewrite lemmas.
private def nativeInclusion {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.toModules ⟶ Scheme.Modules.unitObj X := I.toModulesInclusion

private def nativeOffSupportFrame {X : Scheme.{u}} (I : X.IdealSheafData)
    (V : X.Opens) (hV : V ≤ I.support.compl) :
    (Scheme.Modules.pullback V.ι).obj I.toModules ≅ Scheme.Modules.unitObj V.toScheme :=
  I.pullbackModuleIsoOfLeComplSupport V hV

private theorem offSupportFrame_hom {X : Scheme.{u}} (I : X.IdealSheafData)
    (V : X.Opens) (hV : V ≤ I.support.compl) :
    (nativeOffSupportFrame I V hV).hom =
      (Scheme.Modules.pullback V.ι).map (nativeInclusion I) ≫
        (Scheme.Modules.pullbackUnitIso V.ι).hom := by
  let c := Scheme.Modules.restrictFunctorIsoPullback V.ι
  have hn := c.inv.naturality (nativeInclusion I)
  have h0 : (nativeOffSupportFrame I V hV).hom =
      c.inv.app I.toModules ≫ (Scheme.Modules.restrictFunctor V.ι).map (nativeInclusion I) ≫
        (Scheme.Modules.restrictUnitIso V.ι).hom := rfl
  have h1 : c.inv.app I.toModules ≫
      (Scheme.Modules.restrictFunctor V.ι).map (nativeInclusion I) ≫
        (Scheme.Modules.restrictUnitIso V.ι).hom =
      (Scheme.Modules.pullback V.ι).map (nativeInclusion I) ≫
        c.inv.app (Scheme.Modules.unitObj X) ≫ (Scheme.Modules.restrictUnitIso V.ι).hom :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (Scheme.Modules.restrictUnitIso V.ι).hom) hn.symm).trans
        (Category.assoc _ _ _))
  have h2 : (Scheme.Modules.pullback V.ι).map (nativeInclusion I) ≫
      c.inv.app (Scheme.Modules.unitObj X) ≫ (Scheme.Modules.restrictUnitIso V.ι).hom =
      (Scheme.Modules.pullback V.ι).map (nativeInclusion I) ≫
        (Scheme.Modules.pullbackUnitIso V.ι).hom :=
    congrArg ((Scheme.Modules.pullback V.ι).map (nativeInclusion I) ≫ ·)
      (ModularCurves.restrictFunctorIsoPullback_inv_comp_restrictUnitIsoLow V.ι)
  exact h0.trans (h1.trans h2)

private theorem factor_unit {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D)
    (f : B ⟶ D) (h : g ≫ b = f) :
    (Scheme.Modules.frameFactorIso g b f h (Scheme.Modules.unitObj D)).inv ≫
        (Scheme.Modules.pullback g).map (Scheme.Modules.pullbackUnitIso b).hom ≫
          (Scheme.Modules.pullbackUnitIso g).hom =
      (Scheme.Modules.pullbackUnitIso f).hom := by
  subst f
  change (Scheme.Modules.pullbackComp g b).inv.app (Scheme.Modules.unitObj D) ≫ _ = _
  rw [← ModularCurves.pullbackUnitIso_compLow g b]
  exact Iso.inv_hom_id_assoc ((Scheme.Modules.pullbackComp g b).app (Scheme.Modules.unitObj D)) _

private theorem offSupportFrame_factor_hom {A X : Scheme.{u}}
    (I : X.IdealSheafData) (V : X.Opens) (hV : V ≤ I.support.compl)
    (g : A ⟶ V.toScheme) (p : A ⟶ X) (hg : g ≫ V.ι = p) :
    (Scheme.Modules.frameViaFactor g V.ι p hg (nativeOffSupportFrame I V hV)).hom =
      (Scheme.Modules.pullback p).map (nativeInclusion I) ≫
        (Scheme.Modules.pullbackUnitIso p).hom := by
  let c := (Scheme.Modules.pullbackComp g V.ι) ≪≫ Scheme.Modules.pullbackCongr hg
  have hn := c.inv.naturality (nativeInclusion I)
  simp only [Functor.comp_map] at hn
  change c.inv.app I.toModules ≫
      (Scheme.Modules.pullback g).map (nativeOffSupportFrame I V hV).hom ≫
        (Scheme.Modules.pullbackUnitIso g).hom = _
  rw [offSupportFrame_hom, Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hn]
  exact congrArg ((Scheme.Modules.pullback p).map (nativeInclusion I) ≫ ·)
    (factor_unit g V.ι p hg)

private theorem offSupportFrame_generic {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} [IsProper f]
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (I : X.IdealSheafData) (hI : I.IsInvertible) (V : X.Opens)
    (hV : V ≤ I.support.compl) (hy : y.1.point ∈ V)
    (hn : modelIdealNorm I hb y ≠ 0) :
    Scheme.Modules.frameViaFactor (supportResidueFactor y.1.point V hy) V.ι
      (X.fromSpecResidueField y.1.point) (supportResidueFactor_comp y.1.point V hy)
      (nativeOffSupportFrame I V hV) = genericIdealInclusionIso hb y I hI hn := by
  apply Iso.ext
  exact (offSupportFrame_factor_hom I V hV (supportResidueFactor y.1.point V hy)
    (X.fromSpecResidueField y.1.point) (supportResidueFactor_comp y.1.point V hy)).trans
      (genericIdealInclusionIso_hom hb y I hI hn).symm

/-- The canonical actual generic ideal unit is the residue pullback of the
inverse original inclusion frame, at EVERY point of the true support-open. -/
theorem genericIdealUnitSection_eq_supportFrame
    {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} [IsProper f]
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (I : X.IdealSheafData) (hI : I.IsInvertible) (V : X.Opens)
    (hV : V ≤ I.support.compl) (hy : y.1.point ∈ V) :
    ∃ hn : modelIdealNorm I hb y ≠ 0,
      genericIdealUnitSection hb y I hI hn =
        ((Scheme.Modules.frameViaFactor (supportResidueFactor y.1.point V hy) V.ι
          (X.fromSpecResidueField y.1.point) (supportResidueFactor_comp y.1.point V hy)
          (I.pullbackModuleIsoOfLeComplSupport V hV)).inv.val.app (op ⊤)).hom
            (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤)) := by
  have hn : modelIdealNorm I hb y ≠ 0 := by
    rw [ne_eq, modelIdealNorm_eq_zero_iff]
    exact hV hy
  refine ⟨hn, ?_⟩
  exact congrArg
    (fun e : genericLineModule y I.toModules ≅ Scheme.Modules.unitObj
      (Spec (CommRingCat.of (X.residueField y.1.point))) =>
      (e.inv.val.app (op ⊤)).hom
        (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤)))
    (offSupportFrame_generic hb y I hI V hV hy hn).symm

end EnvelopeProperty.NumericalSectionRegauging
