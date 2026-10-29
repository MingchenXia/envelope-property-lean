import EnvelopeProperty.Vanishing.NadelNefBigExceptionalGenerators
import EnvelopeProperty.AlgGeom.SchemeGeneratedLineCoefficients
/-! # The actual exceptional generator has its exact whole original Rees ratio in the actual pivot frame -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelNefBigExceptionalFrames
open NadelNefBigExceptionalGenerators NadelBlowupCanonicalExceptionalGenerators
open SchemeGeneratingSectionsUnit SchemeGeneratedLineCoefficients SchemeLineSectionEvaluation
variable {A : Type u} [CommRing A] (I : Ideal A)

def chartFrame (a : I) :
    (pullback (affineBlowUp.chart I a)).obj (affineBlowUp.exceptionalIdeal I).toModules ≅
      unitObj (Spec (.of (affineBlowUpAlgebra I a))) := by
  let := chart_pivot_isIso I a
  exact (asIso (pullbackSectionHom (affineBlowUp.chart I a) (exceptionalSection I a))).symm

theorem coefficient_chartFrame {ι : Type u} (g : ι → I)
    (hspan : Ideal.span (Set.range (fun i => (g i : A))) = I) (a : I) (i : ι) :
    coefficient (ClosedProjectiveGlobalGeneration.pullback_generatingSections (affineBlowUp.chart I a)
      (generatingSections I g hspan)) (chartFrame I a) i =
      (Scheme.ΓSpecIso (.of (affineBlowUpAlgebra I a))).inv.hom
        (affineBlowUpAlgebra.ratio I a (g i)) := by
  let c := affineBlowUp.chart I a
  let G := generatingSections I g hspan
  let K := ClosedProjectiveGlobalGeneration.pullback_generatingSections c G
  have hg : generatorHom K i = pullbackSectionHom c (exceptionalSection I (g i)) := by
    have h0 : generatorHom K i = pullbackSectionHom c (generatorHom G i) :=
      generatorHom_pullback c G i
    exact h0.trans (congrArg (pullbackSectionHom c) (generatorHom_generatingSections I g hspan i))
  let := chart_pivot_isIso I a
  have hcmp : generatorHom K i ≫ (chartFrame I a).hom =
      ModularCurves.unitEndomorphismOfTopSection
        ((Scheme.ΓSpecIso (.of (affineBlowUpAlgebra I a))).inv.hom
          (affineBlowUpAlgebra.ratio I a (g i))) := by
    rw [hg, chart_section_ratio, Category.assoc]
    have hu : pullbackSectionHom c (exceptionalSection I a) ≫ (chartFrame I a).hom = 𝟙 _ :=
      (asIso (pullbackSectionHom c (exceptionalSection I a))).hom_inv_id
    rw [hu, Category.comp_id]
  apply (coefficient_apply K (chartFrame I a) i).trans
  change ((generatorHom K i ≫ (chartFrame I a).hom).val.app (op ⊤)).hom
    (1 : Γ(Spec (.of (affineBlowUpAlgebra I a)), ⊤)) = _
  rw [hcmp]
  change 1 * (Spec (.of (affineBlowUpAlgebra I a))).presheaf.map
    (homOfLE (le_top : (⊤ : (Spec (.of (affineBlowUpAlgebra I a))).Opens) ≤ ⊤)).op
    ((Scheme.ΓSpecIso (.of (affineBlowUpAlgebra I a))).inv.hom
      (affineBlowUpAlgebra.ratio I a (g i))) = _
  have hid : (homOfLE (le_top : (⊤ : (Spec (.of (affineBlowUpAlgebra I a))).Opens) ≤ ⊤)).op =
      𝟙 (op (⊤ : (Spec (.of (affineBlowUpAlgebra I a))).Opens)) := Subsingleton.elim _ _
  rw [hid, CategoryTheory.Functor.map_id]
  exact one_mul _
end EnvelopeProperty.Vanishing.NadelNefBigExceptionalFrames
