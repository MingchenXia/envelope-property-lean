import EnvelopeProperty.Vanishing.NadelBlowupCanonicalExceptionalSections
import Hironaka.Scheme.BlowUp.CoordinateSubspace.ExceptionalProj
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Membership

/-! # Actual original coordinate sections of the native exceptional ideal -/

open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalExceptionalGenerators
open NadelBlowupCanonicalExceptionalSections SchemeLineSectionEvaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The same original affine ideal, with the native original Spec coordinates. -/
abbrev originalIdeal : (Spec (.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (.of R)).inv.hom)

private theorem original_member (a : I) :
    (Scheme.ΓSpecIso (.of R)).inv.hom (a : R) ∈
      (originalIdeal I).ideal ⟨⊤, isAffineOpen_top _⟩ := by
  rw [originalIdeal, ofIdealTop_ideal_top]
  exact Ideal.mem_map_of_mem (Scheme.ΓSpecIso (.of R)).inv.hom a.2

/-- Every actual original ideal element gives its actual original affine ideal section. -/
def originalSection (a : I) : unitObj (Spec (.of R)) ⟶ (originalIdeal I).toModules :=
  topSectionHom _ (((originalIdeal I).toModulesSectionsEquiv ⟨⊤, isAffineOpen_top _⟩).symm
    ⟨(Scheme.ΓSpecIso (.of R)).inv.hom a, original_member I a⟩)

theorem originalSection_inclusion (a : I) :
    originalSection I a ≫ (originalIdeal I).toModulesInclusion =
      ModularCurves.unitEndomorphismOfTopSection ((Scheme.ΓSpecIso (.of R)).inv.hom a) :=
  topSectionHom_inclusion _ _

/-- The actual original affine ideal element, pulled through the actual
canonical comap-module epimorphism to the native blowup's exceptional ideal. -/
def exceptionalSection (a : I) :
    unitObj (affineBlowUp I) ⟶ (affineBlowUp.exceptionalIdeal I).toModules :=
  pullbackSectionHom (affineBlowUp.π I) (originalSection I a) ≫
    (originalIdeal I).toModulesComapPullbackMap (affineBlowUp.π I)

theorem exceptionalSection_inclusion (a : I) :
    exceptionalSection I a ≫ (affineBlowUp.exceptionalIdeal I).toModulesInclusion =
      ModularCurves.unitEndomorphismOfTopSection
        ((affineBlowUp.π I).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom a)) := by
  calc
    _ = pullbackSectionHom (affineBlowUp.π I) (originalSection I a) ≫
        (originalIdeal I).pullbackModuleInclusion (affineBlowUp.π I) :=
      (Category.assoc _ _ _).trans (congrArg
        (fun q => pullbackSectionHom (affineBlowUp.π I) (originalSection I a) ≫ q)
        ((originalIdeal I).pullbackModuleInclusion_eq (affineBlowUp.π I)).symm)
    _ = _ := pullback_section_inclusion _ _ _ _ (originalSection_inclusion I a)

theorem chart_section_inclusion (a b : I) :
    pullbackSectionHom (affineBlowUp.chart I a) (exceptionalSection I b) ≫
      (affineBlowUp.exceptionalIdeal I).pullbackModuleInclusion (affineBlowUp.chart I a) =
      ModularCurves.unitEndomorphismOfTopSection
        ((Scheme.ΓSpecIso (.of (affineBlowUpAlgebra I a))).inv.hom
          (algebraMap R (affineBlowUpAlgebra I a) b)) := by
  rw [pullback_section_inclusion _ _ _ _ (exceptionalSection_inclusion I b)]
  apply congrArg ModularCurves.unitEndomorphismOfTopSection
  calc
    _ = (affineBlowUp.chart I a ≫ affineBlowUp.π I).appTop.hom
        ((Scheme.ΓSpecIso (.of R)).inv.hom b) := rfl
    _ = (Spec.map (CommRingCat.ofHom (algebraMap R (affineBlowUpAlgebra I a)))).appTop.hom
        ((Scheme.ΓSpecIso (.of R)).inv.hom b) :=
      congrArg (fun f => f.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom b))
        (affineBlowUp.chart_π I a)
    _ = _ := congrArg (fun q => q.hom (b : R))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
        (algebraMap R (affineBlowUpAlgebra I a)))).symm

/-- The actual original pivot section is a whole genuine frame on its
original blowup chart, derived from that chart's regular principal ideal. -/
theorem chart_pivot_isIso (a : I) :
    IsIso (pullbackSectionHom (affineBlowUp.chart I a) (exceptionalSection I a)) := by
  let J := affineBlowUp.exceptionalIdeal I
  let c := affineBlowUp.chart I a
  have hc : IsIso (J.toModulesComapPullbackMap c) :=
    J.toModulesComapPullbackMap_isIso_of_isOpenImmersion c
  let := hc
  have h : IsIso (pullbackSectionHom c (exceptionalSection I a) ≫
      J.toModulesComapPullbackMap c) := by
    apply isIso_of_regular_inclusion (J.comap c) (affineBlowUp.chartGenerator I a)
      (affineBlowUp.chartGenerator_mem_nonZeroDivisors I a)
      (affineBlowUp.ideal_comap_exceptionalIdeal_chart_top I a)
    rw [Category.assoc, ← Scheme.IdealSheafData.pullbackModuleInclusion_eq]
    exact chart_section_inclusion I a a
  let := h
  exact IsIso.of_isIso_comp_right _ (J.toModulesComapPullbackMap c)

/-- The actual native ratio multiplied by the actual pivot is the actual
original coordinate function, in the native original blowup chart ring. -/
theorem ratio_mul_pivot (a b : I) :
    affineBlowUpAlgebra.ratio I a b * algebraMap R (affineBlowUpAlgebra I a) a =
      algebraMap R (affineBlowUpAlgebra I a) b := by
  apply Subtype.ext
  change awayFrac (a : R) 1 (b : R) * algebraMap R (Localization.Away (a : R)) a =
    algebraMap R (Localization.Away (a : R)) b
  rw [awayFrac_one_eq]
  rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf (a : R)), IsLocalization.Away.mul_invSelf,
    mul_one]

/-- Every actual original ideal section has precisely its original native
ratio to the same actual pivot frame, as a whole sheaf-map identity. -/
theorem chart_section_ratio (a b : I) :
    pullbackSectionHom (affineBlowUp.chart I a) (exceptionalSection I b) =
      ModularCurves.unitEndomorphismOfTopSection
        ((Scheme.ΓSpecIso (.of (affineBlowUpAlgebra I a))).inv.hom
          (affineBlowUpAlgebra.ratio I a b)) ≫
        pullbackSectionHom (affineBlowUp.chart I a) (exceptionalSection I a) := by
  let J := affineBlowUp.exceptionalIdeal I
  let c := affineBlowUp.chart I a
  let : Mono (J.pullbackModuleInclusion c) :=
    (affineBlowUp.isInvertible_exceptionalIdeal I).pullbackModuleInclusion_mono c
  apply (cancel_mono (J.pullbackModuleInclusion c)).mp
  rw [Category.assoc, chart_section_inclusion I a b, chart_section_inclusion I a a,
    ModularCurves.unitEndomorphismOfTopSection_comp]
  apply congrArg ModularCurves.unitEndomorphismOfTopSection
  rw [← map_mul, ratio_mul_pivot]

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalExceptionalGenerators
