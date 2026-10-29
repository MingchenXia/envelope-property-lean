/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.IdealModuleFunctorial
import EnvelopeProperty.Berkovich.SchemeIdealPullback

/-!
# Actual ideal module trivialization away from its true support

The actual original inclusion is an isomorphism after true restriction to
any open disjoint from the support. This constructs a true module pullback
trivialization using only existing genuine open-immersion comparisons.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X : Scheme.{u}}

/-- The whole genuine geometric ideal comap is the unit ideal on any original
open disjoint from the actual original support. -/
theorem comap_open_eq_top_of_le_compl_support (I : X.IdealSheafData) (U : X.Opens)
    (hU : U ≤ I.support.compl) : I.comap U.ι = ⊤ := by
  rw [← support_eq_bot_iff, support_comap]
  ext x
  change U.ι x ∈ I.support ↔ False
  exact iff_false_intro (hU x.property)

/-- The actual ideal on each original affine open off the true support is
the entire original section ring. -/
theorem ideal_eq_top_of_le_compl_support (I : X.IdealSheafData) (U : X.affineOpens)
    (hU : U.1 ≤ I.support.compl) : I.ideal U = ⊤ := by
  let : IsAffine U.1.toScheme := U.2
  have h := I.comap_open_ideal_top_map U.2
  have h0 : (I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩ = ⊤ :=
    congrArg (fun K : U.1.toScheme.IdealSheafData =>
      K.ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩)
        (I.comap_open_eq_top_of_le_compl_support U hU)
  exact h.symm.trans ((congrArg (Ideal.map U.1.topIso.hom.hom) h0).trans (Ideal.map_top _))

/-- Every actual section on any entire original open away from the true
support belongs to the actual original ideal module. -/
theorem isLocallyMem_of_le_compl_support (I : X.IdealSheafData) (W : X.Opens)
    (hW : W ≤ I.support.compl) (s : Γ(X, W)) : I.IsLocallyMem W s := by
  intro U hUW
  rw [I.ideal_eq_top_of_le_compl_support U (hUW.trans hW)]
  trivial

/-- The actual original ideal-module inclusion is a true sheaf isomorphism
on the whole original open away from the actual support. -/
theorem toModulesInclusion_isIso_restrict_of_le_compl_support
    (I : X.IdealSheafData) (U : X.Opens) (hU : U ≤ I.support.compl) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map I.toModulesInclusion) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (fun s : I.toSubmodule.obj (op (U.ι ''ᵁ V)) => s.1)
  refine ⟨Subtype.val_injective, fun s => ⟨⟨s, ?_⟩, rfl⟩⟩
  apply I.isLocallyMem_of_le_compl_support
  rintro x ⟨y, _hy, rfl⟩
  exact hU y.property

/-- The true original ideal-module inclusion gives its canonical whole-open
restriction trivialization off the actual support. -/
def restrictModuleIsoOfLeComplSupport (I : X.IdealSheafData) (U : X.Opens)
    (hU : U ≤ I.support.compl) :
    I.toModules.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf := by
  let := I.toModulesInclusion_isIso_restrict_of_le_compl_support U hU
  exact asIso ((Scheme.Modules.restrictFunctor U.ι).map I.toModulesInclusion) ≪≫
    Scheme.Modules.restrictUnitIso U.ι

/-- The genuine native open-immersion pullback comparison constructs the
actual whole pullback-unit trivialization off the original support. -/
def pullbackModuleIsoOfLeComplSupport (I : X.IdealSheafData) (U : X.Opens)
    (hU : U ≤ I.support.compl) :
    (Scheme.Modules.pullback U.ι).obj I.toModules ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app I.toModules ≪≫
    I.restrictModuleIsoOfLeComplSupport U hU

end AlgebraicGeometry.Scheme.IdealSheafData
