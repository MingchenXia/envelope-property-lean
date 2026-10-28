import EnvelopeProperty.AlgGeom.CartierInvariantLinearization
import EnvelopeProperty.AlgGeom.IdealModuleQuasicoherent
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorQuasicoherent
import ModularCurves.Picard.InvertibleSheafLocallyFree
import EnvelopeProperty.AlgGeom.SchemeLineSectionFactorization
import EnvelopeProperty.AlgGeom.SchemeSectionPreservingGluing

/-! # Actual ideal-section frames for the exceptional line comparison -/

open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalExceptionalSections
open SchemeLineSectionEvaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original ideal section retains precisely its original included function. -/
theorem topSectionHom_inclusion {X : Scheme.{u}} (I : X.IdealSheafData)
    (s : Γ(I.toModules, ⊤)) :
    topSectionHom I.toModules s ≫ I.toModulesInclusion =
      ModularCurves.unitEndomorphismOfTopSection
        (s : I.toSubmodule.obj (op ⊤)).1 := by
  rw [unitHom_eq_globalScalar (topSectionHom I.toModules s ≫ I.toModulesInclusion)]
  apply congrArg ModularCurves.unitEndomorphismOfTopSection
  change (show I.toSubmodule.obj (op ⊤) from
    (topSectionHom I.toModules s).val.app (op ⊤) (1 : Γ(X, ⊤))).1 = _
  rw [topSectionHom_app_top_apply_one]

/-- Pulling an actual included ideal section gives exactly the actual
original scheme-function pullback, under the genuine unit comparison. -/
theorem pullback_section_inclusion {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (f : X ⟶ Y) (a : unitObj Y ⟶ I.toModules) (r : Γ(Y, ⊤))
    (ha : a ≫ I.toModulesInclusion = ModularCurves.unitEndomorphismOfTopSection r) :
    pullbackSectionHom f a ≫ I.pullbackModuleInclusion f =
      ModularCurves.unitEndomorphismOfTopSection (f.appTop.hom r) := by
  change (pullbackUnitIso f).inv ≫ (pullback f).map a ≫
    ((pullback f).map I.toModulesInclusion ≫ (pullbackUnitIso f).hom) = _
  rw [← Category.assoc ((pullback f).map a), ← Functor.map_comp, ha]
  exact ModularCurves.pullback_unitEndomorphismOfTopSection f r

/-- A whole affine ideal-section map is a true isomorphism if its original
included function is the actual regular generator of that same original ideal. -/
theorem isIso_of_regular_inclusion {X : Scheme.{u}} [IsAffine X]
    (I : X.IdealSheafData) (r : Γ(X, ⊤)) (hr : r ∈ nonZeroDivisors Γ(X, ⊤))
    (hI : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {r})
    (a : unitObj X ⟶ I.toModules)
    (ha : a ≫ I.toModulesInclusion = ModularCurves.unitEndomorphismOfTopSection r) :
    IsIso a := by
  let : I.toModules.IsQuasicoherent := I.isQuasicoherent_toModules
  let : (unitObj X).IsQuasicoherent := (isInvertible_unit (X := X)).isQuasicoherent
  apply Scheme.Modules.isIso_of_isQuasicoherent_of_isIso_app_top
  rw [ConcreteCategory.isIso_iff_bijective]
  have he (x : Γ(X, ⊤)) :
      (show I.toSubmodule.obj (op ⊤) from a.val.app (op ⊤) x).1 = x * r := by
    have h := congrArg (fun q : unitObj X ⟶ unitObj X =>
      q.val.app (op ⊤) x) ha
    change (show I.toSubmodule.obj (op ⊤) from a.val.app (op ⊤) x).1 =
      (ModularCurves.unitEndomorphismOfTopSection r).val.app (op ⊤) x at h
    exact h.trans (by
      rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
      simp only [homOfLE_refl, op_id]
      exact congrArg (x * ·) (ConcreteCategory.congr_hom (X.presheaf.map_id (op ⊤)) r))
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    apply (mul_right_mem_nonZeroDivisors_eq_zero_iff hr).mp
    rw [sub_mul, ← he x, ← he y, hxy, sub_self]
  · intro y
    have hy : (I.toModulesSectionsEquiv ⟨⊤, isAffineOpen_top X⟩ y).1 ∈ Ideal.span {r} := by
      rw [← hI]
      exact (I.toModulesSectionsEquiv ⟨⊤, isAffineOpen_top X⟩ y).2
    obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp hy
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact (he x).trans hx

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalExceptionalSections
