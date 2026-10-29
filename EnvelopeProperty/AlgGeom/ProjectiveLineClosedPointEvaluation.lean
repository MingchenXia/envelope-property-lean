import EnvelopeProperty.AlgGeom.ProjectiveClosedPointResidueDegrees
import EnvelopeProperty.AlgGeom.LocalSchemeLineTriviality
import EnvelopeProperty.AlgGeom.ProjectiveFactorizationRingIso
import EnvelopeProperty.AlgGeom.ProjectiveHomogeneousSectionZeroLocus
import EnvelopeProperty.AlgGeom.SchemeLineSectionUnitFrames
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechPushforward
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Actual closed-point evaluation and nonzero original line sections

The fiber is literally the global sections of the original line pulled back
along the original residue-field point. No ampleness of that line is assumed.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.ProjectiveLineClosedPointEvaluation
open SchemeCoherentEulerIndex SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def fiberResidueIso {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (x : X) (L : X.Modules) (hL : IsInvertible L) :
    letI := AffineSchemeLocalDegrees.residueAlgebra p x
    fieldSections (X.fromSpecResidueField x ≫ p)
      ((Scheme.Modules.pullback (X.fromSpecResidueField x)).obj L) ≅
        ModuleCat.of k (X.residueField x) := by
  let i := X.fromSpecResidueField x
  let P := (Scheme.Modules.pullback i).obj L
  let := AffineSchemeLocalDegrees.residueAlgebra p x
  let := FiniteClosedIdealLocalDegrees.structureSectionsAlgebra (i ≫ p)
  let e := (hL.pullback i).nonempty_iso_unit_on_localSpec.some
  exact fieldSectionsIso (i ≫ p) e ≪≫
    FiniteClosedIdealLocalDegrees.structureFieldSectionsIso (i ≫ p) ≪≫
      (ProjectiveClosedPointResidueDegrees.sectionsResidueAlgEquiv p x).toLinearEquiv.toModuleIso

/-- The SAME actual original pullback line fiber is finite over the original
field and has the SAME original residue degree, independently of the line. -/
theorem fiber_finite_finrank_eq_residue {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p] (x : X)
    (hx : IsClosed ({x} : Set X)) (L : X.Modules) (hL : IsInvertible L) :
    letI := AffineSchemeLocalDegrees.residueAlgebra p x
    Module.Finite k (fieldSections (X.fromSpecResidueField x ≫ p)
      ((Scheme.Modules.pullback (X.fromSpecResidueField x)).obj L)) ∧
    Module.finrank k (fieldSections (X.fromSpecResidueField x ≫ p)
      ((Scheme.Modules.pullback (X.fromSpecResidueField x)).obj L)) =
        Module.finrank k (X.residueField x) := by
  let := AffineSchemeLocalDegrees.residueAlgebra p x
  let : Module.Finite k (X.residueField x) :=
    ProjectiveClosedPointResidueDegrees.residueField_finite p
      (ProjectiveFactorizationRingIso.of_isProjective p) x hx
  let e := fiberResidueIso p x L hL
  exact ⟨Module.Finite.equiv e.symm.toLinearEquiv, e.toLinearEquiv.finrank_eq⟩

private def pullbackEvaluation {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (i : Y ⟶ X) (M : X.Modules) :
    fieldSections p M ⟶ fieldSections (i ≫ p) ((Scheme.Modules.pullback i).obj M) :=
  (ModuleCat.restrictScalars (baseScalar (k := k))).map
    (baseSectionsMap p ((pullbackPushforwardAdjunction i).unit.app M) ≫
      (baseSectionsPushforwardIso i p ((Scheme.Modules.pullback i).obj M)).inv)

private theorem pullbackEvaluation_apply {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (i : Y ⟶ X) (M : X.Modules)
    (t : fieldSections p M) :
    pullbackEvaluation p i M t = sectionAtOne (pullbackSectionHom i (topSectionHom M t)) := by
  let P := (Scheme.Modules.pullback i).obj M
  let α := pullbackSectionHom i (topSectionHom M t)
  let e := baseSectionsPushforwardIso i p P
  apply (ConcreteCategory.bijective_of_isIso
    ((ModuleCat.restrictScalars (baseScalar (k := k))).map e.hom)).1
  change e.hom (e.inv ((baseSectionsMap p ((pullbackPushforwardAdjunction i).unit.app M)) t)) =
    e.hom (sectionAtOne α)
  rw [Iso.inv_hom_id_apply]
  change ((pullbackPushforwardAdjunction i).unit.app M).val.app (op ⊤) t =
    P.presheaf.map (eqToHom (Scheme.Hom.preimage_top i)).op
      (α.val.app (op ⊤) (1 : Γ(Y, ⊤)))
  have h := pullback_unit_app_top_applyT i M t
  rw [map_one] at h
  have hn := PresheafOfModules.naturality_apply α.val
    (eqToHom (Scheme.Hom.preimage_top i)).op (1 : Γ(Y, ⊤))
  change α.val.app (op (i ⁻¹ᵁ ⊤))
    (Y.presheaf.map (eqToHom (Scheme.Hom.preimage_top i)).op (1 : Γ(Y, ⊤))) =
      P.presheaf.map (eqToHom (Scheme.Hom.preimage_top i)).op
        (α.val.app (op ⊤) (1 : Γ(Y, ⊤))) at hn
  rw [map_one] at hn
  exact h.trans hn

private theorem section_zero_of_sectionAtOne_zero {X : Scheme.{u}} {M : X.Modules}
    (s : unitObj X ⟶ M) (hs : sectionAtOne s = 0) : s = 0 := by
  apply M.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  have hn := PresheafOfModules.naturality_apply s.val
    (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op (1 : Γ(X, ⊤))
  change s.val.app U
    (X.presheaf.map (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op (1 : Γ(X, ⊤))) =
      M.presheaf.map (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op (sectionAtOne s) at hn
  rw [map_one] at hn
  change s.val.app U (1 : Γ(X, U.unop)) = 0
  rw [hn]
  change M.presheaf.map _ (sectionAtOne s) = 0
  rw [hs, map_zero]

private theorem zero_pullback_mem_support {X : Scheme.{u}} (x : X)
    (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L)
    (hs : pullbackSectionHom (X.fromSpecResidueField x) s = 0) :
    x ∈ (LineSectionZeroIdeal.zeroIdeal L hL s).support := by
  classical
  have hLcopy := hL
  obtain ⟨ι, V, hV, eV⟩ := hLcopy
  have hxV : x ∈ iSup V := by rw [hV]; trivial
  obtain ⟨a, hxa⟩ := Opens.mem_iSup.mp hxV
  obtain ⟨W, hWa, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxa
  let U : X.affineOpens := ⟨W, hWa⟩
  let e : (Scheme.Modules.pullback U.1.ι).obj L ≅ unitObj U.1.toScheme :=
    restrictTrivialization hWV (eV a).some
  let r := SchemeLineSectionUnitFrames.frameScalar e (pullbackSectionHom U.1.ι s)
  have hr : pullbackSectionHom U.1.ι s ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection r :=
    SchemeLineSectionUnitFrames.frameScalar_identity e _
  let c : Γ(X, U.1) := U.1.topIso.hom.hom r
  have hD : (LineSectionZeroIdeal.zeroIdeal L hL s).ideal U = Ideal.span ({c} : Set Γ(X, U.1)) :=
    ProjectiveHomogeneousSectionZeroLocus.zeroIdeal_ideal_of_pullbackFrame L hL s U e r hr
  let i := X.fromSpecResidueField x
  obtain ⟨g, hg⟩ := Scheme.exists_lift_open_of_closedPoint_mem i U.1
    (by
      change X.fromSpecResidueField x (IsLocalRing.closedPoint _) ∈ W
      rw [Scheme.fromSpecResidueField_apply]
      exact hxW)
  have h := frameViaFactor_sectionHom_scalar g U.1.ι i hg e s r hr
  rw [hs, zero_comp] at h
  have hscalar : g.appTop.hom r = 0 := by
    have hh := congrArg (fun q : unitObj (Spec (X.residueField x)) ⟶
        unitObj (Spec (X.residueField x)) => q.val.app (op ⊤)
          (1 : Γ(Spec (X.residueField x), ⊤))) h
    change (0 : Γ(Spec (X.residueField x), ⊤)) =
      (topSectionHom (unitObj (Spec (X.residueField x))) (g.appTop.hom r)).val.app
        (op ⊤) (1 : Γ(Spec (X.residueField x), ⊤)) at hh
    rw [topSectionHom_app_top_apply_one] at hh
    exact hh.symm
  have hopen : (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom c = r := by
    rw [Scheme.Opens.ι_appLE]
    change U.1.topIso.inv.hom (U.1.topIso.hom.hom r) = r
    exact ConcreteCategory.congr_hom U.1.topIso.hom_inv_id r
  have hcomp := Scheme.Hom.appLE_comp_appLE g U.1.ι U.1 ⊤ ⊤
    U.1.ι_preimage_self.ge (le_top : ⊤ ≤ g ⁻¹ᵁ ⊤)
  have ht : g.appLE ⊤ ⊤ (le_top : ⊤ ≤ g ⁻¹ᵁ ⊤) = g.appTop := by simp [Scheme.Hom.appLE]
  have heval : X.evaluation U.1 x hxW c = 0 := by
    have hg' : g ≫ U.1.ι = X.fromSpecResidueField x := hg
    have hfun : ∀ hh : ⊤ ≤ (g ≫ U.1.ι) ⁻¹ᵁ U.1,
        (g ≫ U.1.ι).appLE U.1 ⊤ hh ≫ (Scheme.ΓSpecIso (X.residueField x)).hom =
          X.evaluation U.1 x hxW := by
      rw [hg']
      intro hh
      exact Berkovich.SchemeValuedPoint.fromSpecResidueField_appLE_top x U.1 hxW hh
    have hres := hfun (by
      rw [hg', Berkovich.SchemeValuedPoint.fromSpecResidueField_preimage_eq_top x U.1 hxW])
    rw [← hcomp, ht] at hres
    have hh := ConcreteCategory.congr_hom hres c
    change (Scheme.ΓSpecIso (X.residueField x)).hom (g.appTop.hom
      ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom c)) = _ at hh
    rw [hopen, hscalar, map_zero] at hh
    exact hh.symm
  rw [(LineSectionZeroIdeal.zeroIdeal L hL s).mem_support_iff_of_mem (U := U) hxW,
    hD, X.zeroLocus_span, X.zeroLocus_singleton]
  exact (X.evaluation_eq_zero_iff_notMem_basicOpen x hxW c).mp heval

/-- A genuine original H0/fiber dimension inequality internally produces a
nonzero SAME original line section, zero on the original residue point, with
a real closed factor of the literal original reduced closed point into its zero subscheme. -/
theorem exists_nonzero_section_vanishing_at_closedPoint_of_finrank_gt
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p] (x : X)
    (hx : IsClosed ({x} : Set X)) (L : X.Modules) (hL : IsInvertible L)
    (hdim : Module.finrank k (fieldSections (X.fromSpecResidueField x ≫ p)
        ((Scheme.Modules.pullback (X.fromSpecResidueField x)).obj L)) <
      Module.finrank k (fieldSections p L)) :
    ∃ s : unitObj X ⟶ L, s ≠ 0 ∧
      pullbackSectionHom (X.fromSpecResidueField x) s = 0 ∧
      let I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
      let D := LineSectionZeroIdeal.zeroIdeal L hL s
      ∃ j : I.subscheme ⟶ D.subscheme,
        IsClosedImmersion j ∧ j ≫ D.subschemeι = I.subschemeι := by
  classical
  let i := X.fromSpecResidueField x
  let f := pullbackEvaluation p i L
  let := AffineSchemeLocalDegrees.residueAlgebra p x
  let : Module.Finite k (fieldSections (i ≫ p) ((Scheme.Modules.pullback i).obj L)) :=
    (fiber_finite_finrank_eq_residue p x hx L hL).1
  have hker : LinearMap.ker f.hom ≠ ⊥ := by
    intro h
    exact (not_le_of_gt hdim) (LinearMap.finrank_le_finrank_of_injective
      (LinearMap.ker_eq_bot.mp h))
  obtain ⟨t, ht, htne⟩ := (LinearMap.ker f.hom).ne_bot_iff.mp hker
  let s := topSectionHom L t
  have hs : s ≠ 0 := by
    intro h
    have hh := congrArg (fun q : unitObj X ⟶ L => q.val.app (op ⊤) (1 : Γ(X, ⊤))) h
    rw [topSectionHom_app_top_apply_one] at hh
    exact htne hh
  have hsz : pullbackSectionHom i s = 0 := by
    apply section_zero_of_sectionAtOne_zero
    exact (pullbackEvaluation_apply p i L t).symm.trans ht
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  let D := LineSectionZeroIdeal.zeroIdeal L hL s
  have hDI : D ≤ I := Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp (by
    intro y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact zero_pullback_mem_support x L hL s hsz)
  let j : I.subscheme ⟶ D.subscheme := Scheme.IdealSheafData.inclusion hDI
  have hj : j ≫ D.subschemeι = I.subschemeι := Scheme.IdealSheafData.inclusion_subschemeι hDI
  have hjclosed : IsClosedImmersion j := by
    have : IsClosedImmersion (j ≫ D.subschemeι) := by rw [hj]; infer_instance
    exact IsClosedImmersion.of_comp j D.subschemeι
  exact ⟨s, hs, hsz, j, hjclosed, hj⟩

#print axioms fiberResidueIso
#print axioms fiber_finite_finrank_eq_residue
#print axioms pullbackEvaluation
#print axioms pullbackEvaluation_apply
#print axioms section_zero_of_sectionAtOne_zero
#print axioms zero_pullback_mem_support
#print axioms exists_nonzero_section_vanishing_at_closedPoint_of_finrank_gt
end EnvelopeProperty.ProjectiveLineClosedPointEvaluation
