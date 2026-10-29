import EnvelopeProperty.AlgGeom.ModuleKernelIdeal
import EnvelopeProperty.AlgGeom.ProperLocalClosedSupport
import ModularCurves.Picard.DualPullback.PullbackSection

/-!
# Detection of original module sections on the closed fibre of a local base

The actual annihilator support of a quasi-coherent unit-map section is closed.
Universal closedness forces a nonempty such support to meet the closed fibre.
All maps and sections are the original ones, with no finite global-sections
hypothesis or supplied support comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section
universe u

namespace EnvelopeProperty.ProperLocalSectionDetection

variable {S : Type u} [CommRing S] [IsLocalRing S] {Y : Scheme.{u}}
  (q : Y ⟶ Spec (.of S)) [UniversallyClosed q]

section UnitMap

variable (M : Y.Modules) [M.IsQuasicoherent]
  (α : Scheme.Modules.unitObj Y ⟶ M)

omit [IsLocalRing S] q [UniversallyClosed q] in
/-- The actual annihilator support is empty exactly when the ENTIRE original map vanishes. -/
theorem unitMapKernel_support_eq_bot_iff :
    (Scheme.Modules.unitMapKernelIdealSheaf α).support = ⊥ ↔ α = 0 := by
  constructor
  · intro h
    have hI : Scheme.Modules.unitMapKernelIdealSheaf α = ⊤ :=
      (Scheme.IdealSheafData.support_eq_bot_iff _).mp h
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change α.val.app U a = 0
    apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
    intro x hx
    obtain ⟨V, hVa, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
    refine ⟨V, hVU, hxV, ?_⟩
    have ha : α.val.app (op V) (Y.presheaf.map (homOfLE hVU).op a) = 0 := by
      change Y.presheaf.map (homOfLE hVU).op a ∈
        (Scheme.Modules.unitMapKernelIdealSheaf α).ideal ⟨V, hVa⟩
      rw [hI]
      trivial
    have hn := PresheafOfModules.naturality_apply α.val (homOfLE hVU).op a
    change α.val.app (op V) (Y.presheaf.map (homOfLE hVU).op a) =
      M.presheaf.map (homOfLE hVU).op (α.val.app U a) at hn
    change M.presheaf.map (homOfLE hVU).op (α.val.app U a) = _
    erw [← hn, ha, map_zero]
  · rintro rfl
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mpr
    ext V a
    simp [Scheme.Modules.unitMapKernelIdealSheaf, Scheme.Modules.unitMapKernelIdeal]
    rfl

omit [IsLocalRing S] q [UniversallyClosed q] in
/-- Zero of the original global section germ excludes the point from its actual annihilator support. -/
theorem notMem_unitMapKernel_support_of_germ_eq_zero (y : Y)
    (h : M.presheaf.germ ⊤ y trivial
      (α.val.app (op ⊤) (1 : Γ(Y, ⊤))) = 0) :
    y ∉ (Scheme.Modules.unitMapKernelIdealSheaf α).support := by
  obtain ⟨W, hyW, i, j, he⟩ := M.presheaf.germ_eq (U := ⊤) (V := ⊤) y trivial trivial
    (α.val.app (op ⊤) (1 : Γ(Y, ⊤))) 0 (by simpa only [map_zero] using h)
  have hW : M.presheaf.map i.op (α.val.app (op ⊤) (1 : Γ(Y, ⊤))) = 0 := by
    simpa only [map_zero] using he
  obtain ⟨V, hVa, hyV, hVW⟩ := exists_isAffineOpen_mem_and_subset hyW
  have hV : M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
      (α.val.app (op ⊤) (1 : Γ(Y, ⊤))) = 0 := by
    have hres := congrArg (M.presheaf.map (homOfLE hVW).op) hW
    rw [map_zero, ← M.presheaf.map_comp_apply] at hres
    exact hres
  have hone : (1 : Γ(Y, V)) ∈
      (Scheme.Modules.unitMapKernelIdealSheaf α).ideal ⟨V, hVa⟩ := by
    change α.val.app (op V) (1 : Γ(Y, V)) = 0
    have hn := PresheafOfModules.naturality_apply α.val
      (homOfLE (show V ≤ ⊤ from le_top)).op (1 : Γ(Y, ⊤))
    change α.val.app (op V) (Y.presheaf.map _ (1 : Γ(Y, ⊤))) = _ at hn
    rw [map_one] at hn
    exact hn.trans hV
  intro hy
  have hz := (Scheme.IdealSheafData.mem_support_iff.mp hy) ⟨V, hVa⟩
  have hnot := (Y.mem_zeroLocus_iff _ y).mp hz 1 hone
  exact hnot (by simpa only [Y.basicOpen_one] using hyV)

/-- Zero germs at every point of the original closed fibre force the ENTIRE original unit map to vanish. -/
theorem unitMap_eq_zero_of_closedFiber_germs
    (h : ∀ y, q y = IsLocalRing.closedPoint S →
      M.presheaf.germ ⊤ y trivial (α.val.app (op ⊤) (1 : Γ(Y, ⊤))) = 0) : α = 0 := by
  apply (unitMapKernel_support_eq_bot_iff M α).mp
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mpr
  exact idealSheaf_eq_top_of_closedFiber q _ fun y hy =>
    notMem_unitMapKernel_support_of_germ_eq_zero M α y (h y hy)

/-- Every original quasi-coherent global section is detected by all actual closed-fibre germs. -/
theorem section_eq_zero_of_closedFiber_germs (m : Γ(M, ⊤))
    (h : ∀ y, q y = IsLocalRing.closedPoint S → M.presheaf.germ ⊤ y trivial m = 0) : m = 0 := by
  have hα : Scheme.Modules.topSectionHom M m = 0 :=
    unitMap_eq_zero_of_closedFiber_germs q M (Scheme.Modules.topSectionHom M m)
      (by simpa only [Scheme.Modules.topSectionHom_app_top_apply_one] using h)
  have he := congrArg (fun β : Scheme.Modules.unitObj Y ⟶ M =>
    β.val.app (op ⊤) (1 : Γ(Y, ⊤))) hα
  change (Scheme.Modules.topSectionHom M m).val.app (op ⊤) (1 : Γ(Y, ⊤)) = 0 at he
  rwa [Scheme.Modules.topSectionHom_app_top_apply_one] at he

/-- Actual finite type reduces vanishing of the WHOLE original unit map to closed source points over the closed point. -/
theorem unitMap_eq_zero_of_closedPoint_closedFiber_germs [LocallyOfFiniteType q]
    (h : ∀ y, IsClosed ({y} : Set Y) → q y = IsLocalRing.closedPoint S →
      M.presheaf.germ ⊤ y trivial (α.val.app (op ⊤) (1 : Γ(Y, ⊤))) = 0) : α = 0 := by
  apply (unitMapKernel_support_eq_bot_iff M α).mp
  apply SetLike.coe_injective
  exact closedSubset_eq_empty_of_closedPoint_closedFiber q
    (Scheme.Modules.unitMapKernelIdealSheaf α).supportSet
    (Scheme.Modules.unitMapKernelIdealSheaf α).isClosed_supportSet fun y hyc hy =>
      notMem_unitMapKernel_support_of_germ_eq_zero M α y (h y hyc hy)

/-- Arbitrary original global sections are detected at CLOSED points of the actual original closed fibre. -/
theorem section_eq_zero_of_closedPoint_closedFiber_germs [LocallyOfFiniteType q] (m : Γ(M, ⊤))
    (h : ∀ y, IsClosed ({y} : Set Y) → q y = IsLocalRing.closedPoint S →
      M.presheaf.germ ⊤ y trivial m = 0) : m = 0 := by
  have hα : Scheme.Modules.topSectionHom M m = 0 :=
    unitMap_eq_zero_of_closedPoint_closedFiber_germs q M (Scheme.Modules.topSectionHom M m)
      (by simpa only [Scheme.Modules.topSectionHom_app_top_apply_one] using h)
  have he := congrArg (fun β : Scheme.Modules.unitObj Y ⟶ M =>
    β.val.app (op ⊤) (1 : Γ(Y, ⊤))) hα
  change (Scheme.Modules.topSectionHom M m).val.app (op ⊤) (1 : Γ(Y, ⊤)) = 0 at he
  rwa [Scheme.Modules.topSectionHom_app_top_apply_one] at he

/-- A whole original global section vanishes EXACTLY when its closed-fibre closed-point germs vanish. -/
theorem section_eq_zero_iff_closedPoint_closedFiber_germs [LocallyOfFiniteType q] (m : Γ(M, ⊤)) :
    m = 0 ↔ ∀ y, IsClosed ({y} : Set Y) → q y = IsLocalRing.closedPoint S →
      M.presheaf.germ ⊤ y trivial m = 0 := by
  refine ⟨?_, section_eq_zero_of_closedPoint_closedFiber_germs q M m⟩
  rintro rfl y _ _
  exact map_zero _

end UnitMap

end EnvelopeProperty.ProperLocalSectionDetection
