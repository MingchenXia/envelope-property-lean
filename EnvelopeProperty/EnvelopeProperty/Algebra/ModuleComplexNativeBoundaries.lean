import EnvelopeProperty.Algebra.ModuleComplexNativeCycleClasses

/-! # SAME actual native whole classes detect genuine original incoming boundaries -/
noncomputable section
namespace EnvelopeProperty.ModuleComplexNativeBoundaries
open CategoryTheory
universe u
variable {R : Type u} [CommRing R]

private theorem rowClass_eq_iff (S : ShortComplex (ModuleCat.{u} R))
    (z w : LinearMap.ker S.g.hom) :
    S.homologyπ (S.moduleCatCyclesIso.inv z) = S.homologyπ (S.moduleCatCyclesIso.inv w) ↔
      ∃ a : S.X₁, S.moduleCatToCycles a = z-w := by
  constructor
  · intro h
    have he := (S.moduleCatCyclesIso_inv_π_apply z).symm.trans
      (h.trans (S.moduleCatCyclesIso_inv_π_apply w))
    have hq : (Submodule.Quotient.mk z : LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) =
        Submodule.Quotient.mk w := S.moduleCatHomologyIso.symm.toLinearEquiv.injective he
    exact (Submodule.Quotient.eq (LinearMap.range S.moduleCatToCycles)).mp hq
  · intro h
    have hq := congrArg S.moduleCatHomologyIso.inv.hom
      ((Submodule.Quotient.eq (LinearMap.range S.moduleCatToCycles)).mpr h)
    exact (S.moduleCatCyclesIso_inv_π_apply z).trans
      (hq.trans (S.moduleCatCyclesIso_inv_π_apply w).symm)

/-- Equality of SAME actual native whole cycle classes DERIVES an actual original incoming primitive. -/
theorem cycleClass_eq_iff_boundary (K : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ)
    (z w : LinearMap.ker (K.sc q).g.hom) :
    ModuleComplexNativeCycleClasses.cycleClass K q z = ModuleComplexNativeCycleClasses.cycleClass K q w ↔
      ∃ a : (K.sc q).X₁, (K.sc q).moduleCatToCycles a = z-w :=
  rowClass_eq_iff (K.sc q) z w

/-- An actual original cycle has zero SAME native class EXACTLY when it has an actual incoming primitive. -/
theorem cycleClass_eq_zero_iff_boundary (K : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ)
    (z : LinearMap.ker (K.sc q).g.hom) :
    ModuleComplexNativeCycleClasses.cycleClass K q z = 0 ↔
      ∃ a : (K.sc q).X₁, (K.sc q).moduleCatToCycles a = z := by
  have hz : ModuleComplexNativeCycleClasses.cycleClass K q 0 = 0 := by
    exact (congrArg (K.sc q).homologyπ ((K.sc q).moduleCatCyclesIso.inv.hom.map_zero)).trans
      (K.sc q).homologyπ.hom.map_zero
  have h := cycleClass_eq_iff_boundary K q z 0
  simpa only [hz, sub_zero] using h

/-- Zero SAME actual native class PRODUCES a true original predecessor differential preimage. -/
theorem exists_preimage_of_cycleClass_zero (K : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ)
    (z : LinearMap.ker (K.sc q).g.hom)
    (hz : ModuleComplexNativeCycleClasses.cycleClass K q z = 0) :
    ∃ a : K.X ((ComplexShape.up ℕ).prev q), K.d ((ComplexShape.up ℕ).prev q) q a = z.val := by
  obtain ⟨a, ha⟩ := (cycleClass_eq_zero_iff_boundary K q z).mp hz
  exact ⟨a, congrArg Subtype.val ha⟩
end EnvelopeProperty.ModuleComplexNativeBoundaries
