import ModularCurves.ForMathlib.BaseChangeKerCoker
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Flatness of relative arithmetic opcycles

No finiteness over the arithmetic coefficient ring is needed. These lemmas
apply after generic freeness of cohomology finite over a separate relative base.
-/

open CategoryTheory CategoryTheory.Limits TensorProduct

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyFlat

variable {A : Type u} [CommRing A]

/-- An extension of two flat modules is flat, without finite-rank hypotheses. -/
theorem flat_of_flat_submodule {M : Type u} [AddCommGroup M] [Module A M]
    (N : Submodule A M) [Module.Flat A N] [Module.Flat A (M ⧸ N)] : Module.Flat A M := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro P Q _ _ _ _ f hf
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro x hx
    have hxzero : f.rTensor M x = 0 := hx
    have hq : N.mkQ.lTensor P x = 0 := by
      apply Module.Flat.rTensor_preserves_injective_linearMap (M := M ⧸ N) f hf
      rw [map_zero]
      have hc : (f.rTensor (M ⧸ N)).comp (N.mkQ.lTensor P) =
          (N.mkQ.lTensor Q).comp (f.rTensor M) := by
        rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
      have hcomm := LinearMap.congr_fun hc x
      simpa only [LinearMap.comp_apply, hxzero, map_zero] using hcomm
    obtain ⟨y, hy⟩ := (lTensor_exact P (LinearMap.exact_subtype_mkQ N)
      N.mkQ_surjective x).mp hq
    have hyzero : f.rTensor N y = 0 := by
      apply ModularCurves.Module.Flat.lTensor_subtype_injective_of_flat_quotient Q N
      rw [map_zero]
      have hc : (N.subtype.lTensor Q).comp (f.rTensor N) =
          (f.rTensor M).comp (N.subtype.lTensor P) := by
        rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
      have hcomm := LinearMap.congr_fun hc y
      simpa only [LinearMap.comp_apply, hy, hxzero] using hcomm
    have : y = 0 :=
      (Module.Flat.rTensor_preserves_injective_linearMap (M := N) f hf)
        (hyzero.trans (map_zero _).symm)
    simpa only [this, map_zero, Submodule.mem_bot] using hy.symm
  · exact bot_le

/-- Homology and the next flat cokernel force the current opcycles to be flat. -/
theorem opcycles_flat (S : ShortComplex (ModuleCat.{u} A))
    [Module.Flat A S.homology] [Module.Flat A S.X₃]
    [Module.Flat A (S.X₃ ⧸ LinearMap.range S.g.hom)] :
    Module.Flat A S.opcycles := by
  let e : S.homology ≅ ModuleCat.of A (LinearMap.ker S.fromOpcycles.hom) :=
    S.homologyIsKernel.conePointUniqueUpToIso (ModuleCat.kernelIsLimit S.fromOpcycles)
  let : Module.Flat A (LinearMap.ker S.fromOpcycles.hom) :=
    Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  have hr : LinearMap.range S.fromOpcycles.hom = LinearMap.range S.g.hom := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective S.pOpcycles).mp inferInstance x
      exact ⟨y, (ConcreteCategory.congr_hom S.p_fromOpcycles y).symm⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨S.pOpcycles x, ConcreteCategory.congr_hom S.p_fromOpcycles x⟩
  let : Module.Flat A (LinearMap.range S.g.hom) :=
    ModularCurves.Module.Flat.of_flat_quotient _
  let : Module.Flat A (LinearMap.range S.fromOpcycles.hom) := by rwa [hr]
  let : Module.Flat A (S.opcycles ⧸ LinearMap.ker S.fromOpcycles.hom) :=
    Module.Flat.of_linearEquiv (LinearMap.quotKerEquivRange S.fromOpcycles.hom)
  exact flat_of_flat_submodule (LinearMap.ker S.fromOpcycles.hom)

end EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyFlat
