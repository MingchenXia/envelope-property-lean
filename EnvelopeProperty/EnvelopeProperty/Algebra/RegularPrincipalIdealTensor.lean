/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Algebra.IdealTensorBaseChange
import EnvelopeProperty.AlgGeom.CartierIdealModules

open TensorProduct
noncomputable section
universe u v
namespace EnvelopeProperty.IdealTensorBaseChange
variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

/-- The original ideal tensor map is injective when an original regular
principal equation remains regular, without any flatness assumption. -/
theorem toIdealMap_injective_of_regularGenerator (I : Ideal R) (g : R)
    (hg : g ∈ nonZeroDivisors R) (hI : I = Ideal.span {g})
    (hS : algebraMap R S g ∈ nonZeroDivisors S) :
    Function.Injective (toIdealMap S I) := by
  let e := regularGeneratorModuleEquiv I g hg hI
  let q := (e.symm.baseChange R S).trans (AlgebraTensorModule.rid R S S)
  have hformula : ∀ t : S ⊗[R] I,
      (toIdealMap S I t : S) = q t * algebraMap R S g := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s x =>
      obtain ⟨r, rfl⟩ := e.surjective x
      rw [toIdealMap_tmul]
      change s * algebraMap R S (r * g) = _
      dsimp only [q, LinearEquiv.trans_apply]
      rw [LinearEquiv.baseChange_tmul, e.symm_apply_apply,
        AlgebraTensorModule.rid_tmul, map_mul]
      rw [Algebra.smul_def]
      ring
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy, add_mul]
  intro x y hxy
  apply q.injective
  apply sub_eq_zero.mp
  apply (mul_right_mem_nonZeroDivisors_eq_zero_iff hS).mp
  rw [sub_mul, ← hformula x, ← hformula y, hxy, sub_self]

/-- The same original canonical tensor map is a genuine equivalence whenever
an original regular principal equation retains its actual regular image. -/
def equivOfRegularGenerator (I : Ideal R) (g : R)
    (hg : g ∈ nonZeroDivisors R) (hI : I = Ideal.span {g})
    (hS : algebraMap R S g ∈ nonZeroDivisors S) :
    S ⊗[R] I ≃ₗ[S] I.map (algebraMap R S) :=
  LinearEquiv.ofBijective (toIdealMap S I)
    ⟨toIdealMap_injective_of_regularGenerator S I g hg hI hS,
      toIdealMap_surjective S I⟩

/-- The nonflat equivalence preserves every original pure-tensor value. -/
theorem equivOfRegularGenerator_tmul (I : Ideal R) (g : R)
    (hg : g ∈ nonZeroDivisors R) (hI : I = Ideal.span {g})
    (hS : algebraMap R S g ∈ nonZeroDivisors S) (s : S) (x : I) :
    (equivOfRegularGenerator S I g hg hI hS (s ⊗ₜ[R] x) : S) =
      s * algebraMap R S x := toIdealMap_tmul S I s x

end EnvelopeProperty.IdealTensorBaseChange
