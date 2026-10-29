import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic

/-!
# Genuine geometric domain preservation over an algebraically closed field

Two entire nonzero tensor elements descend to one finitely generated coefficient
subalgebra. Localization at the product of actual nonzero basis coefficients
and the Nullstellensatz produce a genuine rational specialization retaining both
entire elements. Their product therefore cannot vanish in a tensor of domains.
No finite-type hypothesis on either original domain, field-extension
certificate, completeness or characteristic restriction is used.
-/

noncomputable section
open scoped TensorProduct
open Algebra
namespace EnvelopeProperty

/-- A genuine nontrivial finite-type algebra over an algebraically closed field has an actual rational evaluator. -/
theorem exists_algHom_to_algClosed
    (k B : Type*) [Field k] [IsAlgClosed k] [CommRing B] [Nontrivial B]
    [Algebra k B] [Algebra.FiniteType k B] : Nonempty (B →ₐ[k] k) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  let : M.IsMaximal := hM
  let := Ideal.Quotient.field M
  have : Module.Finite k (B ⧸ M) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ M)
  exact ⟨(IsAlgClosed.lift : (B ⧸ M) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k M)⟩

/-- Every whole basis coefficient commutes with genuine coefficient specialization. -/
theorem basis_baseChange_repr_tensorMap
    {k B C A ι : Type*} [Field k] [CommRing B] [CommRing C] [CommRing A]
    [Algebra k B] [Algebra k C] [Algebra k A]
    (b : Module.Basis ι k A) (f : B →ₐ[k] C) (z : B ⊗[k] A) (i : ι) :
    (b.baseChange C).repr (Algebra.TensorProduct.map f (AlgHom.id k A) z) i =
      f ((b.baseChange B).repr z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Module.Basis.baseChange_repr_tmul]
  | add x y hx hy => simp [hx, hy]

/-- A true finite-type domain has a rational evaluator avoiding any given nonzero element. -/
theorem exists_algHom_to_algClosed_nonzero
    (k B : Type*) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (a : B) (ha : a ≠ 0) :
    ∃ f : B →ₐ[k] k, f a ≠ 0 := by
  let : NeZero a := ⟨ha⟩
  let L := Localization.Away a
  have : IsDomain L := IsLocalization.Away.isDomain L ha
  have : Algebra.FinitePresentation B L := IsLocalization.Away.finitePresentation a
  have : Algebra.FiniteType B L := Algebra.FiniteType.of_finitePresentation
  have : Algebra.FiniteType k L := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  obtain ⟨f⟩ := exists_algHom_to_algClosed k L
  refine ⟨f.comp (IsScalarTower.toAlgHom k B L), ?_⟩
  exact ((IsLocalization.Away.algebraMap_isUnit (S := L) a).map f.toMonoidHom).ne_zero

/-- Actual coefficient specialization can retain two entire nonzero tensor elements at once. -/
theorem exists_tensorSpecialization_nonzero
    (k B A : Type*) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
    [CommRing A] [Algebra k B] [Algebra k A] [Algebra.FiniteType k B]
    (x y : B ⊗[k] A) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ f : B →ₐ[k] k,
      Algebra.TensorProduct.map f (AlgHom.id k A) x ≠ 0 ∧
      Algebra.TensorProduct.map f (AlgHom.id k A) y ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis k A
  have hxr : (b.baseChange B).repr x ≠ 0 := by
    intro h
    exact hx ((b.baseChange B).repr.injective (h.trans ((b.baseChange B).repr.map_zero).symm))
  have hyr : (b.baseChange B).repr y ≠ 0 := by
    intro h
    exact hy ((b.baseChange B).repr.injective (h.trans ((b.baseChange B).repr.map_zero).symm))
  obtain ⟨i, hi⟩ : ∃ i, (b.baseChange B).repr x i ≠ 0 := by
    by_contra! h
    exact hxr (Finsupp.ext h)
  obtain ⟨j, hj⟩ : ∃ j, (b.baseChange B).repr y j ≠ 0 := by
    by_contra! h
    exact hyr (Finsupp.ext h)
  obtain ⟨f, hf⟩ := exists_algHom_to_algClosed_nonzero k B
    ((b.baseChange B).repr x i * (b.baseChange B).repr y j) (mul_ne_zero hi hj)
  rw [map_mul] at hf
  refine ⟨f, ?_, ?_⟩
  · intro h
    have he := basis_baseChange_repr_tensorMap b f x i
    rw [h, map_zero, Finsupp.zero_apply] at he
    exact (mul_ne_zero_iff.mp hf).1 he.symm
  · intro h
    have he := basis_baseChange_repr_tensorMap b f y j
    rw [h, map_zero, Finsupp.zero_apply] at he
    exact (mul_ne_zero_iff.mp hf).2 he.symm

/-- Whole tensor coefficient injection follows from the genuine basis coefficient formula. -/
theorem tensorMap_left_injective
    {k B C A : Type*} [Field k] [CommRing B] [CommRing C] [CommRing A]
    [Algebra k B] [Algebra k C] [Algebra k A]
    (f : B →ₐ[k] C) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.map f (AlgHom.id k A)) := by
  classical
  let b := Module.Free.chooseBasis k A
  intro x y h
  apply (b.baseChange B).repr.injective
  ext i
  apply hf
  rw [← basis_baseChange_repr_tensorMap b f x i,
    ← basis_baseChange_repr_tensorMap b f y i, h]

/-- Two whole tensor elements descend simultaneously to a genuine finite coefficient subalgebra. -/
theorem exists_fgSubalgebra_tensor_pair
    {k F A : Type*} [Field k] [CommRing F] [CommRing A]
    [Algebra k F] [Algebra k A] (x y : F ⊗[k] A) :
    ∃ (B : Subalgebra k F), B.FG ∧ ∃ xB yB : B ⊗[k] A,
      Algebra.TensorProduct.map B.val (AlgHom.id k A) xB = x ∧
      Algebra.TensorProduct.map B.val (AlgHom.id k A) yB = y := by
  obtain ⟨Bx, hx, x0, hx0⟩ := TensorProduct.Algebra.exists_of_fg x
  obtain ⟨By, hy, y0, hy0⟩ := TensorProduct.Algebra.exists_of_fg y
  let B := Bx ⊔ By
  let ix : Bx →ₐ[k] B := Subalgebra.inclusion le_sup_left
  let iy : By →ₐ[k] B := Subalgebra.inclusion le_sup_right
  refine ⟨B, hx.sup hy, Algebra.TensorProduct.map ix (AlgHom.id k A) x0,
    Algebra.TensorProduct.map iy (AlgHom.id k A) y0, ?_, ?_⟩
  · change Algebra.TensorProduct.map Bx.val (AlgHom.id k A) x0 = x at hx0
    have hm : (Algebra.TensorProduct.map B.val (AlgHom.id k A)).comp
        (Algebra.TensorProduct.map ix (AlgHom.id k A)) =
        Algebra.TensorProduct.map Bx.val (AlgHom.id k A) := by
      ext b <;> simp [ix]
    rw [← AlgHom.comp_apply, hm]
    exact hx0
  · change Algebra.TensorProduct.map By.val (AlgHom.id k A) y0 = y at hy0
    have hm : (Algebra.TensorProduct.map B.val (AlgHom.id k A)).comp
        (Algebra.TensorProduct.map iy (AlgHom.id k A)) =
        Algebra.TensorProduct.map By.val (AlgHom.id k A) := by
      ext b <;> simp [iy]
    rw [← AlgHom.comp_apply, hm]
    exact hy0

/-- Every whole domain algebra over an algebraically closed field remains a domain after arbitrary domain coefficient extension. -/
theorem tensorProduct_isDomain_of_algClosed
    (k F A : Type*) [Field k] [IsAlgClosed k] [CommRing F] [IsDomain F]
    [CommRing A] [IsDomain A] [Algebra k F] [Algebra k A] :
    IsDomain (F ⊗[k] A) := by
  classical
  have : Nontrivial (F ⊗[k] A) :=
    (Algebra.TensorProduct.includeRight_injective
      (R := k) (A := F) (B := A) (RingHom.injective (algebraMap k F))).nontrivial
  have : NoZeroDivisors (F ⊗[k] A) := ⟨fun {x y} hxy => by
    by_cases hx : x = 0
    · exact Or.inl hx
    by_cases hy : y = 0
    · exact Or.inr hy
    exfalso
    obtain ⟨B, hB, xB, yB, hxB, hyB⟩ := exists_fgSubalgebra_tensor_pair x y
    have : Algebra.FiniteType k B := B.fg_iff_finiteType.mp hB
    let j := Algebra.TensorProduct.map B.val (AlgHom.id k A)
    have hj : Function.Injective j := tensorMap_left_injective B.val Subtype.val_injective
    have hxB' : xB ≠ 0 := by
      intro h
      exact hx (hxB.symm.trans (h ▸ j.map_zero))
    have hyB' : yB ≠ 0 := by
      intro h
      exact hy (hyB.symm.trans (h ▸ j.map_zero))
    have hxyB : xB * yB = 0 := by
      apply hj
      rw [map_mul, map_zero]
      exact hxB.symm ▸ hyB.symm ▸ hxy
    obtain ⟨f, hfx, hfy⟩ := exists_tensorSpecialization_nonzero k B A xB yB hxB' hyB'
    let e := Algebra.TensorProduct.lid k A
    let p := Algebra.TensorProduct.map f (AlgHom.id k A)
    have hpx : e (p xB) ≠ 0 := fun h => hfx (e.injective (h.trans e.map_zero.symm))
    have hpy : e (p yB) ≠ 0 := fun h => hfy (e.injective (h.trans e.map_zero.symm))
    exact (mul_ne_zero hpx hpy) (by rw [← map_mul, ← map_mul, hxyB, map_zero, map_zero])⟩
  exact NoZeroDivisors.to_isDomain _

end EnvelopeProperty
