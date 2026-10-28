import EnvelopeProperty.AlgGeom.PrimitiveIntegralGenerator
import EnvelopeProperty.FiniteCurveLineParameter

/-! # Constructing the primitive polynomial parameter of an original integral curve -/

open scoped Polynomial Classical
open Polynomial
noncomputable section
namespace EnvelopeProperty

private theorem primitive_of_same_coefficient_image
    {F G L : Type*} [Field F] [Field G] [Field L] [Algebra F L] [Algebra G L]
    (q : G ≃+* F) (hq : ∀ a, algebraMap G L a = algebraMap F L (q a))
    (b : L) (hb : IntermediateField.adjoin F {b} = ⊤) :
    IntermediateField.adjoin G {b} = ⊤ := by
  let E := IntermediateField.adjoin G ({b} : Set L)
  let E0 : IntermediateField F L :=
    { E.toSubalgebra.toSubsemiring with
      algebraMap_mem' := fun a => by
        obtain ⟨c, rfl⟩ := q.surjective a
        rw [← hq]
        exact E.algebraMap_mem c
      inv_mem' := fun a ha => E.inv_mem ha }
  have hb0 : b ∈ E0 := IntermediateField.subset_adjoin G _ (by simp)
  have hle : IntermediateField.adjoin F ({b} : Set L) ≤ E0 :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hb0)
  have htop : E0 = ⊤ := top_unique (hb ▸ hle)
  apply top_unique
  intro a ha
  have h : a ∈ E0 := htop ▸ IntermediateField.mem_top
  exact h

/-- Construct the actual injective finite free one-variable parameter, the
compatible original fraction map and an actual integral primitive generator. -/
theorem exists_finiteFree_primitive_polynomial_of_dimension_le_one
    (F B : Type*) [Field F] [PerfectField F] [CommRing B] [IsDomain B] [Algebra F B]
    [Algebra.FiniteType F B] [Ring.KrullDimLE 1 B] (hB : ¬ IsField B) :
    ∃ (φ : F[X] →ₐ[F] B)
      (ψ : FractionRing F[X] →+* FractionRing B) (b : B),
      Function.Injective φ ∧ φ.toRingHom.Finite ∧
      (letI := φ.toRingHom.toAlgebra; Module.Free F[X] B) ∧
      (∀ p, ψ (algebraMap F[X] (FractionRing F[X]) p) =
        algebraMap B (FractionRing B) (φ p)) ∧
      (letI := ψ.toAlgebra
       IntermediateField.adjoin (FractionRing F[X]) {algebraMap B (FractionRing B) b} = ⊤) := by
  obtain ⟨n, g, ψ, b, hginj, hfin, _, hcompat, _, hprim⟩ :=
    FcPrimitiveIntegralGenerator.exists_global_normalization_with_integral_primitive_element F B
  let A := MvPolynomial (Fin n) F
  let : Algebra A B := g.toRingHom.toAlgebra
  have : Module.Finite A B := hfin
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hginj
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing F B
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (α := B)
  have : M.IsMaximal := hM
  have hM0 : M ≠ ⊥ := by
    intro h
    exact hB (Ring.isField_iff_maximal_bot.mpr (h ▸ hM))
  have : (M.under A).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) M
  have hheight : M.height = (n : ℕ) := by
    rw [height_eq_under_of_normal_integral (R := A) M]
    exact maximalHeight_mvPolynomialFin F n (M.under A)
  have hn0 : n ≠ 0 := by
    intro h
    have hz : M.height = 0 := by simpa only [h, Nat.cast_zero] using hheight
    exact hM0 (Ideal.height_eq_zero_iff_eq_bot.mp hz)
  have hnle : n ≤ 1 := by
    have hd := Ideal.height_le_ringKrullDim_of_isPrime (I := M)
    have hb := Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 B)
    rw [hheight] at hd
    have hle : (n : ℕ∞) ≤ 1 := WithBot.coe_le_coe.mp (hd.trans hb)
    exact_mod_cast hle
  have hn : n = 1 := by omega
  subst n
  let c : MvPolynomial (Fin 1) F ≃ₐ[F] F[X] := MvPolynomial.uniqueAlgEquiv F (Fin 1)
  let φ : F[X] →ₐ[F] B := g.comp c.symm.toAlgHom
  have hiφ : Function.Injective φ := hginj.comp c.symm.injective
  have hfφ : φ.toRingHom.Finite := hfin.comp
    (RingHom.Finite.of_surjective c.symm.toRingHom c.symm.surjective)
  have hfree : letI := φ.toRingHom.toAlgebra; Module.Free F[X] B := by
    let : Algebra F[X] B := φ.toRingHom.toAlgebra
    have : Module.Finite F[X] B := hfφ
    have : Module.IsTorsionFree F[X] B :=
      (Module.isTorsionFree_iff_algebraMap_injective).mpr hiφ
    infer_instance
  let q : FractionRing F[X] ≃+* FractionRing (MvPolynomial (Fin 1) F) :=
    IsFractionRing.ringEquivOfRingEquiv c.symm.toRingEquiv
  let ψ' : FractionRing F[X] →+* FractionRing B := ψ.comp q.toRingHom
  refine ⟨φ, ψ', b, hiφ, hfφ, hfree, ?_, ?_⟩
  · intro p
    change ψ (q (algebraMap F[X] (FractionRing F[X]) p)) = _
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    exact hcompat (c.symm p)
  · let : Algebra (FractionRing (MvPolynomial (Fin 1) F)) (FractionRing B) := ψ.toAlgebra
    let : Algebra (FractionRing F[X]) (FractionRing B) := ψ'.toAlgebra
    exact primitive_of_same_coefficient_image q (fun _ => rfl)
      (algebraMap B (FractionRing B) b) hprim

end EnvelopeProperty
