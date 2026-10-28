import EnvelopeProperty.Char0.DVRMonomialMultiplierBound
import EnvelopeProperty.Char0.ValuativeMultiplierIdeal
import EnvelopeProperty.Char0.EtaleMultiplierRestriction

/-! # Every actual original monomial Rees tree computes the SAME full all-DVR multiplier ideal -/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- For ANY actual original Rees tree with original etale monomial data,
the intersection of the actual whole clipped leaf monomials is EXACTLY the
SAME original full all-divisorial-DVR multiplier ideal. No selected valuations,
normality, discrepancy bound or coverage certificate is an extra premise. -/
theorem iInf_reesTree_monomial_eq_valuativeMultiplierIdeal
    (C : Subalgebra k K) [IsFractionRing C K] (T : ReesChartTree k K C)
    (n : ℕ) (I : Ideal C) (hI : I ≠ ⊥)
    (v : (i : T.LeafIndex) → Fin n → T.leafAlgebra i)
    (hv : ∀ i, (MvPolynomial.aeval (R := k) (v i)).toRingHom.Etale)
    (τ : T.LeafIndex → Type u) [∀ i, Fintype (τ i)]
    (c : (i : T.LeafIndex) → τ i → Fin n) (hc : ∀ i, Function.Injective (c i))
    (d a : (i : T.LeafIndex) → τ i → ℕ)
    (hIE : ∀ i, I.map (Subalgebra.inclusion
      (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))).toRingHom =
        span {∏ l, v i (c i l) ^ d i l})
    (hJ : ∀ i, letI : Algebra C (T.leafAlgebra i) := (Subalgebra.inclusion
      (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))).toAlgebra
      affineRelativeJacobianIdeal (R := C) (etaleDifferentialBasis (v i) (hv i)) =
        span {∏ l, v i (c i l) ^ a i l}) (q : ℚ) :
    (⨅ i : T.LeafIndex,
      (span {∏ l, v i (c i l) ^ (⌊q * (d i l : ℚ)⌋₊ - a i l)}).comap
        (Subalgebra.inclusion
          (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))).toRingHom) =
      valuativeMultiplierIdeal C I hI q := by
  apply le_antisymm
  · intro f hf
    rw [mem_valuativeMultiplierIdeal_iff]
    intro V
    let := V.property.2.1
    let := V.property.2.2.1
    let := V.property.2.2.2
    obtain ⟨E, hE, hEV⟩ := T.exists_leaf_le (actualDVRValuationSubring V.val) V.property.1
    obtain ⟨i, rfl⟩ := T.exists_leafIndex_of_mem_leaves hE
    let E := T.leafAlgebra i
    let hCE : C ≤ E := T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i)
    let : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
    obtain ⟨m, π, u, hπ, hu⟩ := exists_finite_dvr_coordinates (k := k) V.val
    let u' : ULift.{u} (Fin m) → V.val := fun j => u j.down
    have hu' : IsTranscendenceBasis k (residue V.val ∘ u') := hu.comp_equiv Equiv.ulift
    let e : Fin n ≃ Option (ULift.{u} (Fin m)) :=
      dvrLeafCoordinateIndexEquiv E V.val (v i) (hv i) hπ hu'
    have hfE : Subalgebra.inclusion hCE f ∈
        span {∏ l, v i (c i l) ^ (⌊q * (d i l : ℚ)⌋₊ - a i l)} :=
      (Submodule.mem_iInf _).mp hf i
    have hmem := mem_dvrMultiplierContribution_of_leaf_monomial C E V.val hCE hEV
      hπ hu' e (v i) (hv i) (c i) (hc i) (d i) (a i)
      (fun l => ⌊q * (d i l : ℚ)⌋₊ - a i l) I hI (hIE i) (hJ i) q
      (fun _ => le_rfl) f hfE
    have hintrinsic : f ∈ intrinsicDVRMultiplierContribution C V.val V.property.1 I hI q := by
      rw [intrinsicDVRMultiplierContribution_eq C V.val V.property.1 hπ hu' e I hI q]
      exact hmem
    exact (mem_intrinsicDVRMultiplierContribution_iff C V.val V.property.1 I hI q f).mp hintrinsic
  · apply le_iInf
    intro i
    exact valuativeMultiplierIdeal_le_comap_monomial_of_etale_leaf
      C (T.leafAlgebra i) (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))
      (v i) (hv i) (c i) (hc i) (d i) (a i) I hI (hIE i) (hJ i) q

end EnvelopeProperty.Char0
