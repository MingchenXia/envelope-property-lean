/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.DVRMonomialMultiplierBound
import EnvelopeProperty.Char0.ValuativeMultiplierIdeal
import EnvelopeProperty.Char0.EtaleMultiplierRestriction
import EnvelopeProperty.Char0.BoundaryMultiplierDetection

/-!
# A single finite actual DVR family detects every rational multiplier exponent

The original smooth source produces the actual tree and every monomial
factor internally. Its rounded leaf ideal is contained in the full actual
valuative multiplier ideal, using actual coverage of every divisorial DVR.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private structure FiniteDVRTestingMonomialLeafData
    (C E : Subalgebra k K) (hCE : C ≤ E) (n : ℕ) (I : Ideal C) where
  coordinates : Fin n → E
  coordinates_etale : (MvPolynomial.aeval (R := k) coordinates).toRingHom.Etale
  boundaryIndex : Type u
  boundaryFintype : Fintype boundaryIndex
  boundaryCoordinates : boundaryIndex → Fin n
  boundary_injective : Function.Injective boundaryCoordinates
  idealExponents : boundaryIndex → ℕ
  jacobianExponents : boundaryIndex → ℕ
  ideal_eq : letI := boundaryFintype
    I.map (Subalgebra.inclusion hCE).toRingHom =
      span {∏ l, coordinates (boundaryCoordinates l) ^ idealExponents l}
  jacobian_eq : letI := boundaryFintype
    letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
    affineRelativeJacobianIdeal (R := C) (etaleDifferentialBasis coordinates coordinates_etale) =
      span {∏ l, coordinates (boundaryCoordinates l) ^ jacobianExponents l}

private def finiteDVRTestingMonomialLeafData
    (C E : Subalgebra k K) (hCE : C ≤ E) (n : ℕ) (I : Ideal C)
    (h : EtaleFamilyMonomialLeaf C E hCE n (fun _ : Unit => I)) :
    FiniteDVRTestingMonomialLeafData C E hCE n I :=
  Classical.choice <| by
    obtain ⟨v, hv, τ, hτ, c, hc, d, a, hI, hJ⟩ := h
    exact ⟨⟨v, hv, τ, hτ, c, hc, d (), a, hI (), hJ⟩⟩

private structure FiniteDVRTestingTreeData (C : Subalgebra k K) (I : Ideal C) where
  dimension : ℕ
  tree : ReesChartTree k K C
  leaf : (i : tree.LeafIndex) → FiniteDVRTestingMonomialLeafData C (tree.leafAlgebra i)
    (tree.root_le_of_mem_leaves (tree.leafAlgebra_mem_leaves i)) dimension I

variable [CharZero k]

private def finiteDVRTestingTreeData
    (C : Subalgebra k K) [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (I : Ideal C) (hI : I ≠ ⊥) : FiniteDVRTestingTreeData C I :=
  Classical.choice <| by
    obtain ⟨n, T, h⟩ := exists_smooth_family_rees_tree C (fun _ : Unit => I) (fun _ => hI)
    exact ⟨⟨n, T, fun i => finiteDVRTestingMonomialLeafData C (T.leafAlgebra i)
      (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i)) n I (h i)⟩⟩

private def finiteDVRTestingLeafCutoffIdeal
    {C E : Subalgebra k K} {hCE : C ≤ E} {n : ℕ} {I : Ideal C}
    (d : FiniteDVRTestingMonomialLeafData C E hCE n I) (q : ℚ) : Ideal E :=
  letI := d.boundaryFintype
  span {∏ l, d.coordinates (d.boundaryCoordinates l) ^
    (⌊q * (d.idealExponents l : ℚ)⌋₊ - d.jacobianExponents l)}

private theorem finiteDVRTesting_all_rounded_implies_membership
    (C : Subalgebra k K) [IsFractionRing C K]
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) (f : C)
    (hf : let D := finiteDVRTestingTreeData C I hI
      ∀ i, Subalgebra.inclusion
          (D.tree.root_le_of_mem_leaves (D.tree.leafAlgebra_mem_leaves i)) f ∈
        finiteDVRTestingLeafCutoffIdeal (D.leaf i) q) :
    f ∈ valuativeMultiplierIdeal C I hI q := by
  rw [mem_valuativeMultiplierIdeal_iff]
  intro V
  let := V.property.2.1
  let := V.property.2.2.1
  let := V.property.2.2.2
  let D := finiteDVRTestingTreeData C I hI
  obtain ⟨E, hE, hEV⟩ := D.tree.exists_leaf_le (actualDVRValuationSubring V.val) V.property.1
  obtain ⟨i, rfl⟩ := D.tree.exists_leafIndex_of_mem_leaves hE
  let E := D.tree.leafAlgebra i
  let hCE : C ≤ E := D.tree.root_le_of_mem_leaves (D.tree.leafAlgebra_mem_leaves i)
  let d := D.leaf i
  let := d.boundaryFintype
  have : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
  obtain ⟨m, π, u, hπ, hu⟩ := exists_finite_dvr_coordinates (k := k) V.val
  let u' : ULift.{u} (Fin m) → V.val := fun j => u j.down
  have hu' : IsTranscendenceBasis k (residue V.val ∘ u') := hu.comp_equiv Equiv.ulift
  let e : Fin D.dimension ≃ Option (ULift.{u} (Fin m)) :=
    dvrLeafCoordinateIndexEquiv E V.val d.coordinates d.coordinates_etale hπ hu'
  have hfE : Subalgebra.inclusion hCE f ∈ finiteDVRTestingLeafCutoffIdeal d q := by
    exact hf i
  have hmem := mem_dvrMultiplierContribution_of_leaf_monomial C E V.val hCE hEV
    hπ hu' e d.coordinates d.coordinates_etale d.boundaryCoordinates d.boundary_injective
    d.idealExponents d.jacobianExponents
    (fun l => ⌊q * (d.idealExponents l : ℚ)⌋₊ - d.jacobianExponents l)
    I hI d.ideal_eq d.jacobian_eq q (fun _ => le_rfl) f hfE
  have hintrinsic : f ∈ intrinsicDVRMultiplierContribution C V.val V.property.1 I hI q := by
    rw [intrinsicDVRMultiplierContribution_eq C V.val V.property.1 hπ hu' e I hI q]
    exact hmem
  exact (mem_intrinsicDVRMultiplierContribution_iff C V.val V.property.1 I hI q f).mp hintrinsic

private def finiteDVRTestingPrimeIndex
    (C : Subalgebra k K) [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (I : Ideal C) (hI : I ≠ ⊥) : Type u :=
  let D := finiteDVRTestingTreeData C I hI
  (i : D.tree.LeafIndex) × boundaryMinimalPrimes
    (fun l : (D.leaf i).boundaryIndex => (D.leaf i).coordinates ((D.leaf i).boundaryCoordinates l))

private theorem finite_finiteDVRTestingPrimeIndex
    (C : Subalgebra k K) [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (I : Ideal C) (hI : I ≠ ⊥) : Finite (finiteDVRTestingPrimeIndex C I hI) := by
  let D := finiteDVRTestingTreeData C I hI
  have hfinite (i : D.tree.LeafIndex) : Finite (boundaryMinimalPrimes
      (fun l : (D.leaf i).boundaryIndex => (D.leaf i).coordinates ((D.leaf i).boundaryCoordinates l))) := by
    let d := D.leaf i
    let := d.boundaryFintype
    let := finiteType_of_etale_coordinates d.coordinates d.coordinates_etale
    have : IsNoetherianRing (D.tree.leafAlgebra i) :=
      Algebra.FiniteType.isNoetherianRing k (D.tree.leafAlgebra i)
    let := (finite_boundaryMinimalPrimes (fun l => d.coordinates (d.boundaryCoordinates l))).fintype
    exact inferInstance
  let := hfinite
  exact inferInstanceAs (Finite ((i : D.tree.LeafIndex) × boundaryMinimalPrimes
    (fun l : (D.leaf i).boundaryIndex => (D.leaf i).coordinates ((D.leaf i).boundaryCoordinates l))))

private def finiteDVRTestingBoundaryMap
    (C : Subalgebra k K) [IsFractionRing C K]
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (I : Ideal C) (hI : I ≠ ⊥) (P : finiteDVRTestingPrimeIndex C I hI) : divisorialDVRs C := by
  let D := finiteDVRTestingTreeData C I hI
  let d := D.leaf P.1
  letI := d.boundaryFintype
  exact etaleBoundaryDivisorialDVR C (D.tree.leafAlgebra P.1)
    (D.tree.root_le_of_mem_leaves (D.tree.leafAlgebra_mem_leaves P.1))
    d.coordinates d.coordinates_etale d.boundaryCoordinates P.2

/-- For every original smooth characteristic-zero source and original nonzero
ideal, one internally produced FINITE family of actual divisorial DVRs in the
original function field detects the FULL multiplier ideal for ALL rational
exponents. No selected valuations, resolution, canonical comparison, coordinate
system, discrepancy estimate or finite testing hypothesis is supplied. -/
theorem exists_finite_divisorialDVRs_forall_multiplier_exponents
    (C : Subalgebra k K) [IsFractionRing C K]
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (I : Ideal C) (hI : I ≠ ⊥) :
    ∃ S : Set (divisorialDVRs C), S.Finite ∧ ∀ (q : ℚ) (f : C),
      f ∈ valuativeMultiplierIdeal C I hI q ↔
        ∀ V ∈ S,
          letI := V.property.2.1
          letI := V.property.2.2.1
          letI := V.property.2.2.2
          f ∈ intrinsicDVRMultiplierContribution C V.val V.property.1 I hI q := by
  let S := Set.range (finiteDVRTestingBoundaryMap C I hI)
  let := finite_finiteDVRTestingPrimeIndex C I hI
  refine ⟨S, Set.finite_range _, ?_⟩
  intro q f
  constructor
  · intro hf V _
    let := V.property.2.1
    let := V.property.2.2.1
    let := V.property.2.2.2
    exact valuativeMultiplierIdeal_le_contribution C V.val V.property.1 I hI q hf
  · intro H
    apply finiteDVRTesting_all_rounded_implies_membership C I hI q f
    dsimp only
    intro i
    let D := finiteDVRTestingTreeData C I hI
    let d := D.leaf i
    let := d.boundaryFintype
    apply (mem_rounded_leaf_iff_all_boundaryDVRContributions C (D.tree.leafAlgebra i)
      (D.tree.root_le_of_mem_leaves (D.tree.leafAlgebra_mem_leaves i))
      d.coordinates d.coordinates_etale d.boundaryCoordinates d.boundary_injective
      d.idealExponents d.jacobianExponents I hI d.ideal_eq d.jacobian_eq q f).mpr
    intro P
    exact H (finiteDVRTestingBoundaryMap C I hI ⟨i, P⟩) ⟨⟨i, P⟩, rfl⟩

end EnvelopeProperty.Char0
