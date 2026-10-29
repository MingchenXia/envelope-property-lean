/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SmoothFamilyTree
import EnvelopeProperty.Char0.DVRLeafJacobian
import EnvelopeProperty.Char0.DVRLeafDimension

/-!
# Actual smooth-source family charts in every actual divisorial DVR

An actual simultaneous Rees tree supplies the leaf, its actual containment,
all original family monomials and its genuine original-source Jacobian
monomial. Actual differential bases produce the matching DVR coordinate
indices internally, and actual DVR partials give the exact source ideal.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
  (C V : Subalgebra k K) [IsDiscreteValuationRing V] [IsFractionRing V K]
  [Algebra.EssFiniteType k V] (hCV : C ≤ V) {ι : Type u} [Fintype ι]
  {π : V} {u : ι → V} {n : ℕ}

/-- The actual original-source Jacobian ideal uses every original C-function and the
actual produced DVR partials restricted directly to the original literal source. -/
def dvrOriginalSourceJacobianIdeal (hπ : Irreducible π)
    (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι) : Ideal V :=
  letI : Algebra C V := (Subalgebra.inclusion hCV).toAlgebra
  letI : IsScalarTower k C V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  derivationSourceJacobianIdeal (R := C) (dvrLeafPartials C V hCV hπ hu e)

/-- Actual original-source determinant ideals retain exactly the original functions when
computed through a literal intermediate leaf. -/
theorem dvrSourceJacobianIdeal_through_leaf (E : Subalgebra k K) (hCE : C ≤ E) (hEV : E ≤ V)
    (hπ : Irreducible π) (hu : IsTranscendenceBasis k (residue V ∘ u)) (e : Fin n ≃ Option ι) :
    letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
    letI : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
    letI : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
    derivationSourceJacobianIdeal (R := C) (dvrLeafPartials E V hEV hπ hu e) =
      dvrOriginalSourceJacobianIdeal C V hCV hπ hu e := by
  let _ : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
  let _ : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
  have : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  unfold derivationSourceJacobianIdeal dvrOriginalSourceJacobianIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext w
  congr 1

/-- Every actual divisorial DVR over the smooth source receives a genuinely produced
simultaneous monomial chart and exact original-source DVR Jacobian ideal factorization.
Containment, fraction fields and matching coordinate ranks are derived internally. -/
theorem exists_smooth_family_dvr_chart [IsFractionRing C K]
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    {κ : Type*} [Fintype κ] (I : κ → Ideal C) (hI : ∀ j, I j ≠ ⊥)
    (hπ : Irreducible π) (hu : IsTranscendenceBasis k (residue V ∘ u)) :
    ∃ (n : ℕ) (T : ReesChartTree k K C) (i : T.LeafIndex)
      (hEV : T.leafAlgebra i ≤ V)
      (v : Fin n → T.leafAlgebra i)
      (_hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
      (τ : Type u) (_ : Fintype τ) (c : τ → Fin n), Function.Injective c ∧
      ∃ (d : κ → τ → ℕ) (a : τ → ℕ),
        (∀ j, (I j).map (Subalgebra.inclusion hCV).toRingHom =
          span {∏ l, Subalgebra.inclusion hEV (v (c l)) ^ d j l}) ∧
        ∃ e : Fin n ≃ Option ι,
          dvrOriginalSourceJacobianIdeal C V hCV hπ hu e =
            span {(Matrix.of fun l j => dvrLeafPartials (T.leafAlgebra i) V hEV hπ hu e j
              (v l)).det * ∏ l, Subalgebra.inclusion hEV (v (c l)) ^ a l} := by
  obtain ⟨n, T, hdata⟩ := exists_smooth_family_rees_tree C I hI
  obtain ⟨E, hE, hEV⟩ := T.exists_leaf_le (actualDVRValuationSubring V) hCV
  obtain ⟨i, rfl⟩ := T.exists_leafIndex_of_mem_leaves hE
  let E := T.leafAlgebra i
  let hCE : C ≤ E := T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i)
  have hEV' : E ≤ V := hEV
  let _ : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
  let _ : Algebra E V := (Subalgebra.inclusion hEV').toAlgebra
  have : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
  obtain ⟨v, hv, τ, hτ, c, hcinj, d, a, hd, hJ⟩ := hdata i
  let _ : Fintype τ := hτ
  let e : Fin n ≃ Option ι := dvrLeafCoordinateIndexEquiv E V v hv hπ hu
  refine ⟨n, T, i, hEV', v, hv, τ, hτ, c, hcinj, d, a, ?_, e, ?_⟩
  · intro j
    have h := congrArg (fun J : Ideal E => J.map (Subalgebra.inclusion hEV').toRingHom) (hd j)
    rw [Ideal.map_map, Ideal.map_span, Set.image_singleton] at h
    have hcomp : (Subalgebra.inclusion hEV').toRingHom.comp
        (Subalgebra.inclusion hCE).toRingHom = (Subalgebra.inclusion hCV).toRingHom := rfl
    rw [hcomp] at h
    have hmap (z : E) : (Subalgebra.inclusion hEV').toRingHom z = Subalgebra.inclusion hEV' z := rfl
    simpa only [map_prod, map_pow, hmap] using h
  · have h := dvr_leaf_source_jacobian_ideal E V hEV' C hCE hπ hu e v hv c a hJ
    rw [dvrSourceJacobianIdeal_through_leaf C V hCV E hCE hEV' hπ hu e] at h
    exact h

end EnvelopeProperty.Char0
