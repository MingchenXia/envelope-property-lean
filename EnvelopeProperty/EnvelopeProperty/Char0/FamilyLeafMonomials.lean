/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SNCFamilyJacobianCover
import EnvelopeProperty.Char0.LeafJacobianCoordinates

/-!
# Simultaneous actual factor and Jacobian monomials on literal leaf rings

Actual boundary ideals transfer every family factor to the same actual
leaf coordinates as the genuine literal Jacobian formula.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory Module Ideal
open scoped Classical

universe u

variable {A : Type u} [CommRing A] {Y : Scheme.{u}}

/-- Transfer a native factor monomial through its actual boundary component ideals to any
actual contained leaf coordinates cutting out those pulled-back component ideals. -/
theorem idealOfSpecSheaf_comap_monomial_factor {ι : Type*} [Fintype ι]
    (J : Y.IdealSheafData) (P : ι → Y.IdealSheafData) (U : Y.affineOpens)
    (p : ι → Γ(Y, U.1)) (a : ι → ℕ)
    (hP : ∀ i, (P i).ideal U = span {p i})
    (hJ : J.ideal U = span {∏ i, p i ^ a i})
    (α : Spec (.of A) ⟶ Y) (hα : Set.range α ⊆ (U.1 : Set Y))
    (q : ι → A) (hQ : ∀ i, idealOfSpecSheaf ((P i).comap α) = span {q i}) :
    idealOfSpecSheaf (J.comap α) = span {∏ i, q i ^ a i} := by
  have hfactor : J.ideal U = ∏ i, ((P i).ideal U) ^ a i := by
    rw [hJ]
    calc
      span {∏ i, p i ^ a i} = ∏ i, span {p i ^ a i} := (Ideal.prod_span_singleton _ _).symm
      _ = ∏ i, ((P i).ideal U) ^ a i := by
        apply Finset.prod_congr rfl
        intro i _
        rw [hP i, Ideal.span_singleton_pow]
  have hmapprod : (∏ i, ((P i).ideal U) ^ a i).map (affineOpenChartRingHom α U hα) =
      ∏ i, (((P i).ideal U) ^ a i).map (affineOpenChartRingHom α U hα) :=
    map_prod (Ideal.mapHom (affineOpenChartRingHom α U hα))
      (fun i => ((P i).ideal U) ^ a i) Finset.univ
  rw [idealOfSpecSheaf_comap_affineOpenChart J α U hα, hfactor, hmapprod]
  calc
    (∏ i, (((P i).ideal U) ^ a i).map (affineOpenChartRingHom α U hα)) =
        ∏ i, idealOfSpecSheaf ((P i).comap α) ^ a i := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Ideal.map_pow, ← idealOfSpecSheaf_comap_affineOpenChart (P i) α U hα]
    _ = span {∏ i, q i ^ a i} := by
      simp_rw [hQ, Ideal.span_singleton_pow]
      exact Ideal.prod_span_singleton _ _

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] {κ : Type*}

/-- Every family factor transfers to any actual leaf coordinates adapted to the same
actual pulled-back boundary ideals. -/
theorem exists_family_factor_monomials_in_leaf_coordinates
    (π : Y ⟶ Spec (.of R)) (α : Spec (.of A) ⟶ Y)
    (J : (Spec (.of R)).IdealSheafData) (F : Scheme.DivisorFamily Y) (n : ℕ)
    (B : κ → Y.IdealSheafData) (x : Y) (W : Y.affineOpens)
    (hW : SNCFamilyJacobianNeighbourhood (k := k) π F n J B x W)
    (hαW : Set.range α ⊆ (W.1 : Set Y))
    (vA : Fin n → A) (cA : {i : F.ι // x ∈ (F.component i).support} → Fin n)
    (hFA : ∀ i, idealOfSpecSheaf ((F.component i.1).comap α) = span {vA (cA i)}) :
    ∃ d : κ → {i : F.ι // x ∈ (F.component i).support} → ℕ,
      ∀ j, idealOfSpecSheaf ((B j).comap α) = span {∏ i, vA (cA i) ^ d j i} := by
  obtain ⟨U, v, _, _, c, _, hc, _, d, hB, _, _, s, hWs, _⟩ := hW
  have hαU : Set.range α ⊆ (U.1 : Set Y) := by
    intro y hy
    have hyW := hαW hy
    rw [hWs] at hyW
    exact Y.basicOpen_le s hyW
  refine ⟨d, fun j => ?_⟩
  exact idealOfSpecSheaf_comap_monomial_factor (A := A)
    (ι := {i : F.ι // x ∈ (F.component i).support}) (B j) (fun i => F.component i.1)
    U (fun i => v (c i)) (d j) hc (hB j) α hαU (fun i => vA (cA i)) hFA

variable [Algebra k A] [Algebra R A] [IsScalarTower k R A]

/-- The actual contained leaf has simultaneous factor monomials in exactly the same actual
etale coordinates as its boundary, total-transform and literal unit-monomial Jacobian. -/
theorem exists_family_leaf_coordinates_jacobian_monomials [IsDomain A]
    (π : Y ⟶ Spec (.of R)) (α : Spec (.of A) ⟶ Y) [IsOpenImmersion α]
    (hπ : α ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (J : (Spec (.of R)).IdealSheafData) (F : Scheme.DivisorFamily Y) (n : ℕ)
    (B : κ → Y.IdealSheafData) (x : Y) (W : Y.affineOpens)
    (hW : SNCFamilyJacobianNeighbourhood (k := k) π F n J B x W)
    (hαW : Set.range α ⊆ (W.1 : Set Y))
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    ∃ (v : Fin n → A) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
      (c : {i : F.ι // x ∈ (F.component i).support} → Fin n),
      Function.Injective c ∧
      (∀ i, idealOfSpecSheaf ((F.component i.1).comap α) = span {v (c i)}) ∧
      ∃ (d : κ → {i : F.ι // x ∈ (F.component i).support} → ℕ)
        (e a : {i : F.ι // x ∈ (F.component i).support} → ℕ) (u : Aˣ),
        (∀ j, idealOfSpecSheaf ((B j).comap α) = span {∏ i, v (c i) ^ d j i}) ∧
        idealOfSpecSheaf (J.comap (Spec.map (CommRingCat.ofHom (algebraMap R A)))) =
          span {∏ i, v (c i) ^ e i} ∧
        etaleJacobian v hv (fun i => algebraMap R A (z i)) =
          (u : A) * ∏ i, v (c i) ^ a i := by
  have hSN := SNCFamilyJacobianNeighbourhood.toSNCJacobianNeighbourhood π F n J B x W hW
  obtain ⟨vA, hvA, cA, hcinjA, hFA, eA, aA, u, hJA, hJacA⟩ :=
    exists_leaf_coordinates_jacobian_monomial π α hπ J F n x W hSN hαW z hz
  obtain ⟨d, hd⟩ := exists_family_factor_monomials_in_leaf_coordinates
    π α J F n B x W hW hαW vA cA hFA
  exact ⟨vA, hvA, cA, hcinjA, hFA, d, eA, aA, u, hd, hJA, hJacA⟩

end EnvelopeProperty.Char0
