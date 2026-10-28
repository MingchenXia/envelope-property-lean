/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.PrincipalReesCover

/-!
# Finite actual principal refinements of open covers

Compactness selects finitely many original ring functions whose basic opens
refine a given actual open cover and generate the unit ideal. Their Rees charts
are actual principal refinement nodes inside the original fraction field.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory
open scoped Classical

universe u

/-- Compactness produces a finite principal refinement of an actual open cover, and the actual
covering property forces the chosen original ring functions to generate the unit ideal. -/
theorem exists_finite_principal_refinement {R : Type u} [CommRing R]
    {ι : Type*} (U : ι → TopologicalSpace.Opens (PrimeSpectrum R))
    (hcover : ∀ x : PrimeSpectrum R, ∃ i, x ∈ U i) :
    ∃ (n : ℕ) (g : Fin n → R), Ideal.span (Set.range g) = ⊤ ∧
      ∀ i, ∃ j, PrimeSpectrum.basicOpen (g i) ≤ U j := by
  have hlocal : ∀ x : PrimeSpectrum R, ∃ r : R, x ∈ PrimeSpectrum.basicOpen r ∧
      ∃ i, PrimeSpectrum.basicOpen r ≤ U i := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    obtain ⟨W, ⟨r, rfl⟩, hxr, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi (U i).2
    exact ⟨r, hxr, i, hsub⟩
  choose r hr j hj using hlocal
  have hcov : (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ x, (PrimeSpectrum.basicOpen (r x)).1 := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hr x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (PrimeSpectrum.basicOpen (r x)).1) (fun x => (PrimeSpectrum.basicOpen (r x)).2) hcov
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  let g : Fin (Fintype.card t) → R := fun i => r (e.symm i)
  have hgcover : ∀ x : PrimeSpectrum R, ∃ i, x ∈ PrimeSpectrum.basicOpen (g i) := by
    intro x
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
    obtain ⟨hpt, hxp⟩ := Set.mem_iUnion.mp hp
    refine ⟨e ⟨p, hpt⟩, ?_⟩
    change x ∈ PrimeSpectrum.basicOpen (r p) at hxp
    simpa only [g, Equiv.symm_apply_apply] using hxp
  have htop : (⨆ i, PrimeSpectrum.basicOpen (g i)) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := hgcover x
    exact (le_iSup (fun i => PrimeSpectrum.basicOpen (g i)) i) hi
  refine ⟨_, g, PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp htop, fun i => ?_⟩
  exact ⟨j (e.symm i), hj (e.symm i)⟩

variable {B K : Type u} [CommRing B] [Field K] [Algebra B K]

/-- The actual finite principal Rees node refines the supplied actual open cover. -/
theorem exists_finite_principal_rees_refinement (C : Subalgebra B K)
    {ι : Type*} (U : ι → (Spec (.of C)).Opens)
    (hcover : ∀ x : Spec (.of C), ∃ i, x ∈ U i) :
    ∃ (n : ℕ) (g : Fin n → C) (_hg : Ideal.span (Set.range g) = ⊤),
      (∃ i, g i ≠ 0) ∧
      ∀ i : {i : Fin n // g i ≠ 0}, ∃ j,
        Set.range (subalgebraSpecMap (le_reesTreeChart C g i)) ⊆ (U j).1 := by
  obtain ⟨n, g, hg, hsub⟩ := exists_finite_principal_refinement U hcover
  refine ⟨n, g, hg, exists_nonzero_of_span_eq_top C g hg, fun i => ?_⟩
  obtain ⟨j, hj⟩ := hsub i
  refine ⟨j, ?_⟩
  rw [range_principalReesChartMap C g hg i i.2]
  exact hj

end EnvelopeProperty.Char0
