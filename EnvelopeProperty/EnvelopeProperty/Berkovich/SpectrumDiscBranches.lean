/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumDiscMaps
import EnvelopeProperty.Berkovich.DiscPolynomialUnits

/-! # Whole original Gauss-disc branch sets and split-factorization cover -/
open scoped NNReal Polynomial Topology
open Polynomial Topology Set
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {K : Type*} [CommRing K] (v : Valuation K ℝ≥0)

private theorem val_C_self (x : RelativeSpectrum v K[X]) (a : K) : x.1.val (C a) = v a :=
  x.2 a

/-- The actual Gauss point of the ORIGINAL closed coordinate disc. -/
def discGaussPoint (r : ℝ≥0) : CoordinateDisc (A := K) v r :=
  ⟨gauss (self v) r, by rw [gauss_val_X]⟩

/-- An ORIGINAL strict translated disc inside the SAME closed coordinate disc. -/
def discBranch (r : ℝ≥0) (a : K) : Set (CoordinateDisc (A := K) v r) :=
  {x | x.1.1.val (X - C a) < r}

/-- Actual evaluation continuity makes every original branch open. -/
theorem isOpen_discBranch (r : ℝ≥0) (a : K) : IsOpen (discBranch v r a) :=
  isOpen_lt ((Spectrum.continuous_val_apply _).comp
    (continuous_subtype_val.comp continuous_subtype_val)) continuous_const

/-- The genuine original Gauss point never lies in an original strict branch. -/
theorem discGaussPoint_not_mem_discBranch (r : ℝ≥0) (a : K) :
    discGaussPoint v r ∉ discBranch v r a := by
  intro h
  have hb := le_gaussFun v r (X - C a) 1
  have he : (X - C a).coeff 1 = (1 : K) := by simp
  rw [he, map_one, one_mul, pow_one] at hb
  exact (not_lt_of_ge hb) h

/-- Every actual original branch lies in the genuine Gauss-punctured closed disc. -/
theorem discBranch_subset_compl_gauss (r : ℝ≥0) (a : K) :
    discBranch v r a ⊆ ({discGaussPoint v r} : Set (CoordinateDisc (A := K) v r))ᶜ := by
  intro x hx hgauss
  exact discGaussPoint_not_mem_discBranch v r a (Set.mem_singleton_iff.mp hgauss ▸ hx)

/-- The TRUE strict center inequality makes the original branches equal, over any valued commutative ring. -/
theorem discBranch_eq_of_val_sub_lt (r : ℝ≥0) {a b : K} (hab : v (a-b) < r) :
    discBranch v r a = discBranch v r b := by
  have hin (a b : K) (h : v (a-b) < r) : discBranch v r a ⊆ discBranch v r b := by
    intro x hx
    have he : (X - C b : K[X]) = (X - C a) + C (a-b) := by simp
    change x.1.1.val (X - C b) < r
    rw [he]
    apply (x.1.1.val.map_add _ _).trans_lt
    rw [val_C_self]
    exact max_lt hx h
  exact (hin a b hab).antisymm (hin b a (by
    rw [show b-a = -(a-b) by ring, v.map_neg]
    exact hab))

/-- A WHOLE point in both original strict branches forces the real original center inequality. -/
theorem val_sub_lt_of_mem_discBranch (r : ℝ≥0) {a b : K}
    {x : CoordinateDisc (A := K) v r} (ha : x ∈ discBranch v r a) (hb : x ∈ discBranch v r b) :
    v (a-b) < r := by
  have he : (C (a-b) : K[X]) = (X - C b) - (X - C a) := by simp
  have h : x.1.1.val (C (a-b)) < r := by
    rw [he]
    exact (x.1.1.val.map_sub _ _).trans_lt (max_lt hb ha)
  simpa only [val_C_self] using h

/-- Otherwise the ACTUAL original branches are disjoint. -/
theorem disjoint_discBranch_of_not_val_sub_lt (r : ℝ≥0) {a b : K} (hab : ¬ v (a-b) < r) :
    Disjoint (discBranch v r a) (discBranch v r b) := by
  apply Set.disjoint_left.mpr
  intro x ha hb
  exact hab (val_sub_lt_of_mem_discBranch v r ha hb)

section AlgebraicallyClosed
variable {F : Type*} [Field F] [IsAlgClosed F] {w : Valuation F ℝ≥0}

/-- ALL original linear values and the original prescribed coefficients determine the ENTIRE point. -/
theorem eq_of_linear_values {x y : RelativeSpectrum w F[X]}
    (h : ∀ a : F, x.1.val (X - C a) = y.1.val (X - C a)) : x = y := by
  apply ext_val
  intro p
  rw [(IsAlgClosed.splits p).eq_prod_roots]
  rw [map_mul, map_mul, val_C_self, val_C_self, map_multiset_prod, map_multiset_prod]
  congr 1
  rw [Multiset.map_map, Multiset.map_map]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro a _
  exact h a

/-- Split factorization DERIVES the original strict-branch cover of every whole non-Gauss point. -/
theorem exists_mem_discBranch_of_ne_gauss (r : ℝ≥0) (x : CoordinateDisc (A := F) w r)
    (hx : x ≠ discGaussPoint w r) : ∃ a : F, w a ≤ r ∧ x ∈ discBranch w r a := by
  by_contra hn
  apply hx
  apply Subtype.ext
  apply eq_of_linear_values
  intro a
  change x.1.1.val (X - C a) = gaussFun w r (X - C a)
  rw [gaussFun_X_sub_C]
  by_cases ha : w a ≤ r
  · rw [max_eq_left ha]
    apply le_antisymm
    · exact (x.1.1.val.map_sub _ _).trans (by rw [val_C_self]; exact max_le x.2 ha)
    · exact le_of_not_gt (fun h => hn ⟨a, ha, h⟩)
  · rw [max_eq_right (le_of_not_ge ha)]
    have hlt : x.1.1.val X < x.1.1.val (C a) := by
      rw [val_C_self]
      exact x.2.trans_lt (lt_of_not_ge ha)
    rw [x.1.1.val.map_sub_eq_of_lt_right hlt, val_C_self]

end AlgebraicallyClosed
end EnvelopeProperty.Berkovich.RelativeSpectrum
