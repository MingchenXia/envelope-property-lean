/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.FiniteType
import Mathlib.Data.Finset.Max

/-!
# Finite trees of affine blowup charts

An iterated blowup of a domain can be recorded by a finite tree of affine Rees charts inside
its fraction field. Every valuation ring containing the root contains a leaf: at each node,
choose a generator of maximal multiplicative value and all its coordinate ratios belong to
the valuation ring. This is the elementary covering argument in `PLAN-31C`, §1.2, needed to
use chart presentations of log resolutions in the characteristic-zero smooth-envelope proof.

The construction does not assume existence of log resolutions or any envelope theorem.
-/

noncomputable section

namespace EnvelopeProperty

universe u

variable {B K : Type u} [CommRing B] [Field K] [Algebra B K]

/-- The affine chart obtained by adjoining the ratios of a finite family in `C`. -/
def reesTreeChart (C : Subalgebra B K) {n : ℕ} (g : Fin n → C) (i : Fin n) :
    Subalgebra B K :=
  C ⊔ Algebra.adjoin B (Set.range fun j => (g j : K) / (g i : K))

/-- A chart contains its original algebra. -/
theorem le_reesTreeChart (C : Subalgebra B K) {n : ℕ} (g : Fin n → C) (i : Fin n) :
    C ≤ reesTreeChart C g i := le_sup_left

/-- The defining universal property of the chart algebra. -/
theorem reesTreeChart_le_iff (C D : Subalgebra B K) {n : ℕ} (g : Fin n → C) (i : Fin n) :
    reesTreeChart C g i ≤ D ↔ C ≤ D ∧ ∀ j, (g j : K) / (g i : K) ∈ D := by
  rw [reesTreeChart, sup_le_iff, Algebra.adjoin_le_iff, Set.range_subset_iff]
  rfl

/-- Adjoining the finitely many chart coordinates preserves finite generation. -/
theorem fg_reesTreeChart (C : Subalgebra B K) (hC : C.FG) {n : ℕ}
    (g : Fin n → C) (i : Fin n) : (reesTreeChart C g i).FG :=
  hC.sup (Subalgebra.fg_def.mpr ⟨_, Set.finite_range _, rfl⟩)

/-- The original algebra maps to each of its chart algebras by inclusion. -/
def reesTreeChartIncl (C : Subalgebra B K) {n : ℕ} (g : Fin n → C) (i : Fin n) :
    C →ₐ[B] reesTreeChart C g i :=
  Subalgebra.inclusion (le_reesTreeChart C g i)

/-- The coordinate `gⱼ/gᵢ`, as an element of the actual chart algebra. -/
def reesTreeChartRatio (C : Subalgebra B K) {n : ℕ} (g : Fin n → C) (i j : Fin n) :
    reesTreeChart C g i := by
  refine ⟨(g j : K) / (g i : K), ?_⟩
  exact (show Algebra.adjoin B (Set.range fun j => (g j : K) / (g i : K)) ≤
    reesTreeChart C g i from le_sup_right) (Algebra.subset_adjoin ⟨j, rfl⟩)

/-- The chart coordinates satisfy their original numerator-denominator relations. -/
theorem reesTreeChartIncl_mul_ratio (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (i j : Fin n) (hi : g i ≠ 0) :
    reesTreeChartIncl C g i (g i) * reesTreeChartRatio C g i j =
      reesTreeChartIncl C g i (g j) := by
  apply Subtype.ext
  change (g i : K) * ((g j : K) / (g i : K)) = (g j : K)
  have hiK : (g i : K) ≠ 0 := fun e => hi (Subtype.ext e)
  exact mul_div_cancel₀ _ hiK

/-- The centre ideal becomes principal on each nonempty affine blowup chart. -/
theorem reesTreeChart_map_span_eq (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (i : Fin n) (hi : g i ≠ 0) :
    (Ideal.span (Set.range g)).map (reesTreeChartIncl C g i).toRingHom =
      Ideal.span {reesTreeChartIncl C g i (g i)} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    change reesTreeChartIncl C g i (g j) ∈ Ideal.span {reesTreeChartIncl C g i (g i)}
    exact Ideal.mem_span_singleton.mpr
      ⟨reesTreeChartRatio C g i j, (reesTreeChartIncl_mul_ratio C g i j hi).symm⟩
  · refine Ideal.span_le.mpr ?_
    rintro _ (rfl : _ = _)
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)

/-- A nonzero finite family has a Rees chart contained in any valuation ring containing `C`. -/
theorem exists_reesTreeChart_le (C : Subalgebra B K) (V : ValuationSubring K)
    (hC : C.toSubring ≤ V.toSubring) {n : ℕ} (g : Fin n → C) (hg : ∃ i, g i ≠ 0) :
    ∃ i, g i ≠ 0 ∧ (reesTreeChart C g i).toSubring ≤ V.toSubring := by
  classical
  obtain ⟨j, hj⟩ := hg
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => V.valuation (g i : K)) ⟨j, Finset.mem_univ j⟩
  have hi0 : g i ≠ 0 := by
    intro h
    have hjK : (g j : K) ≠ 0 := fun e => hj (Subtype.ext e)
    have hpos := V.valuation.pos_iff.mpr hjK
    have hle := hi j (Finset.mem_univ j)
    simp only [h, ZeroMemClass.coe_zero, map_zero] at hle
    exact hpos.not_ge hle
  refine ⟨i, hi0, ?_⟩
  let V' : Subalgebra B K :=
    { V.toSubring with algebraMap_mem' := fun b => hC (C.algebraMap_mem b) }
  have hCV : C ≤ V' := hC
  have hratios : Algebra.adjoin B (Set.range fun j => (g j : K) / (g i : K)) ≤ V' := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨a, ha⟩ := (V.valuation_le_iff _ _).mp (hi j (Finset.mem_univ j))
    have hiK : (g i : K) ≠ 0 := fun e => hi0 (Subtype.ext e)
    change (g j : K) / (g i : K) ∈ V
    rw [← ha, mul_div_cancel_right₀ _ hiK]
    exact a.property
  exact sup_le hCV hratios

/-- A finite tree of affine Rees charts, omitting the charts with zero denominator. -/
inductive ReesChartTree (B K : Type u) [CommRing B] [Field K] [Algebra B K] :
    Subalgebra B K → Type u
  | leaf (C : Subalgebra B K) : ReesChartTree B K C
  | node (C : Subalgebra B K) (n : ℕ) (g : Fin n → C) (hg : ∃ i, g i ≠ 0)
      (child : (i : {i // g i ≠ 0}) → ReesChartTree B K (reesTreeChart C g i)) :
      ReesChartTree B K C

namespace ReesChartTree

/-- The leaf algebras of a finite chart tree. -/
def leaves {C : Subalgebra B K} : ReesChartTree B K C → Set (Subalgebra B K)
  | .leaf C => {C}
  | .node _ _ _ _ child => ⋃ i, (child i).leaves

/-- There are finitely many leaf algebras, even if different branches have the same leaf. -/
theorem finite_leaves {C : Subalgebra B K} (T : ReesChartTree B K C) : T.leaves.Finite := by
  induction T with
  | leaf C => exact Set.finite_singleton C
  | node C n g hg child ih => exact Set.finite_iUnion ih

/-- Every finite chart tree has a leaf. -/
theorem leaves_nonempty {C : Subalgebra B K} (T : ReesChartTree B K C) :
    T.leaves.Nonempty := by
  induction T with
  | leaf C => exact Set.singleton_nonempty C
  | node C n g hg child ih =>
    obtain ⟨i, hi⟩ := hg
    obtain ⟨D, hD⟩ := ih ⟨i, hi⟩
    exact ⟨D, Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hD⟩⟩

/-- Every leaf algebra contains the root algebra. -/
theorem root_le_of_mem_leaves {C : Subalgebra B K} (T : ReesChartTree B K C)
    {D : Subalgebra B K} (hD : D ∈ T.leaves) : C ≤ D := by
  induction T with
  | leaf C =>
    obtain rfl := Set.mem_singleton_iff.mp hD
    exact le_rfl
  | node C n g hg child ih =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hD
    exact (le_reesTreeChart C g i).trans (ih i hi)

/-- Every leaf of a tree rooted at a finitely generated algebra is finitely generated. -/
theorem fg_of_mem_leaves {C : Subalgebra B K} (T : ReesChartTree B K C) (hC : C.FG)
    {D : Subalgebra B K} (hD : D ∈ T.leaves) : D.FG := by
  induction T with
  | leaf C =>
    obtain rfl := Set.mem_singleton_iff.mp hD
    exact hC
  | node C n g hg child ih =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hD
    exact ih i (fg_reesTreeChart C hC g i) hi

/-- Finite-type roots have finite-type leaves. -/
theorem finiteType_of_mem_leaves {C : Subalgebra B K} (T : ReesChartTree B K C)
    [Algebra.FiniteType B C] {D : Subalgebra B K} (hD : D ∈ T.leaves) :
    Algebra.FiniteType B D :=
  D.fg_iff_finiteType.mp (T.fg_of_mem_leaves (C.fg_iff_finiteType.mpr inferInstance) hD)

/-- A valuation ring containing the root contains a leaf of the chart tree. -/
theorem exists_leaf_le {C : Subalgebra B K} (T : ReesChartTree B K C)
    (V : ValuationSubring K) (hC : C.toSubring ≤ V.toSubring) :
    ∃ D ∈ T.leaves, D.toSubring ≤ V.toSubring := by
  induction T with
  | leaf C => exact ⟨C, Set.mem_singleton C, hC⟩
  | node C n g hg child ih =>
    obtain ⟨i, hi, hchart⟩ := exists_reesTreeChart_le C V hC g hg
    obtain ⟨D, hD, hDV⟩ := ih ⟨i, hi⟩ hchart
    exact ⟨D, Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hD⟩, hDV⟩

end ReesChartTree

end EnvelopeProperty
