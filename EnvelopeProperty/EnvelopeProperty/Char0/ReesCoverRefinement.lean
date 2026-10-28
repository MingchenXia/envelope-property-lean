/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.FinitePrincipalRefinement

/-!
# Refining actual realized Rees trees by geometric neighborhoods

Existing nodes are retained; each old leaf is replaced by a finite unit-generating
principal Rees node. All maps are actual open immersions with actual root triangles.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory
open scoped Classical

universe u

variable {B K : Type u} [CommRing B] [Field K] [Algebra B K]

/-- Replace every old leaf by actual principal Rees charts subordinate to an actual open
cover. The original nodes, root triangles, and all old image points are retained. -/
theorem exists_rees_cover_refinement {X Y : Scheme.{u}} (π : Y ⟶ X)
    {ι : Type*} (U : ι → Y.Opens) (hcover : ∀ y : Y, ∃ j, y ∈ U j)
    {C : Subalgebra B K} (T : ReesChartTree B K C) :
    ∀ (p : Spec (.of C) ⟶ X)
      (f : (i : T.LeafIndex) → Spec (.of (T.leafAlgebra i)) ⟶ Y),
      (∀ i, IsOpenImmersion (f i)) →
      (∀ i, f i ≫ π =
        subalgebraSpecMap (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i)) ≫ p) →
      ∃ (T' : ReesChartTree B K C)
        (f' : (i : T'.LeafIndex) → Spec (.of (T'.leafAlgebra i)) ⟶ Y),
        (∀ i, IsOpenImmersion (f' i)) ∧
        (∀ i, f' i ≫ π =
          subalgebraSpecMap (T'.root_le_of_mem_leaves (T'.leafAlgebra_mem_leaves i)) ≫ p) ∧
        (∀ (i : T.LeafIndex) (x : Spec (.of (T.leafAlgebra i))),
          ∃ (j : T'.LeafIndex) (z : Spec (.of (T'.leafAlgebra j))), f' j z = f i x) ∧
        (∀ i : T'.LeafIndex, ∃ j, Set.range (f' i) ⊆ (U j).1) := by
  induction T with
  | leaf C =>
    intro p f hopen htriangle
    change (PUnit.{u + 1} → (Spec (.of C) ⟶ Y)) at f
    change (∀ i : PUnit.{u + 1}, IsOpenImmersion (f i)) at hopen
    change (∀ i : PUnit.{u + 1}, f i ≫ π = subalgebraSpecMap (le_refl C) ≫ p) at htriangle
    let V : ι → (Spec (.of C)).Opens := fun j => f PUnit.unit ⁻¹ᵁ U j
    obtain ⟨n, g, hg, hg0, hsub⟩ :=
      exists_finite_principal_rees_refinement C V (fun x => hcover (f PUnit.unit x))
    have ht : f PUnit.unit ≫ π = p := by
      simpa only [subalgebraSpecMap_refl, Category.id_comp] using htriangle PUnit.unit
    refine ⟨.node C n g hg0 (fun i => .leaf (reesTreeChart C g i)),
      fun ij => subalgebraSpecMap (le_reesTreeChart C g ij.1) ≫ f PUnit.unit,
      ?_, ?_, ?_, ?_⟩
    · rintro ⟨i, j⟩
      change IsOpenImmersion (subalgebraSpecMap (le_reesTreeChart C g i) ≫ f PUnit.unit)
      have := hopen PUnit.unit
      have := isOpenImmersion_principalReesChartMap C g hg i i.2
      infer_instance
    · rintro ⟨i, j⟩
      change (subalgebraSpecMap (le_reesTreeChart C g i) ≫ f PUnit.unit) ≫ π =
        subalgebraSpecMap (le_reesTreeChart C g i) ≫ p
      rw [Category.assoc, ht]
    · intro i x
      cases i
      obtain ⟨j, z, hz⟩ := exists_mem_principalReesChartMap C g hg x
      refine ⟨⟨j, PUnit.unit⟩, z, ?_⟩
      change (subalgebraSpecMap (le_reesTreeChart C g j) ≫ f PUnit.unit) z = f PUnit.unit x
      rw [Scheme.Hom.comp_apply, hz]
    · intro ij
      obtain ⟨j, hj⟩ := hsub ij.1
      refine ⟨j, ?_⟩
      rintro y ⟨z, rfl⟩
      change f PUnit.unit (subalgebraSpecMap (le_reesTreeChart C g ij.1) z) ∈ U j
      exact hj ⟨z, rfl⟩
  | node C n g hg child ih =>
    intro p f hopen htriangle
    have hchild := fun i : {i : Fin n // g i ≠ 0} =>
      ih i (subalgebraSpecMap (le_reesTreeChart C g i) ≫ p)
        (fun j => f ⟨i, j⟩) (fun j => hopen ⟨i, j⟩) (by
          intro j
          rw [← Category.assoc, subalgebraSpecMap_comp]
          exact htriangle ⟨i, j⟩)
    choose child' f' hopen' htriangle' hcover' hsub' using hchild
    refine ⟨.node C n g hg child', fun ij => f' ij.1 ij.2, ?_, ?_, ?_, ?_⟩
    · exact fun ij => hopen' ij.1 ij.2
    · intro ij
      change f' ij.1 ij.2 ≫ π = _
      rw [htriangle' ij.1 ij.2, ← Category.assoc, subalgebraSpecMap_comp]
      rfl
    · intro ij x
      obtain ⟨j, z, hz⟩ := hcover' ij.1 ij.2 x
      exact ⟨⟨ij.1, j⟩, z, hz⟩
    · exact fun ij => hsub' ij.1 ij.2

/-- A realized affine leaf cover remains an actual cover after subdivision, and its actual
leaf images are subordinate to the given geometric open cover. -/
theorem exists_rees_leaf_cover_subordinate {X Y : Scheme.{u}} (π : Y ⟶ X)
    {C : Subalgebra B K} (T : ReesChartTree B K C) (p : Spec (.of C) ⟶ X)
    (f : (i : T.LeafIndex) → Spec (.of (T.leafAlgebra i)) ⟶ Y)
    (hopen : ∀ i, IsOpenImmersion (f i))
    (htriangle : ∀ i, f i ≫ π =
      subalgebraSpecMap (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i)) ≫ p)
    (hcover : ∀ y : Y, ∃ (i : T.LeafIndex) (x : Spec (.of (T.leafAlgebra i))), f i x = y)
    {ι : Type*} (U : ι → Y.Opens) (hU : ∀ y : Y, ∃ j, y ∈ U j) :
    ∃ (T' : ReesChartTree B K C)
      (f' : (i : T'.LeafIndex) → Spec (.of (T'.leafAlgebra i)) ⟶ Y),
      (∀ i, IsOpenImmersion (f' i)) ∧
      (∀ i, f' i ≫ π =
        subalgebraSpecMap (T'.root_le_of_mem_leaves (T'.leafAlgebra_mem_leaves i)) ≫ p) ∧
      (∀ y : Y, ∃ (i : T'.LeafIndex) (x : Spec (.of (T'.leafAlgebra i))), f' i x = y) ∧
      (∀ i : T'.LeafIndex, ∃ j, Set.range (f' i) ⊆ (U j).1) := by
  obtain ⟨T', f', ho, ht, hc, hs⟩ := exists_rees_cover_refinement π U hU T p f hopen htriangle
  refine ⟨T', f', ho, ht, ?_, hs⟩
  intro y
  obtain ⟨i, x, hx⟩ := hcover y
  obtain ⟨j, z, hz⟩ := hc i x
  exact ⟨j, z, hz.trans hx⟩

/-- An actual blowup sequence has a finite actual Rees leaf cover subordinate to any actual
cover of its final scheme, while retaining the original base triangle. -/
theorem exists_actual_rees_cover_subordinate [IsNoetherianRing B]
    (C : Subalgebra B K) (hC : C.FG) (S : Scheme.BlowUpSequence (Spec (.of C)))
    (V : (Spec (.of C)).Opens) (hV : (V : Set (Spec (.of C))).Nonempty)
    [IsIso (S.composite ∣_ V)] {ι : Type*} (U : ι → S.last.Opens)
    (hU : ∀ y : S.last, ∃ j, y ∈ U j) :
    ∃ (T : ReesChartTree B K C)
      (f : (i : T.LeafIndex) → Spec (.of (T.leafAlgebra i)) ⟶ S.last),
      (∀ i, IsOpenImmersion (f i)) ∧
      (∀ i, f i ≫ S.composite =
        subalgebraSpecMap (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))) ∧
      (∀ y : S.last, ∃ (i : T.LeafIndex) (x : Spec (.of (T.leafAlgebra i))), f i x = y) ∧
      (∀ i : T.LeafIndex, ∃ j, Set.range (f i) ⊆ (U j).1) := by
  obtain ⟨T, f, ho, ht, hc⟩ := exists_actual_rees_cover C hC S V hV
  obtain ⟨T', f', ho', ht', hc', hs'⟩ := exists_rees_leaf_cover_subordinate
    S.composite T (𝟙 _) f ho (fun i => by simpa using ht i) hc U hU
  exact ⟨T', f', ho', fun i => by simpa using ht' i, hc', hs'⟩

end EnvelopeProperty.Char0
