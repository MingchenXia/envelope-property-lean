/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.BlowUpOpenIso

/-!
# Realizing actual finite blowup sequences by Rees chart trees

Leaf occurrences retain the branch data even when two branches produce the same
subalgebra. This permits a literal finite affine covering of the final scheme.
-/

noncomputable section

namespace EnvelopeProperty

open AlgebraicGeometry CategoryTheory
open scoped Classical

universe u

variable {B K : Type u} [CommRing B] [Field K] [Algebra B K]

namespace ReesChartTree

/-- The occurrences of leaves, retaining branch indices even when algebras coincide. -/
def LeafIndex {C : Subalgebra B K} : ReesChartTree B K C → Type u
  | .leaf _ => PUnit
  | .node _ _ _ _ child => (i : _) × (child i).LeafIndex

/-- The actual subalgebra at a leaf occurrence. -/
def leafAlgebra {C : Subalgebra B K} : (T : ReesChartTree B K C) →
    T.LeafIndex → Subalgebra B K
  | .leaf C => fun _ => C
  | .node _ _ _ _ child => fun ij => (child ij.1).leafAlgebra ij.2

/-- There are finitely many leaf occurrences. -/
instance finite_leafIndex {C : Subalgebra B K} (T : ReesChartTree B K C) :
    Finite T.LeafIndex := by
  induction T with
  | leaf C => exact inferInstanceAs (Finite PUnit)
  | node C n g hg child ih => exact inferInstanceAs (Finite ((i : _) × (child i).LeafIndex))

/-- Every finite Rees tree has an actual leaf occurrence. -/
instance nonempty_leafIndex {C : Subalgebra B K} (T : ReesChartTree B K C) :
    Nonempty T.LeafIndex := by
  induction T with
  | leaf C => exact ⟨PUnit.unit⟩
  | node C n g hg child ih =>
    obtain ⟨i, hi⟩ := hg
    obtain ⟨j⟩ := ih ⟨i, hi⟩
    exact ⟨⟨⟨i, hi⟩, j⟩⟩

/-- Every occurrence's algebra is an actual leaf of the original set-valued tree. -/
theorem leafAlgebra_mem_leaves {C : Subalgebra B K} (T : ReesChartTree B K C)
    (i : T.LeafIndex) : T.leafAlgebra i ∈ T.leaves := by
  induction T with
  | leaf C => exact Set.mem_singleton C
  | node C n g hg child ih =>
    exact Set.mem_iUnion.mpr ⟨i.1, ih i.1 i.2⟩

/-- Conversely every leaf algebra comes from an actual leaf occurrence. -/
theorem exists_leafIndex_of_mem_leaves {C : Subalgebra B K} (T : ReesChartTree B K C)
    {D : Subalgebra B K} (hD : D ∈ T.leaves) : ∃ i : T.LeafIndex, T.leafAlgebra i = D := by
  induction T with
  | leaf C =>
    obtain rfl := Set.mem_singleton_iff.mp hD
    exact ⟨PUnit.unit, rfl⟩
  | node C n g hg child ih =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hD
    obtain ⟨j, hj⟩ := ih i hi
    exact ⟨⟨i, j⟩, hj⟩

end ReesChartTree

namespace Char0

/-- The actual spectrum map induced by an inclusion of subalgebras. -/
def subalgebraSpecMap {C D : Subalgebra B K} (h : C ≤ D) :
    Spec (.of D) ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)

/-- Reflexive inclusion induces the identity spectrum map. -/
theorem subalgebraSpecMap_refl (C : Subalgebra B K) :
    subalgebraSpecMap (le_refl C) = 𝟙 (Spec (.of C)) := by
  change Spec.map (𝟙 (.of C)) = _
  exact Spec.map_id _

/-- Inclusion-induced spectrum maps compose by transitivity of the inclusions. -/
theorem subalgebraSpecMap_comp {C D E : Subalgebra B K} (hCD : C ≤ D) (hDE : D ≤ E) :
    subalgebraSpecMap hDE ≫ subalgebraSpecMap hCD = subalgebraSpecMap (hCD.trans hDE) := by
  rw [subalgebraSpecMap, subalgebraSpecMap, ← Spec.map_comp]
  rfl

private theorem actualReesCoverAux [IsNoetherianRing B] (N : ℕ) :
    ∀ (C : Subalgebra B K), C.FG →
    ∀ (S : Scheme.BlowUpSequence (Spec (.of C))), S.length = N →
    ∀ (U : (Spec (.of C)).Opens), (U : Set (Spec (.of C))).Nonempty →
    IsIso (S.composite ∣_ U) →
    ∃ (T : ReesChartTree B K C)
      (f : (i : T.LeafIndex) → Spec (.of (T.leafAlgebra i)) ⟶ S.last),
      (∀ i, IsOpenImmersion (f i)) ∧
      (∀ i, f i ≫ S.composite =
        subalgebraSpecMap (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))) ∧
      (∀ x : S.last, ∃ (i : T.LeafIndex) (y : Spec (.of (T.leafAlgebra i))), f i y = x) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro C hC S hS U hU hIso
    cases S with
    | nil =>
      refine ⟨.leaf C, fun _ => 𝟙 _, ?_, ?_, ?_⟩
      · intro i
        change IsOpenImmersion (𝟙 (Spec (.of C)))
        infer_instance
      · intro i
        change 𝟙 (Spec (.of C)) ≫ 𝟙 _ = subalgebraSpecMap _
        rw [Category.id_comp, subalgebraSpecMap_refl]
      · exact fun x => ⟨PUnit.unit, x, rfl⟩
    | cons X J rest =>
      let _ : Algebra.FiniteType B C := C.fg_iff_finiteType.mp hC
      let _ : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing B C
      obtain ⟨x⟩ := nonempty_of_isIso_restrict
        (Scheme.BlowUpSequence.cons _ J rest).composite U hU
      obtain ⟨n, g, hg, hg0⟩ := exists_finite_generators_of_blowUp_point J (rest.composite x)
      have hchild : ∀ i : {i : Fin n // g i ≠ 0},
          ∃ (T : ReesChartTree B K (reesTreeChart C g i))
            (f : (j : T.LeafIndex) → Spec (.of (T.leafAlgebra j)) ⟶
              (rest.pullback (globalReesBlowUpChart C J g hg i i.2)).last),
            (∀ j, IsOpenImmersion (f j)) ∧
            (∀ j, f j ≫ (rest.pullback (globalReesBlowUpChart C J g hg i i.2)).composite =
              subalgebraSpecMap (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves j))) ∧
            (∀ y : (rest.pullback (globalReesBlowUpChart C J g hg i i.2)).last,
              ∃ (j : T.LeafIndex) (z : Spec (.of (T.leafAlgebra j))), f j z = y) := by
        intro i
        obtain ⟨V, hV, hV_iso⟩ :=
          exists_nonempty_isIso_restrict_rees_tail C J rest U hU g hg i i.2
        exact ih rest.length (by change rest.length + 1 = N at hS; omega)
          (reesTreeChart C g i) (fg_reesTreeChart C hC g i)
          (rest.pullback (globalReesBlowUpChart C J g hg i i.2))
          (length_pullback _ _) V hV hV_iso
      choose child f hopen htriangle hcover using hchild
      refine ⟨.node C n g hg0 child,
        fun ij => f ij.1 ij.2 ≫ rest.pullbackLastHom
          (globalReesBlowUpChart C J g hg ij.1 ij.1.2), ?_, ?_, ?_⟩
      · intro ij
        change IsOpenImmersion (f ij.1 ij.2 ≫ rest.pullbackLastHom
          (globalReesBlowUpChart C J g hg ij.1 ij.1.2))
        have := hopen ij.1 ij.2
        have := isOpenImmersion_pullbackLastHom rest
          (globalReesBlowUpChart C J g hg ij.1 ij.1.2)
        infer_instance
      · intro ij
        change (f ij.1 ij.2 ≫ rest.pullbackLastHom _) ≫ (rest.composite ≫ J.blowUpπ) = _
        rw [Category.assoc, (isPullback_pullbackLastHom rest
          (globalReesBlowUpChart C J g hg ij.1 ij.1.2)).w_assoc,
          ← Category.assoc, htriangle ij.1 ij.2]
        rw [globalReesBlowUpChart_π]
        exact subalgebraSpecMap_comp (le_reesTreeChart C g ij.1)
          ((child ij.1).root_le_of_mem_leaves ((child ij.1).leafAlgebra_mem_leaves ij.2))
      · intro y
        let 𝒰 := globalReesBlowUpOpenCover C J g hg
        let i : {i : Fin n // g i ≠ 0} := 𝒰.idx (rest.composite y)
        obtain ⟨q, hq⟩ := 𝒰.covers (rest.composite y)
        have hy : y ∈ Set.range (rest.pullbackLastHom
            (globalReesBlowUpChart C J g hg i i.2)) := by
          rw [range_pullbackLastHom]
          exact ⟨q, hq⟩
        obtain ⟨z, hz⟩ := hy
        obtain ⟨j, w, hw⟩ := hcover i z
        refine ⟨⟨i, j⟩, w, ?_⟩
        change (f i j ≫ rest.pullbackLastHom _) w = y
        rw [Scheme.Hom.comp_apply, hw, hz]

/-- Every actual finite blowup sequence, isomorphic over a nonempty open, has a finite Rees
tree whose literal leaf spectra form an actual affine open cover of the final scheme. -/
theorem exists_actual_rees_cover [IsNoetherianRing B] (C : Subalgebra B K) (hC : C.FG)
    (S : Scheme.BlowUpSequence (Spec (.of C))) (U : (Spec (.of C)).Opens)
    (hU : (U : Set (Spec (.of C))).Nonempty) [IsIso (S.composite ∣_ U)] :
    ∃ (T : ReesChartTree B K C)
      (f : (i : T.LeafIndex) → Spec (.of (T.leafAlgebra i)) ⟶ S.last),
      (∀ i, IsOpenImmersion (f i)) ∧
      (∀ i, f i ≫ S.composite =
        subalgebraSpecMap (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))) ∧
      (∀ x : S.last, ∃ (i : T.LeafIndex) (y : Spec (.of (T.leafAlgebra i))), f i y = x) :=
  actualReesCoverAux S.length C hC S rfl U hU inferInstance

/-- Package literal leaf spectra and their actual covering maps as an actual affine open cover. -/
def reesLeafAffineOpenCover {C : Subalgebra B K} (T : ReesChartTree B K C)
    {Y : Scheme.{u}} (f : (i : T.LeafIndex) → Spec (.of (T.leafAlgebra i)) ⟶ Y)
    (hopen : ∀ i, IsOpenImmersion (f i))
    (hcover : ∀ y : Y, ∃ (i : T.LeafIndex) (x : Spec (.of (T.leafAlgebra i))), f i x = y) :
    Y.AffineOpenCover where
  I₀ := T.LeafIndex
  X i := .of (T.leafAlgebra i)
  f := f
  map_prop := hopen
  idx y := (hcover y).choose
  covers y := (hcover y).choose_spec

/-- The resulting actual affine cover has finitely many charts. -/
instance finite_reesLeafAffineOpenCover_index {C : Subalgebra B K} (T : ReesChartTree B K C)
    {Y : Scheme.{u}} (f : (i : T.LeafIndex) → Spec (.of (T.leafAlgebra i)) ⟶ Y)
    (hopen : ∀ i, IsOpenImmersion (f i))
    (hcover : ∀ y : Y, ∃ (i : T.LeafIndex) (x : Spec (.of (T.leafAlgebra i))), f i x = y) :
    Finite (reesLeafAffineOpenCover T f hopen hcover).I₀ := by
  change Finite T.LeafIndex
  infer_instance

end Char0

end EnvelopeProperty
