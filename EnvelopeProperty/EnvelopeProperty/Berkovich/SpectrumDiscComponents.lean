/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumDiscBranches
import EnvelopeProperty.Berkovich.TranslatedFibreDiscs

/-! # Genuine translated branch contractions and actual connected components -/
open scoped Polynomial NNReal Topology
open Polynomial Topology Set
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {K : Type*} [CommRing K] (v : Valuation K ℝ≥0)

private theorem proj_eq_self (x : RelativeSpectrum v K[X]) : proj x = self v := by
  apply ext_val
  intro a
  exact x.2 a

private theorem coordinate_le_of_centered (r : ℝ≥0) (a : K) (ha : v a ≤ r)
    (x : CenteredFibreOpenDisc (self v) a r) : x.1.1.val X ≤ r := by
  have he : (X : K[X]) = (X - C a) + C a := by ring
  calc
    x.1.1.val X = x.1.1.val ((X - C a) + C a) := congrArg x.1.1.val he
    _ ≤ max (x.1.1.val (X - C a)) (x.1.1.val (C a)) := x.1.1.val.map_add _ _
    _ ≤ r := max_le x.2.2.le ((x.1.2 a).le.trans ha)

/-- True original coefficient/coordinate inequalities identify the SAME centered disc with its branch subtype. -/
def discBranchCenteredHomeomorph (r : ℝ≥0) (a : K) (ha : v a ≤ r) :
    CenteredFibreOpenDisc (self v) a r ≃ₜ discBranch v r a where
  toFun x := ⟨⟨x.1, coordinate_le_of_centered v r a ha x⟩, x.2.2⟩
  invFun x := ⟨x.1.1, proj_eq_self v x.1.1, x.2⟩
  left_inv _x := Subtype.ext rfl
  right_inv _x := Subtype.ext (Subtype.ext rfl)
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The actual polynomial translation gives a WHOLE original strict-disc chart of every genuine branch. -/
def discBranchHomeomorph (r : ℝ≥0) (a : K) (ha : v a ≤ r) :
    FibreOpenDisc (self v) r ≃ₜ discBranch v r a :=
  (FibreOpenDisc.centeredHomeomorph (self v) a r).trans (discBranchCenteredHomeomorph v r a ha)

/-- This SAME branch chart retains EVERY original polynomial value, not merely a chosen coordinate. -/
theorem discBranchHomeomorph_val_apply (r : ℝ≥0) (a : K) (ha : v a ≤ r)
    (x : FibreOpenDisc (self v) r) (p : K[X]) :
    (discBranchHomeomorph v r a ha x).1.1.1.val p =
      x.1.1.val (Polynomial.algEquivAevalXAddC a p) := rfl

/-- Every actual positive-radius original branch has a genuinely constructed contraction. -/
theorem contractibleSpace_discBranch (r : ℝ≥0) (hr : 0 < r) (a : K) (ha : v a ≤ r) :
    ContractibleSpace (discBranch v r a) := by
  let := CenteredFibreOpenDisc.contractibleSpace (self v) a r hr
  exact (discBranchCenteredHomeomorph v r a ha).symm.contractibleSpace

/-- In particular every genuine original branch is nonempty and connected. -/
theorem isConnected_discBranch (r : ℝ≥0) (hr : 0 < r) (a : K) (ha : v a ≤ r) :
    IsConnected (discBranch v r a) := by
  let := contractibleSpace_discBranch v r hr a ha
  exact isConnected_iff_connectedSpace.mpr inferInstance

/-- The original strict center inequality is EXACTLY equality of the actual nonempty branches. -/
theorem discBranch_eq_iff (r : ℝ≥0) (hr : 0 < r) {a b : K} (ha : v a ≤ r) :
    discBranch v r a = discBranch v r b ↔ v (a-b) < r := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := (isConnected_discBranch v r hr a ha).nonempty
    exact val_sub_lt_of_mem_discBranch v r hx (h ▸ hx)
  · exact discBranch_eq_of_val_sub_lt v r

section AlgebraicallyClosed
variable {F : Type*} [Field F] [IsAlgClosed F] (w : Valuation F ℝ≥0)

/-- Genuine open separation and actual connectedness identify the ORIGINAL connected component set. -/
theorem connectedComponentIn_compl_gauss_eq_discBranch (r : ℝ≥0) (hr : 0 < r) (a : F)
    (ha : w a ≤ r) (x : CoordinateDisc (A := F) w r) (hx : x ∈ discBranch w r a) :
    connectedComponentIn ({discGaussPoint w r}ᶜ : Set (CoordinateDisc (A := F) w r)) x =
      discBranch w r a := by
  let O : Set (CoordinateDisc (A := F) w r) :=
    ⋃ (b : F) (_hb : w b ≤ r) (_hab : ¬ w (a-b) < r), discBranch w r b
  have hO : IsOpen O := isOpen_iUnion fun b => isOpen_iUnion fun _ =>
    isOpen_iUnion fun _ => isOpen_discBranch w r b
  have hdis : Disjoint (discBranch w r a) O := by
    apply Set.disjoint_left.mpr
    intro y hya hyO
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hyO
    obtain ⟨_, hb⟩ := Set.mem_iUnion.mp hb
    obtain ⟨hab, hyb⟩ := Set.mem_iUnion.mp hb
    exact hab (val_sub_lt_of_mem_discBranch w r hya hyb)
  have hcover : ({discGaussPoint w r}ᶜ : Set (CoordinateDisc (A := F) w r)) ⊆
      discBranch w r a ∪ O := by
    intro y hy
    obtain ⟨b, hb, hyb⟩ := exists_mem_discBranch_of_ne_gauss r y (by simpa using hy)
    by_cases hab : w (a-b) < r
    · exact Or.inl ((discBranch_eq_of_val_sub_lt w r hab).symm ▸ hyb)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr
        ⟨hb, Set.mem_iUnion.mpr ⟨hab, hyb⟩⟩⟩)
  have hxp : x ∈ ({discGaussPoint w r}ᶜ : Set (CoordinateDisc (A := F) w r)) :=
    discBranch_subset_compl_gauss w r a hx
  apply Set.Subset.antisymm
  · exact IsPreconnected.subset_left_of_subset_union (isOpen_discBranch w r a) hO hdis
      ((connectedComponentIn_subset _ _).trans hcover)
      ⟨x, mem_connectedComponentIn hxp, hx⟩ isPreconnected_connectedComponentIn
  · exact (isConnected_discBranch w r hr a ha).isPreconnected.subset_connectedComponentIn hx
      (discBranch_subset_compl_gauss w r a)

/-- Every WHOLE original non-Gauss point has an actual component equal to a genuinely constructed branch. -/
theorem exists_connectedComponentIn_eq_discBranch (r : ℝ≥0) (hr : 0 < r)
    (x : CoordinateDisc (A := F) w r) (hx : x ≠ discGaussPoint w r) :
    ∃ a : F, w a ≤ r ∧ connectedComponentIn ({discGaussPoint w r}ᶜ :
      Set (CoordinateDisc (A := F) w r)) x = discBranch w r a := by
  obtain ⟨a, ha, hxa⟩ := exists_mem_discBranch_of_ne_gauss r x hx
  exact ⟨a, ha, connectedComponentIn_compl_gauss_eq_discBranch w r hr a ha x hxa⟩

end AlgebraicallyClosed
end EnvelopeProperty.Berkovich.RelativeSpectrum
