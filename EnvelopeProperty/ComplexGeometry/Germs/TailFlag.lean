import EnvelopeProperty.ComplexGeometry.Germs.SmoothFlags
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.NestedFlattening

noncomputable section

namespace HolomorphicGerms

open Set
open scoped Manifold ContDiff
open ComplexGeometry.Pluripotential
open ComplexGeometry.Pluripotential.BlowupSequences
open ComplexGeometry.Pluripotential.RegularLocusDense
open ComplexGeometry.Pluripotential.RegularPatchNeighborhood
open ComplexGeometry.AnalyticGeometry

/-- Inside the actual larger coordinate plane, projection preserves exactly
the original smaller plane. -/
theorem coordinateProjection_mem_plane_iff {n k l : ℕ} (hkn : k ≤ n)
    {v : ComplexModel n} (hv : v ∈ complexCoordinatePlane n k) :
    coordinateProjection n k v ∈ complexCoordinatePlane k l ↔
      v ∈ complexCoordinatePlane n l := by
  constructor
  · intro h i hi
    by_cases hik : (i : ℕ) < k
    · have hi' := h (⟨i, hik⟩ : Fin k) hi
      simpa only [coordinateProjection_apply, dif_pos i.isLt] using hi'
    · exact hv i (not_lt.mp hik)
  · intro h i hi
    have hin : (i : ℕ) < n := lt_of_lt_of_le i.isLt hkn
    simpa only [coordinateProjection_apply, dif_pos hin] using h ⟨i, hin⟩ hi

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Main's genuine simultaneous flattening produces regularity of the actual
smaller carrier in the real flattened atlas of the larger submanifold. -/
theorem regularAtDim_subtype_of_nested {C N : Set X} {k l : ℕ}
    (hkn : k ≤ n) (hlk : l ≤ k)
    (hN : ∀ x ∈ N, RegularAtDim (n := n) N x k)
    (hC : ∀ x ∈ C, RegularAtDim (n := n) C x l) (hCN : C ⊆ N) :
    letI := SubmanifoldChartedSpace.chartedSpace hkn hN
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hkn hN
    ∀ x ∈ (Subtype.val ⁻¹' C : Set N),
      RegularAtDim (n := k) (Subtype.val ⁻¹' C : Set N) x l := by
  let := SubmanifoldChartedSpace.chartedSpace hkn hN
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hkn hN
  intro x hx
  obtain ⟨Φ, hΦt, hΦ0, hΦmem⟩ :=
    NestedFlattening.exists_nested_flattening hlk (hC x hx) (hN x x.property) hCN
  let F : SubmanifoldChartedSpace.FlatData n k X N := {
    amb := complexChartAt (n := n) (x : X)
    flat := Φ.toOpenPartialHomeomorph
    differentiableOn_flat := Φ.toFun_holomorphic
    differentiableOn_flat_symm := Φ.invFun_holomorphic
    flat_source_subset := hΦt
    mem_iff := fun y hy hyΦ => (hΦmem hy hyΦ).2
    base := x
    base_mem := x.property }
  let e : ComplexChart k N := ⟨F.chart hkn, ⟨F, rfl⟩⟩
  let ep := complexChartAt (n := k) x
  let T := chartTransition ep e
  have hxF : x ∈ e.val.source :=
    ⟨mem_complexChartAt_source (x : X), Φ.center_mem_source⟩
  have hxP : x ∈ ep.val.source := mem_complexChartAt_source x
  have he0 : e.val x = 0 := by
    change coordinateProjection n k (Φ.toFun ((complexChartAt (n := n) (x : X)).val x)) = 0
    rw [hΦ0, map_zero]
  have hTsource : T.source = ep.val.target ∩ ep.val.symm ⁻¹' e.val.source := rfl
  have hTp : ep.val x ∈ T.source := by
    rw [hTsource]
    refine ⟨ep.val.map_source hxP, ?_⟩
    change ep.val.symm (ep.val x) ∈ e.val.source
    rw [ep.val.left_inv hxP]
    exact hxF
  let Ψ : LocalHolomorphicEquivAt (n := k) (ep.val x) := {
    source := T.source
    target := T.target
    isOpen_source := T.open_source
    isOpen_target := T.open_target
    center_mem_source := hTp
    toFun := T
    invFun := T.symm
    toFun_holomorphic := differentiableOn_chartTransition ep e
    invFun_holomorphic := differentiableOn_chartTransition_symm ep e
    mapsTo_toFun := T.mapsTo
    mapsTo_invFun := T.symm.mapsTo
    left_inv := fun z hz => T.left_inv hz
    right_inv := fun z hz => T.right_inv hz }
  refine ⟨hlk, hx, Ψ, fun z hz => hz.1, ?_, ?_⟩
  · change e.val (ep.val.symm (ep.val x)) = 0
    rw [ep.val.left_inv hxP, he0]
  · intro y hy hyΨ
    have hyF : y ∈ e.val.source := by
      have h := hyΨ.2
      change ep.val.symm (ep.val y) ∈ e.val.source at h
      rwa [ep.val.left_inv hy] at h
    change (y : X) ∈ C ↔ T (ep.val y) ∈ complexCoordinatePlane k l
    change (y : X) ∈ C ↔ e.val (ep.val.symm (ep.val y)) ∈ complexCoordinatePlane k l
    rw [ep.val.left_inv hy]
    change (y : X) ∈ C ↔
      coordinateProjection n k (Φ.toFun ((complexChartAt (n := n) (x : X)).val y)) ∈
        complexCoordinatePlane k l
    have hmem := hΦmem hyF.1 hyF.2
    rw [coordinateProjection_mem_plane_iff hkn (hmem.2.mp y.property)]
    exact hmem.1

/-- Closedness and connectedness transfer through the genuine subtype topology;
the nested holomorphic flattening supplies the full submanifold assertion. -/
theorem isClosedConnectedSubmanifold_subtype_of_nested {C N : Set X} {k l : ℕ}
    (hN : IsClosedConnectedSubmanifold n N k)
    (hC : IsClosedConnectedSubmanifold n C l) (hCN : C ⊆ N) (hlk : l ≤ k) :
    letI := SubmanifoldChartedSpace.chartedSpace
      (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hN) hN.2.2
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
      (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hN) hN.2.2
    IsClosedConnectedSubmanifold k (Subtype.val ⁻¹' C : Set N) l := by
  let := SubmanifoldChartedSpace.chartedSpace
    (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hN) hN.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hN) hN.2.2
  refine ⟨hC.1.preimage continuous_subtype_val, ?_,
    regularAtDim_subtype_of_nested
      (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hN) hlk hN.2.2 hC.2.2 hCN⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hC.2.1.nonempty
    exact ⟨⟨x, hCN hx⟩, hx⟩
  · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have himage : Subtype.val '' (Subtype.val ⁻¹' C : Set N) = C := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hCN hx⟩, hx, rfl⟩
    rw [himage]
    exact hC.2.1.isPreconnected

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The actual source tail carriers, in the genuine first-level subtype. -/
def tailFlag (Y : Fin (m + 2) → Set M) :
    Fin (m + 1) → Set (Y (1 : Fin (m + 2))) :=
  fun i => Subtype.val ⁻¹' Y i.succ

/-- Every original tail is a smooth flag in the actual inherited complex
submanifold atlas, so recursive trace valuations have the genuine source domain. -/
theorem IsSmoothFlag.tail_isSmoothFlag {Y : Fin (m + 2) → Set M}
    (hY : IsSmoothFlag (n := m + 1) Y) :
    let hN : IsClosedConnectedSubmanifold (m + 1) (Y (1 : Fin (m + 2))) m :=
      by simpa using hY.2.2 (1 : Fin (m + 2))
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hN.2.2
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m) hN.2.2
    IsSmoothFlag (n := m) (tailFlag Y) := by
  have hN : IsClosedConnectedSubmanifold (m + 1) (Y (1 : Fin (m + 2))) m :=
    by simpa using hY.2.2 (1 : Fin (m + 2))
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hN.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m) hN.2.2
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp [tailFlag]
  · intro i j hij x hx
    exact hY.2.1 (Fin.succ_le_succ_iff.mpr hij) hx
  · intro i
    have hC : IsClosedConnectedSubmanifold (m + 1) (Y i.succ) (m - (i : ℕ)) :=
      by simpa using hY.2.2 i.succ
    have hCN : Y i.succ ⊆ Y (1 : Fin (m + 2)) := by
      apply hY.2.1
      change 1 ≤ (i : ℕ) + 1
      omega
    exact isClosedConnectedSubmanifold_subtype_of_nested hN hC hCN (Nat.sub_le m i)

end HolomorphicGerms
