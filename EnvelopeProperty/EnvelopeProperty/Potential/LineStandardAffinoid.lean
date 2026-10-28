import EnvelopeProperty.Potential.LineTopology

/-!
# Actual standard affinoids and their inflation paths

A standard affinoid is an actual closed outer disc with finitely many disjoint
open holes removed. Its carrier is compact and path connected. The paths retain
the original relative seminorm points and stay outside every open hole.
-/

open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {F : Type*} [CommRing F] (v : Valuation F ℝ≥0)

private theorem fc_component_closure_meets_closed_of_path
    {X : Type*} [TopologicalSpace X] {U B : Set X} (hB : IsClosed B)
    {x y : X} (hx : x ∈ U \ B) (hy : y ∈ B) (p : Path x y) (hp : ∀ t, p t ∈ U) :
    ∃ z ∈ B, z ∈ closure (connectedComponentIn (U \ B) x) := by
  have hc : IsClosed (p ⁻¹' B) := hB.preimage p.continuous
  have hne : (p ⁻¹' B).Nonempty := ⟨1,by simpa using hy⟩
  obtain ⟨t,htB,hmin⟩ := hc.isCompact.exists_isLeast hne
  have htne : t ≠ 0 := by
    intro h
    apply hx.2
    have hb := htB
    rw [h] at hb
    simpa using hb
  have ht0 : (0 : unitInterval) < t := lt_of_le_of_ne bot_le htne.symm
  have hsub : p '' Set.Iio t ⊆ U \ B := by
    rintro z ⟨s,hs,rfl⟩
    refine ⟨hp s,?_⟩
    intro hsb
    exact not_le_of_gt hs (hmin hsb)
  have hcomp : p '' Set.Iio t ⊆ connectedComponentIn (U \ B) x :=
    (isPreconnected_Iio.image p p.continuous.continuousOn).subset_connectedComponentIn
      ⟨0,ht0,p.source⟩ hsub
  have htcl : t ∈ closure (Set.Iio t) := by
    rw [closure_Iio' (show (Set.Iio t).Nonempty from ⟨0,ht0⟩)]
    exact (le_rfl : t ≤ t)
  exact ⟨p t,htB,closure_mono hcomp (mem_closure_image p.continuous.continuousAt htcl)⟩

/-- The literal disc-with-open-holes definition of a standard line affinoid. -/
structure FCStandardAffinoid (m : ℕ) where
  center : F
  radius : ℝ≥0
  holeCenter : Fin m → F
  holeRadius : Fin m → ℝ≥0
  holeRadius_pos : ∀ j, 0 < holeRadius j
  holeRadius_le : ∀ j, holeRadius j ≤ radius
  holeCenter_le : ∀ j, v (holeCenter j-center) ≤ radius
  holes_disjoint : Pairwise fun i j => Disjoint
    {x : RelativeSpectrum v F[X] | val x (X-C (holeCenter i)) < holeRadius i}
    {x : RelativeSpectrum v F[X] | val x (X-C (holeCenter j)) < holeRadius j}

namespace FCStandardAffinoid

variable {v} {m : ℕ} (U : FCStandardAffinoid v m)

/-- A genuine closed disc, including radius zero, is a standard affinoid without holes. -/
def ofDisc (a : F) (r : ℝ≥0) : FCStandardAffinoid v 0 where
  center := a
  radius := r
  holeCenter := Fin.elim0
  holeRadius := Fin.elim0
  holeRadius_pos := fun j => Fin.elim0 j
  holeRadius_le := fun j => Fin.elim0 j
  holeCenter_le := fun j => Fin.elim0 j
  holes_disjoint := fun i => Fin.elim0 i

/-- The actual affinoid locus, as a subset of the original analytic line. -/
def carrier : Set (RelativeSpectrum v F[X]) :=
  {x | val x (X-C U.center) ≤ U.radius ∧
    ∀ j, U.holeRadius j ≤ val x (X-C (U.holeCenter j))}

/-- The original Gauss point on the outer boundary. -/
def outerGauss : RelativeSpectrum v F[X] :=
  centeredGauss (self v) U.center U.radius

/-- The finite boundary specified in the paper. -/
def boundary : Set (RelativeSpectrum v F[X]) :=
  insert U.outerGauss (Set.range fun j => centeredGauss (self v) (U.holeCenter j) (U.holeRadius j))

theorem outerGauss_mem : U.outerGauss ∈ U.carrier := by
  constructor
  · simp [outerGauss, fc_centeredGauss_val_X_sub_C]
  · intro j
    exact (U.holeRadius_le j).trans (by
      rw [outerGauss, fc_centeredGauss_val_X_sub_C]
      exact le_max_right _ _)

theorem carrier_nonempty : U.carrier.Nonempty := ⟨U.outerGauss, U.outerGauss_mem⟩

/-- Positive hole radii force a zero-radius outer disc to have no holes. -/
theorem no_holes_of_radius_zero (h : U.radius = 0) : m = 0 := by
  by_contra hm
  let j : Fin m := ⟨0,Nat.pos_of_ne_zero hm⟩
  have hj := (U.holeRadius_pos j).trans_le (U.holeRadius_le j)
  rw [h] at hj
  exact lt_irrefl _ hj

/-- Equal inner and outer radii give one and the same original Gauss boundary point. -/
theorem holeGauss_eq_outer_of_radius_eq (j : Fin m) (h : U.holeRadius j = U.radius) :
    centeredGauss (self v) (U.holeCenter j) (U.holeRadius j) = U.outerGauss := by
  rw [h]
  exact fc_centeredGauss_eq_of_center_dist_le _ _ _ (U.holeCenter_le j)

theorem holeGauss_mem (j : Fin m) :
    centeredGauss (self v) (U.holeCenter j) (U.holeRadius j) ∈ U.carrier := by
  constructor
  · rw [fc_centeredGauss_val_X_sub_C]
    exact max_le (U.holeCenter_le j) (U.holeRadius_le j)
  · intro i
    rw [fc_centeredGauss_val_X_sub_C]
    by_cases hij : i = j
    · subst i
      simp
    · apply le_of_not_gt
      intro hbad
      let z := centeredGauss (self v) (U.holeCenter j) 0
      have hi : z ∈ {x : RelativeSpectrum v F[X] |
          val x (X-C (U.holeCenter i)) < U.holeRadius i} := by
        change val z (X-C (U.holeCenter i)) < U.holeRadius i
        dsimp only [z]
        rw [fc_centeredGauss_val_X_sub_C]
        simpa only [max_zero] using (le_max_left _ _).trans_lt hbad
      have hj : z ∈ {x : RelativeSpectrum v F[X] |
          val x (X-C (U.holeCenter j)) < U.holeRadius j} := by
        simpa [z,fc_centeredGauss_val_X_sub_C] using U.holeRadius_pos j
      exact Set.disjoint_left.mp (U.holes_disjoint hij) hi hj

theorem boundary_subset : U.boundary ⊆ U.carrier := by
  intro x hx
  rcases Set.mem_insert_iff.mp hx with h | h
  · exact h ▸ U.outerGauss_mem
  · obtain ⟨j,rfl⟩ := h
    exact U.holeGauss_mem j

theorem finite_boundary : U.boundary.Finite := (Set.finite_range _).insert _

theorem isClosed_carrier : IsClosed U.carrier := by
  have h : IsClosed ({x : RelativeSpectrum v F[X] | val x (X-C U.center) ≤ U.radius} ∩
      ⋂ j, {x | U.holeRadius j ≤ val x (X-C (U.holeCenter j))}) :=
    (isClosed_le (continuous_val_apply _) continuous_const).inter
      (isClosed_iInter fun j => isClosed_le continuous_const (continuous_val_apply _))
  convert h using 1
  ext x
  simp only [carrier, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]

theorem isCompact_carrier : IsCompact U.carrier :=
  (fc_isCompact_closedDisc U.center U.radius).of_isClosed_subset U.isClosed_carrier
    (fun _ hx => hx.1)

/-- Inflation preserves the entire actual outer disc and every open-hole complement. -/
theorem inflation_mem {x : RelativeSpectrum v F[X]} (hx : x ∈ U.carrier)
    {s : ℝ≥0} (hs : s ≤ U.radius) : fcCenteredInflation U.center x s ∈ U.carrier := by
  constructor
  · rw [fcCenteredInflation_val_X_sub_C]
    exact max_le hx.1 hs
  · intro j
    rw [fcCenteredInflation_val_X_sub_C]
    exact (hx.2 j).trans (le_max_left _ _)

/-- The actual radius path from any affinoid point to the original outer Gauss point. -/
def pathToOuter (x : U.carrier) : Path x.1 U.outerGauss where
  toFun t := fcCenteredInflation U.center x.1 (U.radius * Real.toNNReal (t : ℝ))
  continuous_toFun := (continuous_fcCenteredInflation U.center x.1).comp (by fun_prop)
  source' := by simp
  target' := by
    simpa only [show ((1 : unitInterval) : ℝ) = 1 from rfl,
      Real.toNNReal_one, mul_one, outerGauss] using
      fcCenteredInflation_eq_gauss U.center x.1 U.radius x.2.1

theorem pathToOuter_mem (x : U.carrier) (t : unitInterval) :
    U.pathToOuter x t ∈ U.carrier := by
  apply U.inflation_mem x.2
  have ht : Real.toNNReal (t : ℝ) ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal (t : ℝ) t.2.1]
    exact t.2.2
  exact (mul_le_mul_of_nonneg_left ht (show 0 ≤ U.radius from zero_le)).trans_eq (mul_one _)

theorem joinedIn_outer {x : RelativeSpectrum v F[X]} (hx : x ∈ U.carrier) :
    JoinedIn U.carrier x U.outerGauss :=
  ⟨U.pathToOuter ⟨x,hx⟩, U.pathToOuter_mem ⟨x,hx⟩⟩

theorem isPathConnected_carrier : IsPathConnected U.carrier :=
  ⟨U.outerGauss, U.outerGauss_mem, fun _ hx => (U.joinedIn_outer hx).symm⟩

theorem isConnected_carrier : IsConnected U.carrier := U.isPathConnected_carrier.isConnected

/-- Each actual component of the affinoid with its finite Gauss boundary removed approaches a boundary point. -/
theorem exists_boundary_mem_closure_component {x : RelativeSpectrum v F[X]}
    (hx : x ∈ U.carrier \ U.boundary) :
    ∃ z ∈ U.boundary, z ∈ closure (connectedComponentIn (U.carrier \ U.boundary) x) := by
  have hy : U.outerGauss ∈ U.boundary := Set.mem_insert _ _
  exact fc_component_closure_meets_closed_of_path U.finite_boundary.isClosed hx hy
    (U.pathToOuter ⟨x,hx.1⟩) (U.pathToOuter_mem ⟨x,hx.1⟩)

end FCStandardAffinoid

namespace FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
variable {m : ℕ} (U : FCStandardAffinoid w m)

/-- The whole topological interior removes exactly the finite original Gauss boundary. -/
theorem interior_carrier : interior U.carrier = U.carrier \ U.boundary := by
  have he : U.carrier =
      {x : RelativeSpectrum w K[X] | val x (X-C U.center) ≤ U.radius} ∩
        ⋂ j, {x | U.holeRadius j ≤ val x (X-C (U.holeCenter j))} := by
    ext x
    simp only [carrier, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  have hh : ∀ j : Fin m,
      interior {x : RelativeSpectrum w K[X] | U.holeRadius j ≤ val x (X-C (U.holeCenter j))} =
        {x | U.holeRadius j ≤ val x (X-C (U.holeCenter j))} \
          {centeredGauss (self w) (U.holeCenter j) (U.holeRadius j)} :=
    fun j => fc_interior_discExterior (w := w) (U.holeCenter j) (U.holeRadius j)
      (U.holeRadius_pos j)
  have hD := fc_interior_closedDisc (w := w) U.center U.radius
  rw [he, interior_inter, interior_iInter_of_finite, hD]
  simp_rw [hh]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_iInter, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, boundary, outerGauss, Set.mem_insert_iff, Set.mem_range]
  constructor
  · rintro ⟨⟨hD,hnD⟩,hholes⟩
    refine ⟨⟨hD,fun j => (hholes j).1⟩,?_⟩
    rintro (h | ⟨j,h⟩)
    · exact hnD h
    · exact (hholes j).2 h.symm
  · rintro ⟨⟨hD,hholes⟩,hnb⟩
    exact ⟨⟨hD,fun h => hnb (Or.inl h)⟩,
      fun j => ⟨hholes j,fun h => hnb (Or.inr ⟨j,h.symm⟩)⟩⟩

/-- The finite Gauss boundary is the actual topological frontier of the affinoid. -/
theorem frontier_carrier : frontier U.carrier = U.boundary := by
  rw [frontier, U.isClosed_carrier.closure_eq, U.interior_carrier]
  ext x
  simp only [Set.mem_sdiff]
  constructor
  · rintro ⟨hU,h⟩
    by_contra hB
    exact h ⟨hU,hB⟩
  · intro hx
    exact ⟨U.boundary_subset hx, fun h => h.2 hx⟩

end FCStandardAffinoid

variable {v}

/-- The already constructed whole polynomial contraction joins every two actual line points. -/
theorem fc_joinedIn_line (x y : RelativeSpectrum v F[X]) :
    JoinedIn Set.univ x y := by
  let _ := contractibleSpace_affineLine v
  exact joinedIn_univ.mpr (PathConnectedSpace.joined x y)

theorem fc_isPathConnected_line : IsPathConnected (Set.univ : Set (RelativeSpectrum v F[X])) :=
  ⟨gauss (self v) 0, Set.mem_univ _, fun _ _ => fc_joinedIn_line _ _⟩

theorem fc_isConnected_line : IsConnected (Set.univ : Set (RelativeSpectrum v F[X])) :=
  fc_isPathConnected_line.isConnected

end EnvelopeProperty.Berkovich.RelativeSpectrum
