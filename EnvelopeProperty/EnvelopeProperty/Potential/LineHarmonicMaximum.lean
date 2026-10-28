import EnvelopeProperty.Potential.LineHarmonic
import Mathlib.Topology.Connected.Clopen

/-!
# Actual harmonic boundary comparison

Compactness, connectedness and the derived all-point local maximum theorem
give the weak maximum principle on the original finite Gauss boundary.
-/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

/-- The whole maximum is achieved on the actual finite boundary, including coincident boundary points. -/
theorem harmonicExpression_exists_boundary_max (c : ℝ) (γ : Fin m → ℝ) :
    ∃ z ∈ U.boundary, ∀ x ∈ U.carrier,
      U.harmonicExpression c γ x ≤ U.harmonicExpression c γ z := by
  let _ : CompactSpace U.carrier := isCompact_iff_compactSpace.mp U.isCompact_carrier
  let _ : ConnectedSpace U.carrier := isConnected_iff_connectedSpace.mp U.isConnected_carrier
  let f : U.carrier → ℝ := fun x => U.harmonicExpression c γ x.1
  have hf : Continuous f := U.continuous_harmonicExpression c γ
  have hnonempty : (Set.univ : Set U.carrier).Nonempty :=
    ⟨⟨U.outerGauss,U.outerGauss_mem⟩,Set.mem_univ _⟩
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMaxOn hnonempty hf.continuousOn
  have hmax : ∀ y : U.carrier, f y ≤ f x := fun y => hx (Set.mem_univ y)
  by_cases hboundary : ∃ z : U.carrier, z.1 ∈ U.boundary ∧ f z = f x
  · obtain ⟨z,hzB,hz⟩ := hboundary
    refine ⟨z.1,hzB,?_⟩
    intro y hy
    exact (hmax ⟨y,hy⟩).trans_eq hz.symm
  · let M : Set U.carrier := {y | f y = f x}
    have hclosed : IsClosed M := isClosed_eq hf continuous_const
    have hopen : IsOpen M := by
      apply isOpen_iff_mem_nhds.mpr
      intro z hz
      change f z = f x at hz
      have hzB : z.1 ∉ U.boundary := fun hB => hboundary ⟨z,hB,hz⟩
      have hzInt : z.1 ∈ interior U.carrier := by
        rw [U.interior_carrier]
        exact ⟨z.2,hzB⟩
      have hU : ∀ᶠ y in 𝓝 z.1, y ∈ interior U.carrier :=
        isOpen_interior.mem_nhds hzInt
      have hlocal : IsLocalMax (U.harmonicExpression c γ) z.1 := hU.mono fun y hy => by
        exact (hmax ⟨y,interior_subset hy⟩).trans_eq hz.symm
      have he := U.harmonicExpression_eventually_eq_of_isLocalMax c γ z.1
        (fun j => U.holeCoordinate_pos z j) hlocal
      have hs : Tendsto (fun y : U.carrier => y.1) (𝓝 z) (𝓝 z.1) :=
        continuous_subtype_val.tendsto z
      exact (hs.eventually he).mono fun y hy => hy.trans hz
    have hMuniv : M = Set.univ := (show IsClopen M from ⟨hclosed,hopen⟩).eq_univ ⟨x,rfl⟩
    have houter : (⟨U.outerGauss,U.outerGauss_mem⟩ : U.carrier) ∈ M := by
      rw [hMuniv]
      exact Set.mem_univ _
    exact False.elim (hboundary ⟨⟨U.outerGauss,U.outerGauss_mem⟩,Set.mem_insert _ _,houter⟩)

theorem harmonicExpression_exists_boundary_ge (c : ℝ) (γ : Fin m → ℝ)
    {x : RelativeSpectrum w K[X]} (hx : x ∈ U.carrier) :
    ∃ z ∈ U.boundary, U.harmonicExpression c γ x ≤ U.harmonicExpression c γ z := by
  obtain ⟨z,hz,hmax⟩ := U.harmonicExpression_exists_boundary_max c γ
  exact ⟨z,hz,hmax x hx⟩

omit [IsAlgClosed K] in
theorem harmonicExpression_neg (c : ℝ) (γ : Fin m → ℝ) (x : RelativeSpectrum w K[X]) :
    U.harmonicExpression (-c) (fun j => -γ j) x = -U.harmonicExpression c γ x := by
  simp only [harmonicExpression,neg_mul,Finset.sum_neg_distrib,neg_add_rev]
  ring

omit [IsAlgClosed K] in
theorem harmonicExpression_sub (c d : ℝ) (γ δ : Fin m → ℝ) (x : RelativeSpectrum w K[X]) :
    U.harmonicExpression (c-d) (fun j => γ j-δ j) x =
      U.harmonicExpression c γ x-U.harmonicExpression d δ x := by
  simp only [harmonicExpression,sub_mul,Finset.sum_sub_distrib]
  ring

theorem harmonicExpression_eq_zero_of_boundary_zero (c : ℝ) (γ : Fin m → ℝ)
    (hB : ∀ z ∈ U.boundary, U.harmonicExpression c γ z = 0)
    {x : RelativeSpectrum w K[X]} (hx : x ∈ U.carrier) :
    U.harmonicExpression c γ x = 0 := by
  obtain ⟨z,hz,hupper⟩ := U.harmonicExpression_exists_boundary_ge c γ hx
  rw [hB z hz] at hupper
  obtain ⟨y,hy,hlower⟩ := U.harmonicExpression_exists_boundary_ge (-c) (fun j => -γ j) hx
  rw [U.harmonicExpression_neg,U.harmonicExpression_neg,hB y hy,neg_zero] at hlower
  exact le_antisymm hupper (neg_nonpos.mp hlower)

theorem harmonicExpression_eq_of_boundary_eq (c d : ℝ) (γ δ : Fin m → ℝ)
    (hB : ∀ z ∈ U.boundary, U.harmonicExpression c γ z = U.harmonicExpression d δ z)
    {x : RelativeSpectrum w K[X]} (hx : x ∈ U.carrier) :
    U.harmonicExpression c γ x = U.harmonicExpression d δ x := by
  have hz := U.harmonicExpression_eq_zero_of_boundary_zero (c-d) (fun j => γ j-δ j)
    (fun z hz => by rw [U.harmonicExpression_sub,hB z hz,sub_self]) hx
  rw [U.harmonicExpression_sub] at hz
  exact sub_eq_zero.mp hz

/-- Dirichlet uniqueness concerns the actual harmonic functions, not their coefficient witnesses. -/
theorem IsHarmonic.eq_of_boundary {h k : U.carrier → ℝ} (hh : U.IsHarmonic h)
    (hk : U.IsHarmonic k) (hB : ∀ z : U.carrier, z.1 ∈ U.boundary → h z = k z) : h = k := by
  obtain ⟨c,γ,hγ⟩ := hh
  obtain ⟨d,δ,hδ⟩ := hk
  funext x
  rw [hγ,hδ]
  apply U.harmonicExpression_eq_of_boundary_eq c d γ δ _ x.2
  intro z hz
  let q : U.carrier := ⟨z,U.boundary_subset hz⟩
  simpa only [hγ,hδ] using hB q hz

/-- The strong maximum propagates through the actual connected interior component, permitting touching boundary vertices. -/
theorem harmonicExpression_eq_on_interior_component (c : ℝ) (γ : Fin m → ℝ)
    (x : RelativeSpectrum w K[X]) (hx : x ∈ interior U.carrier)
    (hmax : ∀ y ∈ U.carrier, U.harmonicExpression c γ y ≤ U.harmonicExpression c γ x) :
    ∀ y ∈ connectedComponentIn (U.carrier \ U.boundary) x,
      U.harmonicExpression c γ y = U.harmonicExpression c γ x := by
  rw [← U.interior_carrier]
  let f : interior U.carrier → ℝ := fun z => U.harmonicExpression c γ z.1
  let toCarrier : interior U.carrier → U.carrier := fun z => ⟨z.1,interior_subset z.2⟩
  have hfU : ContinuousOn (U.harmonicExpression c γ) U.carrier :=
    continuousOn_iff_continuous_domRestrict.mpr (U.continuous_harmonicExpression c γ)
  have hf : Continuous f :=
    continuousOn_iff_continuous_domRestrict.mp (hfU.mono interior_subset)
  let M : Set (interior U.carrier) := {z | f z = U.harmonicExpression c γ x}
  have hclosed : IsClosed M := isClosed_eq hf continuous_const
  have hopen : IsOpen M := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    change f z = U.harmonicExpression c γ x at hz
    have hU : ∀ᶠ y in 𝓝 z.1, y ∈ interior U.carrier :=
      isOpen_interior.mem_nhds z.2
    have hlocal : IsLocalMax (U.harmonicExpression c γ) z.1 := hU.mono fun y hy => by
      exact (hmax y (interior_subset hy)).trans_eq hz.symm
    have he := U.harmonicExpression_eventually_eq_of_isLocalMax c γ z.1
      (fun j => U.holeCoordinate_pos (toCarrier z) j) hlocal
    have hs : Tendsto (fun y : interior U.carrier => y.1) (𝓝 z) (𝓝 z.1) :=
      continuous_subtype_val.tendsto z
    exact (hs.eventually he).mono fun y hy => hy.trans hz
  have hclopen : IsClopen M := ⟨hclosed,hopen⟩
  let C := connectedComponentIn (interior U.carrier) x
  have hC : IsPreconnected C := isPreconnected_connectedComponentIn
  let _ : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hC
  let embed : C → interior U.carrier :=
    fun z => ⟨z.1,connectedComponentIn_subset (interior U.carrier) x z.2⟩
  have hembed : Continuous embed := continuous_subtype_val.subtype_mk _
  have hrange : IsPreconnected (Set.range embed) := by
    simpa only [Set.image_univ] using isPreconnected_univ.image embed hembed.continuousOn
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hmeet : (Set.range embed ∩ M).Nonempty :=
    ⟨embed ⟨x,hxC⟩,⟨⟨x,hxC⟩,rfl⟩,rfl⟩
  have hsub : Set.range embed ⊆ M := hrange.subset_isClopen hclopen hmeet
  intro y hy
  exact hsub ⟨⟨y,hy⟩,rfl⟩

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
