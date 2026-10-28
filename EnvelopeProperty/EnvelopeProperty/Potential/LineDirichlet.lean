import EnvelopeProperty.Potential.LineSkeleton
import EnvelopeProperty.Potential.LineHarmonic
import EnvelopeProperty.Potential.LineHarmonicMaximum
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Actual logarithmic Dirichlet interpolation at distinct Gauss boundary points -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

/-- The original Gauss point of a specified open hole. -/
def holeBoundaryPoint (j : Fin m) : RelativeSpectrum w K[X] :=
  centeredGauss (self w) (U.holeCenter j) (U.holeRadius j)

theorem holeBoundaryPoint_mem_boundary (j : Fin m) : U.holeBoundaryPoint j ∈ U.boundary :=
  Set.mem_insert_of_mem _ ⟨j,rfl⟩

/-- Actual disjoint open holes force the original centre-distance bound. -/
theorem holeRadius_le_center_distance (i j : Fin m) (hij : i ≠ j) :
    U.holeRadius j ≤ w (U.holeCenter i-U.holeCenter j) := by
  apply le_of_not_gt
  intro hbad
  let z := centeredGauss (self w) (U.holeCenter i) 0
  have hi : val z (X-C (U.holeCenter i)) < U.holeRadius i := by
    simpa [z,fc_centeredGauss_val_X_sub_C] using U.holeRadius_pos i
  have hj : val z (X-C (U.holeCenter j)) < U.holeRadius j := by
    simpa [z,fc_centeredGauss_val_X_sub_C] using hbad
  exact Set.disjoint_left.mp (U.holes_disjoint hij) hi hj

/-- Distinct original Gauss boundaries give a strict distance above the smaller radius. -/
theorem holeRadius_lt_center_distance_of_boundary_ne (i j : Fin m)
    (hij : U.holeBoundaryPoint i ≠ U.holeBoundaryPoint j)
    (hr : U.holeRadius i ≤ U.holeRadius j) :
    U.holeRadius i < w (U.holeCenter i-U.holeCenter j) := by
  have hne : i ≠ j := fun h => hij (congrArg U.holeBoundaryPoint h)
  have hd := U.holeRadius_le_center_distance i j hne
  apply lt_of_not_ge
  intro hbad
  have heq : U.holeRadius i = U.holeRadius j := le_antisymm hr (hd.trans hbad)
  apply hij
  change centeredGauss (self w) (U.holeCenter i) (U.holeRadius i) =
    centeredGauss (self w) (U.holeCenter j) (U.holeRadius j)
  rw [← heq]
  apply (fc_centeredGauss_eq_of_center_dist_le _ _ _ ?_).symm
  rwa [show U.holeCenter j-U.holeCenter i = -(U.holeCenter i-U.holeCenter j) by ring,
    Valuation.map_neg]

theorem holeRadius_lt_outer_of_boundary_ne (j : Fin m)
    (hj : U.holeBoundaryPoint j ≠ U.outerGauss) : U.holeRadius j < U.radius := by
  apply lt_of_le_of_ne (U.holeRadius_le j)
  intro h
  exact hj (U.holeGauss_eq_outer_of_radius_eq j h)

/-- The normalized original logarithmic coordinate, zero at the outer boundary. -/
def dirichletPotential (j : Fin m) (x : RelativeSpectrum w K[X]) : ℝ :=
  Real.log (U.radius : ℝ) - Real.log (val x (X-C (U.holeCenter j)) : ℝ)

theorem dirichletPotential_outer (j : Fin m) : U.dirichletPotential j U.outerGauss = 0 := by
  have hd : w (U.center-U.holeCenter j) ≤ U.radius := by
    rw [show U.center-U.holeCenter j = -(U.holeCenter j-U.center) by ring,Valuation.map_neg]
    exact U.holeCenter_le j
  simp only [dirichletPotential,outerGauss,fc_centeredGauss_val_X_sub_C,max_eq_right hd,sub_self]

/-- Distinct non-outer actual boundary points give independent logarithmic potentials. -/
theorem dirichletPotential_coefficients_eq_zero {ι : Type*} [Fintype ι]
    (j : ι → Fin m) (hj : Function.Injective fun i => U.holeBoundaryPoint (j i))
    (houter : ∀ i, U.holeBoundaryPoint (j i) ≠ U.outerGauss) (γ : ι → ℝ)
    (hzero : ∀ x ∈ U.carrier, ∑ i, γ i * U.dirichletPotential (j i) x = 0) : γ = 0 := by
  classical
  by_contra hγ
  let s := Finset.univ.filter fun i => γ i ≠ 0
  have hs : s.Nonempty := by
    by_contra hs
    apply hγ
    funext i
    by_contra hi
    exact hs ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  obtain ⟨i,hi,hmin⟩ := s.exists_min_image (fun k => U.holeRadius (j k)) hs
  let bounds : Finset ℝ≥0 := insert U.radius
    ((s.erase i).image fun k => w (U.holeCenter (j i)-U.holeCenter (j k)))
  have hb : bounds.Nonempty := Finset.insert_nonempty _ _
  let q := bounds.min' hb
  have hrq : U.holeRadius (j i) < q := by
    apply (Finset.lt_min'_iff bounds hb).mpr
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact U.holeRadius_lt_outer_of_boundary_ne (j i) (houter i)
    · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hr
      have hki := (Finset.mem_erase.mp hk).1
      exact U.holeRadius_lt_center_distance_of_boundary_ne (j i) (j k)
        (fun h => hki (hj h).symm) (hmin k (Finset.mem_erase.mp hk).2)
  obtain ⟨t,hit,htq⟩ := exists_between hrq
  have hqR : q ≤ U.radius := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have htR : t ≤ U.radius := htq.le.trans hqR
  have hdist (k : ι) (hk : k ∈ s) (hki : k ≠ i) :
      t < w (U.holeCenter (j i)-U.holeCenter (j k)) :=
    htq.trans_le (Finset.min'_le bounds _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hki,hk⟩))))
  let x₀ := U.holeBoundaryPoint (j i)
  let x₁ := centeredGauss (self w) (U.holeCenter (j i)) t
  have hx₀ : x₀ ∈ U.carrier := U.holeGauss_mem (j i)
  have hx₁ : x₁ ∈ U.carrier := U.radialSegment_mem (j i) t hit.le htR
  have hdif : (∑ k, γ k * (U.dirichletPotential (j k) x₁-U.dirichletPotential (j k) x₀)) =
      γ i * (Real.log (U.holeRadius (j i) : ℝ)-Real.log (t : ℝ)) := by
    rw [Finset.sum_eq_single i]
    · simp only [dirichletPotential,x₀,x₁,holeBoundaryPoint,fc_centeredGauss_val_X_sub_C,
        sub_self,map_zero,zero_max]
      ring
    · intro k _ hki
      by_cases hk0 : γ k = 0
      · rw [hk0,zero_mul]
      have hk : k ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk0⟩
      have hkt := hdist k hk hki
      have hkr := hit.trans hkt
      simp only [dirichletPotential,x₀,x₁,holeBoundaryPoint,fc_centeredGauss_val_X_sub_C,
        max_eq_left hkt.le,max_eq_left hkr.le,sub_self,mul_zero]
    · intro hi'
      exact False.elim (hi' (Finset.mem_univ _))
  have hsum : (∑ k, γ k * (U.dirichletPotential (j k) x₁-U.dirichletPotential (j k) x₀)) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,hzero x₁ hx₁,hzero x₀ hx₀,sub_self]
  rw [hdif] at hsum
  have hlog : Real.log (U.holeRadius (j i) : ℝ) < Real.log (t : ℝ) :=
    Real.log_lt_log (by exact_mod_cast U.holeRadius_pos (j i)) (by exact_mod_cast hit)
  exact (mul_ne_zero (Finset.mem_filter.mp hi).2 (sub_ne_zero.mpr hlog.ne)) hsum

/-- A finite combination of normalized actual hole potentials is literally harmonic. -/
theorem dirichletPotential_sum_isHarmonic {ι : Type*} [Fintype ι]
    (j : ι → Fin m) (c : ℝ) (γ : ι → ℝ) :
    U.IsHarmonic (fun x : U.carrier => c + ∑ i, γ i * U.dirichletPotential (j i) x.1) := by
  classical
  refine ⟨c + ∑ i, γ i * Real.log (U.radius : ℝ),
    (fun k => ∑ i, if j i = k then -γ i else 0),?_⟩
  intro x
  have hfib : (∑ k, (∑ i, if j i = k then -γ i else 0) *
      Real.log (val x.1 (X-C (U.holeCenter k)) : ℝ)) =
      - ∑ i, γ i * Real.log (val x.1 (X-C (U.holeCenter (j i))) : ℝ) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [ite_mul]
  unfold harmonicExpression dirichletPotential
  rw [hfib]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- Actual evaluation of the normalized hole potentials on the selected Gauss boundaries. -/
def dirichletEvaluationMap {ι : Type*} [Fintype ι] (j : ι → Fin m) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun γ i := ∑ k, γ k * U.dirichletPotential (j k) (U.holeBoundaryPoint (j i))
  map_add' γ δ := by
    ext i
    simp [add_mul,Finset.sum_add_distrib]
  map_smul' c γ := by
    ext i
    simp [smul_eq_mul,Finset.mul_sum,mul_assoc]

variable [IsAlgClosed K]

/-- The actual square boundary evaluation map is injective, by the proved weak maximum principle. -/
theorem dirichletEvaluationMap_injective {ι : Type*} [Fintype ι]
    (j : ι → Fin m) (hj : Function.Injective fun i => U.holeBoundaryPoint (j i))
    (houter : ∀ i, U.holeBoundaryPoint (j i) ≠ U.outerGauss)
    (hcover : ∀ z ∈ U.boundary, z = U.outerGauss ∨ ∃ i, z = U.holeBoundaryPoint (j i)) :
    Function.Injective (U.dirichletEvaluationMap j) := by
  have hker (γ : ι → ℝ) (hγ : U.dirichletEvaluationMap j γ = 0) : γ = 0 := by
    obtain ⟨c,δ,hδ⟩ := U.dirichletPotential_sum_isHarmonic j 0 γ
    have hδ' (x : RelativeSpectrum w K[X]) (hx : x ∈ U.carrier) :
        (∑ i, γ i * U.dirichletPotential (j i) x) = U.harmonicExpression c δ x := by
      simpa only [zero_add] using hδ ⟨x,hx⟩
    have hB : ∀ z ∈ U.boundary, U.harmonicExpression c δ z = 0 := by
      intro z hz
      rw [← hδ' z (U.boundary_subset hz)]
      rcases hcover z hz with rfl | ⟨i,rfl⟩
      · simp only [U.dirichletPotential_outer,mul_zero,Finset.sum_const_zero]
      · have hi := congrFun hγ i
        change (∑ k, γ k * U.dirichletPotential (j k) (U.holeBoundaryPoint (j i))) = 0 at hi
        exact hi
    apply U.dirichletPotential_coefficients_eq_zero j hj houter γ
    intro x hx
    rw [hδ' x hx]
    exact U.harmonicExpression_eq_zero_of_boundary_zero c δ hB hx
  intro γ δ h
  have hz : U.dirichletEvaluationMap j (γ-δ) = 0 := by rw [map_sub,h,sub_self]
  exact sub_eq_zero.mp (hker (γ-δ) hz)

/-- Finiteness turns the constructed injective actual evaluation map into a surjection. -/
theorem dirichletEvaluationMap_surjective {ι : Type*} [Fintype ι]
    (j : ι → Fin m) (hj : Function.Injective fun i => U.holeBoundaryPoint (j i))
    (houter : ∀ i, U.holeBoundaryPoint (j i) ≠ U.outerGauss)
    (hcover : ∀ z ∈ U.boundary, z = U.outerGauss ∨ ∃ i, z = U.holeBoundaryPoint (j i)) :
    Function.Surjective (U.dirichletEvaluationMap j) :=
  LinearMap.surjective_of_injective (U.dirichletEvaluationMap_injective j hj houter hcover)

/-- Every function on the actual finite Gauss boundary has a genuine harmonic extension. -/
theorem exists_isHarmonic_boundary_values (β : U.boundary → ℝ) :
    ∃ h : U.carrier → ℝ, U.IsHarmonic h ∧
      ∀ z : U.boundary, h ⟨z.1,U.boundary_subset z.2⟩ = β z := by
  classical
  let I := {z : RelativeSpectrum w K[X] // z ∈ U.boundary ∧ z ≠ U.outerGauss}
  have hfinite : {z : RelativeSpectrum w K[X] | z ∈ U.boundary ∧ z ≠ U.outerGauss}.Finite :=
    U.finite_boundary.subset fun _ hz => hz.1
  let : Fintype I := hfinite.fintype
  have hex (z : I) : ∃ j : Fin m, U.holeBoundaryPoint j = z.1 := by
    rcases Set.mem_insert_iff.mp z.2.1 with h | h
    · exact False.elim (z.2.2 h)
    · exact h
  choose j hj using hex
  have hjinj : Function.Injective fun i => U.holeBoundaryPoint (j i) := by
    intro i k h
    apply Subtype.ext
    exact (hj i).symm.trans (h.trans (hj k))
  have houter (i : I) : U.holeBoundaryPoint (j i) ≠ U.outerGauss :=
    fun h => i.2.2 ((hj i).symm.trans h)
  have hcover : ∀ z ∈ U.boundary, z = U.outerGauss ∨ ∃ i, z = U.holeBoundaryPoint (j i) := by
    intro z hz
    by_cases ho : z = U.outerGauss
    · exact Or.inl ho
    · exact Or.inr ⟨⟨z,hz,ho⟩,(hj ⟨z,hz,ho⟩).symm⟩
  let z₀ : U.boundary := ⟨U.outerGauss,Set.mem_insert _ _⟩
  let c := β z₀
  obtain ⟨γ,hγ⟩ := U.dirichletEvaluationMap_surjective j hjinj houter hcover
    (fun i : I => β ⟨i.1,i.2.1⟩-c)
  refine ⟨(fun x => c + ∑ i, γ i * U.dirichletPotential (j i) x.1),
    U.dirichletPotential_sum_isHarmonic j c γ,?_⟩
  intro z
  by_cases ho : z.1 = U.outerGauss
  · have hz₀ : z = z₀ := Subtype.ext ho
    rw [hz₀]
    simp only [z₀,U.dirichletPotential_outer,mul_zero,Finset.sum_const_zero,add_zero]
    rfl
  · let i : I := ⟨z.1,z.2,ho⟩
    have he := congrFun hγ i
    change (∑ k, γ k * U.dirichletPotential (j k) (U.holeBoundaryPoint (j i))) = β z-c at he
    rw [hj i] at he
    change (∑ k, γ k * U.dirichletPotential (j k) z.1) = β z-c at he
    linarith

/-- The Dirichlet solution is unique as an actual function, including coincident Gauss boundaries. -/
theorem existsUnique_isHarmonic_boundary_values (β : U.boundary → ℝ) :
    ∃! h : U.carrier → ℝ, U.IsHarmonic h ∧
      ∀ z : U.boundary, h ⟨z.1,U.boundary_subset z.2⟩ = β z := by
  obtain ⟨h,hh,hB⟩ := U.exists_isHarmonic_boundary_values β
  refine ⟨h,⟨hh,hB⟩,?_⟩
  intro k hk
  apply IsHarmonic.eq_of_boundary U hk.1 hh
  intro z hz
  exact (hk.2 ⟨z.1,hz⟩).trans (hB ⟨z.1,hz⟩).symm
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
