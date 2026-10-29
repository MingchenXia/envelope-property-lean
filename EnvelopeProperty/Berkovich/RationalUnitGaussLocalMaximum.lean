/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.RationalUnitMaxima
import Mathlib.Topology.Order.LocalExtr

/-! # Genuine Gauss-vertex local constancy of original finite rational-unit maxima -/
open scoped NNReal ENNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.RationalUnitFamily
variable {K J ι : Type*} [Field K] [Fintype J] [IsAlgClosed K]
    (v : Valuation K ℝ≥0) (r : ℝ≥0) (hr : 0<r) (p q : J → K[X])
    (hp : ∀ j, p j≠0) (hq : ∀ j, q j≠0) (I : Finset ι) (hI : I.Nonempty)
    (c : ι → ℝ) (α : ι → J → ℝ)

include hr hp hq

/-- Actual original positive-length Gauss rays DERIVE each outgoing slope's nonpositivity from the SAME function's local maximum. -/
theorem maxSlope_nonpos_of_isLocalMax
    (hmax : IsLocalMax (maxValue v p q I hI c α) (gauss (self v) r))
    (d : Direction v r p q) : maxSlope v r p q I hI c α d≤0 := by
  have hN : ∀ᶠ x in 𝓝 (gauss (self v) r), x ∈ maxNeighborhood v r hr p q I hI c α :=
    (isOpen_maxNeighborhood v r hr p q I hI c α).mem_nhds
      (gauss_mem_maxNeighborhood v r hr p q I hI c α)
  have hE : ∀ᶠ x in 𝓝 (gauss (self v) r),
      x ∈ maxNeighborhood v r hr p q I hI c α ∧
        maxValue v p q I hI c α x ≤ maxValue v p q I hI c α (gauss (self v) r) :=
    hN.and hmax
  cases d with
  | none =>
    have hc : Continuous (fun t : ℝ≥0 => gauss (self v) t) :=
      continuous_gauss_prod.comp (continuous_const.prodMk continuous_id)
    have hEt := hc.continuousAt.eventually hE
    have hcl : r ∈ closure (Set.Ioi r) := by
      rw [closure_Ioi]
      change r≤r
      exact le_rfl
    obtain ⟨t, ht, htN, htm⟩ := ((mem_closure_iff_frequently.mp hcl).and_eventually hEt).exists
    have hval : (gauss (self v) t).1.val X=t := by rw [← val_apply,gauss_val_X]
    have he := maxValue_on_outer v r hr p q hp hq I hI c α (gauss (self v) t)
      (by rwa [hval]) htN
    rw [hval] at he
    have hlen : 0<Real.log (t : ℝ)-Real.log (r : ℝ) :=
      sub_pos.mpr (Real.log_lt_log (by exact_mod_cast hr) (by exact_mod_cast ht))
    nlinarith
  | some B =>
    obtain ⟨b,hb,hbB⟩ := (mem_rationalRootBranches_iff v r (numeratorProduct p) (numeratorProduct q) B.1).mp B.2
    have hvb := val_le_of_mem_insideRootCenters v r (numeratorProduct p) (numeratorProduct q) hb
    have hEr : ∀ᶠ x in 𝓝 (centeredGauss (self v) b r),
        x ∈ maxNeighborhood v r hr p q I hI c α ∧
          maxValue v p q I hI c α x ≤ maxValue v p q I hI c α (gauss (self v) r) := by
      rwa [centeredGauss_eq_gauss_of_val_le (self v) b r hvb]
    have hEt := (continuous_centeredGauss (self v) b).continuousAt.eventually hEr
    have hcl : r ∈ closure (Set.Ioo 0 r) := by
      rw [closure_Ioo hr.ne]
      exact ⟨hr.le,le_rfl⟩
    obtain ⟨t,⟨ht,htr⟩,htN,htm⟩ := ((mem_closure_iff_frequently.mp hcl).and_eventually hEt).exists
    let z := centeredDiscPoint v r b hvb t htr.le
    have hz : z ∈ discBranch v r b := centeredDiscPoint_mem_branch v r b hvb t htr.le htr
    have he := maxValue_on_listed_branch v r hr p q hp hq I hI c α b hb z hz htN
    have hd : centerDirection v r p q b hb=some B := by
      apply congrArg (fun C : ↥(branchFamily v r p q) => some C)
      exact Subtype.ext hbB
    have hval : z.1.1.val (X-C b)=t := by
      change (centeredGauss (self v) b t).1.val (X-C b)=t
      rw [← val_apply,centeredGauss_val_X_sub_C]
    rw [hd,hval] at he
    have hlen : 0<Real.log (r : ℝ)-Real.log (t : ℝ) :=
      sub_pos.mpr (Real.log_lt_log (by exact_mod_cast ht) (by exact_mod_cast htr))
    change maxValue v p q I hI c α z.1≤_ at htm
    nlinarith

/-- Genuine unit balancing and the DERIVED local-maximum signs force EVERY original outgoing slope to vanish. -/
theorem maxSlope_eq_zero_of_isLocalMax
    (hmax : IsLocalMax (maxValue v p q I hI c α) (gauss (self v) r))
    (d : Direction v r p q) : maxSlope v r p q I hI c α d=0 := by
  classical
  have hs : ∑ d : Direction v r p q, maxSlope v r p q I hI c α d=0 :=
    le_antisymm
      (Finset.sum_nonpos (fun d _ => maxSlope_nonpos_of_isLocalMax v r hr p q hp hq I hI c α hmax d))
      (sum_maxSlope_nonneg v r p q hp hq I hI c α)
  exact (Finset.sum_eq_zero_iff_of_nonpos
    (fun d _ => maxSlope_nonpos_of_isLocalMax v r hr p q hp hq I hI c α hmax d)).mp hs d (Finset.mem_univ d)

/-- EVERY whole point of the actual original neighborhood has the SAME maximum value, from actual zero slopes and genuine branch cover. -/
theorem maxValue_eq_of_isLocalMax_on_maxNeighborhood
    (hmax : IsLocalMax (maxValue v p q I hI c α) (gauss (self v) r))
    (x : RelativeSpectrum v K[X]) (hxN : x ∈ maxNeighborhood v r hr p q I hI c α) :
    maxValue v p q I hI c α x=maxValue v p q I hI c α (gauss (self v) r) := by
  classical
  by_cases hxr : x.1.val X≤r
  · let z : CoordinateDisc (A := K) v r := ⟨x,hxr⟩
    by_cases hzg : z=discGaussPoint v r
    · exact congrArg (maxValue v p q I hI c α) (congrArg Subtype.val hzg)
    · obtain ⟨a,ha,hza⟩ := exists_mem_discBranch_of_ne_gauss r z hzg
      by_cases hB : discBranch v r a ∈ branchFamily v r p q
      · obtain ⟨b,hb,hba⟩ := (mem_rationalRootBranches_iff v r (numeratorProduct p) (numeratorProduct q) _).mp hB
        have hzb : z ∈ discBranch v r b := hba.symm ▸ hza
        have he := maxValue_on_listed_branch v r hr p q hp hq I hI c α b hb z hzb hxN
        rw [maxSlope_eq_zero_of_isLocalMax v r hr p q hp hq I hI c α hmax,zero_mul,add_zero] at he
        exact he
      · exact maxValue_on_unlisted_branch v r hr p q hp hq I hI c α a ha hB z hza
  · have he := maxValue_on_outer v r hr p q hp hq I hI c α x (lt_of_not_ge hxr) hxN
    rw [maxSlope_eq_zero_of_isLocalMax v r hr p q hp hq I hI c α hmax,zero_mul,add_zero] at he
    exact he

/-- A TRUE local maximum of the SAME original finite unit maximum gives actual open local constancy, wholly inside every original unit locus. -/
theorem exists_open_maxValue_constant_of_isLocalMax
    (hmax : IsLocalMax (maxValue v p q I hI c α) (gauss (self v) r)) :
    ∃ W : Set (RelativeSpectrum v K[X]), IsOpen W ∧ gauss (self v) r∈W ∧
      (∀ x∈W, maxValue v p q I hI c α x=maxValue v p q I hI c α (gauss (self v) r)) ∧
      ∀ x∈W, ∀ j, x.1.val ((p j)*(q j))≠0 :=
  ⟨maxNeighborhood v r hr p q I hI c α,
    isOpen_maxNeighborhood v r hr p q I hI c α,
    gauss_mem_maxNeighborhood v r hr p q I hI c α,
    fun x hx => maxValue_eq_of_isLocalMax_on_maxNeighborhood v r hr p q hp hq I hI c α hmax x hx,
    fun x hx j => unit_mul_ne_zero_on_maxNeighborhood v r hr p q hp hq I hI c α j x hx⟩

end EnvelopeProperty.Berkovich.RelativeSpectrum.RationalUnitFamily
