/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.RationalUnitFamilySlopes
import EnvelopeProperty.FiniteAffineMax

/-! # Actual finite maxima of original rational-unit affine expressions -/
open scoped NNReal ENNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.RationalUnitFamily
variable {K J ι : Type*} [Field K] [Fintype J] (v : Valuation K ℝ≥0)

/-- The ACTUAL finite maximum of the ORIGINAL unit-affine functions, on their genuine common unit locus. -/
def maxValue (p q : J → K[X]) (I : Finset ι) (hI : I.Nonempty) (c : ι → ℝ)
    (α : ι → J → ℝ) (x : RelativeSpectrum v K[X]) : ℝ :=
  I.sup' hI (fun i => affineValue v p q (c i) (α i) x)

/-- Actual original unit-affine values at eta determine the genuine active indices. -/
def activeIndices (r : ℝ≥0) (p q : J → K[X]) (I : Finset ι) (hI : I.Nonempty)
    (c : ι → ℝ) (α : ι → J → ℝ) : Finset ι :=
  FiniteAffineMax.active I hI (fun i => affineValue v p q (c i) (α i) (gauss (self v) r))

/-- This actual active set is genuinely nonempty, by finite ORIGINAL value attainment. -/
theorem activeIndices_nonempty (r : ℝ≥0) (p q : J → K[X]) (I : Finset ι) (hI : I.Nonempty)
    (c : ι → ℝ) (α : ι → J → ℝ) : (activeIndices v r p q I hI c α).Nonempty :=
  FiniteAffineMax.active_nonempty I hI _

/-- Active membership is EXACT original finite-maximum attainment, with no profile input. -/
theorem mem_activeIndices_iff (r : ℝ≥0) (p q : J → K[X]) (I : Finset ι) (hI : I.Nonempty)
    (c : ι → ℝ) (α : ι → J → ℝ) (i : ι) :
    i ∈ activeIndices v r p q I hI c α ↔ i ∈ I ∧
      affineValue v p q (c i) (α i) (gauss (self v) r)=maxValue v p q I hI c α (gauss (self v) r) := by
  classical
  exact Finset.mem_filter

/-- The outgoing maximum slope is CONSTRUCTED from the genuine ORIGINAL active functions and directions. -/
def maxSlope (r : ℝ≥0) (p q : J → K[X]) (I : Finset ι) (hI : I.Nonempty)
    (c : ι → ℝ) (α : ι → J → ℝ) (d : Direction v r p q) : ℝ :=
  FiniteAffineMax.activeSlope I hI
    (fun i => affineValue v p q (c i) (α i) (gauss (self v) r))
    (fun i d => affineSlope v r p q (α i) d) d

/-- The constructed slope is the TRUE finite maximum over EXACTLY the actual active indices. -/
theorem maxSlope_eq_sup_active (r : ℝ≥0) (p q : J → K[X]) (I : Finset ι) (hI : I.Nonempty)
    (c : ι → ℝ) (α : ι → J → ℝ) (d : Direction v r p q) :
    maxSlope v r p q I hI c α d =
      (activeIndices v r p q I hI c α).sup' (activeIndices_nonempty v r p q I hI c α)
        (fun i => affineSlope v r p q (α i) d) := rfl

/-- Genuine ORIGINAL unit/root balancing DERIVES the nonnegative total outgoing maximum slope. -/
theorem sum_maxSlope_nonneg (r : ℝ≥0) (p q : J → K[X])
    (hp : ∀ j, p j≠0) (hq : ∀ j, q j≠0) (I : Finset ι) (hI : I.Nonempty)
    (c : ι → ℝ) (α : ι → J → ℝ) : 0≤∑ d : Direction v r p q, maxSlope v r p q I hI c α d := by
  classical
  exact FiniteAffineMax.sum_activeSlope_nonneg I hI Finset.univ _ _
    (fun i _ => sum_affineSlope_eq_zero v r p q hp hq (α i))

/-- The common positive length is CONSTRUCTED from actual original intercepts and actual real unit slopes. -/
def activeLengthBound (r : ℝ≥0) (p q : J → K[X]) (I : Finset ι) (hI : I.Nonempty)
    (c : ι → ℝ) (α : ι → J → ℝ) : ℝ :=
  (FiniteAffineMax.exists_pos_eventual_max I hI (Finset.univ : Finset (Direction v r p q))
    (fun i => affineValue v p q (c i) (α i) (gauss (self v) r))
    (fun i d => affineSlope v r p q (α i) d)).choose

/-- That actual finite-data length is genuinely positive. -/
theorem activeLengthBound_pos (r : ℝ≥0) (p q : J → K[X]) (I : Finset ι) (hI : I.Nonempty)
    (c : ι → ℝ) (α : ι → J → ℝ) : 0<activeLengthBound v r p q I hI c α :=
  (FiniteAffineMax.exists_pos_eventual_max I hI (Finset.univ : Finset (Direction v r p q))
    (fun i => affineValue v p q (c i) (α i) (gauss (self v) r))
    (fun i d => affineSlope v r p q (α i) d)).choose_spec.1

private theorem active_profile (r : ℝ≥0) (p q : J → K[X]) (I : Finset ι) (hI : I.Nonempty)
    (c : ι → ℝ) (α : ι → J → ℝ) (d : Direction v r p q) (t : ℝ)
    (ht : 0≤t) (htε : t<activeLengthBound v r p q I hI c α) :
    I.sup' hI (fun i => affineValue v p q (c i) (α i) (gauss (self v) r) +
      affineSlope v r p q (α i) d*t) =
        maxValue v p q I hI c α (gauss (self v) r)+maxSlope v r p q I hI c α d*t :=
  (FiniteAffineMax.exists_pos_eventual_max I hI (Finset.univ : Finset (Direction v r p q))
    (fun i => affineValue v p q (c i) (α i) (gauss (self v) r))
    (fun i d => affineSlope v r p q (α i) d)).choose_spec.2 d (Finset.mem_univ d) t ht htε

section Geometry
variable [IsAlgClosed K] (r : ℝ≥0) (hr : 0<r) (p q : J → K[X])
    (hp : ∀ j, p j≠0) (hq : ∀ j, q j≠0) (I : Finset ι) (hI : I.Nonempty)
    (c : ι → ℝ) (α : ι → J → ℝ)

/-- A TRUE original-point neighborhood combines the genuine root collars and actual finite active length. -/
def maxNeighborhood : Set (RelativeSpectrum v K[X]) :=
  (neighborhood v r hr p q ∩
    {x | Spectrum.logAbs X x.1 < ((Real.log (r : ℝ)+activeLengthBound v r p q I hI c α : ℝ) : EReal)}) ∩
    {x | ∀ b ∈ insideRootCenters v r (numeratorProduct p) (numeratorProduct q),
      ((Real.log (r : ℝ)-activeLengthBound v r p q I hI c α : ℝ) : EReal) < Spectrum.logAbs (X-C b) x.1}

omit [IsAlgClosed K] in
/-- Every original inequality defining the actual finite-max neighborhood is genuinely open. -/
theorem isOpen_maxNeighborhood : IsOpen (maxNeighborhood v r hr p q I hI c α) := by
  have ho : IsOpen {x : RelativeSpectrum v K[X] |
      Spectrum.logAbs X x.1 < ((Real.log (r : ℝ)+activeLengthBound v r p q I hI c α : ℝ) : EReal)} :=
    isOpen_lt ((Spectrum.continuous_logAbs X).comp continuous_subtype_val) continuous_const
  have hi : IsOpen {x : RelativeSpectrum v K[X] |
      ∀ b ∈ insideRootCenters v r (numeratorProduct p) (numeratorProduct q),
        ((Real.log (r : ℝ)-activeLengthBound v r p q I hI c α : ℝ) : EReal) < Spectrum.logAbs (X-C b) x.1} := by
    simp only [Set.ofPred_forall]
    apply isOpen_biInter_finset
    intro b hb
    exact isOpen_lt continuous_const ((Spectrum.continuous_logAbs _).comp continuous_subtype_val)
  exact ((isOpen_neighborhood v r hr p q).inter ho).inter hi

omit [IsAlgClosed K] in
/-- The ENTIRE original Gauss point belongs to the true finite-max neighborhood. -/
theorem gauss_mem_maxNeighborhood : gauss (self v) r ∈ maxNeighborhood v r hr p q I hI c α := by
  have he := activeLengthBound_pos v r p q I hI c α
  have hX : Spectrum.logAbs X (gauss (self v) r).1 = ((Real.log (r : ℝ) : ℝ) : EReal) := by
    change ENNReal.log ((gauss (self v) r).1.val X : ℝ≥0∞) = _
    rw [← val_apply,gauss_val_X]
    exact ENNReal.log_of_nnreal hr.ne'
  refine ⟨⟨gauss_mem_neighborhood v r hr p q,?_⟩,?_⟩
  · change Spectrum.logAbs X (gauss (self v) r).1 < _
    rw [hX]
    exact_mod_cast (show Real.log (r : ℝ)<Real.log (r : ℝ)+activeLengthBound v r p q I hI c α by linarith)
  · intro b hb
    have hvb := val_le_of_mem_insideRootCenters v r (numeratorProduct p) (numeratorProduct q) hb
    have hB : Spectrum.logAbs (X-C b) (gauss (self v) r).1 = ((Real.log (r : ℝ) : ℝ) : EReal) := by
      change ENNReal.log (gaussFun v r (X-C b) : ℝ≥0∞) = _
      rw [gaussFun_X_sub_C,max_eq_left hvb]
      exact ENNReal.log_of_nnreal hr.ne'
    rw [hB]
    exact_mod_cast (show Real.log (r : ℝ)-activeLengthBound v r p q I hI c α<Real.log (r : ℝ) by linarith)

include hp hq in
/-- EVERY original unit is defined throughout the ACTUAL maximum neighborhood. -/
theorem unit_mul_ne_zero_on_maxNeighborhood (j : J) (x : RelativeSpectrum v K[X])
    (hxN : x ∈ maxNeighborhood v r hr p q I hI c α) : x.1.val ((p j)*(q j))≠0 :=
  unit_mul_ne_zero_on_neighborhood v r hr p q hp hq j x hxN.1.1

/-- An ORIGINAL root center determines its ACTUAL branch-set direction in the common family. -/
def centerDirection (b : K)
    (hb : b ∈ insideRootCenters v r (numeratorProduct p) (numeratorProduct q)) : Direction v r p q :=
  some ⟨discBranch v r b,
    (mem_rationalRootBranches_iff v r (numeratorProduct p) (numeratorProduct q) _).mpr ⟨b,hb,rfl⟩⟩

include hp hq in
/-- At EVERY original listed-branch point of the true neighborhood, the SAME finite maximum has its constructed active slope. -/
theorem maxValue_on_listed_branch (b : K)
    (hb : b ∈ insideRootCenters v r (numeratorProduct p) (numeratorProduct q))
    (x : CoordinateDisc (A := K) v r) (hx : x ∈ discBranch v r b)
    (hxN : x.1 ∈ maxNeighborhood v r hr p q I hI c α) :
    maxValue v p q I hI c α x.1 = maxValue v p q I hI c α (gauss (self v) r)+
      maxSlope v r p q I hI c α (centerDirection v r p q b hb)*
        (Real.log (r : ℝ)-Real.log (x.1.1.val (X-C b) : ℝ)) := by
  have ht : 0<x.1.1.val (X-C b) :=
    (innerRadius_pos v r hr p q b).trans (hxN.1.1.2 b hb)
  have htR : (x.1.1.val (X-C b) : ℝ)≤(r : ℝ) := by exact_mod_cast hx.le
  have hℓ : 0≤Real.log (r : ℝ)-Real.log (x.1.1.val (X-C b) : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast ht) htR)
  have hlog : Spectrum.logAbs (X-C b) x.1.1 =
      ((Real.log (x.1.1.val (X-C b) : ℝ) : ℝ) : EReal) := by
    exact ENNReal.log_of_nnreal ht.ne'
  have hh := hxN.2 b hb
  rw [hlog] at hh
  have hh' : Real.log (r : ℝ)-activeLengthBound v r p q I hI c α<
      Real.log (x.1.1.val (X-C b) : ℝ) := by exact_mod_cast hh
  have hsmall : Real.log (r : ℝ)-Real.log (x.1.1.val (X-C b) : ℝ)<
      activeLengthBound v r p q I hI c α := by linarith
  have he (i : ι) := affineValue_on_listed_branch v r hr p q hp hq b hb x hx hxN.1.1 (c i) (α i)
  unfold maxValue
  simp_rw [he]
  exact active_profile v r p q I hI c α (centerDirection v r p q b hb) _ hℓ hsmall

include hp hq in
/-- The SAME original maximum has its true outward active slope at EVERY outer-collar neighborhood point. -/
theorem maxValue_on_outer (x : RelativeSpectrum v K[X]) (hx : r<x.1.val X)
    (hxN : x ∈ maxNeighborhood v r hr p q I hI c α) :
    maxValue v p q I hI c α x = maxValue v p q I hI c α (gauss (self v) r)+
      maxSlope v r p q I hI c α none*
        (Real.log (x.1.val X : ℝ)-Real.log (r : ℝ)) := by
  have ht := hr.trans hx
  have htR : (r : ℝ)≤(x.1.val X : ℝ) := by exact_mod_cast hx.le
  have hℓ : 0≤Real.log (x.1.val X : ℝ)-Real.log (r : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hr) htR)
  have hlog : Spectrum.logAbs X x.1 = ((Real.log (x.1.val X : ℝ) : ℝ) : EReal) :=
    ENNReal.log_of_nnreal ht.ne'
  have hh := hxN.1.2
  change Spectrum.logAbs X x.1 < _ at hh
  rw [hlog] at hh
  have hh' : Real.log (x.1.val X : ℝ)<Real.log (r : ℝ)+activeLengthBound v r p q I hI c α := by
    exact_mod_cast hh
  have hsmall : Real.log (x.1.val X : ℝ)-Real.log (r : ℝ)<
      activeLengthBound v r p q I hI c α := by linarith
  have he (i : ι) := affineValue_outward_collar v r hr p q hp hq x hx hxN.1.1.1 (c i) (α i)
  unfold maxValue
  simp_rw [he]
  exact active_profile v r p q I hI c α none _ hℓ hsmall

include hr hp hq in
/-- EVERY point of EVERY unlisted original branch keeps the SAME original finite maximum constant. -/
theorem maxValue_on_unlisted_branch (a : K) (ha : v a≤r)
    (hB : discBranch v r a ∉ branchFamily v r p q)
    (x : CoordinateDisc (A := K) v r) (hx : x ∈ discBranch v r a) :
    maxValue v p q I hI c α x.1 = maxValue v p q I hI c α (gauss (self v) r) := by
  unfold maxValue
  congr 1
  funext i
  exact affineValue_on_unlisted_branch v r hr p q hp hq a ha hB x hx (c i) (α i)

end Geometry
end EnvelopeProperty.Berkovich.RelativeSpectrum.RationalUnitFamily
