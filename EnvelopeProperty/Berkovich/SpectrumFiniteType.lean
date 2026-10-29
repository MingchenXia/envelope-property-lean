/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumIntegralProper

/-!
# Finite type relative spectra over an arbitrary prescribed base seminorm

Polynomial evaluations are bounded by the maximum seminorm of their coefficients
times a power of a bound on their variables. The coefficient seminorm is fixed by
the relative spectrum and is not assumed to be trivial or globally bounded by one.

Generating polydiscs are compact. For a finitely generated algebra over any
commutative coefficient ring, finite generating polydiscs give actual compact
neighbourhoods and a countable compact exhaustion. Integral properness and closedness
are supplied by the imported stronger ultrafilter producers, without finite type
or local compactness hypotheses. No field or completeness hypothesis is imposed.
-/

open scoped NNReal Topology
open Filter Topology Set

noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {R : Type*} [CommRing R] {v : Valuation R ℝ≥0}
  {A : Type*} [CommRing A] [Algebra R A]

/-- The maximum prescribed-base seminorm of the nonzero coefficients of a polynomial. -/
def coeffBound {ι : Type*} (v : Valuation R ℝ≥0) (p : MvPolynomial ι R) : ℝ≥0 :=
  p.support.sup fun m => v (p.coeff m)

/-- A polynomial is bounded by its coefficient seminorm bound times the variable bound
to its total degree. -/
theorem val_aeval_le_coeffBound_mul_pow {ι : Type*} (z : ι → A)
    (x : RelativeSpectrum v A) {M : ℝ≥0} (hM : 1 ≤ M)
    (hz : ∀ i, val x (z i) ≤ M) (p : MvPolynomial ι R) :
    val x (MvPolynomial.aeval z p) ≤ coeffBound v p * M ^ p.totalDegree := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine (val x).map_sum_le fun m hm => ?_
  rw [map_mul, map_prod, val_algebraMap]
  calc v (p.coeff m) * ∏ i ∈ m.support, val x (z i ^ m i)
      ≤ coeffBound v p * ∏ i ∈ m.support, M ^ m i := by
        gcongr with i
        · exact Finset.le_sup (f := fun m => v (p.coeff m)) hm
        · rw [map_pow]
          exact pow_le_pow_left₀ zero_le (hz i) _
    _ = coeffBound v p * M ^ (∑ i ∈ m.support, m i) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ coeffBound v p * M ^ p.totalDegree :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM (MvPolynomial.le_totalDegree hm)) zero_le

/-- A generating family bounds every evaluation, with its prescribed-base coefficient factor. -/
theorem exists_abs_le_mul_pow_of_adjoin_eq_top {S : Set A} (hS : Algebra.adjoin R S = ⊤)
    (a : A) : ∃ C : ℝ≥0, ∃ d : ℕ, ∀ (x : RelativeSpectrum v A) (M : ℝ≥0),
      1 ≤ M → (∀ s ∈ S, val x s ≤ M) → val x a ≤ C * M ^ d := by
  have ha : a ∈ Algebra.adjoin R S := by
    rw [hS]
    exact Algebra.mem_top
  rw [Algebra.adjoin_eq_range] at ha
  obtain ⟨p, hp⟩ := (AlgHom.mem_range _).1 ha
  refine ⟨coeffBound v p, p.totalDegree, fun x M hM hx => ?_⟩
  rw [← hp]
  exact val_aeval_le_coeffBound_mul_pow (fun i : S => (i : A)) x hM
    (fun i => hx i.1 i.2) p

/-- Polydiscs for any family of evaluations are closed. -/
theorem isClosed_setOf_forall_abs_le (S : Set A) (r : ℝ≥0) :
    IsClosed {x : RelativeSpectrum v A | ∀ s ∈ S, val x s ≤ r} := by
  have he : {x : RelativeSpectrum v A | ∀ s ∈ S, val x s ≤ r} =
      ⋂ s ∈ S, {x | val x s ≤ r} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter]
  rw [he]
  exact isClosed_biInter fun s _ => isClosed_le (continuous_val_apply s) continuous_const

/-- Strict polydiscs for finitely many evaluations are open. -/
theorem isOpen_setOf_forall_abs_lt (S : Finset A) (r : ℝ≥0) :
    IsOpen {x : RelativeSpectrum v A | ∀ s ∈ S, val x s < r} := by
  have he : {x : RelativeSpectrum v A | ∀ s ∈ S, val x s < r} =
      ⋂ s ∈ S, {x | val x s < r} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter]
  rw [he]
  exact isOpen_biInter_finset fun s _ => isOpen_lt (continuous_val_apply s) continuous_const

/-- A polydisc of any generating set is compact, with an arbitrary prescribed base valuation. -/
theorem isCompact_setOf_forall_abs_le {S : Set A} (hS : Algebra.adjoin R S = ⊤) (r : ℝ≥0) :
    IsCompact {x : RelativeSpectrum v A | ∀ s ∈ S, val x s ≤ r} := by
  choose C d hd using exists_abs_le_mul_pow_of_adjoin_eq_top (v := v) hS
  refine (isCompact_setOf_forall_val_le (fun a => C a * (max 1 r) ^ d a)).of_isClosed_subset
    (isClosed_setOf_forall_abs_le S r) ?_
  exact fun x hx a => hd a x (max 1 r) (le_max_left _ _) fun s hs =>
    (hx s hs).trans (le_max_right _ _)

/-- A finite generating polydisc is compact over any prescribed base seminorm. -/
theorem isCompact_setOf_forall_abs_le_finset {S : Finset A}
    (hS : Algebra.adjoin R (S : Set A) = ⊤) (r : ℝ≥0) :
    IsCompact {x : RelativeSpectrum v A | ∀ s ∈ S, val x s ≤ r} :=
  isCompact_setOf_forall_abs_le hS r

/-- A finite type algebra admits a finite algebra-generating set. -/
theorem exists_finset_adjoin_eq_top [Algebra.FiniteType R A] :
    ∃ S : Finset A, Algebra.adjoin R (S : Set A) = ⊤ :=
  Algebra.FiniteType.out

/-- Finite generating polydiscs provide actual compact neighbourhoods. -/
instance instWeaklyLocallyCompactSpace [Algebra.FiniteType R A] :
    WeaklyLocallyCompactSpace (RelativeSpectrum v A) where
  exists_compact_mem_nhds x := by
    obtain ⟨S, hS⟩ := exists_finset_adjoin_eq_top (R := R) (A := A)
    refine ⟨_, isCompact_setOf_forall_abs_le hS ((S.sup fun s => val x s) + 1), ?_⟩
    refine mem_of_superset ((isOpen_setOf_forall_abs_lt S ((S.sup fun s => val x s) + 1)).mem_nhds
      ?_) ?_
    · exact fun s hs => (Finset.le_sup (f := fun s => val x s) hs).trans_lt (lt_add_one _)
    · exact fun y hy s hs => (hy s hs).le

/-- Relative spectra of finite type algebras over any prescribed seminorm are locally compact. -/
instance instLocallyCompactSpace [Algebra.FiniteType R A] :
    LocallyCompactSpace (RelativeSpectrum v A) := inferInstance

/-- Natural-radius finite generating polydiscs give a countable compact exhaustion. -/
instance instSigmaCompactSpace [Algebra.FiniteType R A] :
    SigmaCompactSpace (RelativeSpectrum v A) := by
  obtain ⟨S, hS⟩ := exists_finset_adjoin_eq_top (R := R) (A := A)
  refine ⟨⟨fun n : ℕ => {x | ∀ s ∈ S, val x s ≤ n},
    fun n => isCompact_setOf_forall_abs_le hS _, ?_⟩⟩
  refine iUnion_eq_univ_iff.2 fun x => ?_
  obtain ⟨n, hn⟩ := exists_nat_ge (S.sup fun s => val x s)
  exact ⟨n, fun s hs => (Finset.le_sup (f := fun s => val x s) hs).trans hn⟩


end EnvelopeProperty.Berkovich.RelativeSpectrum
