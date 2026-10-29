import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Real.Basic

/-!
# Valuation filtrations on section spaces and local-frame invariance

An actual Mathlib additive valuation on a field gives threshold subspaces of
any vector space mapped linearly into that field, provided the valuation is
trivial on nonzero base-field scalars. Multiplicativity comes from the valuation
law. A valuation nonnegative on a local coefficient ring has value zero on its
units, so changing a local frame does not change the section value.

These algebraic constructions are the local kernels of `defn:section-filtration`
and the filtration preliminaries for joint counting. Constructing the
global section ring and obtaining the finite-discrepancy linear growth bound
are separate geometric obligations.
-/

namespace ComplexSchemes

section LinearFiltration

variable {K F V : Type*} [Field K] [Field F] [Algebra K F]
  [AddCommGroup V] [Module K V]

/-- The actual valuation threshold subspace, with the source's additive order.
The linear map may be any section-representative map; an embedding is needed
only for subsequent separation and finite-jumping-value assertions. -/
def valuationFiltration (v : AddValuation F (WithTop ℝ)) (ι : V →ₗ[K] F)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (a : ℝ) : Submodule K V where
  carrier := {s | (a : WithTop ℝ) ≤ v (ι s)}
  zero_mem' := by simp
  add_mem' := by
    intro s t hs ht
    change (a : WithTop ℝ) ≤ v (ι (s + t))
    rw [map_add]
    exact v.map_le_add hs ht
  smul_mem' := by
    intro c s hs
    by_cases hc : c = 0
    · subst c
      simp
    · change (a : WithTop ℝ) ≤ v (ι (c • s))
      rw [map_smul, Algebra.smul_def, v.map_mul, htrivial c hc, zero_add]
      exact hs

@[simp]
theorem mem_valuationFiltration (v : AddValuation F (WithTop ℝ))
    (ι : V →ₗ[K] F) (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (a : ℝ) (s : V) : s ∈ valuationFiltration v ι htrivial a ↔
      (a : WithTop ℝ) ≤ v (ι s) := Iff.rfl

/-- Raising the additive valuation threshold shrinks the actual subspace. -/
theorem valuationFiltration_antitone (v : AddValuation F (WithTop ℝ))
    (ι : V →ₗ[K] F) (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0) :
    Antitone (valuationFiltration v ι htrivial) := by
  intro a b hab s hs
  exact (WithTop.coe_le_coe.mpr hab).trans hs

/-- Products of threshold elements have the sum of the two thresholds. -/
theorem valuation_product_threshold (v : AddValuation F (WithTop ℝ))
    {a b : ℝ} {s t : F} (hs : (a : WithTop ℝ) ≤ v s)
    (ht : (b : WithTop ℝ) ≤ v t) :
    ((a + b : ℝ) : WithTop ℝ) ≤ v (s * t) := by
  rw [v.map_mul, WithTop.coe_add]
  exact add_le_add hs ht

/-- An injective representative map gives finite valuation to every nonzero
section, rather than assigning an arbitrary jumping weight. -/
theorem valuation_ne_top_of_injective (v : AddValuation F (WithTop ℝ))
    (ι : V →ₗ[K] F) (hι : Function.Injective ι) {s : V} (hs : s ≠ 0) :
    v (ι s) ≠ ⊤ := by
  rw [v.ne_top_iff]
  intro hz
  apply hs
  apply hι
  simpa using hz

/-- A nonzero base-field scalar does not change the representative value. -/
theorem valuation_smul_of_ne_zero (v : AddValuation F (WithTop ℝ))
    (ι : V →ₗ[K] F) (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    {c : K} (hc : c ≠ 0) (s : V) : v (ι (c • s)) = v (ι s) := by
  rw [map_smul, Algebra.smul_def, v.map_mul, htrivial c hc, zero_add]

/-- The term of uniquely smallest valuation survives in a finite sum. -/
theorem valuation_sum_eq_of_unique_min {I : Type*} [DecidableEq I]
    (v : AddValuation F (WithTop ℝ)) (s : Finset I) (f : I → F) {i : I}
    (hi : i ∈ s) (hfinite : v (f i) ≠ ⊤)
    (hmin : ∀ j ∈ s, j ≠ i → v (f i) < v (f j)) :
    v (∑ j ∈ s, f j) = v (f i) := by
  have hrest : v (f i) < v (∑ j ∈ s.erase i, f j) := by
    apply v.map_lt_sum' (lt_top_iff_ne_top.mpr hfinite)
    intro j hj
    exact hmin j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1
  rw [← Finset.sum_erase_add s f hi, add_comm]
  exact v.map_add_eq_of_lt_left hrest

/-- Vectors with distinct actual valuation values are linearly independent.
The scalar-triviality hypothesis is used to keep every nonzero coefficient
from changing its term's value. -/
theorem linearIndependent_of_injective_valuation {I : Type*}
    (v : AddValuation F (WithTop ℝ)) (ι : V →ₗ[K] F)
    (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (u : I → V) (hu : ∀ i, u i ≠ 0)
    (hvalue : Function.Injective (fun i => v (ι (u i)))) :
    LinearIndependent K u := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  let t := s.filter (fun j => g j ≠ 0)
  have hti : i ∈ t := Finset.mem_filter.mpr ⟨hi, hgi⟩
  obtain ⟨j, hj, hjmin⟩ := Finset.exists_min_image t (fun j => v (ι (u j))) ⟨i, hti⟩
  have hgj : g j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hsumt : ∑ l ∈ t, g l • u l = 0 := by
    change ∑ l ∈ s.filter (fun l => g l ≠ 0), g l • u l = 0
    rw [Finset.sum_filter]
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro l hl
    split_ifs with h
    · rfl
    · simp only [not_not] at h
      simp [h]
  have hjfinite : v (ι (g j • u j)) ≠ ⊤ := by
    rw [valuation_smul_of_ne_zero v ι htrivial hgj]
    exact valuation_ne_top_of_injective v ι hι (hu j)
  have hsmall : ∀ l ∈ t, l ≠ j → v (ι (g j • u j)) < v (ι (g l • u l)) := by
    intro l hl hlj
    have hgl : g l ≠ 0 := (Finset.mem_filter.mp hl).2
    rw [valuation_smul_of_ne_zero v ι htrivial hgj,
      valuation_smul_of_ne_zero v ι htrivial hgl]
    exact lt_of_le_of_ne (hjmin l hl) (fun heq => hlj (hvalue heq.symm))
  have hval := valuation_sum_eq_of_unique_min v t (fun l => ι (g l • u l))
    hj hjfinite hsmall
  rw [← map_sum, hsumt, map_zero, v.map_zero] at hval
  exact hjfinite hval.symm

/-- The actual finite-valued nonzero representative values, as a subset of ℝ. -/
def valuationValues (v : AddValuation F (WithTop ℝ)) (ι : V →ₗ[K] F) : Set ℝ :=
  {a | ∃ s : V, s ≠ 0 ∧ v (ι s) = (a : WithTop ℝ)}

/-- Select one vector realizing each value; the existence is part of membership
in the actual value set, not additional weight data. -/
noncomputable def valuationValueRepresentative (v : AddValuation F (WithTop ℝ))
    (ι : V →ₗ[K] F) (a : valuationValues v ι) : V := Classical.choose a.property

/-- The selected representative is nonzero and realizes its actual value. -/
theorem valuationValueRepresentative_spec (v : AddValuation F (WithTop ℝ))
    (ι : V →ₗ[K] F) (a : valuationValues v ι) :
    valuationValueRepresentative v ι a ≠ 0 ∧
      v (ι (valuationValueRepresentative v ι a)) = ((a : ℝ) : WithTop ℝ) :=
  Classical.choose_spec a.property

/-- One actual vector per distinct value is a linearly independent family. -/
theorem valuationValueRepresentative_linearIndependent (v : AddValuation F (WithTop ℝ))
    (ι : V →ₗ[K] F) (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0) :
    LinearIndependent K (valuationValueRepresentative v ι) := by
  apply linearIndependent_of_injective_valuation v ι hι htrivial
  · intro a
    exact (valuationValueRepresentative_spec v ι a).1
  · intro a b hab
    simp only [(valuationValueRepresentative_spec v ι a).2,
      (valuationValueRepresentative_spec v ι b).2, WithTop.coe_inj] at hab
    exact Subtype.ext hab

/-- Finite dimension forces the actual set of jumping values to be finite. -/
theorem valuationValues_finite [FiniteDimensional K V]
    (v : AddValuation F (WithTop ℝ)) (ι : V →ₗ[K] F) (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0) :
    (valuationValues v ι).Finite := by
  let : Finite (valuationValues v ι) :=
    (valuationValueRepresentative_linearIndependent v ι hι htrivial).finite
  exact Set.finite_def.mpr ⟨Fintype.ofFinite (valuationValues v ι)⟩

/-- There are at most `dim V` distinct actual valuation jumping values. -/
theorem valuationValues_card_le_finrank [FiniteDimensional K V]
    (v : AddValuation F (WithTop ℝ)) (ι : V →ₗ[K] F) (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0) :
    Nat.card (valuationValues v ι) ≤ Module.finrank K V := by
  let : Fintype (valuationValues v ι) := (valuationValues_finite v ι hι htrivial).fintype
  simpa only [Nat.card_eq_fintype_card] using
    (valuationValueRepresentative_linearIndependent v ι hι htrivial).fintype_card_le_finrank

end LinearFiltration

section LocalFrames

variable {A F : Type*} [CommRing A] [Field F]

/-- Nonnegativity on a coefficient ring forces every unit to have value zero.
This applies in particular to the local ring at the center of a valuation. -/
theorem valuation_unit_eq_zero (v : AddValuation F (WithTop ℝ)) (f : A →+* F)
    (hcenter : ∀ r : A, (0 : WithTop ℝ) ≤ v (f r)) (u : Aˣ) :
    v (f (u : A)) = 0 := by
  have hu : (0 : WithTop ℝ) ≤ v (f (u : A)) := hcenter u
  have hinv : (0 : WithTop ℝ) ≤ v (f (↑u⁻¹ : A)) := hcenter ↑u⁻¹
  have hsum : v (f (u : A)) + v (f (↑u⁻¹ : A)) = 0 := by
    rw [← v.map_mul, ← map_mul]
    simp
  exact le_antisymm ((le_add_of_nonneg_right hinv).trans hsum.le) hu

/-- Multiplication by a unit in the coefficient ring leaves section value
unchanged, proving the local-frame invariance used in local-frame calculations. -/
theorem valuation_frame_independent (v : AddValuation F (WithTop ℝ)) (f : A →+* F)
    (hcenter : ∀ r : A, (0 : WithTop ℝ) ≤ v (f r)) (u : Aˣ) (s : F) :
    v (f (u : A) * s) = v s := by
  rw [v.map_mul, valuation_unit_eq_zero v f hcenter u, zero_add]

end LocalFrames

end ComplexSchemes
