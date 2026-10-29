import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # Homogeneous equations for retaining a prescribed closed locus

Finite projective-point avoidance is derived inside the same original
homogeneous ideal and every sufficiently large degree. This is a
cut-equation prerequisite, not an asserted horizontal surface construction.
-/
noncomputable section
open scoped Classical
open MvPolynomial
namespace EnvelopeProperty.PLGaussVerticalCurveSurfaceSelection
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k R σ ι : Type*} [Field k] [Infinite k] [CommRing R] [Algebra k R]

/-- A homogeneous component witnesses noncontainment in any ideal. -/
theorem exists_homogeneous_mem_notMem
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) (P : Ideal (MvPolynomial σ R))
    (hIP : ¬ I.toIdeal ≤ P) :
    ∃ (e : ℕ) (g : MvPolynomial σ R), g.IsHomogeneous e ∧ g ∈ I ∧ g ∉ P := by
  obtain ⟨a, haI, haP⟩ := Set.not_subset.mp hIP
  by_contra h
  push Not at h
  apply haP
  rw [← MvPolynomial.sum_homogeneousComponent a]
  exact P.sum_mem fun e _ => h e (homogeneousComponent e a)
    (homogeneousComponent_mem e a)
    (homogeneousComponent_mem_of_mem I.isHomogeneous haI e)

include k in
/-- Large homogeneous ideal pieces avoid a finite family of relevant prime ideals. -/
theorem exists_eventually_homogeneous_avoiding [Finite ι]
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) (P : ι → Ideal (MvPolynomial σ R))
    (hP : ∀ i, (P i).IsPrime) (hIP : ∀ i, ¬ I.toIdeal ≤ P i)
    (hX : ∀ i, ∃ j, (MvPolynomial.X j : MvPolynomial σ R) ∉ P i) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∃ f : MvPolynomial σ R,
      f.IsHomogeneous d ∧ f ∈ I ∧ ∀ i, f ∉ P i := by
  let _ := Fintype.ofFinite ι
  choose e g hg hgin hgnot using fun i => exists_homogeneous_mem_notMem I (P i) (hIP i)
  choose j hj using hX
  refine ⟨Finset.univ.sup e, ?_⟩
  intro d hd
  let W : Submodule k (MvPolynomial σ R) :=
    I.toIdeal.restrictScalars k ⊓ (homogeneousSubmodule σ R d).restrictScalars k
  let Q (i : ι) : Submodule k W := ((P i).restrictScalars k).comap W.subtype
  have hQ (i : ι) : Q i ≠ ⊤ := by
    have hei : e i ≤ d := (Finset.le_sup (f := e) (Finset.mem_univ i)).trans hd
    let a := g i * MvPolynomial.X (j i) ^ (d - e i)
    have haI : a ∈ I := I.toIdeal.mul_mem_right _ (hgin i)
    have haH : a.IsHomogeneous d := by
      simpa only [Nat.add_sub_of_le hei] using
        (hg i).mul (MvPolynomial.isHomogeneous_X_pow (R := R) (j i) (d - e i))
    have haP : a ∉ P i := by
      intro ha
      rcases (hP i).mem_or_mem ha with h | h
      · exact hgnot i h
      · exact hj i ((hP i).mem_of_pow_mem (d - e i) h)
    intro heq
    have hmem : (⟨a, haI, haH⟩ : W) ∈ Q i := by rw [heq]; trivial
    exact haP hmem
  obtain ⟨f, hf⟩ := Submodule.exists_forall_notMem_of_forall_ne_top Q hQ
  exact ⟨f.1, f.2.2, f.2.1, fun i => hf i⟩

/-- The relevance of an original polynomial projective point supplies a coordinate. -/
theorem exists_coordinate_notMem (x : ProjectiveSpectrum (homogeneousSubmodule σ R)) :
    ∃ j, (MvPolynomial.X j : MvPolynomial σ R) ∉ x.asHomogeneousIdeal := by
  by_contra h
  push Not at h
  apply x.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le]
  intro d hd f hf
  have hspan : f ∈ Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ R)) := by
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hm0 : m ≠ 0 := by
      intro heq
      subst m
      exact (MvPolynomial.mem_support_iff.mp hm)
        (hf.coeff_eq_zero (by simpa using (Nat.ne_of_gt hd).symm))
    have hex : ∃ j, m j ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hm0 (Finsupp.ext hn)
    obtain ⟨j, hj⟩ := hex
    exact ⟨j, Set.mem_univ j, hj⟩
  exact (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact h j)) hspan

include k in
/-- Every large-degree hypersurface contains the original locus and avoids prescribed points. -/
theorem exists_eventually_projective_hypersurface_avoiding [Finite ι]
    (I : HomogeneousIdeal (homogeneousSubmodule σ R))
    (x : ι → ProjectiveSpectrum (homogeneousSubmodule σ R))
    (hx : ∀ i, x i ∉ ProjectiveSpectrum.zeroLocus (homogeneousSubmodule σ R) (I : Set _)) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∃ f : MvPolynomial σ R,
      f.IsHomogeneous d ∧ f ∈ I ∧
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule σ R) (I : Set _) ⊆
        ProjectiveSpectrum.zeroLocus (homogeneousSubmodule σ R) {f} ∧
      ∀ i, x i ∉ ProjectiveSpectrum.zeroLocus (homogeneousSubmodule σ R) {f} := by
  obtain ⟨N, hN⟩ := exists_eventually_homogeneous_avoiding (k := k) I
    (fun i => (x i).asHomogeneousIdeal.toIdeal) (fun i => (x i).isPrime) hx
    (fun i => exists_coordinate_notMem (x i))
  refine ⟨N, ?_⟩
  intro d hd
  obtain ⟨f, hfH, hfI, hf⟩ := hN d hd
  refine ⟨f, hfH, hfI, ?_, ?_⟩
  · intro y hy a ha
    have heq : a = f := Set.mem_singleton_iff.mp ha
    exact heq ▸ hy hfI
  · intro i hi
    exact hf i (hi (Set.mem_singleton f))

end EnvelopeProperty.PLGaussVerticalCurveSurfaceSelection
