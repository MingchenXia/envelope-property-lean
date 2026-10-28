import EnvelopeProperty.Potential.LineSkeleton
import Mathlib.Topology.Order.IsLUB

/-!
# Actual analytic-line classification by nested discs

The infimum of the original linear values is either attained, giving an
original Gauss point, or approached by strictly decreasing linear values.
Their actual Gauss points converge to the original point; their classical
closed discs have empty intersection.
-/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}

/-- The infimum of the actual linear-coordinate seminorm values. -/
def fcLeastLinearValue (x : RelativeSpectrum w K[X]) : ℝ≥0 :=
  sInf (Set.range fun a : K => val x (X-C a))

theorem fc_linearValues_nonempty (x : RelativeSpectrum w K[X]) :
    (Set.range fun a : K => val x (X-C a)).Nonempty :=
  ⟨val x (X-C 0),0,rfl⟩

theorem fc_linearValues_bddBelow (x : RelativeSpectrum w K[X]) :
    BddBelow (Set.range fun a : K => val x (X-C a)) := ⟨0,fun _ _ => zero_le⟩

theorem fcLeastLinearValue_le (x : RelativeSpectrum w K[X]) (a : K) :
    fcLeastLinearValue x ≤ val x (X-C a) :=
  csInf_le (fc_linearValues_bddBelow x) ⟨a,rfl⟩

variable [IsAlgClosed K]

theorem fc_eq_gauss_of_least_linear_attained (x : RelativeSpectrum w K[X]) (a : K)
    (ha : val x (X-C a) = fcLeastLinearValue x) :
    x = centeredGauss (self w) a (fcLeastLinearValue x) := by
  apply fc_ext_linear
  intro b
  rw [fc_centeredGauss_val_X_sub_C]
  apply le_antisymm
  · simpa only [ha,max_comm] using fc_linear_bound x a b
  · have hd := fc_center_distance_bound x a b
    rw [ha,max_eq_right (fcLeastLinearValue_le x b)] at hd
    exact max_le hd (fcLeastLinearValue_le x b)

theorem fcCenteredInflation_least (a : K) (x : RelativeSpectrum w K[X]) :
    fcCenteredInflation a x (fcLeastLinearValue x) = x := by
  apply fc_ext_linear
  intro b
  rw [fcCenteredInflation_val_X_sub_C,max_eq_left (fcLeastLinearValue_le x b)]

/-- The literal classical closed disc in the valued field, as distinguished from its analytic disc. -/
def fcClassicalClosedDisc (a : K) (r : ℝ≥0) : Set K := {b | w (b-a) ≤ r}

/-- The classification uses the original points, original Gauss points and actual nested disc sets. -/
theorem fc_gauss_or_nested_discs (x : RelativeSpectrum w K[X]) :
    (∃ a r, x = centeredGauss (self w) a r) ∨
      ∃ (a : ℕ → K) (r : ℕ → ℝ≥0),
        StrictAnti r ∧ Tendsto r atTop (𝓝 (fcLeastLinearValue x)) ∧
        (∀ n, val x (X-C (a n)) = r n) ∧
        Antitone (fun n => {y : RelativeSpectrum w K[X] | val y (X-C (a n)) ≤ r n}) ∧
        Antitone (fun n => fcClassicalClosedDisc (w := w) (a n) (r n)) ∧
        (⋂ n, fcClassicalClosedDisc (w := w) (a n) (r n)) = ∅ ∧
        Tendsto (fun n => centeredGauss (self w) (a n) (r n)) atTop (𝓝 x) := by
  by_cases hmin : ∃ a : K, val x (X-C a) = fcLeastLinearValue x
  · obtain ⟨a,ha⟩ := hmin
    exact Or.inl ⟨a,fcLeastLinearValue x,fc_eq_gauss_of_least_linear_attained x a ha⟩
  · apply Or.inr
    have hglb : IsGLB (Set.range fun a : K => val x (X-C a)) (fcLeastLinearValue x) :=
      isGLB_csInf (fc_linearValues_nonempty x) (fc_linearValues_bddBelow x)
    have hnot : fcLeastLinearValue x ∉ Set.range (fun a : K => val x (X-C a)) := by
      rintro ⟨a,ha⟩
      exact hmin ⟨a,ha⟩
    obtain ⟨r,hanti,_,hr,hrs⟩ := hglb.exists_seq_strictAnti_tendsto_of_notMem hnot
      (fc_linearValues_nonempty x)
    choose a ha using hrs
    change ∀ n, val x (X-C (a n)) = r n at ha
    have hcenter : ∀ i j : ℕ, i ≤ j → w (a j-a i) ≤ r i := by
      intro i j hij
      have h := fc_center_distance_bound x (a j) (a i)
      rw [ha j,ha i,max_eq_right (hanti.antitone hij)] at h
      exact h
    have hanalytic : Antitone (fun n =>
        {y : RelativeSpectrum w K[X] | val y (X-C (a n)) ≤ r n}) := by
      intro i j hij y hy
      exact (fc_linear_bound y (a j) (a i)).trans
        (max_le (hy.trans (hanti.antitone hij)) (hcenter i j hij))
    have hclassical : Antitone (fun n => fcClassicalClosedDisc (w := w) (a n) (r n)) := by
      intro i j hij b hb
      change w (b-a i) ≤ r i
      change w (b-a j) ≤ r j at hb
      have he : b-a i = (b-a j)+(a j-a i) := by ring
      rw [he]
      exact (w.map_add _ _).trans
        (max_le (hb.trans (hanti.antitone hij)) (hcenter i j hij))
    have hempty : (⋂ n, fcClassicalClosedDisc (w := w) (a n) (r n)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro b hb
      have hxb : ∀ n, val x (X-C b) ≤ r n := by
        intro n
        have hn := Set.mem_iInter.mp hb n
        change w (b-a n) ≤ r n at hn
        have hs : w (a n-b) = w (b-a n) := by
          rw [show a n-b = -(b-a n) by ring,Valuation.map_neg]
        exact (fc_linear_bound x (a n) b).trans (by rw [ha n,hs]; exact max_le le_rfl hn)
      have hle : val x (X-C b) ≤ fcLeastLinearValue x :=
        ge_of_tendsto hr (Eventually.of_forall hxb)
      exact hmin ⟨b,le_antisymm hle (fcLeastLinearValue_le x b)⟩
    have hgauss : ∀ n,
        fcCenteredInflation (0 : K) x (r n) = centeredGauss (self w) (a n) (r n) := by
      intro n
      rw [fcCenteredInflation_center_independent 0 (a n)]
      exact fcCenteredInflation_eq_gauss (a n) x (r n) (ha n).le
    have hlim : Tendsto (fun n => centeredGauss (self w) (a n) (r n)) atTop (𝓝 x) := by
      have hh := ((continuous_fcCenteredInflation (0 : K) x).tendsto
        (fcLeastLinearValue x)).comp hr
      rw [fcCenteredInflation_least] at hh
      have he : (fun n => centeredGauss (self w) (a n) (r n)) =
          fcCenteredInflation (0 : K) x ∘ r := by
        funext n
        exact (hgauss n).symm
      rw [he]
      exact hh
    exact ⟨a,r,hanti,hr,ha,hanalytic,hclassical,hempty,hlim⟩

end EnvelopeProperty.Berkovich.RelativeSpectrum
