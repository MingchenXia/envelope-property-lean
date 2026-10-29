import EnvelopeProperty.AlgGeom.NativeNumericalPositiveAmpleSums
import EnvelopeProperty.AlgGeom.AmpleLinePositivePowers

/-! # Genuine actual ample lines representing positive rational original sums -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.NativeRealNumericalClasses
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (p : X ⟶ Spec (.of k)) [IsProjective p]

/-- A NONEMPTY finite positive integer sum of actual ample-line classes is the exact
class of an internally constructed SAME original geometrically ample line. -/
theorem exists_ample_integer_line_sum {n : ℕ} (hn : 0 < n) (A : Fin n → X.Modules)
    (hA : ∀ i, SchemeLineAmpleness.IsAmple p (A i)) (m : Fin n → ℕ) (hm : ∀ i, 0 < m i) :
    ∃ L : X.Modules, ∃ hL : SchemeLineAmpleness.IsAmple p L,
      lineClass p L hL.isInvertible =
        ∑ i, (m i : ℝ) • lineClass p (A i) (hA i).isInvertible := by
  induction n with
  | zero => omega
  | succ n ih =>
    let P := bundleTensorPower (A 0) (m 0)
    have hP : SchemeLineAmpleness.IsAmple p P :=
      AmpleLinePositivePowers.isAmple_tensorPower p _ (hA 0) _ (hm 0)
    by_cases hn' : 0 < n
    · obtain ⟨L, hL, he⟩ := ih hn' (fun i => A i.succ) (fun i => hA i.succ)
        (fun i => m i.succ) (fun i => hm i.succ)
      let hPL := AmpleTensorLines.isAmple_tensor p P L hP hL
      refine ⟨P ⊗ L, hPL, ?_⟩
      rw [lineClass_tensor p P L hP.isInvertible hL.isInvertible, he,
        lineClass_tensorPower p (A 0) (hA 0).isInvertible (m 0), Fin.sum_univ_succ]
    · have hn0 : n = 0 := by omega
      subst n
      refine ⟨P, hP, ?_⟩
      simpa only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero] using
        lineClass_tensorPower p (A 0) (hA 0).isInvertible (m 0)

private theorem positive_rational_denominator {n : ℕ} (q : Fin n → ℚ) (hq : ∀ i, 0 < q i) :
    ∃ d : ℕ, ∃ m : Fin n → ℕ, 0 < d ∧
      ∀ i, 0 < m i ∧ (q i : ℝ) = (m i : ℝ) / (d : ℝ) := by
  classical
  let d : ℕ := ∏ i, (q i).den
  have hd : 0 < d := Finset.prod_pos fun i _ => (q i).pos
  let m : Fin n → ℕ := fun i => (q i).num.toNat * ∏ j ∈ Finset.univ.erase i, (q j).den
  refine ⟨d, m, hd, fun i => ?_⟩
  have hnum : (0 : ℤ) ≤ (q i).num := Rat.num_nonneg.mpr (hq i).le
  have hsplit : (d : ℚ) = ((q i).den : ℚ) * ∏ j ∈ Finset.univ.erase i, ((q j).den : ℚ) := by
    dsimp [d]
    push_cast
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hfrac : q i * ((q i).den : ℚ) = (q i).num := by
    exact (eq_div_iff (by exact_mod_cast (q i).den_nz)).mp (Rat.num_div_den (q i)).symm
  have hkey : q i * (d : ℚ) = (m i : ℚ) := by
    rw [hsplit, ← mul_assoc, hfrac]
    dsimp [m]
    push_cast
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hnum).symm
  have heq : (q i : ℝ) = (m i : ℝ) / (d : ℝ) := by
    have h := (eq_div_iff (by exact_mod_cast hd.ne' : (d : ℚ) ≠ 0)).mpr hkey
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun t : ℚ => (t : ℝ)) h
  refine ⟨?_, heq⟩
  by_contra hnot
  have hz : m i = 0 := Nat.eq_zero_of_not_pos hnot
  have hpos : 0 < (q i : ℝ) := by exact_mod_cast hq i
  rw [hz, Nat.cast_zero, zero_div] at heq
  exact hpos.ne' heq

/-- EVERY NONEMPTY positive rational finite sum of SAME actual geometrically ample
lines has an INTERNALLY derived positive denominator and an actual ample original line. -/
theorem exists_rational_ample_line_representative {n : ℕ} (hn : 0 < n) (A : Fin n → X.Modules)
    (hA : ∀ i, SchemeLineAmpleness.IsAmple p (A i)) (q : Fin n → ℚ) (hq : ∀ i, 0 < q i) :
    ∃ d : ℕ, 0 < d ∧ ∃ L : X.Modules, ∃ hL : SchemeLineAmpleness.IsAmple p L,
      lineFamilyMap p A (fun i => (hA i).isInvertible) (fun i => (q i : ℝ)) =
        (d : ℝ)⁻¹ • lineClass p L hL.isInvertible := by
  obtain ⟨d, m, hd, hm⟩ := positive_rational_denominator q hq
  obtain ⟨L, hL, he⟩ := exists_ample_integer_line_sum p hn A hA m (fun i => (hm i).1)
  refine ⟨d, hd, L, hL, ?_⟩
  rw [he, lineFamilyMap_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, (hm i).2, div_eq_inv_mul]

end EnvelopeProperty.NativeRealNumericalClasses
