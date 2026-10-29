import EnvelopeProperty.Vanishing.RelativeNadelCoverWeightedExceptionalSnc
import EnvelopeProperty.Char0.RoundedSncIdealSheaf
import Mathlib.Algebra.Order.Floor.Semifield

/-! # Actual exceptional perturbation of the ORIGINAL intrinsic rounded ideal

The actual common original SNC family internally supplies a positive common
denominator and the SAME actual original numerator J^a*E. Its intrinsic
rounded ideal is exactly the original intrinsic rounded ideal at original q.
No coefficient family or perturbation/rounding comparison is input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData
open scoped BigOperators
universe u

namespace EnvelopeProperty.Vanishing.RelativeNadelCoverWeightedExceptionalRounding
open Char0 RelativeNadelCoverWeightedExceptional RelativeNadelCoverWeightedExceptionalSnc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem rational_floor (q : ℚ) (hq : 0 ≤ q) (b : ℕ) :
    ⌊q * (b : ℚ)⌋₊ = q.num.toNat * b / q.den := by
  have hn : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have hc : (q.num.toNat : ℚ) = (q.num : ℚ) := by exact_mod_cast hn
  have hq' : q = (q.num.toNat : ℚ) / (q.den : ℚ) := by
    rw [hc]
    exact q.num_div_den.symm
  have hqb : q * (b : ℚ) = ((q.num.toNat * b : ℕ) : ℚ) / (q.den : ℚ) := by
    calc
      q * (b : ℚ) = ((q.num.toNat : ℚ) / (q.den : ℚ)) * (b : ℚ) :=
        congrArg (fun t : ℚ => t * (b : ℚ)) hq'
      _ = _ := by push_cast; ring
  exact (congrArg (fun t : ℚ => ⌊t⌋₊) hqb).trans (Nat.floor_div_eq_div _ _)

private theorem perturbed_floor (q : ℚ) (hq : 0 ≤ q) (T b e : ℕ)
    (hT : 0 < T) (he : e < T) :
    ⌊((1 : ℚ) / (q.den * T : ℕ)) *
      ((q.num.toNat * T * b + e : ℕ) : ℚ)⌋₊ = ⌊q * (b : ℚ)⌋₊ := by
  have hd : 0 < q.den * T := Nat.mul_pos q.den_pos hT
  have hm : q.num.toNat * b % q.den < q.den := Nat.mod_lt _ q.den_pos
  have hr : (q.num.toNat * b % q.den) * T + e < q.den * T := by
    calc
      (q.num.toNat * b % q.den) * T + e <
          (q.num.toNat * b % q.den) * T + T := Nat.add_lt_add_left he _
      _ = (q.num.toNat * b % q.den + 1) * T := by ring
      _ ≤ q.den * T := Nat.mul_le_mul_right T (Nat.succ_le_of_lt hm)
  have hnum : q.num.toNat * T * b + e =
      (q.den * T) * (q.num.toNat * b / q.den) +
        ((q.num.toNat * b % q.den) * T + e) := by
    calc
      q.num.toNat * T * b + e = (q.num.toNat * b) * T + e := by ring
      _ = (q.num.toNat * b % q.den + q.den * (q.num.toNat * b / q.den)) * T + e :=
        (congrArg (fun z : ℕ => z * T + e) (Nat.mod_add_div (q.num.toNat * b) q.den)).symm
      _ = _ := by ring
  have hdiv : (q.num.toNat * T * b + e) / (q.den * T) = q.num.toNat * b / q.den := by
    rw [hnum, Nat.mul_add_div hd, Nat.div_eq_of_lt hr, Nat.add_zero]
  have hc : ((1 : ℚ) / (q.den * T : ℕ)) *
      ((q.num.toNat * T * b + e : ℕ) : ℚ) =
      ((q.num.toNat * T * b + e : ℕ) : ℚ) / (q.den * T : ℕ) := by ring
  rw [hc, Nat.floor_div_eq_div, hdiv, rational_floor q hq b]

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [FiniteType f] [IsSeparated f]
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
local notation "S" => NadelRelativePrincipalization.sequence f n I hI

/-- The original q and actual weighted exceptional ideal internally produce
an actual SNC numerator and positive denominator with exactly the SAME
original intrinsic rounded ideal. No factorization or comparison is supplied. -/
theorem exists_rounding_preserving_perturbation (w : Fin (S).length → ℕ)
    (q : ℚ) (hq : 0 ≤ q) :
    ∃ (N a : ℕ)
      (hK : ((I.comap (S).composite) ^ a * weightedIdeal f n I hI w).IsIdealOfSncDivisor),
      0 < N ∧ q.den ∣ N ∧ a * q.den = q.num.toNat * N ∧
      RoundedSncIdealSheaf.rounded
          ((I.comap (S).composite) ^ a * weightedIdeal f n I hI w) hK
          ((1 : ℚ) / (N : ℚ)) =
        RoundedSncIdealSheaf.rounded (I.comap (S).composite)
          (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) q := by
  classical
  let g := (S).composite ≫ f
  let : SmoothOfRelativeDimension n g :=
    NadelRelativePrincipalization.stage_smoothOfRelativeDimension f n I hI (Fin.last _)
  let : Smooth g := SmoothOfRelativeDimension.smooth n g
  let J := I.comap (S).composite
  let E := weightedIdeal f n I hI w
  obtain ⟨F, b, e, hF, hJ, hE⟩ := exists_common_snc_presentation f n I hI w
  let T := 1 + ∑ i, e i
  let N := q.den * T
  let a := q.num.toNat * T
  have hT : 0 < T := by dsimp only [T]; omega
  have he (i : F.ι) : e i < T := by
    have hi : e i ≤ ∑ j, e j := Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)
    dsimp only [T]
    omega
  have hKprod : J ^ a * E = ∏ i, F.component i ^ (a * b i + e i) := by
    change (I.comap (S).composite) ^ a * weightedIdeal f n I hI w = _
    rw [hJ, hE, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, ← pow_add, Nat.mul_comm (b i) a]
  have hK : (J ^ a * E).IsIdealOfSncDivisor := ⟨F, fun i => a * b i + e i, hF, hKprod⟩
  refine ⟨N, a, hK, Nat.mul_pos q.den_pos hT, ⟨T, rfl⟩, ?_, ?_⟩
  · change (q.num.toNat * T) * q.den = q.num.toNat * (q.den * T)
    ring
  · rw [RoundedSncIdealSheaf.rounded_eq_product g _ hK hF (fun i => a * b i + e i) hKprod,
      RoundedSncIdealSheaf.rounded_eq_product g _
        (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) hF b hJ]
    unfold RoundedSncIdealSheaf.product
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun m : ℕ => F.component i ^ m) (perturbed_floor q hq T (b i) (e i) hT (he i))

/-- The actual original perturbation denominator internally exceeds ANY
ordinary prescribed bound, while the literal original SNC numerator and
SAME intrinsic rounded-ideal equality are produced without certificates. -/
theorem exists_rounding_preserving_perturbation_ge (w : Fin (S).length → ℕ)
    (q : ℚ) (hq : 0 ≤ q) (lowerBound : ℕ) :
    ∃ (N a : ℕ)
      (hK : ((I.comap (S).composite) ^ a * weightedIdeal f n I hI w).IsIdealOfSncDivisor),
      0 < N ∧ lowerBound ≤ N ∧ q.den ∣ N ∧ a * q.den = q.num.toNat * N ∧
      RoundedSncIdealSheaf.rounded
          ((I.comap (S).composite) ^ a * weightedIdeal f n I hI w) hK
          ((1 : ℚ) / (N : ℚ)) =
        RoundedSncIdealSheaf.rounded (I.comap (S).composite)
          (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) q := by
  classical
  let g := (S).composite ≫ f
  let : SmoothOfRelativeDimension n g :=
    NadelRelativePrincipalization.stage_smoothOfRelativeDimension f n I hI (Fin.last _)
  let : Smooth g := SmoothOfRelativeDimension.smooth n g
  let J := I.comap (S).composite
  let E := weightedIdeal f n I hI w
  obtain ⟨F, b, e, hF, hJ, hE⟩ := exists_common_snc_presentation f n I hI w
  let T := (1 + ∑ i, e i) * (lowerBound + 1)
  let N := q.den * T
  let a := q.num.toNat * T
  have hbase : 0 < 1 + ∑ i, e i := by omega
  have hT : 0 < T := Nat.mul_pos hbase (Nat.succ_pos lowerBound)
  have hbaseT : 1 + ∑ i, e i ≤ T :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos lowerBound)
  have hboundT : lowerBound + 1 ≤ T := Nat.le_mul_of_pos_left _ hbase
  have hTN : T ≤ N := Nat.le_mul_of_pos_left _ q.den_pos
  have hboundN : lowerBound ≤ N := (Nat.le_succ lowerBound).trans (hboundT.trans hTN)
  have he (i : F.ι) : e i < T := by
    have hi : e i ≤ ∑ j, e j := Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)
    omega
  have hKprod : J ^ a * E = ∏ i, F.component i ^ (a * b i + e i) := by
    change (I.comap (S).composite) ^ a * weightedIdeal f n I hI w = _
    rw [hJ, hE, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, ← pow_add, Nat.mul_comm (b i) a]
  have hK : (J ^ a * E).IsIdealOfSncDivisor := ⟨F, fun i => a * b i + e i, hF, hKprod⟩
  refine ⟨N, a, hK, Nat.mul_pos q.den_pos hT, hboundN, ⟨T, rfl⟩, ?_, ?_⟩
  · change (q.num.toNat * T) * q.den = q.num.toNat * (q.den * T)
    ring
  · rw [RoundedSncIdealSheaf.rounded_eq_product g _ hK hF (fun i => a * b i + e i) hKprod,
      RoundedSncIdealSheaf.rounded_eq_product g _
        (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) hF b hJ]
    unfold RoundedSncIdealSheaf.product
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun m : ℕ => F.component i ^ m)
      (RelativeNadelCoverWeightedExceptionalRounding.perturbed_floor q hq T (b i) (e i) hT (he i))


end EnvelopeProperty.Vanishing.RelativeNadelCoverWeightedExceptionalRounding
