import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceBoundedWedge
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # The actual selected original root powers divide the native top differential

The full active-root factor is already proved. The SAME whole mixed algebra
internally makes inactive roots units, so every selected root exponent below
its original degree can be retained in the actual top differential factor.
This is the algebra step needed for the whole original rounded row ideal.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped BigOperators
universe u v
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalSelectedPowers
open CanonicalGeometry NadelMixedKummer NadelCanonicalMixed NadelCanonicalBaseChange
open NadelGlobalCanonicalTrace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)
attribute [local instance] Classical.propDecidable
local notation "Bₘ" => mixedRing x N I σ u

private theorem inactiveRoot_isUnit (hN : ∀ i, 0 < N i)
    (i : Fin q) (hi : i ∉ I) :
    IsUnit (root N (mixedCoefficient x I σ u) i) := by
  have hp : IsUnit (root N (mixedCoefficient x I σ u) i ^ N i) := by
    rw [root_pow]
    simpa only [mixedCoefficient, dif_neg hi] using
      (u i).isUnit.map (algebraMap A Bₘ)
  exact (isUnit_pow_iff (Nat.ne_of_gt (hN i))).mp hp

/-- The literal product of ANY selected original root powers below their
actual original degrees divides the SAME full original active root factor.
Inactive roots are proved units internally; no selected-root regularity or
desired monomial-divisibility premise is supplied. -/
theorem selectedRootProduct_dvd_activeRootProduct
    (hN : ∀ i, 0 < N i) {E : Type v} [Fintype E]
    (h : E ↪ Fin q) (a : E → ℕ) (ha : ∀ i, a i < N (h i)) :
    (∏ i, root N (mixedCoefficient x I σ u) (h i) ^ a i) ∣
      ∏ i : I, root N (mixedCoefficient x I σ u) i.1 ^ (N i.1 - 1) := by
  classical
  let f : Fin q → Bₘ := fun j =>
    if j ∈ I then root N (mixedCoefficient x I σ u) j ^ (N j - 1) else 1
  have hpoint (i : E) : root N (mixedCoefficient x I σ u) (h i) ^ a i ∣ f (h i) := by
    by_cases hi : h i ∈ I
    · dsimp only [f]
      rw [if_pos hi]
      exact pow_dvd_pow _ (by have := ha i; omega)
    · dsimp only [f]
      rw [if_neg hi]
      exact ((inactiveRoot_isUnit x N I σ u hN (h i) hi).pow (a i)).dvd
  have hprod : (∏ i, root N (mixedCoefficient x I σ u) (h i) ^ a i) ∣
      ∏ i, f (h i) :=
    Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hpoint i)
  let S : Finset (Fin q) := Finset.univ.image h
  have hS : (∏ i, f (h i)) = ∏ j ∈ S, f j := by
    dsimp only [S]
    rw [Finset.prod_image]
    intro i _ j _ hij
    exact h.injective hij
  have hrest : (∏ j ∈ S, f j) ∣ ∏ j, f j :=
    ⟨∏ j ∈ Sᶜ, f j, (Finset.prod_mul_prod_compl S f).symm⟩
  have hactive : (∏ j, f j) =
      ∏ i : I, root N (mixedCoefficient x I σ u) i.1 ^ (N i.1 - 1) := by
    apply Finset.prod_congr_set I f
    · intro j hj
      exact if_pos hj
    · intro j hj
      exact if_neg hj
  rw [hS] at hprod
  rw [← hactive]
  exact hprod.trans hrest

/-- The actual original pulled coordinate top form retains the entire
selected-root monomial, including original inactive unit-root factors.
This uses the proved full native wedge and original root-unit equations. -/
theorem mixedCoordinateTopDifferential_selected_factor
    (hN : ∀ i, 0 < N i) {E : Type v} [Fintype E]
    (h : E ↪ Fin q) (a : E → ℕ) (ha : ∀ i, a i < N (h i)) :
    ∃ w : affineCanonicalModule k Bₘ n,
      topPullback (R := k) (A := A) (B := Bₘ) n
        (exteriorPower.ιMulti A n (fun j => KaehlerDifferential.D k A (x j))) =
      (∏ i, root N (mixedCoefficient x I σ u) (h i) ^ a i) • w := by
  obtain ⟨w, hw⟩ := mixedCoordinateTopDifferential_factor (k := k) x N I σ u hN
  obtain ⟨c, hc⟩ := selectedRootProduct_dvd_activeRootProduct x N I σ u hN h a ha
  refine ⟨c • w, ?_⟩
  have hs := mul_smul (α := Bₘ) (β := affineCanonicalModule k Bₘ n)
    (∏ i, root N (mixedCoefficient x I σ u) (h i) ^ a i) c w
  exact hw.trans ((congrArg (fun t : Bₘ => t • w) hc).trans hs)

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalSelectedPowers
