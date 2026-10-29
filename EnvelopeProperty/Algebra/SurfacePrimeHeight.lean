import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.Tactic

/-! # Actual nonzero nonmaximal primes on an original integral surface have height one -/
noncomputable section
namespace EnvelopeProperty.SurfacePrimeHeight
variable {R : Type*} [CommRing R] [IsDomain R]

/-- EVERY actual nonzero nonmaximal prime in an original dimension-at-most-two domain has height one. -/
theorem height_eq_one (hdim : ringKrullDim R ≤ 2) (P : Ideal R) [P.IsPrime]
    (hP0 : P ≠ ⊥) (hPmax : ¬ P.IsMaximal) : P.height = 1 := by
  let p : PrimeSpectrum R := ⟨P,inferInstance⟩
  have hsum : Order.height p + Order.coheight p ≤ 2 := by
    have hh : ((Order.height p + Order.coheight p : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim R := by
      change _ ≤ Order.krullDim (PrimeSpectrum R)
      rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
      exact WithBot.coe_le_coe.mpr (le_iSup (fun a : PrimeSpectrum R => Order.height a + Order.coheight a) p)
    exact WithBot.coe_le_coe.mp (hh.trans hdim)
  have hnmax : ¬ IsMax p := by
    intro hh
    exact hPmax (PrimeSpectrum.isMax_iff.mp hh)
  have hcn : Order.coheight p ≠ 0 := Order.coheight_ne_zero.mpr hnmax
  have hheight : Order.height p ≠ ⊤ := by
    intro hh
    simp [hh] at hsum
  have hcoheight : Order.coheight p ≠ ⊤ := by
    intro hh
    simp [hh] at hsum
  have hheight0 : Order.height p ≠ 0 := by
    intro hh
    have hp : P.height = 0 := (PrimeSpectrum.height_eq_orderHeight p).trans hh
    have hm := Ideal.height_eq_zero_iff.mp hp
    exact hP0 (by simpa only [IsDomain.minimalPrimes_eq_singleton_bot,Set.mem_singleton_iff] using hm)
  lift Order.height p to ℕ using hheight with n hn
  lift Order.coheight p to ℕ using hcoheight with m hm
  have hnm : n + m ≤ 2 := by exact_mod_cast hsum
  have hm0 : m ≠ 0 := by exact_mod_cast hcn
  have hn0 : n ≠ 0 := by exact_mod_cast hheight0
  have hn1 : n = 1 := by omega
  change p.asIdeal.height = 1
  rw [PrimeSpectrum.height_eq_orderHeight]
  rw [← hn]
  exact_mod_cast hn1

end EnvelopeProperty.SurfacePrimeHeight
