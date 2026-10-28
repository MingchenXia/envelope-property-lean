import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingFinite
import Mathlib.RingTheory.Trace.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

/-! # The genuine degree of every original factor and its relative trace

The whole original varying-root basis fixes the positive degree. After any
coefficient extension the trace is relative to the new coefficient ring,
so the auxiliary coefficient-cover degree never enters the normalization.
-/

noncomputable section
universe u v

namespace EnvelopeProperty.Vanishing.NadelWholeCoverDegree

open NadelMixedKummer NadelAdaptedChartMatching
open scoped TensorProduct

variable {q : ℕ} (N : Fin q → ℕ)

/-- Every original root factor contributes its actual degree. -/
def degree : ℕ := ∏ i, N i

/-- The original degree is positive even for the empty family. -/
theorem degree_pos (hN : ∀ i, 0 < N i) : 0 < degree N :=
  Finset.prod_pos fun i _ => hN i

/-- Cardinality of the actual whole original monic basis. -/
theorem basisIndex_card (hN : ∀ i, 0 < N i) :
    Nat.card (NadelKummerCover.Tower.basisIndex (VaryingFamily.degree N) q) = degree N := by
  rw [NadelKummerCover.Tower.basisIndex_card,
    ← Fin.prod_univ_eq_prod_range (fun i => VaryingFamily.degree N i + 1) q]
  exact Finset.prod_congr rfl fun i _ => VaryingFamily.degree_eq N hN i

variable {R : Type u} [CommRing R] [Nontrivial R] (c : Fin q → R)
    (hN : ∀ i, 0 < N i)

include hN

/-- Rank is the same positive degree of the whole quotient, without a domain
or connectedness hypothesis on the original algebra. -/
theorem finrank_eq_degree : Module.finrank R (Ring N c) = degree N := by
  let := NadelKummerCover.Tower.basisIndex_finite (VaryingFamily.degree N) q
  let := Fintype.ofFinite (NadelKummerCover.Tower.basisIndex (VaryingFamily.degree N) q)
  rw [Module.finrank_eq_card_basis (VaryingFinite.basis N c hN),
    ← Nat.card_eq_fintype_card, basisIndex_card N hN]

/-- Native algebra trace on every original scalar retains every root factor. -/
theorem trace_algebraMap (r : R) :
    Algebra.trace R (Ring N c) (algebraMap R (Ring N c) r) = degree N • r := by
  let := NadelKummerCover.Tower.basisIndex_finite (VaryingFamily.degree N) q
  let := Fintype.ofFinite (NadelKummerCover.Tower.basisIndex (VaryingFamily.degree N) q)
  rw [Algebra.trace_algebraMap_of_basis (VaryingFinite.basis N c hN),
    ← Nat.card_eq_fintype_card, basisIndex_card N hN]

/-- The native trace of one is the original degree. -/
theorem trace_one : Algebra.trace R (Ring N c) 1 = (degree N : R) := by
  simpa only [map_one, nsmul_eq_mul, mul_one] using trace_algebraMap N c hN 1

variable (S : Type v) [CommRing S] [Algebra R S]

/-- The actual entire scalar extension has its trace relative to S, with
the original degree, not the auxiliary degree of S over R. -/
theorem baseChange_trace_scalar (s : S) :
    Algebra.trace S (S ⊗[R] Ring N c) (s • (1 : S ⊗[R] Ring N c)) = degree N • s := by
  let := NadelKummerCover.Tower.basisIndex_finite (VaryingFamily.degree N) q
  let := Fintype.ofFinite (NadelKummerCover.Tower.basisIndex (VaryingFamily.degree N) q)
  have h := Algebra.trace_algebraMap_of_basis (R := S) (S := S ⊗[R] Ring N c)
    ((VaryingFinite.basis N c hN).baseChange S) s
  simpa only [Algebra.algebraMap_eq_smul_one, ← Nat.card_eq_fintype_card,
    basisIndex_card N hN] using h

/-- No auxiliary-cover rank appears in the actual trace of one. -/
theorem baseChange_trace_one :
    Algebra.trace S (S ⊗[R] Ring N c) 1 = (degree N : S) := by
  simpa only [one_smul, nsmul_eq_mul, mul_one] using baseChange_trace_scalar N c hN S 1

omit [Nontrivial R] in
/-- The genuine original positive degree is invertible over the original
characteristic-zero field, through its actual coefficient algebra map. -/
theorem degree_isUnit {k : Type v} [Field k] [CharZero k] [Algebra k R] :
    IsUnit (degree N : R) := by
  have h : IsUnit (degree N : k) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (degree_pos N hN)))
  simpa only [map_natCast] using h.map (algebraMap k R)

end EnvelopeProperty.Vanishing.NadelWholeCoverDegree
