/-
Mathlib-only proof port. Original source: BingWangEntropy/BingWangEntropy/ValuationIdeals.lean
Upstream SHA256: 1d617d82da8ba43973601439eb3349ae8c2fb5568c370705ed0a5f9639661234
Upstream canonical-source commit: feaaab87c3197e6e4f18c6176d50b5c739c81b50
Compatibility changes: module imports and enclosing namespace only.
Original mathematical statements and proofs below are preserved.
-/
import EnvelopeProperty.AlgGeom.Canonical.ValuationFiltration
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Actual valuation ideals and finite-piece colengths

The ideal at threshold `a` is defined by the valuation inequality on the ring,
not by prescribed weights or colengths. Nonnegativity on that ring makes it an
ideal. Its kernel on a section-representative space is the actual threshold
filtration. Rank-nullity therefore computes the contribution of that finite
piece to the quotient. Global section-ring construction and finiteness of the
full cone quotient remain separate geometric obligations.
-/

namespace EnvelopeProperty.CanonicalGeometry

section Ideals

variable {R F : Type*} [CommRing R] [Field F]

/-- The literal valuation ideal on a ring where the valuation is nonnegative. -/
def valuationIdeal (v : AddValuation F (WithTop ℝ)) (f : R →+* F)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r)) (a : ℝ) : Ideal R where
  carrier := {r | (a : WithTop ℝ) ≤ v (f r)}
  zero_mem' := by simp
  add_mem' := by
    intro r s hr hs
    change (a : WithTop ℝ) ≤ v (f (r + s))
    rw [map_add]
    exact v.map_le_add hr hs
  smul_mem' := by
    intro r s hs
    change (a : WithTop ℝ) ≤ v (f (r * s))
    rw [map_mul, v.map_mul]
    exact hs.trans (le_add_of_nonneg_left (hcenter r))

@[simp]
theorem mem_valuationIdeal (v : AddValuation F (WithTop ℝ)) (f : R →+* F)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r)) (a : ℝ) (r : R) :
    r ∈ valuationIdeal v f hcenter a ↔ (a : WithTop ℝ) ≤ v (f r) := Iff.rfl

/-- Higher thresholds give smaller ideals. -/
theorem valuationIdeal_antitone (v : AddValuation F (WithTop ℝ)) (f : R →+* F)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r)) :
    Antitone (valuationIdeal v f hcenter) := by
  intro a b hab r hr
  exact (WithTop.coe_le_coe.mpr hab).trans hr

/-- The threshold ideal is the whole ring exactly at nonpositive thresholds. -/
theorem valuationIdeal_eq_top_iff (v : AddValuation F (WithTop ℝ)) (f : R →+* F)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r)) (a : ℝ) :
    valuationIdeal v f hcenter a = ⊤ ↔ a ≤ 0 := by
  rw [Ideal.eq_top_iff_one, mem_valuationIdeal, map_one, v.map_one]
  exact WithTop.coe_le_coe

/-- A positive threshold produces a proper ideal. -/
theorem valuationIdeal_ne_top (v : AddValuation F (WithTop ℝ)) (f : R →+* F)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r)) {a : ℝ} (ha : 0 < a) :
    valuationIdeal v f hcenter a ≠ ⊤ := by
  intro h
  exact (not_le.mpr ha) ((valuationIdeal_eq_top_iff v f hcenter a).mp h)

/-- Products of actual threshold ideals add their thresholds. -/
theorem valuationIdeal_mul_le (v : AddValuation F (WithTop ℝ)) (f : R →+* F)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r)) (a b : ℝ) :
    valuationIdeal v f hcenter a * valuationIdeal v f hcenter b ≤
      valuationIdeal v f hcenter (a + b) := by
  apply Ideal.mul_le.mpr
  intro r hr s hs
  change ((a + b : ℝ) : WithTop ℝ) ≤ v (f (r * s))
  rw [map_mul]
  exact valuation_product_threshold v hr hs

/-- The center's actual positive-valuation ideal. -/
def positiveValuationIdeal (v : AddValuation F (WithTop ℝ)) (f : R →+* F)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r)) : Ideal R where
  carrier := {r | (0 : WithTop ℝ) < v (f r)}
  zero_mem' := by simp
  add_mem' := by
    intro r s hr hs
    change (0 : WithTop ℝ) < v (f (r + s))
    rw [map_add]
    exact v.map_lt_add hr hs
  smul_mem' := by
    intro r s hs
    change (0 : WithTop ℝ) < v (f (r * s))
    rw [map_mul, v.map_mul]
    exact hs.trans_le (le_add_of_nonneg_left (hcenter r))

@[simp]
theorem mem_positiveValuationIdeal (v : AddValuation F (WithTop ℝ)) (f : R →+* F)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r)) (r : R) :
    r ∈ positiveValuationIdeal v f hcenter ↔ (0 : WithTop ℝ) < v (f r) := Iff.rfl

/-- The positive-valuation ideal really is prime; no chosen center is input. -/
theorem positiveValuationIdeal_isPrime (v : AddValuation F (WithTop ℝ)) (f : R →+* F)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r)) :
    (positiveValuationIdeal v f hcenter).IsPrime := by
  constructor
  · intro htop
    have h := (Ideal.eq_top_iff_one _).mp htop
    simp only [mem_positiveValuationIdeal, map_one, v.map_one, lt_self_iff_false] at h
  · intro r s hrs
    by_contra h
    simp only [not_or, mem_positiveValuationIdeal] at h
    have hr : v (f r) = 0 := le_antisymm (not_lt.mp h.1) (hcenter r)
    have hs : v (f s) = 0 := le_antisymm (not_lt.mp h.2) (hcenter s)
    change (0 : WithTop ℝ) < v (f (r * s)) at hrs
    rw [map_mul, v.map_mul, hr, hs, zero_add] at hrs
    exact (lt_irrefl _) hrs

/-- The ordinary quotient map kills exactly the actual threshold elements. -/
theorem valuationIdeal_quotient_eq_zero_iff (v : AddValuation F (WithTop ℝ))
    (f : R →+* F) (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r)) (a : ℝ) (r : R) :
    Ideal.Quotient.mk (valuationIdeal v f hcenter a) r = 0 ↔
      (a : WithTop ℝ) ≤ v (f r) := by
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_valuationIdeal]

end Ideals

section FinitePieces

variable {K R F V : Type*} [Field K] [CommRing R] [Field F]
  [Algebra K R] [Algebra K F] [AddCommGroup V] [Module K V]

/-- The actual section-piece map into the quotient by the valuation ideal. -/
noncomputable def valuationPieceQuotientMap (v : AddValuation F (WithTop ℝ))
    (f : R →ₐ[K] F) (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r))
    (ι : V →ₗ[K] R) (a : ℝ) :
    V →ₗ[K] R ⧸ valuationIdeal v f.toRingHom hcenter a :=
  (Ideal.Quotient.mkₐ K (valuationIdeal v f.toRingHom hcenter a)).toLinearMap.comp ι

/-- Its kernel is the threshold filtration on the actual section representatives. -/
theorem valuationPieceQuotientMap_ker (v : AddValuation F (WithTop ℝ))
    (f : R →ₐ[K] F) (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r))
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (ι : V →ₗ[K] R) (a : ℝ) :
    LinearMap.ker (valuationPieceQuotientMap v f hcenter ι a) =
      valuationFiltration v (f.toLinearMap.comp ι) htrivial a := by
  ext s
  change Ideal.Quotient.mk (valuationIdeal v f.toRingHom hcenter a) (ι s) = 0 ↔
    (a : WithTop ℝ) ≤ v (f (ι s))
  exact valuationIdeal_quotient_eq_zero_iff v f.toRingHom hcenter a (ι s)

/-- The finite-piece quotient dimension is derived by rank-nullity, without
assuming a dimension formula or finite colength for the entire cone ring. -/
theorem valuationPiece_colength_add_filtration [FiniteDimensional K V]
    (v : AddValuation F (WithTop ℝ)) (f : R →ₐ[K] F)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r))
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (ι : V →ₗ[K] R) (a : ℝ) :
    Module.finrank K (LinearMap.range (valuationPieceQuotientMap v f hcenter ι a)) +
      Module.finrank K (valuationFiltration v (f.toLinearMap.comp ι) htrivial a) =
        Module.finrank K V := by
  rw [← valuationPieceQuotientMap_ker v f hcenter htrivial ι a]
  exact LinearMap.finrank_range_add_finrank_ker (valuationPieceQuotientMap v f hcenter ι a)

end FinitePieces

end EnvelopeProperty.CanonicalGeometry
