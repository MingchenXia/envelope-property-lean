import EnvelopeProperty.AlgGeom.NativeLineFSPowerComparison

/-! # Exact denominator division and rational constant recovery on the original ray

Class arithmetic for the native finite rational Fubini--Study functions
`NativeLineFubiniStudy.IsFinFS p L hL a φ` of an invertible module `L` on a proper
`k`-scheme (FHX §2.2, `eq:FS-function`: `φ = m⁻¹ max_j (log |s_j| + λ_j)`; the analogous
constructions for the projective-space data `ProjBerk.FSData` are `ProjBerk.FSData.smul` and
`ProjBerk.FSData.const`).

* `IsFinFS.divideDenominator`: if `φ = m⁻¹ max_j (log |s_j| + λ_j)` with `s_j` sections of
  `L^{deg}`, `deg = m a`, then `N⁻¹ φ = (m N)⁻¹ max_j (log |s_j| + λ_j)` is a finite FS
  function of class `a / N`, realized by the SAME sections and weights.
* `IsFinFS.addRational`: `φ + c = m⁻¹ max_j (log |s_j| + (λ_j + m c))`, so adding a rational
  constant keeps the class, the sections, and rationality of the weights.

These are the two operations needed to pass from the exact finite FS realization of
`b · pot(M) + a · pot(H)` (class `1` for `L^b ⊗ K^a`) to `pot(M) + (a/b) pot(H)` (class `1/b`).
-/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
open scoped Classical NNReal ENNReal
noncomputable section
universe u
namespace EnvelopeProperty.NativeLineFubiniStudy
open Berkovich CanonicalGeometry SchemeGlobalSectionModelNormIsometries
variable {k : Type u} [Field k] {X : Scheme.{u}}
    {L : X.Modules} {a : ℚ}

/-- Divide the exact original class and entire function by a positive
natural denominator, keeping ALL original sections, degrees and weights. -/
def FSData.divideDenominator (D : FSData L a) (N : ℕ) (hN : 0 < N) :
    FSData L (a / (N : ℚ)) where
  m := D.m * N
  m_pos := Nat.mul_pos D.m_pos hN
  deg := D.deg
  deg_eq := by rw [D.deg_eq, Nat.cast_mul]; field_simp [Nat.ne_of_gt hN]
  terms := D.terms

variable (p : X ⟶ Spec (.of k)) [IsProper p] (hL : IsInvertible L)

/-- The entire original weighted evaluation is divided by N, including
all infinite values; no point or section is replaced. -/
theorem FSData.divideDenominator_eval (D : FSData L a) (N : ℕ) (hN : 0 < N)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
    (D.divideDenominator N hN).eval p hL y =
      (((N : ℝ)⁻¹ : ℝ) : EReal) * D.eval p hL y := by
  change ((((D.m * N : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * _ =
    (((N : ℝ)⁻¹ : ℝ) : EReal) * ((((D.m : ℝ)⁻¹ : ℝ) : EReal) * _)
  rw [ProjBerk.ereal_coe_mul_coe_mul, Nat.cast_mul, mul_inv_rev]
  rfl

/-- Original rational weights remain literally unchanged. -/
theorem FSData.IsRational.divideDenominator {D : FSData L a} (hD : D.IsRational)
    (N : ℕ) (hN : 0 < N) : (D.divideDenominator N hN).IsRational := hD

/-- Exact finite FS denominator division retains the SAME original whole
sections and their actual absence of common zeros at every original point. -/
theorem IsFinFS.divideDenominator (N : ℕ) (hN : 0 < N)
    {phi : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (hphi : IsFinFS p L hL a phi) :
    IsFinFS p L hL (a / (N : ℚ)) (fun y => (((N : ℝ)⁻¹ : ℝ) : EReal) * phi y) := by
  obtain ⟨D, hD, hNZ, hphi⟩ := hphi
  refine ⟨D.divideDenominator N hN, hD.divideDenominator N hN, hNZ, ?_⟩
  intro y
  exact (congrArg (fun z : EReal => (((N : ℝ)⁻¹ : ℝ) : EReal) * z) (hphi y)).trans
    (D.divideDenominator_eval p hL N hN y).symm

/-- Add m*c to the actual original weights, preserving all original
whole sections, their degree, positive denominator and exact original class. -/
def FSData.shiftWeights (D : FSData L a) (c : ℝ) : FSData L a where
  m := D.m
  m_pos := D.m_pos
  deg := D.deg
  deg_eq := D.deg_eq
  terms := D.terms.image fun q => (q.1, q.2 + (D.m : ℝ) * c)

/-- The actual rational weight shift adds the SAME constant to the
entire original function, including the empty supremum and zero sections. -/
theorem FSData.shiftWeights_eval (D : FSData L a) (c : ℝ)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
    (D.shiftWeights c).eval p hL y = D.eval p hL y + (c : EReal) := by
  let term := fun q : Γ(bundleTensorPower L D.deg, ⊤) × ℝ =>
    ENNReal.log (globalSectionNorm _root_.Valuation.one_apply_le_one y (bundleTensorPower L D.deg)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg) q.1 : ℝ≥0∞) + (q.2 : EReal)
  have hs : (D.terms.image fun q => (q.1, q.2 + (D.m : ℝ) * c)).sup term =
      D.terms.sup term + (((D.m : ℝ) * c : ℝ) : EReal) := by
    rw [Finset.sup_image, Finset.apply_sup_eq_sup_comp_of_linearOrder (s := D.terms)
      (fun z : EReal => z + (((D.m : ℝ) * c : ℝ) : EReal))
      (fun _ _ h => add_le_add_left h _) (EReal.bot_add _)]
    refine Finset.sup_congr rfl fun q _ => ?_
    simp only [Function.comp_apply, term, EReal.coe_add, add_assoc]
  change (((D.m : ℝ)⁻¹ : ℝ) : EReal) *
    (D.terms.image fun q => (q.1, q.2 + (D.m : ℝ) * c)).sup term =
    (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup term + (c : EReal)
  rw [hs,
    ProjBerk.ereal_coe_mul_add (inv_nonneg.mpr (Nat.cast_nonneg D.m)),
    ← EReal.coe_mul, ← mul_assoc,
    inv_mul_cancel₀ (show (D.m : ℝ) ≠ 0 by exact_mod_cast D.m_pos.ne'), one_mul]

/-- A rational constant changes each original rational weight by the
literal rational m*c, with no section change. -/
theorem FSData.IsRational.shiftWeights {D : FSData L a} (hD : D.IsRational) (c : ℚ) :
    (D.shiftWeights (c : ℝ)).IsRational := by
  intro q hq
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨b, hb⟩ := hD t ht
  exact ⟨b + (D.m : ℚ) * c, by simp only [hb, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]⟩

/-- Recover the SAME rational constant by actual original finite weights;
the original whole sections still witness no common zero at every point. -/
theorem IsFinFS.addRational (c : ℚ)
    {phi : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (hphi : IsFinFS p L hL a phi) :
    IsFinFS p L hL a (fun y => phi y + ((c : ℝ) : EReal)) := by
  obtain ⟨D, hD, hNZ, hphi⟩ := hphi
  refine ⟨D.shiftWeights (c : ℝ), hD.shiftWeights c, ?_, ?_⟩
  · intro y
    obtain ⟨q, hq, hq0⟩ := hNZ y
    exact ⟨_, Finset.mem_image.mpr ⟨q, hq, rfl⟩, hq0⟩
  · intro y
    exact (congrArg (fun z : EReal => z + ((c : ℝ) : EReal)) (hphi y)).trans
      (D.shiftWeights_eval p hL (c : ℝ) y).symm

end EnvelopeProperty.NativeLineFubiniStudy
