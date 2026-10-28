import EnvelopeProperty.Cartier.DVR
import EnvelopeProperty.Cartier.Polynomial

/-!
# The Frobenius trace estimate at a divisorial valuation (FHX Lemma 3.3, (3.11))

Let `k` be a perfect field of characteristic `p`, `F` a field with a `p`-basis `y`, and `R ⊆ F` a DVR
essentially of finite type over `k` with fraction field `F`, uniformizer `ϖ`, containing the `y_i`
(`y_i = y'_i ∈ R`). Let `u` be a `p`-basis of `R` (it exists by
`EnvelopeProperty.Cartier.exists_isPBasis_of_essFiniteType`) and
`J = J(y/u) = det(∂y_i/∂u_j) ∈ R`, so that `dy_1 ∧ ⋯ ∧ dy_m = J du_1 ∧ ⋯ ∧ du_m` and `ξ = du` generates
the regular top forms at `R`. Then `J ≠ 0`; its order `a = ord_R J ≥ 0` does not depend on `u`
(`IsPBasis.jac_associated`), and `A(ord_R) = 1 + a` is the log discrepancy of `ord_R` with respect to
the coordinates `y`. The main results are

* `ordGE_trace_of_jac`: `ord_R(Φ_y f) ≥ ⌊(ord_R f + a)/p⌋ - a`;
* `ordGE_traceIter_of_jac`: `ord_R(Φ_y^e f) ≥ ⌊(ord_R f + a)/p^e⌋ - a` for every `e`;
* `exists_logDiscrepancy`: the packaged statement with the existence of `u` and `a`;
* `ordGE_polyTrace_of_jac`, `exists_logDiscrepancy_polynomial`: the case `F = Frac k[y]` and
  `Φ_e` the polynomial Frobenius trace (FHX eq. (3.6)), i.e. FHX (3.11) for `w = ord_R`:
  `ord_R(Φ_e f) ≥ ⌊(ord_R f + a)/p^e⌋ - a ≥ (ord_R f - (p^e - 1)(a + 1))/p^e`
  (the last step is `sub_mul_succ_le_mul_ediv_sub`);
* `le_scaled_of_ordGE`: the version for `w = r · ord_R`, `r > 0` (real numbers), with
  `A(w) = r (1 + a)`.

Proof (FHX, proof of Lemma 3.3): by the independence of the Cartier operator
(`IsPBasis.trace_eq_trace_jac_pow_mul`), `Φ_u = Φ_y(J^{p-1} ·)`, and `Φ_u(R) ⊆ R` since `u` is a
`p`-basis of `R`. Hence `Φ_y(ϖ^{(p-1)a} R) ⊆ R`, which gives the one-step bound by
`ordGE_trace_of_bound`, and the bound for `Φ_y^e` by iteration (`ordGE_traceIter_of_step`).
-/

noncomputable section

open scoped NNReal ENNReal Topology

namespace EnvelopeProperty.Cartier

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Compatibility with ring homomorphisms -/

section Map

variable {A B : Type*} [CommRing A] [CommRing B] [CharP A p] [CharP B p] (φ : A →+* B)
  {σ : Type*} [Fintype σ] [DecidableEq σ] {y : σ → A} (hy : IsPBasis p y)
  (hφy : IsPBasis p (φ ∘ y))

include hy

theorem IsPBasis.coeff_map (f : A) : hφy.coeff (φ f) = φ ∘ hy.coeff f := by
  apply hφy.coeff_eq_of_sum_eq
  rw [← pSum_apply, ← map_pSum, hy.pSum_coeff]

theorem IsPBasis.trace_map (f : A) : hφy.trace (φ f) = φ (hy.trace f) := by
  rw [trace_apply, trace_apply, hy.coeff_map φ hφy]
  rfl

theorem IsPBasis.pderiv_map (i : σ) (f : A) : hφy.pderiv i (φ f) = φ (hy.pderiv i f) := by
  rw [pderiv_apply, pderiv_apply, pderivFun, pderivFun, hy.coeff_map φ hφy, map_sum]
  refine sum_congr rfl fun a _ => ?_
  simp [map_mono]

theorem IsPBasis.jac_map (y' : σ → A) : hφy.jac (φ ∘ y') = φ (hy.jac y') := by
  rw [jac, jac, RingHom.map_det]
  congr 1
  ext i j
  simp [hy.pderiv_map φ hφy]

end Map

/-! ### Independence of the order of the Jacobian -/

section Jacobian

variable {R : Type*} [CommRing R] [CharP R p] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The Jacobians of a family with respect to two `p`-bases differ by a unit. -/
theorem IsPBasis.jac_associated {u u' : σ → R} (hu : IsPBasis p u) (hu' : IsPBasis p u')
    (y : σ → R) : Associated (hu.jac y) (hu'.jac y) := by
  obtain ⟨w, hw⟩ := isUnit_jac hu' hu
  exact ⟨w, by rw [hw, ← jac_mul]⟩

end Jacobian

/-! ### The trace estimate -/

section Estimate

variable {R F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharP R p] [Field F]
  [Algebra R F] [IsFractionRing R F] [CharP F p] {σ : Type*} [Fintype σ] [DecidableEq σ]
  {u y' : σ → R} (hu : IsPBasis p u) (hy : IsPBasis p (algebraMap R F ∘ y')) {ϖ : R}
  (hϖ : Irreducible ϖ)

include hu hy hϖ

set_option linter.unusedSectionVars false in
omit [IsDiscreteValuationRing R] hϖ in
/-- The Jacobian `J(y/u)` is nonzero. -/
theorem jac_ne_zero : hu.jac y' ≠ 0 := by
  intro h0
  have huF := hu.map_of_isFractionRing (K := F)
  have h1 := IsPBasis.isUnit_jac huF hy
  rw [hu.jac_map (algebraMap R F) huF y', h0, map_zero] at h1
  exact not_isUnit_zero h1

/-- The Jacobian is `v ϖ^a` with `v` a unit and `a = ord_R J ≥ 0`. -/
theorem exists_jac_eq_unit_mul_pow : ∃ (a : ℕ) (v : Rˣ), hu.jac y' = v * ϖ ^ a := by
  obtain ⟨a, v, h⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (jac_ne_zero hu hy) hϖ
  exact ⟨a, v, h⟩

omit [IsDiscreteValuationRing R] in
/-- **One-step trace estimate.** With `J(y/u) = v ϖ^a`:
`ord_R(Φ_y f) ≥ ⌊(ord_R f + a)/p⌋ - a`. -/
theorem ordGE_trace_of_jac {a : ℕ} {v : Rˣ} (hJ : hu.jac y' = v * ϖ ^ a) {n : ℤ} {f : F}
    (hf : OrdGE ϖ n f) : OrdGE ϖ ((n + a) / p - a) (hy.trace f) := by
  have hϖ0 := algebraMap_uniformizer_ne_zero (F := F) hϖ
  have huF := hu.map_of_isFractionRing (K := F)
  -- `Φ_y(ϖ^{(p-1)a} R) ⊆ R`
  have hbound : ∀ g : F, OrdGE ϖ (((p - 1) * a : ℕ) : ℤ) g → OrdGE ϖ 0 (hy.trace g) := by
    rintro g ⟨r, rfl⟩
    have hJF : huF.jac (algebraMap R F ∘ y') = algebraMap R F ((v : R) * ϖ ^ a) := by
      rw [hu.jac_map (algebraMap R F) huF y', hJ]
    have hg : algebraMap R F ϖ ^ (((p - 1) * a : ℕ) : ℤ) * algebraMap R F r =
        huF.jac (algebraMap R F ∘ y') ^ (p - 1) *
          algebraMap R F ((↑v⁻¹ : R) ^ (p - 1) * r) := by
      rw [hJF, zpow_natCast, ← map_pow, ← map_pow, ← map_mul, ← map_mul]
      congr 1
      have hvv : (v : R) ^ (p - 1) * (↑v⁻¹ : R) ^ (p - 1) = 1 := by
        rw [← mul_pow, Units.mul_inv, one_pow]
      rw [mul_pow, ← pow_mul, mul_comm a (p - 1)]
      linear_combination (-(ϖ ^ ((p - 1) * a) * r)) * hvv
    rw [hg, ← hy.trace_eq_trace_jac_pow_mul huF, hu.trace_map (algebraMap R F) huF]
    exact ordGE_algebraMap _
  have h := ordGE_trace_of_bound p hy hϖ0 hbound hf
  convert h using 2
  push_cast
  rw [show n - (p - 1 : ℕ) * (a : ℤ) = n + a + (-(a : ℤ)) * p by
    rw [Nat.cast_sub hp.out.one_lt.le]; push_cast; ring,
    Int.add_mul_ediv_right _ _ (by exact_mod_cast hp.out.ne_zero)]
  ring

omit [IsDiscreteValuationRing R] in
/-- **Trace estimate for all `e`** (FHX, first display of the proof of Lemma 3.3): with
`J(y/u) = v ϖ^a`, `ord_R(Φ_y^e f) ≥ ⌊(ord_R f + a)/p^e⌋ - a`. -/
theorem ordGE_traceIter_of_jac {a : ℕ} {v : Rˣ} (hJ : hu.jac y' = v * ϖ ^ a) (e : ℕ) {n : ℤ}
    {f : F} (hf : OrdGE ϖ n f) : OrdGE ϖ ((n + a) / (p ^ e : ℕ) - a) (hy.traceIter e f) :=
  ordGE_traceIter_of_step p hy (fun _ _ hf => ordGE_trace_of_jac hu hy hϖ hJ hf) e hf

end Estimate

/-! ### Packaged statements -/

section Packaged

variable {R F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharP R p] [Field F]
  [Algebra R F] [IsFractionRing R F] [CharP F p] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **The log discrepancy bound** (FHX Lemma 3.3, first display of the proof). Let `R` be a DVR
essentially of finite type over a perfect field `k` of characteristic `p`, with fraction field `F`
and uniformizer `ϖ`, and let `y = y'` be a `p`-basis of `F` consisting of elements of `R`. There are
a `p`-basis `u` of `R`, `a : ℕ` and a unit `v` with `J(y/u) = v ϖ^a` (so `a = ord_R(dy/du)` and
`A(ord_R) = 1 + a`), such that for all `e`, `n` and `f ∈ F`, `ord_R f ≥ n` implies
`ord_R(Φ_y^e f) ≥ ⌊(n + a)/p^e⌋ - a`. -/
theorem exists_logDiscrepancy (k : Type*) [Field k] [CharP k p] [PerfectRing k p] [Algebra k R]
    [Algebra.EssFiniteType k R] {y' : σ → R} (hy : IsPBasis p (algebraMap R F ∘ y')) {ϖ : R}
    (hϖ : Irreducible ϖ) :
    ∃ (u : σ → R) (hu : IsPBasis p u) (a : ℕ) (v : Rˣ), hu.jac y' = v * ϖ ^ a ∧
      ∀ (e : ℕ) (n : ℤ) (f : F), OrdGE ϖ n f →
        OrdGE ϖ ((n + a) / (p ^ e : ℕ) - a) (hy.traceIter e f) := by
  obtain ⟨u, hu, -⟩ := exists_isPBasis_of_essFiniteType k hy hϖ
  obtain ⟨a, v, hJ⟩ := exists_jac_eq_unit_mul_pow hu hy hϖ
  exact ⟨u, hu, a, v, hJ, fun e n f hf => ordGE_traceIter_of_jac hu hy hϖ hJ e hf⟩

end Packaged

/-! ### Polynomial rings -/

section Polynomial

variable {k : Type*} [Field k] [CharP k p] [PerfectRing k p] {σ : Type*} [Fintype σ]
  [DecidableEq σ] {F : Type*} [Field F] [Algebra (MvPolynomial σ k) F]
  [IsFractionRing (MvPolynomial σ k) F] [CharP F p]
  {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharP R p] [Algebra R F]
  [IsFractionRing R F]

omit [IsDomain R] [IsDiscreteValuationRing R] [CharP R p] [IsFractionRing R F] in
/-- The `p`-basis `x` of `F = k(x)` seen inside `R ⊇ k[x]`. -/
theorem isPBasis_of_polynomial_le {y' : σ → R}
    (hy' : ∀ i, algebraMap R F (y' i) = algebraMap (MvPolynomial σ k) F (MvPolynomial.X i)) :
    IsPBasis p (algebraMap R F ∘ y') := by
  have h : (algebraMap R F ∘ y') = fun i => algebraMap (MvPolynomial σ k) F (MvPolynomial.X i) :=
    funext hy'
  rw [h]
  exact isPBasis_X_fractionRing p

omit [IsDiscreteValuationRing R] in
/-- **FHX (3.11) for `w = ord_R`, polynomial version.** Let `P = k[x]`, `F = Frac P` and `R ⊆ F` a
DVR with fraction field `F` and uniformizer `ϖ` containing `P` (`x_i = y'_i ∈ R`). If `u` is a
`p`-basis of `R` and `J(x/u) = v ϖ^a` with `v` a unit, then for every `f ∈ P` and `e`,
`ord_R f ≥ n` implies `ord_R(Φ_e f) ≥ ⌊(n + a)/p^e⌋ - a`, where `Φ_e` is the polynomial Frobenius
trace (`polyTrace`). -/
theorem ordGE_polyTrace_of_jac {y' : σ → R}
    (hy' : ∀ i, algebraMap R F (y' i) = algebraMap (MvPolynomial σ k) F (MvPolynomial.X i))
    {u : σ → R} (hu : IsPBasis p u) {ϖ : R} (hϖ : Irreducible ϖ) {a : ℕ} {v : Rˣ}
    (hJ : hu.jac y' = v * ϖ ^ a) (e : ℕ) {n : ℤ} {f : MvPolynomial σ k}
    (hf : OrdGE ϖ n (algebraMap (MvPolynomial σ k) F f)) :
    OrdGE ϖ ((n + a) / (p ^ e : ℕ) - a)
      (algebraMap (MvPolynomial σ k) F (polyTrace p e f)) := by
  have hy := isPBasis_of_polynomial_le (k := k) (p := p) hy'
  have h := ordGE_traceIter_of_jac hu hy hϖ hJ e hf
  have hcomp : (algebraMap R F ∘ y') = fun i => algebraMap (MvPolynomial σ k) F (MvPolynomial.X i) :=
    funext hy'
  have key : ∀ (z : σ → F) (hz : IsPBasis p z)
      (_ : z = fun i => algebraMap (MvPolynomial σ k) F (MvPolynomial.X i)),
      hz.traceIter e (algebraMap (MvPolynomial σ k) F f) =
        algebraMap (MvPolynomial σ k) F (polyTrace p e f) := by
    rintro z hz rfl
    exact traceIter_X_fractionRing p e f
  rwa [key _ hy hcomp] at h

/-- **FHX (3.11) for `w = ord_R`, packaged.** For `P = k[x] ⊆ R ⊆ F = Frac P`, `R` a DVR essentially
of finite type over `k` with uniformizer `ϖ`, there is `a : ℕ` (`a = ord_R(dx/ξ)` for `ξ = du`, `u`
a `p`-basis of `R`, so `A(ord_R) = 1 + a`) such that for all `e`, `n` and `f ∈ P`,
`ord_R f ≥ n ⟹ ord_R(Φ_e f) ≥ ⌊(n + a)/p^e⌋ - a`; moreover
`p^e (⌊(n + a)/p^e⌋ - a) ≥ n - (p^e - 1)(a + 1)` (`sub_mul_succ_le_mul_ediv_sub`). -/
theorem exists_logDiscrepancy_polynomial [Algebra k R] [Algebra.EssFiniteType k R] {y' : σ → R}
    (hy' : ∀ i, algebraMap R F (y' i) = algebraMap (MvPolynomial σ k) F (MvPolynomial.X i))
    {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ (u : σ → R) (hu : IsPBasis p u) (a : ℕ) (v : Rˣ), hu.jac y' = v * ϖ ^ a ∧
      ∀ (e : ℕ) (n : ℤ) (f : MvPolynomial σ k), OrdGE ϖ n (algebraMap (MvPolynomial σ k) F f) →
        OrdGE ϖ ((n + a) / (p ^ e : ℕ) - a)
          (algebraMap (MvPolynomial σ k) F (polyTrace p e f)) := by
  have hy := isPBasis_of_polynomial_le (k := k) (p := p) hy'
  obtain ⟨u, hu, -⟩ := exists_isPBasis_of_essFiniteType k hy hϖ
  obtain ⟨a, v, hJ⟩ := exists_jac_eq_unit_mul_pow hu hy hϖ
  exact ⟨u, hu, a, v, hJ, fun e n f hf => ordGE_polyTrace_of_jac hy' hu hϖ hJ e hf⟩

end Polynomial

/-! ### Real-valued form (FHX (3.11) for `w = r ord_R`) -/

/-- If `ord_R(Φ f) ≥ m := ⌊(n + a)/q⌋ - a` whenever `ord_R f ≥ n`, then for `w = r · ord_R` with
`r > 0`: `r m ≥ r n / q - (1 - 1/q) A(w)`, `A(w) = r (1 + a)`. -/
theorem le_scaled_of_ordGE {q : ℕ} (hq : 0 < q) (n a : ℤ) {r : ℝ} (hr : 0 < r) :
    r * n / q - (1 - 1 / (q : ℝ)) * (r * (1 + a)) ≤ r * (((n + a) / (q : ℤ) - a : ℤ) : ℝ) := by
  have h := sub_mul_succ_le_mul_ediv_sub (q := (q : ℤ)) (by exact_mod_cast hq) n a
  have h' : ((n - ((q : ℤ) - 1) * (a + 1) : ℤ) : ℝ) ≤ (((q : ℤ) * ((n + a) / (q : ℤ) - a) : ℤ) : ℝ) :=
    by exact_mod_cast h
  push_cast at h'
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [show r * n / q - (1 - 1 / (q : ℝ)) * (r * (1 + a)) =
    r * ((n - (q - 1) * (a + 1)) / q) by field_simp; ring]
  apply mul_le_mul_of_nonneg_left _ hr.le
  rw [div_le_iff₀ hq']
  push_cast
  linarith

end EnvelopeProperty.Cartier
