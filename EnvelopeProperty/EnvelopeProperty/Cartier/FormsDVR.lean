import EnvelopeProperty.Cartier.Forms
import EnvelopeProperty.Cartier.Discrepancy

/-!
# The Cartier operator on regular top forms at a DVR, and on polynomial charts

Corollaries of `EnvelopeProperty.Cartier.Forms` and `EnvelopeProperty.Cartier.Discrepancy` phrased
with top differential forms `Ω^m_{F/k} = ⋀^m Ω_{F/k}` (items 3–6 of the CO lane; FHX Lemma 3.3,
`lem:divisorial-trace-estimate`).

* `cartier_polynomial`: for `F = Frac k[x]`, `C_e(f dx) = Φ_e(f) dx` with `Φ_e = polyTrace` the
  coefficient of `x^{(q-1,…,q-1)}` over `P^q`; so `C_e(P dx) ⊆ P dx`.
* `cartier_regular`: for a `p`-basis `u` of a DVR `R` with `ξ = du`, `C_e(r ξ) = Φ_u^e(r) ξ`, so
  `C_e(R ξ) ⊆ R ξ`.
* `ordGE_cartier`: writing `ord_R(ω) = ord_R(ω/ξ)`, `ord_R(C_e ω) ≥ ⌊ord_R(ω)/p^e⌋`.
* `topCoeff_topForm_eq_jac`: `dy/ξ = J(y/u)`, so `a = ord_R(dy/ξ)` is the exponent in
  `EnvelopeProperty.Cartier.exists_logDiscrepancy` and `A(ord_R) = 1 + a`.
-/

noncomputable section

open scoped NNReal ENNReal Topology

namespace EnvelopeProperty.Cartier

open KaehlerDifferential

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Polynomial charts -/

section Polynomial

variable {k : Type*} [Field k] [CharP k p] [PerfectRing k p] {m : ℕ} {F : Type*} [Field F]
  [Algebra (MvPolynomial (Fin m) k) F] [IsFractionRing (MvPolynomial (Fin m) k) F] [CharP F p]
  [Algebra k F]

/-- **The Cartier operator on a polynomial chart.** For `F = Frac k[x_1, …, x_m]`,
`C_e(f dx) = Φ_e(f) dx`, where `dx = dx_1 ∧ ⋯ ∧ dx_m` and `Φ_e = polyTrace p e`. -/
theorem cartier_polynomial (e : ℕ) (f : MvPolynomial (Fin m) k) :
    (isPBasis_X_fractionRing (σ := Fin m) (k := k) (F := F) p).cartier k e
        (algebraMap _ F f • topForm k fun i =>
          algebraMap (MvPolynomial (Fin m) k) F (MvPolynomial.X i)) =
      algebraMap _ F (polyTrace p e f) • topForm k fun i =>
        algebraMap (MvPolynomial (Fin m) k) F (MvPolynomial.X i) := by
  rw [IsPBasis.cartier_smul_topForm, traceIter_X_fractionRing]

end Polynomial

/-! ### Regular top forms at a DVR -/

section DVR

variable {k : Type*} [Field k] [CharP k p] [PerfectRing k p] {R F : Type*} [CommRing R]
  [IsDomain R] [IsDiscreteValuationRing R] [CharP R p] [Field F] [Algebra R F]
  [IsFractionRing R F] [CharP F p] [Algebra k F] {m : ℕ} {u : Fin m → R} (hu : IsPBasis p u)

theorem IsPBasis.traceIter_map {A B : Type*} [CommRing A] [CommRing B] [CharP A p] [CharP B p]
    (φ : A →+* B) {σ : Type*} [Fintype σ] [DecidableEq σ] {y : σ → A} (hy : IsPBasis p y)
    (hφy : IsPBasis p (φ ∘ y)) (e : ℕ) (f : A) :
    hφy.traceIter e (φ f) = φ (hy.traceIter e f) := by
  induction e with
  | zero => rfl
  | succ e ih => rw [traceIter_succ, traceIter_succ, ih, hy.trace_map φ hφy]

omit [IsDiscreteValuationRing R] in
/-- **`C_e` preserves regular top forms.** For a `p`-basis `u` of `R` and `ξ = du`,
`C_e(r ξ) = Φ_u^e(r) ξ` with `Φ_u^e(r) ∈ R`. -/
theorem cartier_regular (e : ℕ) (r : R) :
    (hu.map_of_isFractionRing (K := F)).cartier k e
        (algebraMap R F r • topForm k (algebraMap R F ∘ u)) =
      algebraMap R F (hu.traceIter e r) • topForm k (algebraMap R F ∘ u) := by
  rw [IsPBasis.cartier_smul_topForm, IsPBasis.traceIter_map (algebraMap R F) hu]

set_option linter.unusedSectionVars false in
omit [IsDiscreteValuationRing R] in
/-- `dy / ξ = J(y/u)`: the coordinate of `dy` with respect to `ξ = du` is the Jacobian. -/
theorem topCoeff_topForm_eq_jac (y' : Fin m → R) :
    (hu.map_of_isFractionRing (K := F)).topCoeff k (topForm k (algebraMap R F ∘ y')) =
      algebraMap R F (hu.jac y') := by
  have huF := hu.map_of_isFractionRing (K := F)
  rw [IsPBasis.topForm_eq_jac_smul (hu.map_of_isFractionRing (K := F)) (algebraMap R F ∘ y'),
    IsPBasis.topCoeff_smul, hu.jac_map (algebraMap R F) (hu.map_of_isFractionRing (K := F))]

set_option linter.unusedSectionVars false in
omit [IsDiscreteValuationRing R] in
/-- **The order estimate for the Cartier operator at a DVR** (FHX, proof of Lemma 3.3). With
`ord_R(ω) = ord_R(ω/ξ)` for `ξ = du`, `u` a `p`-basis of `R`: `ord_R(ω) ≥ n` implies
`ord_R(C_e ω) ≥ ⌊n/p^e⌋`. -/
theorem ordGE_cartier {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) {n : ℤ}
    {ω : ⋀[F]^m (Ω[F⁄k])}
    (hω : OrdGE ϖ n ((hu.map_of_isFractionRing (K := F)).topCoeff k ω)) :
    OrdGE ϖ (n / (p ^ e : ℕ))
      ((hu.map_of_isFractionRing (K := F)).topCoeff k
        ((hu.map_of_isFractionRing (K := F)).cartier k e ω)) := by
  set huF := hu.map_of_isFractionRing (K := F)
  rw [IsPBasis.cartier, IsPBasis.topCoeff_smul]
  have hJ : hu.jac u = ((1 : Rˣ) : R) * ϖ ^ 0 := by rw [IsPBasis.jac_self]; simp
  have h := ordGE_traceIter_of_jac hu huF hϖ hJ e hω
  simpa using h

end DVR

end EnvelopeProperty.Cartier
