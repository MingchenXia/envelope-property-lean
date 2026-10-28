/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.DVRJacobian
import EnvelopeProperty.Char0.AnalyticChartLocal

/-!
# The algebraic data of an analytic chart at a divisor

This file contains the algebraic half of the blueprint lemma `lem:c0-analytic-chart`
(`EnvelopeProperty/blueprint/src/char0.tex`). Let `V` be a divisorial valuation ring over `ℂ` in
`N` variables, with coordinates `w = (π, u)` (`lem:c0-dvr-curve`) indexed by `e : Option ι ≃ Fin N`
(`chartW`), and let `θ` be a primitive coordinate (`lem:c0-dvr-primitive`). We produce:

* a polynomial `Φ(T, w)` (a minimal polynomial of `θ` over `A = ℂ[w]_{(π)}` with cleared
  denominators) with `Φ(θ, w) = 0`, `∂_T Φ(θ, w)` a unit of `V`, and the divisibility property
  `ChartDiv` of `EnvelopeProperty.Char0.AnalyticChartLocal` (`exists_chartData`);
* the fact that every `x ∈ V` is `P(θ, w) / Q(θ, w)` with `Q(θ, w)` a unit of `V`
  (`mem_vFrac_chartVar`; the subring `vFrac` of fractions with unit denominators);
* a point `(t₀, p₀)` with `p₀(π) = 0` (a general point of the divisor of `V`), `Φ(t₀, p₀) = 0` and
  `Q(t₀, p₀) ≠ 0` for a given `Q` with `Q(θ, w)` a unit of `V` (`exists_chartPoint`). This is the
  *choice of `u₀`* of the blueprint proof; here it follows from Hilbert's Nullstellensatz applied
  to the prime ideal `{H : H(θ, w) ∈ m_V}`, whose zero set consists of points with `p₀(π) = 0`
  and `Φ(t₀, p₀) = 0`.

## Main results

* `EnvelopeProperty.Char0.exists_chartData_generic`, `EnvelopeProperty.Char0.exists_chartData`:
  the polynomial `Φ` with `ChartDiv`;
* `EnvelopeProperty.Char0.mem_vFrac_chartVar`, `EnvelopeProperty.Char0.mem_vFrac_of_mem_curveDVR`;
* `EnvelopeProperty.Char0.exists_chartPoint`: the general point of the divisor;
* `EnvelopeProperty.Char0.chartW`, `EnvelopeProperty.Char0.chartDeriv`,
  `EnvelopeProperty.Char0.det_chartDeriv_eq_jacobian`: the coordinates, the derivations and the
  Jacobian of `lem:c0-dvr-jacobian` in the indexing by `Fin N`.

## Implementation notes

The blueprint lists finitely many elements of `L = ℂ(u)` (coefficients, discriminants, resultants)
which must be regular and nonzero at `u₀`. Here every element of `V` is written once and for all
as a quotient of polynomials in `(θ, w)` with denominator a unit of `V` (`vFrac`), and the
Nullstellensatz provides a point of the residue variety avoiding one given denominator; no
resultants are needed.
-/

noncomputable section

open scoped NNReal ENNReal Topology Polynomial IntermediateField

open MvPolynomial IsLocalRing

namespace EnvelopeProperty.Char0

/-! ### Units of a subring and fractions with unit denominators -/

section VUnits

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] (V : Subalgebra R K)

/-- The elements of `K` which are units of `V`. -/
def vUnits : Submonoid K where
  carrier := {y | y ∈ V ∧ y⁻¹ ∈ V ∧ y ≠ 0}
  one_mem' := ⟨V.one_mem, by simp [V.one_mem], one_ne_zero⟩
  mul_mem' := by
    rintro x y ⟨h₁, h₂, h₃⟩ ⟨h₁', h₂', h₃'⟩
    exact ⟨V.mul_mem h₁ h₁', by rw [mul_inv]; exact V.mul_mem h₂ h₂', mul_ne_zero h₃ h₃'⟩

variable {V}

theorem mem_vUnits {y : K} : y ∈ vUnits V ↔ y ∈ V ∧ y⁻¹ ∈ V ∧ y ≠ 0 :=
  Iff.rfl

theorem coe_mem_vUnits_of_isUnit {v : V} (hv : IsUnit v) : (v : K) ∈ vUnits V := by
  obtain ⟨u, rfl⟩ := hv
  refine ⟨u.1.2, ?_, ?_⟩
  · have : ((u : V) : K)⁻¹ = (((u⁻¹ : Vˣ) : V) : K) := by
      refine (eq_inv_of_mul_eq_one_right ?_).symm
      rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
    rw [this]
    exact (u⁻¹ : Vˣ).1.2
  · intro h
    exact u.ne_zero (Subtype.ext h)

theorem isUnit_of_mem_vUnits {y : K} (hy : y ∈ vUnits V) : IsUnit (⟨y, hy.1⟩ : V) :=
  isUnit_iff_exists_inv.2 ⟨⟨y⁻¹, hy.2.1⟩, Subtype.ext (mul_inv_cancel₀ hy.2.2)⟩

theorem inv_mem_vUnits {y : K} (hy : y ∈ vUnits V) : y⁻¹ ∈ vUnits V :=
  ⟨hy.2.1, by rw [inv_inv]; exact hy.1, inv_ne_zero hy.2.2⟩

variable (V) in
/-- **Fractions with unit denominators**: the subring of the `x ∈ K` with `x φ(Q) = φ(P)` for
some `P, Q` with `φ(Q)` a unit of `V`. -/
def vFrac {T : Type*} [CommRing T] (φ : T →+* K) : Subring K where
  carrier := {x | ∃ P Q, φ Q ∈ vUnits V ∧ x * φ Q = φ P}
  mul_mem' := by
    rintro x y ⟨P₁, Q₁, h₁, e₁⟩ ⟨P₂, Q₂, h₂, e₂⟩
    refine ⟨P₁ * P₂, Q₁ * Q₂, by rw [map_mul]; exact (vUnits V).mul_mem h₁ h₂, ?_⟩
    rw [map_mul, map_mul, ← e₁, ← e₂]
    ring
  add_mem' := by
    rintro x y ⟨P₁, Q₁, h₁, e₁⟩ ⟨P₂, Q₂, h₂, e₂⟩
    refine ⟨P₁ * Q₂ + P₂ * Q₁, Q₁ * Q₂, by rw [map_mul]; exact (vUnits V).mul_mem h₁ h₂, ?_⟩
    rw [map_mul, map_add, map_mul, map_mul, ← e₁, ← e₂]
    ring
  one_mem' := ⟨1, 1, by rw [map_one]; exact (vUnits V).one_mem, by simp⟩
  zero_mem' := ⟨0, 1, by rw [map_one]; exact (vUnits V).one_mem, by simp⟩
  neg_mem' := by
    rintro x ⟨P, Q, h, e⟩
    exact ⟨-P, Q, h, by rw [map_neg, ← e, neg_mul]⟩

variable {T : Type*} [CommRing T] {φ : T →+* K}

theorem mem_vFrac {x : K} : x ∈ vFrac V φ ↔ ∃ P Q, φ Q ∈ vUnits V ∧ x * φ Q = φ P :=
  Iff.rfl

theorem map_mem_vFrac (P : T) : φ P ∈ vFrac V φ :=
  ⟨P, 1, by rw [map_one]; exact (vUnits V).one_mem, by simp⟩

/-- `vFrac` is closed under inverses of units of `V`. -/
theorem inv_mem_vFrac {x : K} (hx : x ∈ vFrac V φ) (hxu : x ∈ vUnits V) : x⁻¹ ∈ vFrac V φ := by
  obtain ⟨P, Q, hQ, e⟩ := hx
  refine ⟨Q, P, ?_, ?_⟩
  · rw [← e]
    exact (vUnits V).mul_mem hxu hQ
  · rw [← e, ← mul_assoc, inv_mul_cancel₀ hxu.2.2, one_mul]

end VUnits

/-! ### The generic construction

`V` is a discrete valuation ring over a field `L ⊇ ℂ` with uniformizer `π` and primitive
coordinate `θ` (`IsPrimitiveCoordinate`), `A = curveDVR V π`, and `w : Fin N → A` is
algebraically independent over `ℂ` such that every element of `A` is a fraction of polynomials in
`w` with denominator a unit of `V` (`hArep`). -/

section Generic

variable {K : Type*} [Field K] [Algebra ℂ K] {L : IntermediateField ℂ K}
  (V : Subalgebra L K) (π : V) {N : ℕ} {w : Fin N → K} (hwA : ∀ i, w i ∈ curveDVR V π)

include hwA in
theorem aeval_mem_curveDVR (P : MvPolynomial (Fin N) ℂ) : aeval w P ∈ curveDVR V π := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [aeval_C, IsScalarTower.algebraMap_apply ℂ L K]
    exact (curveDVR V π).algebraMap_mem _
  | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
  | mul_X P i hP => rw [map_mul, aeval_X]; exact mul_mem hP (hwA i)

/-- The inclusion `ℂ[w] → A`. -/
def chartOmega : MvPolynomial (Fin N) ℂ →+* curveDVR V π :=
  (aeval w : MvPolynomial (Fin N) ℂ →ₐ[ℂ] K).toRingHom.codRestrict (curveDVR V π)
    (aeval_mem_curveDVR V π hwA)

@[simp]
theorem coe_chartOmega (P : MvPolynomial (Fin N) ℂ) :
    (chartOmega V π hwA P : K) = aeval w P :=
  rfl

/-- The map `Ψ : ℂ[T, w] → A[T]`. -/
def chartPsi : MvPolynomial (Option (Fin N)) ℂ →+* (curveDVR V π)[X] :=
  (Polynomial.mapRingHom (chartOmega V π hwA)).comp
    (optionEquivLeft ℂ (Fin N)).toRingEquiv.toRingHom

theorem chartPsi_apply (H : MvPolynomial (Option (Fin N)) ℂ) :
    chartPsi V π hwA H = (optionEquivLeft ℂ (Fin N) H).map (chartOmega V π hwA) :=
  rfl

@[simp]
theorem chartPsi_X_none : chartPsi V π hwA (X none) = Polynomial.X := by
  rw [chartPsi_apply, optionEquivLeft_X_none, Polynomial.map_X]

@[simp]
theorem chartPsi_X_some (i : Fin N) :
    chartPsi V π hwA (X (some i)) = Polynomial.C (chartOmega V π hwA (X i)) := by
  rw [chartPsi_apply, optionEquivLeft_X_some, Polynomial.map_C]

@[simp]
theorem chartPsi_C (c : ℂ) :
    chartPsi V π hwA (C c) = Polynomial.C (chartOmega V π hwA (C c)) := by
  rw [chartPsi_apply, optionEquivLeft_C, Polynomial.map_C]

theorem chartPsi_rename_some (c : MvPolynomial (Fin N) ℂ) :
    chartPsi V π hwA (rename some c) = Polynomial.C (chartOmega V π hwA c) := by
  have : (chartPsi V π hwA).comp (rename some : MvPolynomial (Fin N) ℂ →ₐ[ℂ] _).toRingHom =
      Polynomial.C.comp (chartOmega V π hwA) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · simp [algebraMap_eq]
    · simp
  exact congrArg (fun φ : MvPolynomial (Fin N) ℂ →+* (curveDVR V π)[X] => φ c) this

/-- `Ψ(H)(θ) = H(θ, w)`. -/
theorem aeval_chartPsi (θ : K) (H : MvPolynomial (Option (Fin N)) ℂ) :
    Polynomial.aeval θ (chartPsi V π hwA H) = aeval (chartVar w θ) H := by
  have : (Polynomial.aeval θ : (curveDVR V π)[X] →ₐ[curveDVR V π] K).toRingHom.comp
      (chartPsi V π hwA) = (aeval (chartVar w θ)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun o => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, chartPsi_C, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, Polynomial.aeval_C, aeval_C]
      exact (coe_chartOmega V π hwA (C c)).trans (aeval_C w c)
    · cases o with
      | none => simp
      | some i =>
        simp only [RingHom.coe_comp, Function.comp_apply, chartPsi_X_some, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, Polynomial.aeval_C, aeval_X, chartVar_some]
        exact (coe_chartOmega V π hwA (X i)).trans (aeval_X w i)
  exact congrArg (fun φ : MvPolynomial (Option (Fin N)) ℂ →+* K => φ H) this

/-- `Ψ` is injective since `w` is algebraically independent. -/
theorem chartPsi_injective (hw : AlgebraicIndependent ℂ w) :
    Function.Injective (chartPsi V π hwA) := by
  have hω : Function.Injective (chartOmega V π hwA) := by
    intro P Q h
    exact hw (congrArg Subtype.val h)
  exact (Polynomial.map_injective _ hω).comp (optionEquivLeft ℂ (Fin N)).injective

/-- `Ψ(∂_T H) = (Ψ H)'`. -/
theorem chartPsi_pderiv_none (H : MvPolynomial (Option (Fin N)) ℂ) :
    chartPsi V π hwA (pderiv none H) = Polynomial.derivative (chartPsi V π hwA H) := by
  induction H using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, map_add, Polynomial.derivative_add]
  | mul_X P o hP =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hP, map_mul,
      Polynomial.derivative_mul, pderiv_X]
    cases o with
    | none => simp; ring
    | some i => simp; ring

variable {V π} in
/-- **Clearing denominators** of a polynomial over `A`: `δ(w) M = Ψ(M')` with `δ(w)` a unit of
`V`. -/
theorem exists_chartPsi_eq
    (hArep : ∀ a ∈ curveDVR V π, a ∈ vFrac V (aeval w : MvPolynomial (Fin N) ℂ →ₐ[ℂ] K).toRingHom)
    (M : (curveDVR V π)[X]) :
    ∃ δ : MvPolynomial (Fin N) ℂ, aeval w δ ∈ vUnits V ∧ ∃ M' : MvPolynomial (Option (Fin N)) ℂ,
      chartPsi V π hwA M' = Polynomial.C (chartOmega V π hwA δ) * M := by
  induction M using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨δ₁, h₁, M₁, e₁⟩ := hp
    obtain ⟨δ₂, h₂, M₂, e₂⟩ := hq
    refine ⟨δ₁ * δ₂, by rw [map_mul]; exact (vUnits V).mul_mem h₁ h₂,
      rename some δ₂ * M₁ + rename some δ₁ * M₂, ?_⟩
    rw [map_add, map_mul, map_mul, chartPsi_rename_some, chartPsi_rename_some, e₁, e₂, map_mul,
      Polynomial.C_mul]
    ring
  | monomial k a =>
    obtain ⟨γ, δ, hδ, e⟩ := hArep a a.2
    refine ⟨δ, hδ, rename some γ * X none ^ k, ?_⟩
    rw [map_mul, map_pow, chartPsi_rename_some, chartPsi_X_none,
      ← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc, ← Polynomial.C_mul]
    congr 2
    apply Subtype.ext
    simp only [coe_chartOmega, Subalgebra.coe_mul]
    change (a : K) * aeval w δ = aeval w γ at e
    rw [← e]
    ring

variable [hπ : Fact (Irreducible π)] [IsDiscreteValuationRing V]

include hwA

variable {V π} in
/-- **The chart data**: a polynomial `Φ(T, w)` with `Φ(θ, w) = 0`, `∂_T Φ(θ, w)` a unit of `V`,
and the divisibility property `ChartDiv`. -/
theorem exists_chartData_generic (hw : AlgebraicIndependent ℂ w)
    (hArep : ∀ a ∈ curveDVR V π, a ∈ vFrac V (aeval w : MvPolynomial (Fin N) ℂ →ₐ[ℂ] K).toRingHom)
    {θ : V} (hθ : IsPrimitiveCoordinate V π θ) :
    ∃ Φ : MvPolynomial (Option (Fin N)) ℂ, aeval (chartVar w (θ : K)) Φ = 0 ∧
      aeval (chartVar w (θ : K)) (pderiv none Φ) ∈ vUnits V ∧ ChartDiv w (θ : K) Φ := by
  obtain ⟨β, hβ, Φ, hΦ⟩ := exists_chartPsi_eq hwA hArep (minpoly (curveDVR V π) (θ : K))
  have hint : IsIntegral (curveDVR V π) (θ : K) := hθ.mem_curveB
  refine ⟨Φ, ?_, ?_, ?_⟩
  · rw [← aeval_chartPsi V π hwA, hΦ, Polynomial.aeval_mul, minpoly.aeval, mul_zero]
  · rw [← aeval_chartPsi V π hwA, chartPsi_pderiv_none, hΦ, Polynomial.derivative_C_mul,
      Polynomial.aeval_mul, Polynomial.aeval_C]
    refine (vUnits V).mul_mem ?_ ?_
    · exact hβ
    · have h := coe_mem_vUnits_of_isUnit hθ.isUnit_aeval_derivative
      rwa [coe_aeval_curveDVR_V] at h
  · intro H hH
    have h1 : Polynomial.aeval (θ : K) (chartPsi V π hwA H) = 0 := by
      rw [aeval_chartPsi]
      exact hH
    obtain ⟨M, hM⟩ := minpoly.isIntegrallyClosed_dvd hint h1
    obtain ⟨δ, hδ, M', hM'⟩ := exists_chartPsi_eq hwA hArep M
    refine ⟨β * δ, ?_, M', ?_⟩
    · intro h0
      have := ((vUnits V).mul_mem hβ hδ).2.2
      rw [← map_mul, h0, map_zero] at this
      exact this rfl
    · apply chartPsi_injective V π hwA hw
      simp only [map_mul, chartPsi_rename_some, hΦ, hM', hM]
      ring

omit hwA in
variable {V π} in
/-- **Every element of `V` is a fraction `P(θ, w) / Q(θ, w)` with `Q(θ, w)` a unit of `V`**
(`V = A[θ]_{𝔫'}`, `lem:c0-dvr-primitive` (3)). -/
theorem mem_vFrac_chartVar
    (hArep : ∀ a ∈ curveDVR V π, a ∈ vFrac V (aeval w : MvPolynomial (Fin N) ℂ →ₐ[ℂ] K).toRingHom)
    {θ : V} (hθ : IsPrimitiveCoordinate V π θ) {x : K} (hx : x ∈ V) :
    x ∈ vFrac V (aeval (R := ℂ) (chartVar w (θ : K))).toRingHom := by
  have hA : ∀ a ∈ curveDVR V π, a ∈ vFrac V (aeval (R := ℂ) (chartVar w (θ : K))).toRingHom := by
    intro a ha
    obtain ⟨γ, δ, hδ, e⟩ := hArep a ha
    refine ⟨rename some γ, rename some δ, ?_, ?_⟩
    · change aeval (chartVar w (θ : K)) (rename some δ) ∈ vUnits V
      rw [aeval_chartVar_rename_some]
      exact hδ
    · change a * aeval (chartVar w (θ : K)) (rename some δ) =
        aeval (chartVar w (θ : K)) (rename some γ)
      rw [aeval_chartVar_rename_some, aeval_chartVar_rename_some]
      exact e
  have hpoly : ∀ P : (curveDVR V π)[X], Polynomial.aeval (θ : K) P ∈
      vFrac V (aeval (R := ℂ) (chartVar w (θ : K))).toRingHom := by
    intro P
    induction P using Polynomial.induction_on with
    | C a => rw [Polynomial.aeval_C]; exact hA a a.2
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial k a _ =>
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
      refine mul_mem ‹_› ?_
      have := map_mem_vFrac (V := V) (φ := (aeval (R := ℂ) (chartVar w (θ : K))).toRingHom) (X none)
      simpa using this
  obtain ⟨P, S, hS, e⟩ := hθ.exists_mul_eq_aeval ⟨x, hx⟩
  have hS' : (Polynomial.aeval θ S : K) ∈ vUnits V := coe_mem_vUnits_of_isUnit hS
  rw [coe_aeval_curveDVR_V] at hS'
  have e' : x * Polynomial.aeval (θ : K) S = Polynomial.aeval (θ : K) P := by
    have := congrArg Subtype.val e
    rwa [Subalgebra.coe_mul, coe_aeval_curveDVR_V, coe_aeval_curveDVR_V] at this
  have hx' : x = Polynomial.aeval (θ : K) P * (Polynomial.aeval (θ : K) S)⁻¹ := by
    rw [← e', mul_assoc, mul_inv_cancel₀ hS'.2.2, mul_one]
  rw [hx']
  exact mul_mem (hpoly P) (inv_mem_vFrac (hpoly S) hS')

end Generic

/-! ### A general point of the divisor (Nullstellensatz) -/

section Point

variable {K : Type*} [Field K] [Algebra ℂ K] {R : Type*} [CommRing R] [Algebra ℂ R] [Algebra R K]
  [IsScalarTower ℂ R K] (V : Subalgebra R K) {N : ℕ} {w : Fin N → K} (hwV : ∀ i, w i ∈ V)
  {θ : K} (hθV : θ ∈ V)

include hwV hθV in
theorem aeval_chartVar_mem (H : MvPolynomial (Option (Fin N)) ℂ) : aeval (chartVar w θ) H ∈ V := by
  induction H using MvPolynomial.induction_on with
  | C c =>
    rw [aeval_C, IsScalarTower.algebraMap_apply ℂ R K]
    exact V.algebraMap_mem _
  | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
  | mul_X P o hP =>
    rw [map_mul, aeval_X]
    refine mul_mem hP ?_
    cases o with
    | none => exact hθV
    | some i => exact hwV i

/-- Evaluation `ℂ[T, w] → V`, `H ↦ H(θ, w)`. -/
def chartEvalV : MvPolynomial (Option (Fin N)) ℂ →+* V :=
  (aeval (R := ℂ) (chartVar w θ)).toRingHom.codRestrict V (aeval_chartVar_mem V hwV hθV)

theorem coe_chartEvalV (H : MvPolynomial (Option (Fin N)) ℂ) :
    (chartEvalV V hwV hθV H : K) = aeval (chartVar w θ) H :=
  rfl

variable [IsLocalRing V]

include hθV in
/-- **The choice of a general point of the divisor** (blueprint proof of `lem:c0-analytic-chart`,
*choice of `u₀`*). If `Q(θ, w)` is a unit of `V`, there is `(t₀, p₀) ∈ ℂ × ℂᴺ` in the zero set of
the prime ideal `{H : H(θ, w) ∈ m_V}` (Nullstellensatz) with `Q(t₀, p₀) ≠ 0`; in particular
`Φ(t₀, p₀) = 0` if `Φ(θ, w) = 0`, and `p₀(s₀) = 0` if `w_{s₀} ∈ m_V`. -/
theorem exists_chartPoint {Φ : MvPolynomial (Option (Fin N)) ℂ}
    (hΦ : aeval (chartVar w θ) Φ = 0) {s0 : Fin N} (hs0 : (⟨w s0, hwV s0⟩ : V) ∈ maximalIdeal V)
    {Q : MvPolynomial (Option (Fin N)) ℂ} (hQ : aeval (chartVar w θ) Q ∈ vUnits V) :
    ∃ (p0 : Fin N → ℂ) (t0 : ℂ), eval (chartPt p0 t0) Q ≠ 0 ∧ eval (chartPt p0 t0) Φ = 0 ∧
      p0 s0 = 0 := by
  set ψ := (residue V).comp (chartEvalV V hwV hθV)
  set P := RingHom.ker ψ
  have : P.IsPrime := RingHom.ker_isPrime ψ
  have hQP : Q ∉ P := by
    rw [RingHom.mem_ker]
    change residue V (chartEvalV V hwV hθV Q) ≠ 0
    rw [residue_ne_zero_iff_isUnit]
    exact isUnit_of_mem_vUnits hQ
  rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) P, mem_vanishingIdeal_iff] at hQP
  push Not at hQP
  obtain ⟨x, hx, hxQ⟩ := hQP
  rw [mem_zeroLocus_iff] at hx
  have hxpt : chartPt (fun i => x (some i)) (x none) = x := funext fun o => by cases o <;> rfl
  refine ⟨fun i => x (some i), x none, ?_, ?_, ?_⟩
  · rw [hxpt]
    exact hxQ
  · rw [hxpt]
    refine hx Φ ?_
    rw [RingHom.mem_ker]
    change residue V (chartEvalV V hwV hθV Φ) = 0
    have : chartEvalV V hwV hθV Φ = 0 := Subtype.ext hΦ
    rw [this, map_zero]
  · have := hx (X (some s0)) ?_
    · simpa using this
    rw [RingHom.mem_ker]
    change residue V (chartEvalV V hwV hθV (X (some s0))) = 0
    rw [residue_eq_zero_iff]
    convert hs0
    rw [coe_chartEvalV, aeval_X, chartVar_some]

end Point

/-! ### Divisorial valuation rings over `ℂ` -/

section BirationalDVR

variable {N : ℕ} {V : BirationalDVR ℂ (MvPolynomial (Fin N) ℂ)} {ι : Type*} [Fintype ι]
  [DecidableEq ι]

variable (π : V.ring) (u : ι → V.ring) (e : Option ι ≃ Fin N)

/-- The coordinates `w = (π, u)` of `lem:c0-dvr-curve`, indexed by `Fin N` via `e`. -/
def chartW : Fin N → FractionRing (MvPolynomial (Fin N) ℂ) :=
  fun i => dvrCoordinates π u (e.symm i)

omit [Fintype ι] [DecidableEq ι] in
theorem chartW_apply_none : chartW π u e (e none) = π := by
  simp [chartW]

omit [Fintype ι] [DecidableEq ι] in
theorem chartW_apply_some (i : ι) : chartW π u e (e (some i)) = u i := by
  simp [chartW]

omit [Fintype ι] [DecidableEq ι] in
theorem chartW_mem (i : Fin N) : chartW π u e i ∈ V.ring := by
  rw [chartW]
  cases e.symm i with
  | none => exact π.2
  | some j => exact (u j).2

variable {π u}

/-- The partial derivatives `∂_j = ∂/∂w_j` of `lem:c0-dvr-jacobian`, indexed by `Fin N`. -/
def chartDeriv (hπ : Irreducible π) (hu : IsTranscendenceBasis ℂ (residue V.ring ∘ u)) :
    Fin N → Derivation ℂ (FractionRing (MvPolynomial (Fin N) ℂ))
      (FractionRing (MvPolynomial (Fin N) ℂ)) :=
  fun j => partialDeriv (isTranscendenceBasis_dvrCoordinates hπ hu) (e.symm j)

theorem isChartDeriv_chartDeriv (hπ : Irreducible π)
    (hu : IsTranscendenceBasis ℂ (residue V.ring ∘ u)) :
    IsChartDeriv (chartW π u e) (chartDeriv e hπ hu) := by
  intro j i
  rw [chartDeriv, chartW, partialDeriv_apply]
  simp only [e.symm.injective.eq_iff]

omit [DecidableEq ι] in
theorem algebraicIndependent_chartW (hπ : Irreducible π)
    (hu : IsTranscendenceBasis ℂ (residue V.ring ∘ u)) :
    AlgebraicIndependent ℂ (chartW π u e) :=
  (isTranscendenceBasis_dvrCoordinates hπ hu).1.comp _ e.symm.injective

/-- The Jacobian `det(∂_j z_i)` in the indexing by `Fin N` is the Jacobian of
`lem:c0-dvr-jacobian`. -/
theorem det_chartDeriv_eq_jacobian (hπ : Irreducible π)
    (hu : IsTranscendenceBasis ℂ (residue V.ring ∘ u)) :
    (Matrix.of fun i j => chartDeriv e hπ hu j
        (algebraMap (MvPolynomial (Fin N) ℂ) (FractionRing (MvPolynomial (Fin N) ℂ)) (X i))).det =
      jacobian (isTranscendenceBasis_dvrCoordinates hπ hu)
        (fun o => algebraMap (MvPolynomial (Fin N) ℂ) (FractionRing (MvPolynomial (Fin N) ℂ))
          (X (e o))) := by
  rw [jacobian, ← Matrix.det_submatrix_equiv_self e.symm]
  congr 1
  ext i j
  simp [chartDeriv]

omit [Fintype ι] [DecidableEq ι] in
/-- Every element of `A = curveDVR` is a fraction of polynomials in `w` with denominator a unit
of `V`. -/
theorem mem_vFrac_of_mem_curveDVR (hπ : Irreducible π)
    (hu : IsTranscendenceBasis ℂ (residue V.ring ∘ u)) {a : FractionRing (MvPolynomial (Fin N) ℂ)}
    (ha : a ∈ curveDVR (extendScalarsOfLE V.ring _ (adjoin_le_dvr hu))
      (extendScalarsOfLEEquiv V.ring _ (adjoin_le_dvr hu) π)) :
    a ∈ vFrac (extendScalarsOfLE V.ring _ (adjoin_le_dvr hu))
      (aeval (R := ℂ) (chartW π u e)).toRingHom := by
  set L := IntermediateField.adjoin ℂ
    (Set.range fun i => (u i : FractionRing (MvPolynomial (Fin N) ℂ)))
  set V' := extendScalarsOfLE V.ring L (adjoin_le_dvr hu)
  set π' : V' := extendScalarsOfLEEquiv V.ring L (adjoin_le_dvr hu) π
  have : Fact (Irreducible π') :=
    ⟨(MulEquiv.irreducible_iff
      (extendScalarsOfLEEquiv V.ring L (adjoin_le_dvr hu)).toMulEquiv).2 hπ⟩
  have hren : ∀ r : MvPolynomial ι ℂ,
      aeval (fun i => (u i : FractionRing (MvPolynomial (Fin N) ℂ))) r =
      aeval (chartW π u e) (rename (fun i => e (some i)) r) := by
    intro r
    have : (chartW π u e ∘ fun i => e (some i)) =
        fun i => (u i : FractionRing (MvPolynomial (Fin N) ℂ)) :=
      funext fun i => chartW_apply_some π u e i
    rw [aeval_rename, this]
  -- elements of `L`
  have hL : ∀ ℓ : L, (ℓ : FractionRing (MvPolynomial (Fin N) ℂ)) ∈
      vFrac V' (aeval (R := ℂ) (chartW π u e)).toRingHom := by
    intro ℓ
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_range_iff ℂ _ _).1 ℓ.2
    by_cases hs : aeval (fun i => (u i : FractionRing (MvPolynomial (Fin N) ℂ))) s = 0
    · rw [hrs, hs, div_zero]
      exact zero_mem _
    have hsL : aeval (fun i => (u i : FractionRing (MvPolynomial (Fin N) ℂ))) s ∈ L :=
      (IntermediateField.mem_adjoin_range_iff ℂ _ _).2 ⟨s, 1, by simp⟩
    refine ⟨rename (fun i => e (some i)) r, rename (fun i => e (some i)) s, ?_, ?_⟩
    · change aeval (chartW π u e) (rename (fun i => e (some i)) s) ∈ vUnits V'
      rw [← hren]
      exact ⟨adjoin_le_dvr hu hsL, adjoin_le_dvr hu (show _ ∈ L from inv_mem hsL), hs⟩
    · change _ * aeval (chartW π u e) (rename (fun i => e (some i)) s) =
        aeval (chartW π u e) (rename (fun i => e (some i)) r)
      rw [← hren, ← hren, hrs, div_mul_cancel₀ _ hs]
  -- `π`
  have hπw : ((π' : V') : FractionRing (MvPolynomial (Fin N) ℂ)) ∈
      vFrac V' (aeval (R := ℂ) (chartW π u e)).toRingHom := by
    have := map_mem_vFrac (V := V') (φ := (aeval (R := ℂ) (chartW π u e)).toRingHom) (X (e none))
    rw [show ((π' : V') : FractionRing (MvPolynomial (Fin N) ℂ)) = chartW π u e (e none) from
      (chartW_apply_none π u e).symm]
    simpa using this
  -- polynomials in `π` over `L`
  have hpoly : ∀ Q : L[X], Polynomial.aeval ((π' : V') : FractionRing (MvPolynomial (Fin N) ℂ)) Q ∈
      vFrac V' (aeval (R := ℂ) (chartW π u e)).toRingHom := by
    intro Q
    induction Q using Polynomial.induction_on with
    | C ℓ => rw [Polynomial.aeval_C]; exact hL ℓ
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial k ℓ _ =>
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
      exact mul_mem ‹_› hπw
  obtain ⟨Q, S, hS, rfl⟩ := (mem_curveDVR_iff V' π').1 ha
  have hSu : Polynomial.aeval ((π' : V') : FractionRing (MvPolynomial (Fin N) ℂ)) S ∈
      vUnits V' := by
    have := coe_mem_vUnits_of_isUnit
      (isUnit_aeval_of_mem_maximalIdeal (pi_mem_maximalIdeal V' π') hS)
    rwa [coe_aeval_pi] at this
  rw [div_eq_mul_inv]
  exact mul_mem (hpoly Q) (inv_mem_vFrac (hpoly S) hSu)

omit [DecidableEq ι] in
/-- **The algebraic chart data at a divisorial valuation ring** (algebraic part of
`lem:c0-analytic-chart`): a primitive coordinate `θ ∈ V` and a polynomial `Φ(T, w)` with
`Φ(θ, w) = 0`, `∂_T Φ(θ, w)` a unit of `V`, the divisibility property `ChartDiv`, and such that
every element of `V` is a fraction `P(θ, w) / Q(θ, w)` with `Q(θ, w)` a unit of `V`. -/
theorem exists_chartData (hπ : Irreducible π) (hu : IsTranscendenceBasis ℂ (residue V.ring ∘ u)) :
    ∃ (θ : FractionRing (MvPolynomial (Fin N) ℂ)) (Φ : MvPolynomial (Option (Fin N)) ℂ),
      θ ∈ V.ring ∧ aeval (chartVar (chartW π u e) θ) Φ = 0 ∧
      aeval (chartVar (chartW π u e) θ) (pderiv none Φ) ∈ vUnits V.ring ∧
      ChartDiv (chartW π u e) θ Φ ∧
      ∀ x ∈ V.ring, x ∈ vFrac V.ring (aeval (R := ℂ) (chartVar (chartW π u e) θ)).toRingHom := by
  set L := IntermediateField.adjoin ℂ
    (Set.range fun i => (u i : FractionRing (MvPolynomial (Fin N) ℂ)))
  set V' := extendScalarsOfLE V.ring L (adjoin_le_dvr hu)
  set π' : V' := extendScalarsOfLEEquiv V.ring L (adjoin_le_dvr hu) π
  have : Fact (Irreducible π') :=
    ⟨(MulEquiv.irreducible_iff
      (extendScalarsOfLEEquiv V.ring L (adjoin_le_dvr hu)).toMulEquiv).2 hπ⟩
  have : Algebra.IsAlgebraic L (ResidueField V') :=
    isAlgebraic_residueField_extendScalarsOfLE V.ring hu
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℂ L).injective
  obtain ⟨θ, hθ⟩ := exists_isPrimitiveCoordinate V' π'
  have hwA : ∀ i, chartW π u e i ∈ curveDVR V' π' := by
    intro i
    refine (mem_curveDVR V' π').2 ⟨?_, chartW_mem π u e i⟩
    rw [chartW]
    cases e.symm i with
    | none => exact IntermediateField.mem_adjoin_simple_self L _
    | some j =>
      have hj : (u j : FractionRing (MvPolynomial (Fin N) ℂ)) ∈ L :=
        IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩
      exact (L⟮((π' : V') : FractionRing (MvPolynomial (Fin N) ℂ))⟯).algebraMap_mem ⟨_, hj⟩
  have hArep : ∀ a ∈ curveDVR V' π', a ∈ vFrac V' (aeval (R := ℂ) (chartW π u e)).toRingHom :=
    fun a ha => mem_vFrac_of_mem_curveDVR e hπ hu ha
  obtain ⟨Φ, h1, h2, h3⟩ :=
    exists_chartData_generic hwA (algebraicIndependent_chartW e hπ hu) hArep hθ
  exact ⟨θ, Φ, θ.2, h1, h2, h3, fun x hx => mem_vFrac_chartVar hArep hθ hx⟩

end BirationalDVR

end EnvelopeProperty.Char0
