/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.BaseChangeDVR
import EnvelopeProperty.Char0.Weights
import EnvelopeProperty.Projective.Jm

/-!
# From the cone ring `k[x₀, …, xₙ][t]` to polynomials on `ℂ^{n+2}`

The ideals `J_m(φ)` and the divisorial points of `(ℙⁿ)^an` live on the cone ring
`k[x₀, …, xₙ][t] = (MvPolynomial (Fin (n + 1)) k)[X]` (`EnvelopeProperty.Projective.Basic`,
`ProjBerk.IsDivisorial`), while the analytic inputs of the characteristic-zero assembly
(`EnvelopeProperty.Char0.AssemblyInputs`) are stated for polynomials `MvPolynomial (Fin (n + 2)) ℂ`
on `ℂ^{n+2}` with `t = z 0` and `x_i = z i.succ` (`conv:c0` of the blueprint chapter `char0.tex`).
This file provides the dictionary used in the assembly `prop:c0-key-inequality` (Fang–Han–Xia,
*The envelope property for unibranch projective varieties*, Theorem 3.1 on `ℙⁿ` in
characteristic `0`).

## Main definitions

* `EnvelopeProperty.Char0.coneMvEquiv R n : R[x₀, …, xₙ][t] ≃ₐ[R] R[z₀, …, z_{n+1}]`, the inverse of
  `MvPolynomial.finSuccEquiv` (`t ↦ z 0`, `xᵢ ↦ z i.succ`).
* `EnvelopeProperty.Char0.xHomogeneousSubmodule k n e`: the `k`-subspace `R_e[t]` of elements of
  `x`-degree `e`.
* `EnvelopeProperty.BirationalDVR.coneMvBaseChange V K'`: for a divisorial valuation ring `V` of
  `k[x][t]` and a field `K' ⊇ k`, the extension of scalars `V_{K'}` (`lem:c0-base-change-dvr`) as a
  divisorial valuation ring of `K'[z₀, …, z_{n+1}]`.

## Main results

* `isXHomogeneous_finSuccEquiv_iff`: `x`-homogeneity in the two models (`xWeightFin`).
* `isXTBihomogeneous_coneMvEquiv_monomial`: `s(x) t^ℓ` with `s` a form of degree `D` is
  bihomogeneous of `x`-degree `D` and `t`-degree `ℓ` on `ℂ^{n+2}`.
* `mem_span_coneMap_xHomogeneousSubmodule`: a polynomial over `K'` of `x`-degree `e` lies in the
  `K'`-span of the image of `R_e[t]` (over `k`).
* `BirationalDVR.ord_coneMvBaseChange`, `BirationalDVR.ord_coneMvBaseChange_coneMap`:
  `ord_{V_{K'}}(f) = ord_V(f)` for `f ∈ k[x][t]` (`cor:c0-base-change-orders`(2)).
-/

open scoped Polynomial

open Polynomial

noncomputable section

namespace EnvelopeProperty

namespace Char0

/-! ### The two models of the polynomial ring in `n + 2` variables -/

section Models

variable (R : Type*) [CommSemiring R] (n : ℕ)

/-- `R[x₀, …, xₙ][t] ≃ R[z₀, …, z_{n+1}]` with `t ↦ z 0` and `xᵢ ↦ z i.succ`: the inverse of
`MvPolynomial.finSuccEquiv`. -/
def coneMvEquiv : (MvPolynomial (Fin (n + 1)) R)[X] ≃ₐ[R] MvPolynomial (Fin (n + 2)) R :=
  (MvPolynomial.finSuccEquiv R (n + 1)).symm

variable {R n}

@[simp]
theorem finSuccEquiv_coneMvEquiv (G : (MvPolynomial (Fin (n + 1)) R)[X]) :
    MvPolynomial.finSuccEquiv R (n + 1) (coneMvEquiv R n G) = G :=
  (MvPolynomial.finSuccEquiv R (n + 1)).apply_symm_apply G

@[simp]
theorem coneMvEquiv_finSuccEquiv (P : MvPolynomial (Fin (n + 2)) R) :
    coneMvEquiv R n (MvPolynomial.finSuccEquiv R (n + 1) P) = P :=
  (MvPolynomial.finSuccEquiv R (n + 1)).symm_apply_apply P

/-- The coefficient of `z^m` is the coefficient of `x^{m.tail}` in the coefficient of `t^{m 0}`. -/
theorem coeff_eq_coeff_coeff_finSuccEquiv (P : MvPolynomial (Fin (n + 2)) R)
    (m : Fin (n + 2) →₀ ℕ) :
    MvPolynomial.coeff m P =
      MvPolynomial.coeff m.tail ((MvPolynomial.finSuccEquiv R (n + 1) P).coeff (m 0)) := by
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, Finsupp.cons_tail]

/-- `weight 1 = degree` for `ℕ`-valued finitely supported functions. -/
theorem finsupp_weight_one_eq_degree {σ : Type*} (μ : σ →₀ ℕ) : Finsupp.weight 1 μ = μ.degree := by
  rw [Finsupp.degree_eq_weight_one]
  rfl

/-- The degree of the `x`-part `m.tail` of an exponent `m = (m 0, m.tail)`. -/
theorem degree_tail_eq_sum_succ (m : Fin (n + 2) →₀ ℕ) :
    m.tail.degree = ∑ i : Fin (n + 1), m i.succ := by
  rw [Finsupp.degree_eq_sum]
  rfl

end Models

/-! ### `x`-homogeneity -/

section XHomogeneous

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- `x`-homogeneity in the two models: `G = finSuccEquiv P` is homogeneous of `x`-degree `e`
(`IsXHomogeneous`) if and only if `P` is weighted homogeneous of degree `e` for the weight
`xWeightFin = (0, 1, …, 1)`. -/
theorem isXHomogeneous_finSuccEquiv_iff {P : MvPolynomial (Fin (n + 2)) R} {e : ℕ} :
    IsXHomogeneous (MvPolynomial.finSuccEquiv R (n + 1) P) e ↔
      P.IsWeightedHomogeneous xWeightFin e := by
  constructor
  · intro h m hm
    rw [coeff_eq_coeff_coeff_finSuccEquiv] at hm
    have h1 := h (m 0) hm
    rw [finsupp_weight_one_eq_degree, degree_tail_eq_sum_succ] at h1
    rw [weight_xWeightFin, h1]
  · intro h ℓ μ hμ
    rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hμ
    have h1 := h hμ
    rw [weight_xWeightFin] at h1
    simp only [Finsupp.cons_succ] at h1
    rw [finsupp_weight_one_eq_degree, Finsupp.degree_eq_sum, ← h1]

/-- `x`-homogeneity transported to `R[z₀, …, z_{n+1}]`. -/
theorem isWeightedHomogeneous_coneMvEquiv {G : (MvPolynomial (Fin (n + 1)) R)[X]} {e : ℕ}
    (hG : IsXHomogeneous G e) : (coneMvEquiv R n G).IsWeightedHomogeneous xWeightFin e := by
  rw [← isXHomogeneous_finSuccEquiv_iff, finSuccEquiv_coneMvEquiv]
  exact hG

/-- `s(x) t^ℓ` has `t`-degree `ℓ` (for the weight `tWeightFin = (1, 0, …, 0)`). -/
theorem isWeightedHomogeneous_tWeightFin_coneMvEquiv_monomial (ℓ : ℕ)
    (s : MvPolynomial (Fin (n + 1)) R) :
    (coneMvEquiv R n (Polynomial.monomial ℓ s)).IsWeightedHomogeneous tWeightFin ℓ := by
  intro m hm
  rw [coeff_eq_coeff_coeff_finSuccEquiv, finSuccEquiv_coneMvEquiv, Polynomial.coeff_monomial]
    at hm
  rw [weight_tWeightFin]
  by_contra h
  exact hm (by rw [if_neg (Ne.symm h), MvPolynomial.coeff_zero])

end XHomogeneous

/-- `s(x) t^ℓ`, with `s` a form of degree `D`, is bihomogeneous of `x`-degree `D` and `t`-degree `ℓ`
on `ℂ^{n+2}` (`conv:c0`). -/
theorem isXTBihomogeneous_coneMvEquiv_monomial {n D : ℕ} {s : MvPolynomial (Fin (n + 1)) ℂ}
    (hs : s.IsHomogeneous D) (ℓ : ℕ) :
    IsXTBihomogeneous D ℓ (coneMvEquiv ℂ n (Polynomial.monomial ℓ s)) :=
  ⟨isWeightedHomogeneous_coneMvEquiv (IsXHomogeneous.monomial hs ℓ),
    isWeightedHomogeneous_tWeightFin_coneMvEquiv_monomial ℓ s⟩

/-! ### The spaces `R_e[t]` and their extension of scalars -/

section Span

variable (k : Type*) [Field k] (n : ℕ)

/-- The `k`-subspace `R_e[t] ⊆ k[x₀, …, xₙ][t]` of elements homogeneous of `x`-degree `e`. -/
def xHomogeneousSubmodule (e : ℕ) : Submodule k (MvPolynomial (Fin (n + 1)) k)[X] where
  carrier := {g | IsXHomogeneous g e}
  add_mem' hg hh := IsXHomogeneous.add hg hh
  zero_mem' := IsXHomogeneous.zero e
  smul_mem' a g hg := fun ℓ => by
    rw [Polynomial.coeff_smul, MvPolynomial.smul_eq_C_mul]
    exact (hg ℓ).C_mul a

variable {k n}

theorem mem_xHomogeneousSubmodule {e : ℕ} {g : (MvPolynomial (Fin (n + 1)) k)[X]} :
    g ∈ xHomogeneousSubmodule k n e ↔ IsXHomogeneous g e :=
  Iff.rfl

variable (K' : Type*) [Field K'] [Algebra k K']

/-- **Extension of scalars of `R_e[t]`**: an element of `K'[x₀, …, xₙ][t]` of `x`-degree `e` lies in
the `K'`-span of the image of `R_e[t]` under `k[x][t] → K'[x][t]`: it is a `K'`-combination of
monomials `x^μ t^ℓ` with `|μ| = e`, which are defined over `k`. -/
theorem mem_span_coneMap_xHomogeneousSubmodule {e : ℕ} {G : (MvPolynomial (Fin (n + 1)) K')[X]}
    (hG : IsXHomogeneous G e) :
    G ∈ Submodule.span K' (coneMap K' '' (xHomogeneousSubmodule k n e :
      Set (MvPolynomial (Fin (n + 1)) k)[X])) := by
  classical
  rw [Polynomial.as_sum_support G]
  refine Submodule.sum_mem _ fun ℓ _ => ?_
  rw [MvPolynomial.as_sum (G.coeff ℓ), map_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hdeg : μ.degree = e := by
    have h := hG ℓ (MvPolynomial.mem_support_iff.1 hμ)
    rwa [finsupp_weight_one_eq_degree] at h
  have hmem : Polynomial.monomial ℓ (MvPolynomial.monomial μ (1 : k)) ∈
      xHomogeneousSubmodule k n e :=
    IsXHomogeneous.monomial (MvPolynomial.isHomogeneous_monomial _ hdeg) ℓ
  have heq : Polynomial.monomial ℓ (MvPolynomial.monomial μ (MvPolynomial.coeff μ (G.coeff ℓ))) =
      MvPolynomial.coeff μ (G.coeff ℓ) •
        coneMap K' (Polynomial.monomial ℓ (MvPolynomial.monomial μ (1 : k))) := by
    rw [coneMap_apply, Polynomial.map_monomial, MvPolynomial.map_monomial, map_one,
      Polynomial.smul_monomial, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hmem, rfl⟩)

end Span

end Char0

/-! ### Divisorial valuation rings of `K'[z₀, …, z_{n+1}]` -/

namespace BirationalDVR

open Char0

variable {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}
  (V : BirationalDVR k (MvPolynomial (Fin (n + 1)) k)[X]) (K' : Type*) [Field K'] [Algebra k K']

/-- **Extension of scalars on `ℂ^{n+2}`** (`lem:c0-base-change-dvr`): for a divisorial valuation
ring `k[x₀, …, xₙ][t] ⊆ V ⊆ k(x, t)` (as in `ProjBerk.IsDivisorial`) and a field `K' ⊇ k`, the
extension of scalars `V_{K'}` as a divisorial valuation ring `K'[z] ⊆ V_{K'} ⊆ K'(z)` in the
`n + 2` variables `z = (t, x₀, …, xₙ)`. -/
def coneMvBaseChange : BirationalDVR K' (MvPolynomial (Fin (n + 2)) K') :=
  (V.coneBaseChange K').mapEquiv (coneMvEquiv K' n)

theorem ord_coneMvBaseChange (P : MvPolynomial (Fin (n + 2)) K') :
    (V.coneMvBaseChange K').ord P =
      (V.coneBaseChange K').ord (MvPolynomial.finSuccEquiv K' (n + 1) P) := by
  conv_lhs => rw [← coneMvEquiv_finSuccEquiv P]
  exact ord_mapEquiv _ _ _

theorem ord_coneMvBaseChange_coneMvEquiv (G : (MvPolynomial (Fin (n + 1)) K')[X]) :
    (V.coneMvBaseChange K').ord (coneMvEquiv K' n G) = (V.coneBaseChange K').ord G :=
  ord_mapEquiv _ _ _

/-- **`cor:c0-base-change-orders`(2) on `ℂ^{n+2}`**: `ord_{V_{K'}}(f) = ord_V(f)` for
`f ∈ k[x][t]`. -/
theorem ord_coneMvBaseChange_coneMap (g : (MvPolynomial (Fin (n + 1)) k)[X]) :
    (V.coneMvBaseChange K').ord (coneMvEquiv K' n (coneMap K' g)) = V.ord g := by
  rw [ord_coneMvBaseChange_coneMvEquiv, ord_coneBaseChange_map]

end BirationalDVR

end EnvelopeProperty
