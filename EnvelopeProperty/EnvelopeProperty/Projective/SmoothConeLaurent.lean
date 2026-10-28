/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.TestIdeal.PBasisPolynomial
import EnvelopeProperty.Cartier.SmoothPBasis

/-!
# Homogeneous `p`-bases of `A[Y, Y⁻¹][t]`

Let `A` be a commutative ring of prime characteristic `p` with a finite `p`-basis `u : σ → A`, and
let `L = A[Y, Y⁻¹][t]` (`(LaurentPolynomial A)[X]`). By `lem:sg-pbasis-basics`(4) of the blueprint
chapter `smooth-general.tex`, `ζ = (u, Y, t)` is a `p`-basis of `L`
(`EnvelopeProperty.Cartier.IsPBasis.polynomial_laurentPolynomial`, indexed by `Option (Option σ)`,
`none ↦ t`, `some none ↦ Y`). This file contains the computations on `L` behind
`lem:sg-homog-pbasis` and `lem:sg-jacobians`, used for Fang–Han–Xia, *The envelope property for
unibranch projective varieties*, Theorem 3.1 (`thm:smooth-EP`) on smooth projective varieties: the
bigrading `L_{(b, λ)} = A Y^b t^λ` is put into explicit monomials `C (C c * T b) * X ^ λ`.

## Main results

* `EnvelopeProperty.Cartier.IsPBasis.of_isUnit_jac`: in a field, a family whose Jacobian with
  respect to a `p`-basis is a unit is a `p`-basis.
* `IsPBasis.pderiv_polynomial_C_none`, `IsPBasis.pderiv_polynomial_C_some`,
  `IsPBasis.pderiv_laurentPolynomial_C_none`, `IsPBasis.pderiv_laurentPolynomial_C_some` and
  `IsPBasis.pderiv_laurentFamily_C_C`: the derivations of `(u, X)`, `(u, T)` and `(u, Y, t)` on
  constants (`∂/∂Y` and `∂/∂t` kill `A`, `∂/∂u_i` restricts to the derivation of `u`); they rest on
  `IsPBasis.eq_zero_of_isDerivation`: an additive map satisfying the Leibniz rule along a ring
  homomorphism and vanishing on a `p`-basis vanishes.
* `IsPBasis.jac_coneFamily`: for `g : Option σ → A` the family `z = (t, g_o Y)`
  (`EnvelopeProperty.Cartier.coneFamily`) has Jacobian `J(z/ζ) = det N · Y^{|σ|}`
  (`N = coneJacMatrix`, `N_{o, none} = g_o`, `N_{o, some m} = ∂g_o/∂u_m`): it is bihomogeneous of
  bidegree `(|σ|, 0)`.
* `IsPBasis.traceIter_laurentFamily_monomial`: the Frobenius trace of `ζ` on monomials,
  `Φ^e_ζ(c Y^b t^λ) = Φ^e_u(c) Y^{⌊b/Q⌋} t^{⌊λ/Q⌋}` if `b ≡ λ ≡ Q - 1 (mod Q)` and `0` otherwise
  (`Q = p^e`).
* For a field `F` and a fraction field `K` of `L = F[Y, Y⁻¹][t]`:
  `isPBasis_algebraMap_coneFamily` (`z` is a `p`-basis of `K` when `det N ≠ 0`) and
  `traceIter_algebraMap_coneFamily` (`lem:sg-homog-pbasis`(2)):
  `Φ^e_z(c Y^b t^λ) = Φ^e_ζ(J(z/ζ)^{-(Q-1)} c Y^b t^λ)` is a monomial of bidegree
  `((b - (n + 1)(Q - 1))/Q, (λ - (Q - 1))/Q)` when these are integers, `n = |σ|`, and `0` otherwise
  (`exists_traceIter_algebraMap_coneFamily_eq`).
-/

noncomputable section

open scoped NNReal ENNReal Topology Polynomial

namespace EnvelopeProperty.Cartier

open Finset Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Determinants over `Option` -/

section Det

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant of an `Option ι`-indexed matrix whose `none`-row vanishes off the diagonal. -/
theorem det_option_of_row_none_eq_zero (M : Matrix (Option ι) (Option ι) R)
    (h : ∀ j, M none (some j) = 0) :
    M.det = M none none * (Matrix.of fun i j => M (some i) (some j)).det := by
  have key := Matrix.twoBlockTriangular_det' M (fun i => i.isNone = true) (fun i hi j hj => by
    rw [Option.isNone_iff_eq_none] at hi
    subst hi
    cases j with
    | none => exact absurd rfl hj
    | some j' => exact h j')
  have h2 : (M.toSquareBlockProp fun i => ¬ i.isNone = true).det =
      (Matrix.of fun i j => M (some i) (some j)).det := by
    let e : ι ≃ {a : Option ι // ¬ a.isNone = true} :=
      { toFun := fun i => ⟨some i, by simp⟩
        invFun := fun a => Option.get a.1 (by
          have := a.2
          rw [Option.isNone_iff_eq_none] at this
          exact Option.ne_none_iff_isSome.1 this)
        left_inv := fun i => rfl
        right_inv := fun a => Subtype.ext (Option.some_get _) }
    rw [← Matrix.det_submatrix_equiv_self e]
    rfl
  rw [key]
  refine congrArg₂ (· * ·) ?_ h2
  refine (Matrix.det_eq_elem_of_card_eq_one ?_ ⟨none, rfl⟩).trans rfl
  refine Fintype.card_eq_one_iff.2 ⟨⟨none, rfl⟩, fun a => Subtype.ext ?_⟩
  exact Option.isNone_iff_eq_none.1 a.2

end Det

/-! ### `p`-bases from Jacobians -/

section Jacobian

variable {F : Type*} [Field F] [CharP F p] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **The Jacobian criterion.** In a field of characteristic `p`, a family `z` whose Jacobian
`J(z/u)` with respect to a `p`-basis `u` is a unit is a `p`-basis: the derivations
`∑_j (∂z/∂u)⁻¹_{jc} ∂/∂u_j` are dual to `z`. -/
theorem IsPBasis.of_isUnit_jac {u z : σ → F} (hu : IsPBasis p u) (hz : IsUnit (hu.jac z)) :
    IsPBasis p z := by
  classical
  set A : Matrix σ σ F := Matrix.of fun i j => hu.pderiv j (z i) with hA
  have hAB : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hz
  let D : σ → Derivation ℤ F F := fun c => ∑ j, A⁻¹ j c • hu.pderiv j
  have hD : ∀ i c, D c (z i) = if i = c then 1 else 0 := by
    intro i c
    have h1 : D c (z i) = ∑ j, A i j * A⁻¹ j c := by
      simp only [D, derivation_sum_apply, Derivation.smul_apply, smul_eq_mul, hA, Matrix.of_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [h1, ← Matrix.mul_apply, hAB, Matrix.one_apply]
  let e : Fin (Fintype.card σ) ≃ σ := (Fintype.equivFin σ).symm
  have hinj : Function.Injective (pSum p (z ∘ e)) :=
    injective_pSum_of_derivations (z ∘ e) (fun l => D (e l)) fun i j => by
      simp only [Function.comp_apply, hD, e.injective.eq_iff]
  have h1 : IsPBasis p (z ∘ e) :=
    isPBasis_of_linearIndependent hu (by rw [Fintype.card_fin])
      (linearIndependent_of_injective_pSum hinj)
  have h2 := h1.comp_equiv e.symm
  have h3 : (z ∘ e) ∘ e.symm = z := by
    funext i
    simp
  rwa [h3] at h2

end Jacobian

/-! ### Derivations on constants -/

section Constants

variable {A B : Type*} [CommRing A] [CommRing B] [CharP A p] [CharP B p]
  {σ : Type*} [Fintype σ] [DecidableEq σ] {u : σ → A}

/-- An additive map `δ : A → B` satisfying the Leibniz rule along a ring homomorphism `φ` and
vanishing on a `p`-basis vanishes. -/
theorem IsPBasis.eq_zero_of_isDerivation (hu : IsPBasis p u) (φ : A →+* B) (δ : A → B)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y) (hδ : ∀ x y, δ (x * y) = φ x * δ y + φ y * δ x)
    (h0 : ∀ i, δ (u i) = 0) (f : A) : δ f = 0 := by
  let δ' : A →+ B := AddMonoidHom.mk' δ hadd
  have h1 : δ 1 = 0 := by
    have h := hδ 1 1
    rw [mul_one, φ.map_one, one_mul] at h
    have h2 : δ 1 + δ 1 = δ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  have hpow : ∀ (x : A) (n : ℕ), δ (x ^ n) = (n : B) * φ x ^ (n - 1) * δ x := by
    intro x n
    induction n with
    | zero => simp [h1]
    | succ n ih =>
      rw [pow_succ, hδ, ih, map_pow]
      rcases n with _ | n
      · simp
      · simp only [Nat.add_sub_cancel, pow_succ]
        push_cast
        ring
  have hp0 : ∀ x : A, δ (x ^ p) = 0 := fun x => by
    rw [hpow, CharP.cast_eq_zero, zero_mul, zero_mul]
  have hmono : ∀ n : σ → ℕ, δ (mono u n) = 0 := by
    intro n
    unfold mono
    induction (univ : Finset σ) using Finset.induction_on with
    | empty => simpa using h1
    | insert i s hi ih =>
      rw [prod_insert hi, hδ, ih, hpow, h0]
      simp
  change δ' f = 0
  rw [← hu.sum_coeff f, map_sum]
  refine sum_eq_zero fun a _ => ?_
  change δ _ = 0
  rw [hδ, hp0, hmono, mul_zero, mul_zero, add_zero]

/-- `∂/∂X` kills the constants of `A[X]`, for the `p`-basis `(u, X)`. -/
theorem IsPBasis.pderiv_polynomial_C_none (hu : IsPBasis p u) (a : A) :
    hu.polynomial.pderiv none (C a) = 0 := by
  have h0 : ∀ i, hu.polynomial.pderiv none (C (u i)) = 0 := fun i => by
    have h := hu.polynomial.pderiv_self none (some i)
    simpa using h
  exact hu.eq_zero_of_isDerivation (C : A →+* A[X]) (fun a => hu.polynomial.pderiv none (C a))
    (fun x y => by simp only [map_add]) (fun x y => by
      simp only [map_mul, Derivation.leibniz, smul_eq_mul]) h0 a

/-- `∂/∂u_i` on the constants of `A[X]` is the derivation `∂/∂u_i` of `A`. -/
theorem IsPBasis.pderiv_polynomial_C_some (hu : IsPBasis p u) (i : σ) (a : A) :
    hu.polynomial.pderiv (some i) (C a) = C (hu.pderiv i a) := by
  have h0 : ∀ j, hu.polynomial.pderiv (some i) (C (u j)) - C (hu.pderiv i (u j)) = 0 := by
    intro j
    have h1 := hu.polynomial.pderiv_self (some i) (some j)
    simp only [Option.elim_some] at h1
    rw [h1, hu.pderiv_self i j]
    by_cases hij : i = j <;> simp [hij]
  exact sub_eq_zero.1 (hu.eq_zero_of_isDerivation (C : A →+* A[X])
    (fun a => hu.polynomial.pderiv (some i) (C a) - C (hu.pderiv i a))
    (fun x y => by simp only [map_add]; ring)
    (fun x y => by simp only [map_mul, map_add, Derivation.leibniz, smul_eq_mul]; ring) h0 a)

/-- `∂/∂T` kills the constants of `A[T, T⁻¹]`, for the `p`-basis `(u, T)`. -/
theorem IsPBasis.pderiv_laurentPolynomial_C_none (hu : IsPBasis p u) (a : A) :
    hu.laurentPolynomial.pderiv none (LaurentPolynomial.C a) = 0 := by
  have h0 : ∀ i, hu.laurentPolynomial.pderiv none (LaurentPolynomial.C (u i)) = 0 := fun i => by
    have h := hu.laurentPolynomial.pderiv_self none (some i)
    simpa using h
  exact hu.eq_zero_of_isDerivation (LaurentPolynomial.C : A →+* LaurentPolynomial A)
    (fun a => hu.laurentPolynomial.pderiv none (LaurentPolynomial.C a))
    (fun x y => by simp only [map_add]) (fun x y => by
      simp only [map_mul, Derivation.leibniz, smul_eq_mul]) h0 a

/-- `∂/∂u_i` on the constants of `A[T, T⁻¹]` is the derivation `∂/∂u_i` of `A`. -/
theorem IsPBasis.pderiv_laurentPolynomial_C_some (hu : IsPBasis p u) (i : σ) (a : A) :
    hu.laurentPolynomial.pderiv (some i) (LaurentPolynomial.C a) =
      LaurentPolynomial.C (hu.pderiv i a) := by
  have h0 : ∀ j, hu.laurentPolynomial.pderiv (some i) (LaurentPolynomial.C (u j)) -
      LaurentPolynomial.C (hu.pderiv i (u j)) = 0 := by
    intro j
    have h1 := hu.laurentPolynomial.pderiv_self (some i) (some j)
    simp only [Option.elim_some] at h1
    rw [h1, hu.pderiv_self i j]
    by_cases hij : i = j <;> simp [hij]
  exact sub_eq_zero.1 (hu.eq_zero_of_isDerivation (LaurentPolynomial.C : A →+* LaurentPolynomial A)
    (fun a => hu.laurentPolynomial.pderiv (some i) (LaurentPolynomial.C a) -
      LaurentPolynomial.C (hu.pderiv i a))
    (fun x y => by simp only [map_add]; ring)
    (fun x y => by simp only [map_mul, map_add, Derivation.leibniz, smul_eq_mul]; ring) h0 a)

/-- The derivations of `ζ = (u, Y, t)` on the constants of `A[Y, Y⁻¹][t]`: `∂/∂t` and `∂/∂Y` kill
`A`, and `∂/∂u_i` restricts to `∂/∂u_i` on `A`. -/
theorem IsPBasis.pderiv_laurentFamily_C_C (hu : IsPBasis p u) (o : Option (Option σ)) (a : A) :
    hu.laurentPolynomial.polynomial.pderiv o (C (LaurentPolynomial.C a)) =
      o.elim 0 fun o' => o'.elim 0 fun i => C (LaurentPolynomial.C (hu.pderiv i a)) := by
  rcases o with _ | _ | i
  · exact hu.laurentPolynomial.pderiv_polynomial_C_none _
  · rw [hu.laurentPolynomial.pderiv_polynomial_C_some, hu.pderiv_laurentPolynomial_C_none,
      map_zero]
    rfl
  · rw [hu.laurentPolynomial.pderiv_polynomial_C_some, hu.pderiv_laurentPolynomial_C_some]
    rfl

end Constants

/-! ### The cone family `(t, g_o Y)` and its Jacobian -/

section ConeFamily

variable {A : Type*} [CommRing A] [CharP A p] {σ : Type*} [Fintype σ] [DecidableEq σ]
  {u : σ → A}

/-- The family `z = (t, g_o Y)_{o}` of `A[Y, Y⁻¹][t]`, indexed like `ζ = (u, Y, t)`:
`none ↦ t`, `some o ↦ g_o Y`. -/
def coneFamily (g : Option σ → A) : Option (Option σ) → (LaurentPolynomial A)[X] :=
  fun o => o.elim X fun o' => C (LaurentPolynomial.C (g o') * LaurentPolynomial.T 1)

/-- The matrix `N` with `N_{o, none} = g_o` and `N_{o, some m} = ∂g_o/∂u_m`. -/
def coneJacMatrix (hu : IsPBasis p u) (g : Option σ → A) : Matrix (Option σ) (Option σ) A :=
  Matrix.of fun o o' => o'.elim (g o) fun m => hu.pderiv m (g o)

/-- **The Jacobian of the cone family** (proof of `lem:sg-jacobians`(1)):
`J(z/ζ) = det N · Y^{|σ|}` for `z = (t, g_o Y)` and `ζ = (u, Y, t)`. In particular `J(z/ζ)` is
bihomogeneous of bidegree `(|σ|, 0)`. -/
theorem IsPBasis.jac_coneFamily (hu : IsPBasis p u) (g : Option σ → A) :
    hu.laurentPolynomial.polynomial.jac (coneFamily g) =
      C (LaurentPolynomial.C (coneJacMatrix hu g).det *
        LaurentPolynomial.T (Fintype.card σ : ℤ)) := by
  set hζ := hu.laurentPolynomial.polynomial with hζdef
  have hY : ∀ o, hζ.pderiv o (C (LaurentPolynomial.T 1)) = if o = some none then 1 else 0 :=
    fun o => hζ.pderiv_self o (some none)
  have hX : ∀ o, hζ.pderiv o X = if o = none then 1 else 0 := fun o => hζ.pderiv_self o none
  have hentry : ∀ o o' : Option σ, hζ.pderiv (some o') (coneFamily g (some o)) =
      C (LaurentPolynomial.C (coneJacMatrix hu g o o')) *
        o'.elim (1 : (LaurentPolynomial A)[X]) fun _ => C (LaurentPolynomial.T 1) := by
    intro o o'
    have h1 : coneFamily g (some o) =
        C (LaurentPolynomial.C (g o)) * C (LaurentPolynomial.T 1) := by
      simp only [coneFamily, Option.elim_some, map_mul]
    rw [h1, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hY, hu.pderiv_laurentFamily_C_C]
    rcases o' with _ | m
    · simp [coneJacMatrix]
    · rw [if_neg (by simp), mul_zero, zero_add]
      simp only [Option.elim_some, coneJacMatrix, Matrix.of_apply]
      ring
  have hM : (Matrix.of fun o o' => hζ.pderiv (some o') (coneFamily g (some o))) =
      ((Polynomial.C.comp LaurentPolynomial.C).mapMatrix (coneJacMatrix hu g)) *
        Matrix.diagonal (fun o' : Option σ =>
          o'.elim (1 : (LaurentPolynomial A)[X]) fun _ => C (LaurentPolynomial.T 1)) := by
    ext o o'
    rw [Matrix.mul_diagonal, Matrix.of_apply, hentry]
    rfl
  rw [jac, det_option_of_row_none_eq_zero _ (fun j => by
    rw [Matrix.of_apply]
    exact (hX (some j)).trans (if_neg (Option.some_ne_none j)))]
  have h0 : (Matrix.of fun i j => hζ.pderiv j (coneFamily g i)) none none = 1 := by
    rw [Matrix.of_apply]
    exact (hX none).trans (if_pos rfl)
  rw [h0, one_mul]
  change (Matrix.of fun o o' => hζ.pderiv (some o') (coneFamily g (some o))).det = _
  rw [hM, Matrix.det_mul, ← RingHom.map_det, Matrix.det_diagonal, Fintype.prod_option]
  simp only [Option.elim_none, Option.elim_some, one_mul, prod_const, card_univ,
    RingHom.coe_comp, Function.comp_apply]
  rw [← map_pow, LaurentPolynomial.T_pow, mul_one, ← map_mul]

/-- **The Frobenius trace of `ζ` on monomials** (proof of `lem:sg-homog-pbasis`(2)): for
`Q = p^e`, `Φ^e_ζ(c Y^b t^λ) = Φ^e_u(c) Y^{⌊b/Q⌋} t^{⌊λ/Q⌋}` if `b ≡ λ ≡ Q - 1 (mod Q)`, and `0`
otherwise. -/
theorem IsPBasis.traceIter_laurentFamily_monomial (hu : IsPBasis p u) (e : ℕ) (c : A) (b : ℤ)
    (l : ℕ) :
    hu.laurentPolynomial.polynomial.traceIter e
        (C (LaurentPolynomial.C c * LaurentPolynomial.T b) * X ^ l) =
      if b % (p : ℤ) ^ e = (p : ℤ) ^ e - 1 ∧ l % p ^ e = p ^ e - 1 then
        C (LaurentPolynomial.C (hu.traceIter e c) * LaurentPolynomial.T (b / (p : ℤ) ^ e)) *
          X ^ (l / p ^ e)
      else 0 := by
  rw [hu.laurentPolynomial.traceIter_polynomial_C_mul_X_pow,
    hu.traceIter_laurentPolynomial_C_mul_T]
  by_cases h1 : b % (p : ℤ) ^ e = (p : ℤ) ^ e - 1 <;>
    by_cases h2 : l % p ^ e = p ^ e - 1 <;> simp [h1, h2]

end ConeFamily

/-! ### The fraction field of `F[Y, Y⁻¹][t]` -/

section FractionField

variable {F : Type*} [Field F] [CharP F p] {σ : Type*} [Fintype σ] [DecidableEq σ] {u : σ → F}
  {K : Type*} [Field K] [CharP K p] [Algebra (LaurentPolynomial F)[X] K]
  [IsFractionRing (LaurentPolynomial F)[X] K]

/-- A nonzero monomial `c Y^b t^λ` of `F[Y, Y⁻¹][t]`. -/
theorem C_C_mul_T_mul_X_pow_ne_zero {c : F} (hc : c ≠ 0) (b : ℤ) (l : ℕ) :
    (C (LaurentPolynomial.C c * LaurentPolynomial.T b) * X ^ l : (LaurentPolynomial F)[X]) ≠ 0 := by
  refine mul_ne_zero ?_ (pow_ne_zero _ X_ne_zero)
  rw [Ne, C_eq_zero]
  exact mul_ne_zero ((map_ne_zero_iff _ (LaurentPolynomial.C : F →+* _).injective).2 hc)
    (LaurentPolynomial.isUnit_T b).ne_zero

omit [CharP K p] [IsFractionRing (LaurentPolynomial F)[X] K] in
/-- Products of monomials. -/
theorem algebraMap_monomial_mul_monomial (c c' : F) (b b' : ℤ) (l l' : ℕ) :
    algebraMap (LaurentPolynomial F)[X] K
        (C (LaurentPolynomial.C c * LaurentPolynomial.T b) * X ^ l) *
        algebraMap (LaurentPolynomial F)[X] K
          (C (LaurentPolynomial.C c' * LaurentPolynomial.T b') * X ^ l') =
      algebraMap (LaurentPolynomial F)[X] K
        (C (LaurentPolynomial.C (c * c') * LaurentPolynomial.T (b + b')) * X ^ (l + l')) := by
  rw [← map_mul]
  congr 1
  rw [map_mul, LaurentPolynomial.T_add, pow_add]
  simp only [map_mul]
  ring

/-- **`ζ = (u, Y, t)` is a `p`-basis of `K = Frac F[Y, Y⁻¹][t]`**
(`lem:sg-pbasis-basics`(2),(4)). -/
theorem IsPBasis.isPBasis_algebraMap_laurentFamily (hu : IsPBasis p u) :
    IsPBasis p (algebraMap (LaurentPolynomial F)[X] K ∘ fun o : Option (Option σ) =>
      o.elim X fun o' => C (o'.elim (LaurentPolynomial.T 1) fun i => LaurentPolynomial.C (u i))) :=
  hu.laurentPolynomial.polynomial.map_of_isFractionRing

/-- The Jacobian of `z = (t, g_o Y)` with respect to `ζ = (u, Y, t)` in `K`. -/
theorem IsPBasis.jac_algebraMap_coneFamily (hu : IsPBasis p u) (g : Option σ → F) :
    (hu.isPBasis_algebraMap_laurentFamily (K := K)).jac
        (algebraMap (LaurentPolynomial F)[X] K ∘ coneFamily g) =
      algebraMap (LaurentPolynomial F)[X] K (C (LaurentPolynomial.C (coneJacMatrix hu g).det *
        LaurentPolynomial.T (Fintype.card σ : ℤ))) := by
  rw [IsPBasis.jac_map (algebraMap _ K) hu.laurentPolynomial.polynomial, hu.jac_coneFamily]

/-- **The cone family is a `p`-basis of `K`** when `det N ≠ 0` (the Jacobian `J(z/ζ)` is then a
unit). -/
theorem IsPBasis.isPBasis_algebraMap_coneFamily (hu : IsPBasis p u) (g : Option σ → F)
    (hd : (coneJacMatrix hu g).det ≠ 0) :
    IsPBasis p (algebraMap (LaurentPolynomial F)[X] K ∘ coneFamily g) := by
  refine (hu.isPBasis_algebraMap_laurentFamily (K := K)).of_isUnit_jac ?_
  rw [hu.jac_algebraMap_coneFamily]
  refine isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective _ K)).2 ?_)
  simpa using C_C_mul_T_mul_X_pow_ne_zero hd (Fintype.card σ : ℤ) 0

/-- **`lem:sg-homog-pbasis`(2), explicit form.** For the cone family `z = (t, g_o Y)` with
`det N ≠ 0`, `n = |σ|` and `Q = p^e`: `Φ^e_z(c Y^b t^λ) = Φ^e_ζ(J(z/ζ)^{-(Q-1)} c Y^b t^λ)` is
`Φ^e_u((det N)^{-(Q-1)} c) Y^{⌊(b - n(Q - 1))/Q⌋} t^{⌊λ/Q⌋}` if `b - n(Q - 1) ≡ λ ≡ Q - 1 (mod Q)`,
and `0` otherwise. -/
theorem IsPBasis.traceIter_algebraMap_coneFamily (hu : IsPBasis p u) (g : Option σ → F)
    (hd : (coneJacMatrix hu g).det ≠ 0) (e : ℕ) (c : F) (b : ℤ) (l : ℕ) :
    (hu.isPBasis_algebraMap_coneFamily (K := K) g hd).traceIter e
        (algebraMap _ K (C (LaurentPolynomial.C c * LaurentPolynomial.T b) * X ^ l)) =
      if (b - Fintype.card σ * ((p : ℤ) ^ e - 1)) % (p : ℤ) ^ e = (p : ℤ) ^ e - 1 ∧
          l % p ^ e = p ^ e - 1 then
        algebraMap _ K (C (LaurentPolynomial.C (hu.traceIter e
            ((coneJacMatrix hu g).det⁻¹ ^ (p ^ e - 1) * c)) *
          LaurentPolynomial.T ((b - Fintype.card σ * ((p : ℤ) ^ e - 1)) / (p : ℤ) ^ e)) *
            X ^ (l / p ^ e))
      else 0 := by
  set hζK := hu.isPBasis_algebraMap_laurentFamily (K := K)
  set hzK := hu.isPBasis_algebraMap_coneFamily (K := K) g hd
  set d := (coneJacMatrix hu g).det
  set n : ℤ := (Fintype.card σ : ℤ)
  have hq1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.out.pos
  have hcast : ((p ^ e - 1 : ℕ) : ℤ) = (p : ℤ) ^ e - 1 := by push_cast [Nat.cast_sub hq1]; ring
  -- `J(ζ/z) = J(z/ζ)⁻¹ = d⁻¹ Y^{-n}`
  have hinv : hzK.jac (algebraMap (LaurentPolynomial F)[X] K ∘ fun o : Option (Option σ) =>
      o.elim X fun o' => C (o'.elim (LaurentPolynomial.T 1) fun i => LaurentPolynomial.C (u i))) =
      algebraMap _ K (C (LaurentPolynomial.C d⁻¹ * LaurentPolynomial.T (-n))) := by
    have h1 : algebraMap (LaurentPolynomial F)[X] K (C (LaurentPolynomial.C d *
        LaurentPolynomial.T n)) * hzK.jac (algebraMap (LaurentPolynomial F)[X] K ∘
          fun o : Option (Option σ) => o.elim X fun o' =>
            C (o'.elim (LaurentPolynomial.T 1) fun i => LaurentPolynomial.C (u i))) = 1 := by
      have := IsPBasis.jac_mul_jac hζK hzK
      rwa [hu.jac_algebraMap_coneFamily] at this
    refine (eq_inv_of_mul_eq_one_right h1).trans (inv_eq_of_mul_eq_one_right ?_)
    have h2 := algebraMap_monomial_mul_monomial (K := K) d d⁻¹ n (-n) 0 0
    simpa [mul_inv_cancel₀ hd] using h2
  rw [IsPBasis.traceIter_eq_traceIter_jac_pow_mul hζK hzK, hinv, ← map_pow]
  have h3 : (C (LaurentPolynomial.C d⁻¹ * LaurentPolynomial.T (-n)) :
      (LaurentPolynomial F)[X]) ^ (p ^ e - 1) =
      C (LaurentPolynomial.C (d⁻¹ ^ (p ^ e - 1)) * LaurentPolynomial.T (-(n * ((p : ℤ) ^ e - 1))))
        * X ^ 0 := by
    rw [pow_zero, mul_one, ← map_pow, mul_pow, ← map_pow, LaurentPolynomial.T_pow, hcast]
    ring_nf
  rw [h3, algebraMap_monomial_mul_monomial, zero_add, show -(n * ((p : ℤ) ^ e - 1)) + b =
    b - n * ((p : ℤ) ^ e - 1) by ring]
  rw [IsPBasis.traceIter_map (algebraMap (LaurentPolynomial F)[X] K)
    hu.laurentPolynomial.polynomial hζK, hu.traceIter_laurentFamily_monomial]
  split_ifs <;> simp

/-- **`lem:sg-homog-pbasis`(2).** `Φ^e_z(c Y^b t^λ)` is either `0` or a monomial `c' Y^{b'} t^{λ'}`
with `Q b' = b - (n + 1)(Q - 1)` and `Q λ' = λ - (Q - 1)` (`n = |σ|`, `Q = p^e`). -/
theorem IsPBasis.exists_traceIter_algebraMap_coneFamily_eq (hu : IsPBasis p u) (g : Option σ → F)
    (hd : (coneJacMatrix hu g).det ≠ 0) (e : ℕ) (c : F) (b : ℤ) (l : ℕ) :
    (hu.isPBasis_algebraMap_coneFamily (K := K) g hd).traceIter e
        (algebraMap _ K (C (LaurentPolynomial.C c * LaurentPolynomial.T b) * X ^ l)) = 0 ∨
      ∃ (c' : F) (b' : ℤ) (l' : ℕ),
        (p : ℤ) ^ e * b' + (Fintype.card σ + 1) * ((p : ℤ) ^ e - 1) = b ∧
        p ^ e * l' + (p ^ e - 1) = l ∧
        (hu.isPBasis_algebraMap_coneFamily (K := K) g hd).traceIter e
            (algebraMap _ K (C (LaurentPolynomial.C c * LaurentPolynomial.T b) * X ^ l)) =
          algebraMap _ K (C (LaurentPolynomial.C c' * LaurentPolynomial.T b') * X ^ l') := by
  rw [hu.traceIter_algebraMap_coneFamily g hd]
  split_ifs with h
  · refine Or.inr ⟨_, _, _, ?_, ?_, rfl⟩
    · have := Int.mul_ediv_add_emod (b - Fintype.card σ * ((p : ℤ) ^ e - 1)) ((p : ℤ) ^ e)
      rw [h.1] at this
      linarith
    · have := Nat.div_add_mod l (p ^ e)
      rw [h.2] at this
      exact this
  · exact Or.inl rfl

end FractionField

end EnvelopeProperty.Cartier
