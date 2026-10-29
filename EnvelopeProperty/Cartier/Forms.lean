import EnvelopeProperty.Cartier.Exchange

/-!
# The Cartier operator on top differential forms

Let `k` be a perfect field of characteristic `p` and `F ⊇ k` a field with a `p`-basis
`y = (y_1, …, y_m)` (e.g. `F = k(y_1, …, y_m)`). Then `Ω_{F/k}` is free with basis `dy_1, …, dy_m`
(`IsPBasis.kaehlerBasis`, with coordinates `∂/∂y_i`), so `Ω^m = ⋀^m Ω_{F/k}` is free of rank one
with generator `dy = dy_1 ∧ ⋯ ∧ dy_m` (`IsPBasis.topForm`, coordinate `IsPBasis.topCoeff`), and
`dy = J(y/u) du` for another `p`-basis `u` (`IsPBasis.topForm_eq_jac_smul`).

The `e`-th Cartier operator on top forms (`IsPBasis.cartier`) is
`C_e(f dy) = Φ_y^e(f) dy`,
and it does not depend on the `p`-basis (`IsPBasis.cartier_eq`): this is the classical
coordinate-free Cartier operator `C_e : Ω^m_{F/k} → Ω^m_{F/k}`. It is additive, `p^{-e}`-linear
(`C_e(g^{p^e} ω) = g C_e ω`), and `C_e ∘ C_{e'} = C_{e+e'}` (`IsPBasis.cartier_cartier`).

In FHX this is the Frobenius trace on top forms (proof of Lemma 3.3,
`lem:divisorial-trace-estimate`, which identifies the traces of `S` and of the birational model
`V` at the common generic point with this operator).
-/

noncomputable section

open scoped NNReal ENNReal Topology

namespace EnvelopeProperty.Cartier

open Finset Module KaehlerDifferential

variable {p : ℕ} [hp : Fact p.Prime]
variable {k F : Type*} [Field k] [CharP k p] [PerfectRing k p] [Field F] [Algebra k F] [CharP F p]

/-! ### Kähler differentials -/

section Kaehler

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {y : σ → F} (hy : IsPBasis p y)

omit [CharP F p] in
include hp in
theorem algebraMap_eq_pow (c : k) :
    algebraMap k F c = (algebraMap k F ((frobeniusEquiv k p).symm c)) ^ p := by
  rw [← map_pow, frobeniusEquiv_symm_pow_p]

variable (k) in
/-- `∂/∂y_i` as a `k`-linear derivation (`k ⊆ F^p` since `k` is perfect). -/
def IsPBasis.pderivK (i : σ) : Derivation k F F :=
  Derivation.mk'
    { toFun := hy.pderiv i
      map_add' := map_add _
      map_smul' := fun c f => by
        rw [Algebra.smul_def, algebraMap_eq_pow (p := p), hy.pderiv_pow_mul, ← algebraMap_eq_pow,
          RingHom.id_apply, Algebra.smul_def] }
    fun f g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
      exact (hy.pderiv i).leibniz f g

theorem IsPBasis.pderivK_apply (i : σ) (f : F) : hy.pderivK k i f = hy.pderiv i f :=
  rfl

omit [CharP k p] [PerfectRing k p] [CharP F p] in
theorem derivation_sum_apply' {M : Type*} [AddCommGroup M] [Module F M] [Module k M]
    [IsScalarTower k F M] {ι : Type*} (s : Finset ι) (D : ι → Derivation k F M) (f : F) :
    (∑ i ∈ s, D i) f = ∑ i ∈ s, D i f := by
  rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  rfl

omit [CharP k p] [PerfectRing k p] in
include hy in
/-- A derivation (into any `F`-module) vanishing on the `p`-basis vanishes. -/
theorem IsPBasis.derivation_eq_zero_of_apply_eq_zero' {M : Type*} [AddCommGroup M] [Module F M]
    [Module k M] [IsScalarTower k F M] (E : Derivation k F M) (h : ∀ i, E (y i) = 0) : E = 0 := by
  have hpow : ∀ c : F, E (c ^ p) = 0 := by
    intro c
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]
  have hmono : ∀ n : σ → ℕ, E (mono y n) = 0 := by
    intro n
    unfold mono
    induction (univ : Finset σ) using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [prod_insert hi, Derivation.leibniz, ih, Derivation.leibniz_pow, h i]
      simp
  ext f
  rw [← hy.sum_coeff f, map_sum]
  refine sum_eq_zero fun a _ => ?_
  rw [Derivation.leibniz, hmono, hpow]
  simp

/-- `D f = ∑_i ∂f/∂y_i D y_i` for every derivation `D` (into any `F`-module). -/
theorem IsPBasis.derivation_apply_eq_sum' {M : Type*} [AddCommGroup M] [Module F M] [Module k M]
    [IsScalarTower k F M] (D : Derivation k F M) (f : F) :
    D f = ∑ i, hy.pderiv i f • D (y i) := by
  let E : Derivation k F M :=
    D - ∑ i, (LinearMap.toSpanSingleton F M (D (y i))).compDer (hy.pderivK k i)
  have hcomp : ∀ (g : F →ₗ[F] M) (D' : Derivation k F F) (x : F), g.compDer D' x = g (D' x) :=
    fun _ _ _ => rfl
  have hE : E = 0 := by
    refine hy.derivation_eq_zero_of_apply_eq_zero' E fun j => ?_
    simp only [E, Derivation.coe_sub, Pi.sub_apply, derivation_sum_apply']
    simp only [hcomp, LinearMap.toSpanSingleton_apply, pderivK_apply,
      pderiv_self, ite_smul, one_smul, zero_smul]
    rw [sum_ite_eq']
    simp
  have := congrArg (fun E : Derivation k F M => E f) hE
  simp only [E, Derivation.coe_sub, Pi.sub_apply, derivation_sum_apply', Derivation.zero_apply,
    sub_eq_zero, hcomp, LinearMap.toSpanSingleton_apply, pderivK_apply] at this
  exact this

variable (k) in
/-- The basis `dy_1, …, dy_m` of `Ω_{F/k}`. -/
def IsPBasis.kaehlerBasis : Basis σ F Ω[F⁄k] :=
  Basis.mk (v := fun i => D k F (y i))
    (LinearIndependent.of_pairwise_dual_eq_zero_one _
      (fun i => (hy.pderivK k i).liftKaehlerDifferential)
      (fun i j hij => by
        simp [Derivation.liftKaehlerDifferential_comp_D, pderivK_apply, pderiv_self, hij])
      (fun i => by simp [Derivation.liftKaehlerDifferential_comp_D, pderivK_apply, pderiv_self]))
    (by
      rw [← span_range_derivation k F]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, rfl⟩
      rw [hy.derivation_apply_eq_sum' (D k F) f]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

@[simp]
theorem IsPBasis.kaehlerBasis_apply (i : σ) : hy.kaehlerBasis k i = D k F (y i) :=
  Basis.mk_apply _ _ _

/-- The coordinates of `df` in the basis `dy` are the partial derivatives `∂f/∂y_i`. -/
theorem IsPBasis.kaehlerBasis_repr_D (f : F) (i : σ) :
    (hy.kaehlerBasis k).repr (D k F f) i = hy.pderiv i f := by
  have h : D k F f = ∑ j, hy.pderiv j f • hy.kaehlerBasis k j := by
    rw [hy.derivation_apply_eq_sum' (D k F) f]
    simp
  rw [h, Basis.repr_sum_self]

end Kaehler

/-! ### Top forms -/

section TopForms

/-- An alternating map on a free module of rank `m`, in terms of a basis:
`f v = det_e(v) • f(e)`. -/
theorem alternatingMap_eq_det_smul {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι R M)
    (f : M [⋀^ι]→ₗ[R] N) (v : ι → M) : f v = e.det v • f e := by
  have : f = e.det.smulRight (f e) := by
    refine e.ext_alternating fun w hw => ?_
    have hbij : Function.Bijective w := Finite.injective_iff_bijective.1 hw
    let π : Equiv.Perm ι := Equiv.ofBijective w hbij
    have hw' : (fun i => e (w i)) = (⇑e) ∘ π := rfl
    rw [AlternatingMap.smulRight_apply, hw', f.map_perm, e.det.map_perm, e.det_self]
    simp [Units.smul_def, Int.cast_smul_eq_zsmul]
  conv_lhs => rw [this]
  rfl

variable {m : ℕ} {y u : Fin m → F} (hy : IsPBasis p y) (hu : IsPBasis p u)

variable (k) in
/-- The top form `dy = dy_1 ∧ ⋯ ∧ dy_m ∈ Ω^m_{F/k} = ⋀^m Ω_{F/k}`. -/
def topForm (y : Fin m → F) : ⋀[F]^m (Ω[F⁄k]) :=
  exteriorPower.ιMulti F m fun i => D k F (y i)

variable (k) in
/-- The coordinate of a top form with respect to `dy`: `ω = topCoeff ω • dy`. -/
def IsPBasis.topCoeff : ⋀[F]^m (Ω[F⁄k]) →ₗ[F] F :=
  exteriorPower.alternatingMapLinearEquiv (hy.kaehlerBasis k).det

theorem IsPBasis.topCoeff_topForm : hy.topCoeff k (topForm k y) = 1 := by
  rw [topCoeff, topForm, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    show (fun i => D k F (y i)) = ⇑(hy.kaehlerBasis k) from
      funext fun i => (hy.kaehlerBasis_apply i).symm]
  exact (hy.kaehlerBasis k).det_self

theorem IsPBasis.ιMulti_eq_topCoeff_smul (v : Fin m → Ω[F⁄k]) :
    exteriorPower.ιMulti F m v = (hy.kaehlerBasis k).det v • topForm k y := by
  rw [alternatingMap_eq_det_smul (hy.kaehlerBasis k) (exteriorPower.ιMulti F m) v, topForm]
  congr 2
  funext i
  simp

/-- `Ω^m_{F/k}` is free of rank one with generator `dy`: `ω = topCoeff ω • dy`. -/
theorem IsPBasis.topCoeff_smul_topForm (ω : ⋀[F]^m (Ω[F⁄k])) :
    hy.topCoeff k ω • topForm k y = ω := by
  have h : (LinearMap.smulRight (hy.topCoeff k) (topForm k y) : ⋀[F]^m (Ω[F⁄k]) →ₗ[F] _) =
      LinearMap.id := by
    refine LinearMap.ext_on_range (exteriorPower.ιMulti_span F m (Ω[F⁄k])) fun v => ?_
    rw [LinearMap.smulRight_apply, LinearMap.id_apply, topCoeff,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, hy.ιMulti_eq_topCoeff_smul]
  exact congrArg (fun φ : ⋀[F]^m (Ω[F⁄k]) →ₗ[F] _ => φ ω) h

theorem IsPBasis.topCoeff_smul (f : F) : hy.topCoeff k (f • topForm k y) = f := by
  rw [map_smul, topCoeff_topForm, smul_eq_mul, mul_one]

include hy in
theorem IsPBasis.topForm_ne_zero : topForm k y ≠ 0 := by
  intro h
  have := hy.topCoeff_topForm (k := k)
  rw [h, map_zero] at this
  exact zero_ne_one this

omit hy in
/-- Change of `p`-basis: `dy = J(y/u) du` (for any family `y`). -/
theorem IsPBasis.topForm_eq_jac_smul (y : Fin m → F) : topForm k y = hu.jac y • topForm k u := by
  rw [topForm, hu.ιMulti_eq_topCoeff_smul, Basis.det_apply]
  congr 1
  rw [jac, ← Matrix.det_transpose (Matrix.of fun i j => hu.pderiv j (y i))]
  congr 1
  ext i j
  rw [Basis.toMatrix_apply, hu.kaehlerBasis_repr_D, Matrix.transpose_apply, Matrix.of_apply]

/-! ### The Cartier operator -/

variable (k) in
/-- The `e`-th Cartier operator on top forms, computed in the `p`-basis `y`:
`C_e(f dy) = Φ_y^e(f) dy`. By `IsPBasis.cartier_eq` it does not depend on `y`. -/
def IsPBasis.cartier (e : ℕ) (ω : ⋀[F]^m (Ω[F⁄k])) : ⋀[F]^m (Ω[F⁄k]) :=
  hy.traceIter e (hy.topCoeff k ω) • topForm k y

theorem IsPBasis.cartier_smul_topForm (e : ℕ) (f : F) :
    hy.cartier k e (f • topForm k y) = hy.traceIter e f • topForm k y := by
  rw [cartier, topCoeff_smul]

theorem IsPBasis.cartier_add (e : ℕ) (ω η : ⋀[F]^m (Ω[F⁄k])) :
    hy.cartier k e (ω + η) = hy.cartier k e ω + hy.cartier k e η := by
  rw [cartier, cartier, cartier, map_add, traceIter_add, add_smul]

/-- `C_e(g^{p^e} ω) = g C_e(ω)`. -/
theorem IsPBasis.cartier_pow_smul (e : ℕ) (g : F) (ω : ⋀[F]^m (Ω[F⁄k])) :
    hy.cartier k e (g ^ p ^ e • ω) = g • hy.cartier k e ω := by
  rw [cartier, cartier, map_smul, smul_eq_mul, traceIter_pow_mul, mul_smul]

/-- `C_e ∘ C_{e'} = C_{e+e'}`. -/
theorem IsPBasis.cartier_cartier (e e' : ℕ) (ω : ⋀[F]^m (Ω[F⁄k])) :
    hy.cartier k e (hy.cartier k e' ω) = hy.cartier k (e + e') ω := by
  rw [cartier, cartier, topCoeff_smul, traceIter_traceIter, cartier]

/-- **Independence of the Cartier operator from the `p`-basis**, first for `e = 1`. -/
theorem IsPBasis.cartier_one_eq : hy.cartier k 1 = hu.cartier k 1 := by
  funext ω
  -- write `ω = f • du`
  obtain ⟨f, rfl⟩ : ∃ f, ω = f • topForm k u := ⟨_, (hu.topCoeff_smul_topForm ω).symm⟩
  set J := hu.jac y
  have hJ : IsUnit J := hu.isUnit_jac hy
  have hdy : topForm k y = J • topForm k u := hu.topForm_eq_jac_smul y
  have hω : f • topForm k u = (f * J⁻¹) • topForm k y := by
    rw [hdy, smul_smul, mul_assoc, inv_mul_cancel₀ hJ.ne_zero, mul_one]
  rw [hu.cartier_smul_topForm, hω, hy.cartier_smul_topForm, hdy, smul_smul]
  congr 1
  simp only [traceIter_succ, traceIter_zero]
  rw [hy.trace_eq_trace_jac_pow_mul hu]
  have hp1 : p = p - 1 + 1 := (Nat.sub_add_cancel hp.out.one_lt.le).symm
  rw [show J ^ (p - 1) * f = J ^ p * (f * J⁻¹) by
    conv_rhs => rw [hp1, pow_succ]
    field_simp [hJ.ne_zero], hy.trace_pow_mul, mul_comm]

/-- **Independence of the Cartier operator from the `p`-basis**: `C_e` computed in two
`p`-bases agree; i.e. `C_e : Ω^m_{F/k} → Ω^m_{F/k}` is intrinsic. -/
theorem IsPBasis.cartier_eq (e : ℕ) : hy.cartier k e = hu.cartier k e := by
  induction e with
  | zero =>
    funext ω
    rw [cartier, cartier, traceIter_zero, traceIter_zero, hy.topCoeff_smul_topForm,
      hu.topCoeff_smul_topForm]
  | succ e ih =>
    funext ω
    rw [← hy.cartier_cartier e 1, ← hu.cartier_cartier e 1, hy.cartier_one_eq hu, ih]

end TopForms

end EnvelopeProperty.Cartier
