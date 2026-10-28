/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.MvPolynomial.Nilpotent
import EnvelopeProperty.AlgGeom.KrullDim

/-!
# Noether normalizations adapted to a closed subset and a point

This file contains the finiteness part of the proof of Fang–Han–Xia, *The envelope property for
unibranch projective varieties*, Lemma 5.23 (`lem:projection-existence`), done affinely: instead of
general linear projections of a projective closure (FHX, Wu Lemma 6.16, Stacks Tag 0B1Q) we modify a
Noether normalization of `A = k[Y]` by explicit substitutions which keep `A` integral over the new
coordinates.

* `exists_forall_isIntegral_adjoin_pow_sub` (**the Nagata twist**): if `A` is integral over `R[T]`
  and `a ∈ A`, then `A` is integral over `R[T ^ f - a]` for all large `f`. Iterated in
  `exists_forall_isIntegral_adjoin_twist`, it lets us prescribe the coordinates `yᵢ = tᵢ ^ fᵢ - aᵢ`
  modulo `tᵢ ^ fᵢ`: the `aᵢ` are arbitrary, and the `tᵢ ^ fᵢ` are harmless for the closed immersion
  condition (they lie in `𝔪²` if `tᵢ ∈ 𝔪`, `fᵢ ≥ 2`, or in `I` if `tᵢ ∈ I`) and for separability
  (`d(tᵢ ^ fᵢ) = 0` if the characteristic divides `fᵢ`).
* `exists_isIntegral_adjoin_cons` (**Nagata substitution**): a nonconstant polynomial `G(τ)` in
  Noether coordinates `τ` can be made a Noether coordinate itself; this provides a Noether
  coordinate in the ideal `I` of `Z`. The proof reuses Mathlib's substitution
  `Xᵢ ↦ Xᵢ + X₀ ^ {rᵢ}` from `Mathlib.RingTheory.NoetherNormalization` (private there, copied in
  `EnvelopeProperty.NagataSubstitution`).
* `exists_forall_mem_isIntegral_adjoin`: centering the coordinates at a rational point;
  `bijective_algebraMap_quotient_of_isMaximal` (Nullstellensatz).
* `ringKrullDim_eq_of_isIntegral_of_injective`: a Noether normalization `k[X₁, …, Xₛ] → A` has
  `s = dim A` (going up, `Ideal.exists_ltSeries_of_hasGoingUp`);
  `injective_of_isIntegral_of_ringKrullDim_eq`: an integral `k[X₁, …, Xₙ] → A` with `dim A = n`,
  `A` a domain, is injective.
-/

open Polynomial

namespace EnvelopeProperty

section integral

/-- Integrality over a subalgebra only depends on its elements: if every element of `S₁` lies in
`S₂` (subalgebras over possibly different base rings), integrality over `S₁` implies integrality
over `S₂`. -/
theorem isIntegral_of_forall_mem {R₁ R₂ A : Type*} [CommRing R₁] [CommRing R₂] [CommRing A]
    [Algebra R₁ A] [Algebra R₂ A] {S₁ : Subalgebra R₁ A} {S₂ : Subalgebra R₂ A}
    (h : ∀ y ∈ S₁, y ∈ S₂) {x : A} (hx : IsIntegral S₁ x) : IsIntegral S₂ x := by
  let ψ : S₁ →+* S₂ :=
    { toFun := fun y => ⟨y, h y y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let := ψ.toAlgebra
  have : IsScalarTower S₁ S₂ A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact hx.tower_top

/-- **Transitivity of integrality over subalgebras.** If every element of `S₂` is integral over
`S₁`, every element integral over `S₂` is integral over `S₁`. -/
theorem isIntegral_trans_of_forall_mem {R₁ R₂ A : Type*} [CommRing R₁] [CommRing R₂] [CommRing A]
    [Algebra R₁ A] [Algebra R₂ A] {S₁ : Subalgebra R₁ A} {S₂ : Subalgebra R₂ A}
    (h : ∀ y ∈ S₂, IsIntegral S₁ y) {x : A} (hx : IsIntegral S₂ x) : IsIntegral S₁ x := by
  let C := integralClosure S₁ A
  have hC : IsIntegral C x := isIntegral_of_forall_mem (S₂ := C) (fun y hy => h y hy) hx
  exact isIntegral_trans x hC

end integral

section twist

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **The Nagata twist.** Let `A` be integral over `R[T]` and `a ∈ A`. For all large `f`, `A` is
integral over `R[T ^ f - a]`.

If `a` satisfies `a ^ m + ∑_{j < m} q_j(T) a ^ j = 0` with `q_j ∈ R[X]` of degree `< f`, then `T`
is a root of `G(X) = Q ^ m + ∑_{j < m} q_j(X) Q ^ j`, `Q = X ^ f - (T ^ f - a)`, which is monic of
degree `f m` over `R[T ^ f - a]`; so `T`, hence `R[T]`, hence `A` is integral over
`R[T ^ f - a]`. -/
theorem exists_forall_isIntegral_adjoin_pow_sub (T a : A)
    (hA : ∀ x : A, IsIntegral (Algebra.adjoin R {T}) x) :
    ∃ N : ℕ, ∀ f : ℕ, N ≤ f → ∀ x : A, IsIntegral (Algebra.adjoin R {T ^ f - a}) x := by
  classical
  obtain ⟨p, hpm, hpa⟩ := hA a
  set m := p.natDegree
  -- the coefficients of `p` as polynomials in `T`
  have hcoeff : ∀ j, ∃ q : R[X], aeval T q = (p.coeff j : A) := fun j => by
    have h2 : (p.coeff j : A) ∈ (aeval T : R[X] →ₐ[R] A).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (p.coeff j).2
    obtain ⟨q, hq⟩ := h2
    exact ⟨q, hq⟩
  choose q hq using hcoeff
  refine ⟨(Finset.range m).sup (fun j => (q j).natDegree) + 1, fun f hf x => ?_⟩
  rcases subsingleton_or_nontrivial A with hA0 | hA0
  · exact ⟨X, monic_X, Subsingleton.elim _ _⟩
  have hf1 : f ≠ 0 := by omega
  set S' := Algebra.adjoin R {T ^ f - a}
  let T' : S' := ⟨T ^ f - a, Algebra.subset_adjoin rfl⟩
  let Q : S'[X] := X ^ f - C T'
  have hQ : Q.Monic := monic_X_pow_sub_C T' hf1
  have hQdeg : Q.natDegree = f := natDegree_X_pow_sub_C
  let G : S'[X] := Q ^ m + ∑ j ∈ Finset.range m, (q j).map (algebraMap R S') * Q ^ j
  have hGm : G.Monic := by
    refine (hQ.pow m).add_of_left ?_
    rw [degree_eq_natDegree (hQ.pow m).ne_zero, hQ.natDegree_pow, hQdeg]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro j hj
    rw [Finset.mem_range] at hj
    refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    rw [degree_eq_natDegree (hQ.pow j).ne_zero, hQ.natDegree_pow, hQdeg]
    have hqj : (q j).natDegree < f := by
      have := Finset.le_sup (f := fun j => (q j).natDegree) (Finset.mem_range.mpr hj)
      omega
    have hdeg : ((q j).map (algebraMap R S')).degree < f :=
      lt_of_le_of_lt (degree_map_le) (lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hqj))
    calc ((q j).map (algebraMap R S')).degree + ↑(j * f)
        < ↑f + ↑(j * f) := by
          exact WithBot.add_lt_add_right (WithBot.coe_ne_bot) hdeg
      _ = ↑((j + 1) * f) := by push_cast; ring
      _ ≤ ↑(m * f) := by exact_mod_cast Nat.mul_le_mul_right f hj
  have hQT : aeval T Q = a := by
    simp [Q, T']
  have hGT : aeval T G = 0 := by
    have hp := hpm.as_sum
    rw [← hpa]
    conv_rhs => rw [hp]
    simp only [G, map_add, map_pow, map_sum, map_mul, hQT, eval₂_add, eval₂_X_pow, eval₂_finsetSum,
      eval₂_mul, eval₂_C, eval₂_X_pow, aeval_map_algebraMap, hq]
    rfl
  have hTint : IsIntegral S' T := ⟨G, hGm, hGT⟩
  -- every element of `R[T]` is integral over `S'`
  have hle : ∀ y ∈ Algebra.adjoin R {T}, IsIntegral S' y := by
    intro y hy
    have : Algebra.adjoin R {T} ≤ (integralClosure S' A).restrictScalars R :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hTint)
    exact this hy
  exact isIntegral_trans_of_forall_mem hle (hA x)

/-- The range of a family is its value at `j` together with the image of the other indices. -/
theorem range_eq_insert_image_compl {ι α : Type*} (y : ι → α) (j : ι) :
    Set.range y = insert (y j) (y '' {j}ᶜ) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    by_cases h : i = j
    · subst h; exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨i, h, rfl⟩
  · rintro (rfl | ⟨i, -, rfl⟩) <;> exact ⟨_, rfl⟩

/-- `adjoin R (insert U S)` is `adjoin R S` with `U` adjoined. -/
theorem mem_adjoin_insert_iff (S : Set A) (U y : A) :
    y ∈ Algebra.adjoin R (insert U S) ↔ y ∈ Algebra.adjoin (Algebra.adjoin R S) {U} := by
  rw [Set.insert_eq, Set.union_comm, Algebra.adjoin_union_eq_adjoin_adjoin,
    Subalgebra.mem_restrictScalars]

/-- **The Nagata twist, set version.** If `A` is integral over `R[T, S]`, then for all large `f`
it is integral over `R[T ^ f - a, S]`. -/
theorem exists_forall_isIntegral_adjoin_insert_pow_sub (S : Set A) (T a : A)
    (h : ∀ x : A, IsIntegral (Algebra.adjoin R (insert T S)) x) :
    ∃ N : ℕ, ∀ f : ℕ, N ≤ f →
      ∀ x : A, IsIntegral (Algebra.adjoin R (insert (T ^ f - a) S)) x := by
  obtain ⟨N, hN⟩ := exists_forall_isIntegral_adjoin_pow_sub (R := Algebra.adjoin R S) T a
    (fun x => isIntegral_of_forall_mem (fun y hy => (mem_adjoin_insert_iff S T y).mp hy) (h x))
  exact ⟨N, fun f hf x => isIntegral_of_forall_mem
    (fun y hy => (mem_adjoin_insert_iff S _ y).mpr hy) (hN f hf x)⟩

/-- **Iterated Nagata twists.** Let `A` be integral over `R[t₁, …, tₙ]`, `a₁, …, aₙ ∈ A`,
`J` a set of indices and `P` a property of natural numbers holding for arbitrarily large numbers.
There are exponents `f_i` with `P (f_i)` such that `A` is integral over the algebra generated by
`t_i ^ f_i - a_i` (`i ∈ J`) and `t_i` (`i ∉ J`). -/
theorem exists_forall_isIntegral_adjoin_twist (P : ℕ → Prop) (hP : ∀ N, ∃ f, N ≤ f ∧ P f)
    {n : ℕ} (t a : Fin n → A) (J : Finset (Fin n))
    (ht : ∀ x : A, IsIntegral (Algebra.adjoin R (Set.range t)) x) :
    ∃ f : Fin n → ℕ, (∀ i, P (f i)) ∧ ∀ x : A,
      IsIntegral (Algebra.adjoin R
        (Set.range fun i => if i ∈ J then t i ^ f i - a i else t i)) x := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    obtain ⟨f₀, -, hf₀⟩ := hP 0
    refine ⟨fun _ => f₀, fun _ => hf₀, ?_⟩
    have : (fun i => if i ∈ (∅ : Finset (Fin n)) then t i ^ f₀ - a i else t i) = t := by
      funext i; simp
    rw [this]; exact ht
  | insert j J hj ih =>
    obtain ⟨f, hfP, hf⟩ := ih
    set y := fun i => if i ∈ J then t i ^ f i - a i else t i with hy
    have hyj : y j = t j := by simp [hy, hj]
    have hf' : ∀ x : A, IsIntegral (Algebra.adjoin R (insert (t j) (y '' {j}ᶜ))) x := by
      rw [← hyj, ← range_eq_insert_image_compl y j]; exact hf
    obtain ⟨N, hN⟩ := exists_forall_isIntegral_adjoin_insert_pow_sub (y '' {j}ᶜ) (t j) (a j) hf'
    obtain ⟨g, hgN, hgP⟩ := hP N
    refine ⟨Function.update f j g, fun i => ?_, fun x => ?_⟩
    · by_cases hi : i = j
      · subst hi; simpa using hgP
      · simpa [Function.update_of_ne hi] using hfP i
    · set y' := fun i => if i ∈ insert j J then t i ^ Function.update f j g i - a i else t i
      have h1 : y' j = t j ^ g - a j := by simp [y']
      have h2 : y' '' {j}ᶜ = y '' {j}ᶜ := Set.image_congr fun i hi => by
        have hi' : i ≠ j := hi
        simp [y', hy, hi']
      rw [range_eq_insert_image_compl y' j, h1, h2]
      exact hN g hgN x

end twist

/-! ### Nagata substitution

The lemmas in `EnvelopeProperty.NagataSubstitution` up to `isUnit_leadingCoeff_finSuccEquiv_T`
are copied, with the same proofs, from the private part of
`Mathlib.RingTheory.NoetherNormalization` (© 2025 Sihan Su, Riccardo Brasca, Wan Lin, Xiaoyang Su,
Apache 2.0), where they are used to prove Noether normalization; we need them for
`exists_isIntegral_adjoin_cons`. -/

section NS
open MvPolynomial Ideal Nat RingHom List

namespace NagataSubstitution

variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)

local notation3 "up" => 2 + f.totalDegree

variable {f v} in
private lemma lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  grind

local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

/-- The substitution `X_i ↦ X_i + c X_0 ^ {r_i}` (`i ≠ 0`), `X_0 ↦ X_0`. -/
noncomputable abbrev T1 (c : k) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ r i

private lemma t1_comp_t1_neg (c : k) : (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

/-- The Nagata automorphism `X_i ↦ X_i + X_0 ^ {r_i}` (`i ≠ 0`). -/
noncomputable abbrev T := AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
  (t1_comp_t1_neg f 1) (by simpa using t1_comp_t1_neg f (-1))

private lemma sum_r_mul_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine ne <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up vlt) (lt_up wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
    Fin.val_cast, mul_comm, sum_ofFn] using! h

private lemma degreeOf_zero_t {a : k} (ha : a ≠ 0) : ((T f) (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r i) * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
    ite_false, one_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ, algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp <| by simp [add_comm, leadingCoeff_X_pow_add_C])
  rw [natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul,
    add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm])

private lemma degreeOf_t_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (T f <| monomial v <| coeff v f).degreeOf 0 ≠
    (T f <| monomial w <| coeff w f).degreeOf 0 := by
  rw [degreeOf_zero_t _ _ <| mem_support_iff.mp hv, degreeOf_zero_t _ _ <| mem_support_iff.mp hw]
  refine sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

private lemma leadingCoeff_finSuccEquiv_t :
    (finSuccEquiv k n ((T f) ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap k _ (coeff v f) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
      eval₂Hom_C, coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv k n) ((T1 f) 1 (X j))).leadingCoeff = 1 := fun j ↦ by
      by_cases h : j = 0
      · simp [h, finSuccEquiv_apply]
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_neg h, one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

/-- The Nagata automorphism makes a nonzero `f` a polynomial in `X_0` with invertible leading
coefficient (Mathlib's private `NoetherNormalization.T_leadingcoeff_isUnit`). -/
theorem isUnit_leadingCoeff_finSuccEquiv_T (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (T f f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (T f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n ((T f) (h x))).degree <
      (finSuccEquiv k n ((T f) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using degreeOf_t_ne_of_ne f _ _ h1 vin <| ne_of_not_mem_cons h2
  have coeff : (finSuccEquiv k n ((T f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n ((T f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n ((T f) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem vin h]
  rw [leadingCoeff_finSuccEquiv_t] at coeff
  simpa only [coeff, algebraMap_eq] using (mem_support_iff.mp vin).isUnit.map MvPolynomial.C

/-- Evaluating `H` at `(x₀, v)` is evaluating `finSuccEquiv H` (a polynomial in `X₀` with
coefficients in `k[X₁, …, Xₙ]`) at `x₀` after evaluating its coefficients at `v`. -/
theorem aeval_cons_eq_eval_map {A : Type*} [CommRing A] [Algebra k A] (x₀ : A) (v : Fin n → A)
    (H : MvPolynomial (Fin (n + 1)) k) :
    aeval (Fin.cons x₀ v) H =
      Polynomial.eval x₀ ((finSuccEquiv k n H).map
        (MvPolynomial.aeval (R := k) v).toRingHom) := by
  let Φ : MvPolynomial (Fin (n + 1)) k →ₐ[k] A :=
    ((Polynomial.aeval x₀).restrictScalars k).comp
      ((Polynomial.mapAlgHom (MvPolynomial.aeval v)).comp (finSuccEquiv k n).toAlgHom)
  have : MvPolynomial.aeval (Fin.cons x₀ v) = Φ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    cases i using Fin.cases with
    | zero => simp [Φ, finSuccEquiv_X_zero]
    | succ j => simp [Φ, finSuccEquiv_X_succ]
  rw [this]
  simp [Φ, Polynomial.eval_map]

end NagataSubstitution

section substitution

variable {k : Type*} [Field k]

open NagataSubstitution in
/-- **Nagata substitution: a nonconstant polynomial as a Noether coordinate.** Let `A` be integral
over `k[τ₀, …, τₘ]` and `G ∈ k[X₀, …, Xₘ]` nonconstant. There are `t₀, …, tₘ ∈ A` with
`t₀ = G(τ)` and `A` integral over `k[t₀, …, tₘ]`: take `tᵢ = τᵢ - τ₀ ^ {rᵢ}` (`i ≠ 0`) for the
exponents of Mathlib's proof of Noether normalization, which make `G(τ₀, t₁ + τ₀ ^ {r₁}, …)` a
polynomial in `τ₀` with invertible leading coefficient over `k[t₁, …, tₘ]`. -/
theorem exists_isIntegral_adjoin_cons {A : Type*} [CommRing A] [Algebra k A] {m : ℕ}
    (τ : Fin (m + 1) → A) (hτ : ∀ x : A, IsIntegral (Algebra.adjoin k (Set.range τ)) x)
    (G : MvPolynomial (Fin (m + 1)) k) (hG : ∀ c : k, G ≠ MvPolynomial.C c) :
    ∃ t : Fin (m + 1) → A, t 0 = aeval τ G ∧
      ∀ x : A, IsIntegral (Algebra.adjoin k (Set.range t)) x := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨τ, Subsingleton.elim _ _, fun x => ⟨Polynomial.X, Polynomial.monic_X,
      Subsingleton.elim _ _⟩⟩
  have hG0 : G ≠ 0 := by simpa using hG 0
  let t : Fin (m + 1) → A :=
    Fin.cons (aeval τ G) (fun i => τ i.succ - τ 0 ^ ((2 + G.totalDegree) ^ (i.succ : ℕ)))
  refine ⟨t, rfl, ?_⟩
  set S := Algebra.adjoin k (Set.range t)
  have htS : ∀ i, t i ∈ S := fun i => Algebra.subset_adjoin ⟨i, rfl⟩
  -- `G(τ) = (T G)(τ₀, t₁, …, tₘ)`
  have hev : aeval (Fin.cons (τ 0) (fun i => t i.succ)) (T G G) = aeval τ G := by
    change aeval (Fin.cons (τ 0) (fun i => t i.succ)) (T1 G 1 G) = aeval τ G
    rw [← AlgHom.comp_apply, comp_aeval]
    congr 2
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => simp [t]
  -- the polynomial over `S` with root `τ₀`
  set Q0 := finSuccEquiv k m (T G G)
  let ψ : MvPolynomial (Fin m) k →+* S :=
    (aeval (fun i => (⟨t i.succ, htS _⟩ : S)) : MvPolynomial (Fin m) k →ₐ[k] S)
  have hu : IsUnit (ψ Q0.leadingCoeff) := (isUnit_leadingCoeff_finSuccEquiv_T G hG0).map ψ
  have hu0 : ψ Q0.leadingCoeff ≠ 0 := hu.ne_zero
  have hdeg : 0 < Q0.natDegree := by
    by_contra h0
    have hQ0 : Q0 = Polynomial.C (Q0.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (by omega)
    obtain ⟨c, hc⟩ : ∃ c : k, Q0.coeff 0 = MvPolynomial.C c := by
      have hlc : Q0.leadingCoeff = Q0.coeff 0 := by
        rw [Polynomial.leadingCoeff, show Q0.natDegree = 0 by omega]
      obtain ⟨c, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp
        (hlc ▸ isUnit_leadingCoeff_finSuccEquiv_T G hG0)
      exact ⟨c, hc.2⟩
    apply hG c
    apply (T G).injective
    apply (finSuccEquiv k m).injective
    change Q0 = _
    rw [hQ0, hc]
    simp [finSuccEquiv_apply]
  let P : S[X] := Q0.map ψ - Polynomial.C ⟨t 0, htS 0⟩
  have hPdeg : (Q0.map ψ).natDegree = Q0.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero ψ hu0
  have hPlc : P.leadingCoeff = ψ Q0.leadingCoeff := by
    rw [Polynomial.leadingCoeff_sub_of_degree_lt,
      Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero ψ hu0]
    refine lt_of_le_of_lt Polynomial.degree_C_le ?_
    rw [Polynomial.degree_eq_natDegree (fun h => by simp [h] at hPdeg; omega), hPdeg]
    exact_mod_cast hdeg
  have hroot : Polynomial.aeval (τ 0) P = 0 := by
    have h1 : (Q0.map ψ).map (algebraMap S A) =
        Q0.map (MvPolynomial.aeval (R := k) (fun i : Fin m => t i.succ)).toRingHom := by
      rw [Polynomial.map_map]
      congr 1
      refine RingHom.ext fun H => ?_
      change ((MvPolynomial.aeval (fun i : Fin m => (⟨t i.succ, htS _⟩ : S)) H : S) : A) =
        MvPolynomial.aeval (fun i : Fin m => t i.succ) H
      rw [← Subalgebra.val_apply, ← AlgHom.comp_apply, comp_aeval]
      rfl
    simp only [P, map_sub, Polynomial.aeval_C]
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, h1, ← aeval_cons_eq_eval_map, hev]
    simp [t]
  have h0int : IsIntegral S (τ 0) := by
    have := isIntegral_leadingCoeff_smul P (τ 0) hroot
    rw [hPlc] at this
    obtain ⟨u, hu'⟩ := hu
    have h2 : τ 0 = (↑u⁻¹ : S) • (ψ Q0.leadingCoeff • τ 0) := by
      rw [← hu', smul_smul, Units.inv_mul, one_smul]
    rw [h2]
    exact IsIntegral.smul _ this
  -- every `τᵢ` is integral over `S`
  have hτint : ∀ i, IsIntegral S (τ i) := by
    intro i
    cases i using Fin.cases with
    | zero => exact h0int
    | succ j =>
      have : τ j.succ = t j.succ + τ 0 ^ ((2 + G.totalDegree) ^ (j.succ : ℕ)) := by simp [t]
      rw [this]
      exact (isIntegral_algebraMap (x := (⟨t j.succ, htS _⟩ : S))).add (h0int.pow _)
  have hle : ∀ y ∈ Algebra.adjoin k (Set.range τ), IsIntegral S y := by
    intro y hy
    have : Algebra.adjoin k (Set.range τ) ≤ (integralClosure S A).restrictScalars k :=
      Algebra.adjoin_le (Set.range_subset_iff.mpr hτint)
    exact this hy
  exact fun x => isIntegral_trans_of_forall_mem hle (hτ x)

end substitution

end NS

/-- **Nullstellensatz.** The residue field of a maximal ideal of an algebra of finite type over an
algebraically closed field `k` is `k`. -/
theorem bijective_algebraMap_quotient_of_isMaximal (k : Type*) {A : Type*} [Field k]
    [IsAlgClosed k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (𝔪 : Ideal A)
    [𝔪.IsMaximal] : Function.Bijective (algebraMap k (A ⧸ 𝔪)) := by
  let := Ideal.Quotient.field 𝔪
  have : Module.Finite k (A ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ 𝔪)
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- **Centering Noether coordinates at a rational point.** If `A / 𝔪 = k`, subtracting constants
from `t₁, …, tₙ` gives elements of `𝔪` generating the same subalgebra (so `A` stays integral over
it), leaving unchanged those `tᵢ` already in `𝔪`. -/
theorem exists_forall_mem_isIntegral_adjoin {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (𝔪 : Ideal A) (h𝔪 : Function.Surjective (algebraMap k (A ⧸ 𝔪))) {n : ℕ} (t : Fin n → A)
    (ht : ∀ x : A, IsIntegral (Algebra.adjoin k (Set.range t)) x) :
    ∃ t' : Fin n → A, (∀ i, t' i ∈ 𝔪) ∧ (∀ i, t i ∈ 𝔪 → t' i = t i) ∧
      ∀ x : A, IsIntegral (Algebra.adjoin k (Set.range t')) x := by
  have hc : ∀ i, ∃ c : k, t i - algebraMap k A c ∈ 𝔪 ∧ (t i ∈ 𝔪 → c = 0) := fun i => by
    by_cases hi : t i ∈ 𝔪
    · exact ⟨0, by simpa using hi, fun _ => rfl⟩
    · obtain ⟨c, hc⟩ := h𝔪 (Ideal.Quotient.mk 𝔪 (t i))
      refine ⟨c, ?_, fun h => absurd h hi⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc, Ideal.Quotient.mk_algebraMap, sub_self]
  choose c hc1 hc2 using hc
  refine ⟨fun i => t i - algebraMap k A (c i), hc1, fun i hi => by simp [hc2 i hi], fun x => ?_⟩
  refine isIntegral_of_forall_mem (fun y hy => ?_) (ht x)
  have : Algebra.adjoin k (Set.range t) ≤
      Algebra.adjoin k (Set.range fun i => t i - algebraMap k A (c i)) := by
    refine Algebra.adjoin_le (Set.range_subset_iff.mpr fun i => ?_)
    have h1 : t i - algebraMap k A (c i) ∈
        Algebra.adjoin k (Set.range fun i => t i - algebraMap k A (c i)) :=
      Algebra.subset_adjoin ⟨i, rfl⟩
    have := Subalgebra.add_mem _ h1 (Subalgebra.algebraMap_mem _ (c i))
    simpa using this
  exact this hy

/-- **Going up bounds the dimension from below.** If `f : R → S` is injective and integral, then
`dim R ≤ dim S`: a chain of primes of `R` lifts to a chain of the same length in `S` (lying over
for its first prime, then going up). -/
theorem ringKrullDim_le_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim R ≤ ringKrullDim S := by
  algebraize [f]
  have : Algebra.IsIntegral R S := ⟨hf⟩
  refine iSup_le fun l => ?_
  obtain ⟨P, -, hPp, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S) l.head.asIdeal ⊥
    (by
      rw [Ideal.comap_bot_of_injective (algebraMap R S) hinj]
      exact bot_le)
  have : P.LiesOver l.head.asIdeal := ⟨hPc.symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

/-- **Dimension of a Noether normalization.** If `A` is integral over `k[X₁, …, Xₛ]` via an
injective map, then `dim A = s`. -/
theorem ringKrullDim_eq_of_isIntegral_of_injective {k A : Type*} [Field k] [CommRing A] {s : ℕ}
    (g : MvPolynomial (Fin s) k →+* A) (hg : g.IsIntegral) (hinj : Function.Injective g) :
    ringKrullDim A = s := by
  have h := MvPolynomial.ringKrullDim_of_isNoetherianRing (R := k) (ι := Fin s)
  rw [ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  exact le_antisymm (h ▸ ringKrullDim_le_of_isIntegral g hg)
    (h ▸ ringKrullDim_le_of_isIntegral_of_injective g hg hinj)

/-- **An integral map from `k[X₁, …, Xₙ]` to a domain of dimension `n` is injective**: otherwise
`A` would be integral over a proper quotient `k[X]/𝔭`, of dimension `< n`. -/
theorem injective_of_isIntegral_of_ringKrullDim_eq {k A : Type*} [Field k] [CommRing A]
    [IsDomain A] {n : ℕ} (φ : MvPolynomial (Fin n) k →+* A) (hφ : φ.IsIntegral)
    (hdim : ringKrullDim A = n) : Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  by_contra! H
  obtain ⟨r, hr, hr0⟩ := H
  let B := MvPolynomial (Fin n) k
  have hB : ringKrullDim B = n := by
    have h := MvPolynomial.ringKrullDim_of_isNoetherianRing (R := k) (ι := Fin n)
    rwa [ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  -- `A` is integral over `B / ker φ`
  let φ' : B ⧸ RingHom.ker φ →+* A := RingHom.kerLift φ
  have hφ' : φ'.IsIntegral := by
    have : φ'.comp (Ideal.Quotient.mk (RingHom.ker φ)) = φ := by
      ext x <;> simp [φ']
    have h2 : (φ'.comp (Ideal.Quotient.mk (RingHom.ker φ))).IsIntegral := by rw [this]; exact hφ
    exact RingHom.IsIntegral.tower_top (Ideal.Quotient.mk _) φ' h2
  have h1 : ringKrullDim A ≤ ringKrullDim (B ⧸ RingHom.ker φ) :=
    ringKrullDim_le_of_isIntegral φ' hφ'
  have hle : Ideal.span {r} ≤ RingHom.ker φ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact (RingHom.mem_ker).mpr hr
  have h2 : ringKrullDim (B ⧸ RingHom.ker φ) ≤ ringKrullDim (B ⧸ Ideal.span {r}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
  have h3 : ringKrullDim (B ⧸ Ideal.span {r}) + 1 ≤ ringKrullDim B :=
    ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hr0)
  rw [hB] at h3
  rw [hdim] at h1
  have h5 : (n : WithBot ℕ∞) + 1 ≤ n := by
    calc (n : WithBot ℕ∞) + 1 ≤ ringKrullDim (B ⧸ Ideal.span {r}) + 1 := by
          gcongr; exact h1.trans h2
      _ ≤ n := h3
  exact absurd h5 (by exact_mod_cast Nat.not_succ_le_self n)

end EnvelopeProperty
