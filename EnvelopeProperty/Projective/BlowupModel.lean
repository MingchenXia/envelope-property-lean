/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.BiProj
import EnvelopeProperty.Projective.Subvariety

/-!
# The blowup of a projective variety along forms of one degree

Let `k` be a field with the trivial absolute value, `X = V(I) ⊆ ℙ^M` a projective subvariety
(`ProjSubvariety k M`, homogeneous coordinate ring `S = R_M / I`), and `G₀, …, G_{M'} ∈ R_M` forms
of one degree `d`, not all in `I` (`ProjSubvariety.BlowupCenter`). This file sets up the
analytification of the blowup `X' → X` of `X` along `𝔞 = (Ḡ₀, …, Ḡ_{M'})` in the bigraded model
`BiProjBerk k M M'` of `(ℙ^M × ℙ^{M'})^an` (`EnvelopeProperty.Projective.BiProj`), following the
blueprint `projective-general.tex`, nodes `def:pg-blowup`, `lem:pg-blowup-basic` and
`lem:pg-graph-point`. It is the model used for the modifications of Fang–Han–Xia, *The envelope
property for unibranch projective varieties*, Corollary 5.26 (`cor:normal-weak-global`); the
blowup charts and the surjectivity of `μ` are in `EnvelopeProperty.Projective.BlowupChart`.

## The model (`def:pg-blowup`)

Let `R_{M,M'} = k[x₀, …, x_M, y₀, …, y_{M'}]` (`MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k`,
bigraded by `deg xⱼ = (1, 0)`, `deg y_m = (0, 1)`).

* `B.subst F = F(x, G) ∈ R_M` is the substitution `xⱼ ↦ xⱼ`, `y_m ↦ G_m`; it maps bihomogeneous
  elements of bidegree `(a, b)` to forms of degree `a + b d` (`BlowupCenter.isHomogeneous_subst`).
* `B.reesMap = Θ₀ : R_{M,M'} → R_M[u]`, `xⱼ ↦ xⱼ`, `y_m ↦ G_m u`, and `B.ideal = I' = Θ₀⁻¹(I[u])`;
  this is the kernel of the map `Θ : R_{M,M'} → S[u]`, `xⱼ ↦ x̄ⱼ`, `y_m ↦ Ḡ_m u`, of the blueprint
  (`Θ₀` followed by reduction mod `I`, `ideal_eq_ker`), whose image is the Rees algebra of `𝔞`.
  (Working in `R_M[u]` avoids computing in polynomials over the quotient `S`, where instance
  unification is slow.)
* `B.an = X'^an = {v ∈ (ℙ^M × ℙ^{M'})^an : |F|_v = 0 for F ∈ I'}`, `B.proj = μ : X'^an → X^an`
  (restriction of seminorms to `R_M`, i.e. `BiProjBerk.fst`), and `B.triv = ⋆'`, the trivial
  valuation of `R_{M,M'} / I'`.

## Main results

* `lem:pg-blowup-basic`(1): `I'` is prime (an instance, `I[u]` being prime),
  `Θ₀(F) = F(x, G) u^b` for `F` of bidegree `(a, b)` (`reesMap_of_isWeightedHomogeneous`), so a
  bihomogeneous `F` lies in `I'` iff `F(x, G) ∈ I` (`mem_ideal_iff_of_isWeightedHomogeneous`);
  `I'` contains the bihomogeneous components of its elements
  (`weightedHomogeneousComponent_mem_ideal`, `mem_ideal_iff`);
  `I' ∩ R_M = I` (`rename_inl_mem_ideal_iff`); `I'` contains neither all `xⱼ` nor all `y_m`
  (`exists_X_inl_notMem_ideal`, `exists_X_inr_notMem_ideal`).
* `lem:pg-blowup-basic`(2): `B.triv ∈ X'^an` and `μ(⋆') = ⋆` (`proj_triv`).
* `lem:pg-blowup-basic`(3): `X'^an` is compact Hausdorff, and second countable for countable `k`
  (instances).
* `lem:pg-blowup-basic`(4): `μ` is well defined and continuous (`continuous_proj`).
* `lem:pg-graph-point`: for `x ∈ X^an` with `|𝔞|_x = max_m |G_m|_x ≠ 0`, the **graph point**
  `γ(x) = B.graphPoint x hx ∈ X'^an` with `|F|_{γ(x)} = |F(x, G)|_x / |𝔞|_x^b` for `F` of bidegree
  `(a, b)` (`graphPoint_val_of_isWeightedHomogeneous`, `logAbs_graphPoint_of_isWeightedHomogeneous`;
  `|𝔞|_x` is `B.centerAbs x`) and `μ(γ(x)) = x` (`proj_graphPoint`).

## Auxiliary results

`MvPolynomial.IsWeightedHomogeneous.aeval_pow_mul_pow_mul`: for `F` of weight `(a, b)` for a weight
`w : σ → ℕ × ℕ`, `F((s^{w(v)₁} t^{w(v)₂} f(v))_v) = s^a t^b F(f)`. It computes `Θ₀` here, and the
dehomogenization `δ` of the blowup charts in `BlowupChart`.
-/

open scoped NNReal ENNReal Topology

open Topology MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Rescaled substitutions into weighted homogeneous polynomials -/

section WeightedScaling

variable {R : Type*} [CommSemiring R] {σ : Type*} {L : Type*} [CommSemiring L] [Algebra R L]

/-- For a polynomial `F` of weight `(a, b)` for a weight `w : σ → ℕ × ℕ`, rescaling each variable
`v` by `s^{w(v)₁} t^{w(v)₂}` rescales `F` by `s^a t^b`:
`F((s^{w(v)₁} t^{w(v)₂} f(v))_v) = s^a t^b F(f)`. -/
theorem _root_.MvPolynomial.IsWeightedHomogeneous.aeval_pow_mul_pow_mul {w : σ → ℕ × ℕ}
    {a b : ℕ} {F : MvPolynomial σ R} (hF : F.IsWeightedHomogeneous w (a, b)) (s t : L)
    (f : σ → L) :
    aeval (fun v => s ^ (w v).1 * t ^ (w v).2 * f v) F = s ^ a * t ^ b * aeval f F := by
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => rw [map_add, map_add, ihp, ihq, mul_add]
  | monomial e r hr =>
    rw [aeval_monomial, aeval_monomial]
    have h1 : (e.sum fun v c => c * (w v).1) = a := by
      have := congrArg Prod.fst hr
      rw [Finsupp.weight_apply, Finsupp.sum, Prod.fst_sum] at this
      simpa [Finsupp.sum, mul_comm] using this
    have h2 : (e.sum fun v c => c * (w v).2) = b := by
      have := congrArg Prod.snd hr
      rw [Finsupp.weight_apply, Finsupp.sum, Prod.snd_sum] at this
      simpa [Finsupp.sum, mul_comm] using this
    have key : (e.prod fun v c => (s ^ (w v).1 * t ^ (w v).2 * f v) ^ c) =
        s ^ a * t ^ b * e.prod fun v c => f v ^ c := by
      simp only [mul_pow, Finsupp.prod_mul]
      rw [← h1, ← h2]
      congr 2
      · simp only [Finsupp.prod, Finsupp.sum, ← pow_mul, mul_comm (w _).1,
          Finset.prod_pow_eq_pow_sum]
      · simp only [Finsupp.prod, Finsupp.sum, ← pow_mul, mul_comm (w _).2,
          Finset.prod_pow_eq_pow_sum]
    rw [key]
    ring

end WeightedScaling

/-! ### The blowup centre -/

variable {k : Type u} [Field k] {M : ℕ}

/-- The **centre of a blowup** of `X = V(I) ⊆ ℙ^M` (`def:pg-blowup`): forms `G₀, …, G_{M'}` of one
degree `d`, not all in `I`. The blowup `X' → X` is the blowup of `X` along the ideal sheaf they
generate, i.e. the closure of the graph of the rational map `(G₀ : ⋯ : G_{M'})`
(`rmk:pg-blowup-model`). -/
structure ProjSubvariety.BlowupCenter (V : ProjSubvariety k M) (M' : ℕ) where
  /-- The common degree `d` of the forms `G_m`. -/
  d : ℕ
  /-- The forms `G₀, …, G_{M'}`. -/
  G : Fin (M' + 1) → MvPolynomial (Fin (M + 1)) k
  isHomogeneous : ∀ m, (G m).IsHomogeneous d
  /-- Not all `G_m` lie in `I`. -/
  exists_notMem : ∃ m, G m ∉ V.ideal

namespace ProjSubvariety.BlowupCenter

open ProjBerk

variable {V : ProjSubvariety k M} {M' : ℕ} (B : V.BlowupCenter M')

/-! ### The substitution `F ↦ F(x, G)` and the Rees map -/

/-- The substitution `F ↦ F(x, G)`, `xⱼ ↦ xⱼ`, `y_m ↦ G_m`, from `R_{M,M'}` to `R_M`. -/
def subst : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k →ₐ[k] MvPolynomial (Fin (M + 1)) k :=
  aeval (Sum.elim X B.G)

@[simp]
theorem subst_X_inl (j : Fin (M + 1)) : B.subst (X (Sum.inl j)) = X j := by
  simp [subst]

@[simp]
theorem subst_X_inr (m : Fin (M' + 1)) : B.subst (X (Sum.inr m)) = B.G m := by
  simp [subst]

/-- `f(x)(x, G) = f` for `f ∈ R_M`. -/
@[simp]
theorem subst_rename_inl (f : MvPolynomial (Fin (M + 1)) k) :
    B.subst (rename Sum.inl f) = f := by
  rw [subst, aeval_rename]
  change aeval X f = f
  exact aeval_X_left_apply f

/-- `F(x, G)` is a form of degree `a + b d` for `F` bihomogeneous of bidegree `(a, b)`. -/
theorem isHomogeneous_subst {a b : ℕ} {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    (B.subst F).IsHomogeneous (a + b * B.d) := by
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isHomogeneous_zero _ _ _
  | add p q hp hq ihp ihq => rw [map_add]; exact ihp.add ihq
  | monomial e r hr =>
    rw [subst, aeval_monomial, algebraMap_eq, Finsupp.prod]
    have hdeg : ∀ v, (Sum.elim X B.G v : MvPolynomial (Fin (M + 1)) k).IsHomogeneous
        ((biWeight M M' v).1 + (biWeight M M' v).2 * B.d) := by
      rintro (j | m)
      · simpa using isHomogeneous_X k j
      · simpa using B.isHomogeneous m
    have hsum : (∑ v ∈ e.support, e v * ((biWeight M M' v).1 + (biWeight M M' v).2 * B.d)) =
        a + b * B.d := by
      have h1 := congrArg Prod.fst hr
      have h2 := congrArg Prod.snd hr
      rw [Finsupp.weight_apply, Finsupp.sum, Prod.fst_sum] at h1
      rw [Finsupp.weight_apply, Finsupp.sum, Prod.snd_sum] at h2
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
      rw [← h1, ← h2, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [← zero_add (a + b * B.d), ← hsum]
    refine (isHomogeneous_C _ r).mul (IsHomogeneous.prod _ _ _ fun v _ => ?_)
    rw [mul_comm]
    exact (hdeg v).pow _

/-- The **Rees map** `Θ₀ : R_{M,M'} → R_M[u]`, `xⱼ ↦ xⱼ`, `y_m ↦ G_m u`. Composed with
`R_M[u] → S[u]`, `S = R_M / I`, it is the map `Θ` of `def:pg-blowup`, whose image is the Rees
algebra `S[Ḡ₀u, …, Ḡ_{M'}u]` of `𝔞`; so `I' = ker Θ = Θ₀⁻¹(I[u])` (`BlowupCenter.ideal`). -/
def reesMap :
    MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k →ₐ[k] Polynomial (MvPolynomial (Fin (M + 1)) k) :=
  aeval (Sum.elim (fun j => Polynomial.C (X j)) (fun m => Polynomial.C (B.G m) * Polynomial.X))

/-- `Θ₀(F) = F(x, G) u^b` for `F` bihomogeneous of bidegree `(a, b)`. -/
theorem reesMap_of_isWeightedHomogeneous {a b : ℕ}
    {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    B.reesMap F = Polynomial.C (B.subst F) * Polynomial.X ^ b := by
  have e : (Sum.elim (fun j => Polynomial.C (X j))
      (fun m => Polynomial.C (B.G m) * Polynomial.X) :
        Fin (M + 1) ⊕ Fin (M' + 1) → Polynomial (MvPolynomial (Fin (M + 1)) k)) =
      fun v => (1 : Polynomial (MvPolynomial (Fin (M + 1)) k)) ^ (biWeight M M' v).1 *
        Polynomial.X ^ (biWeight M M' v).2 * Polynomial.CAlgHom (R := k) (Sum.elim X B.G v) := by
    funext v
    rcases v with j | m
    · simp
    · simp only [Sum.elim_inr, biWeight_inr, pow_zero, pow_one, one_mul]
      exact mul_comm _ _
  have h2 : (aeval fun v => Polynomial.CAlgHom (R := k) (Sum.elim X B.G v)) F =
      Polynomial.C (B.subst F) :=
    (DFunLike.congr_fun (comp_aeval (Sum.elim X B.G) (Polynomial.CAlgHom (R := k))) F).symm
  rw [reesMap, e, hF.aeval_pow_mul_pow_mul, h2, one_pow, one_mul, mul_comm]

/-! ### The ideal `I'` of the blowup (`lem:pg-blowup-basic`(1)) -/

/-- The ideal `I' ⊆ R_{M,M'}` of the blowup `X' ⊆ ℙ^M × ℙ^{M'}` (`def:pg-blowup`): the kernel of
`Θ : R_{M,M'} → S[u]`, i.e. the preimage of `I[u]` under `Θ₀ = B.reesMap`. -/
def ideal : Ideal (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :=
  (V.ideal.map (Polynomial.C : MvPolynomial (Fin (M + 1)) k →+* _)).comap B.reesMap

theorem mem_ideal_iff_reesMap {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k} :
    F ∈ B.ideal ↔ ∀ n, (B.reesMap F).coeff n ∈ V.ideal := by
  rw [ideal, Ideal.mem_comap, Ideal.mem_map_C_iff]

/-- `I'` is the kernel of `Θ : R_{M,M'} → S[u]`, `xⱼ ↦ x̄ⱼ`, `y_m ↦ Ḡ_m u` (the definition of
`def:pg-blowup`): `Θ` is `Θ₀` followed by reduction of coefficients mod `I`, whose kernel is
`I[u]`. -/
theorem ideal_eq_ker :
    B.ideal = RingHom.ker ((Polynomial.mapRingHom (Ideal.Quotient.mk V.ideal)).comp
      B.reesMap.toRingHom) := by
  rw [← RingHom.comap_ker, Polynomial.ker_mapRingHom, Ideal.mk_ker]
  rfl

/-- `I'` is prime: `I[u]` is prime. -/
instance isPrime_ideal : B.ideal.IsPrime :=
  have : (V.ideal.map (Polynomial.C : MvPolynomial (Fin (M + 1)) k →+* _)).IsPrime :=
    Ideal.isPrime_map_C_of_isPrime
  Ideal.comap_isPrime _ _

/-- A bihomogeneous `F` lies in `I'` iff `F(x, G) ∈ I` (`lem:pg-blowup-basic`(1)). -/
theorem mem_ideal_iff_of_isWeightedHomogeneous {p : ℕ × ℕ}
    {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') p) : F ∈ B.ideal ↔ B.subst F ∈ V.ideal := by
  obtain ⟨a, b⟩ := p
  rw [mem_ideal_iff_reesMap, B.reesMap_of_isWeightedHomogeneous hF]
  simp only [Polynomial.coeff_C_mul_X_pow]
  refine ⟨fun h => by simpa using h b, fun h n => ?_⟩
  split_ifs
  · exact h
  · exact V.ideal.zero_mem

/-- The coefficient of `u^b` in `Θ₀(F)` is `∑_a F_{(a,b)}(x, G)`. -/
theorem coeff_reesMap (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) (b : ℕ) :
    (B.reesMap F).coeff b = ∑ p ∈ (weightSupport (biWeight M M') F).filter (fun p => b = p.2),
      B.subst (weightedHomogeneousComponent (biWeight M M') p F) := by
  conv_lhs => rw [← sum_weightSupport (w := biWeight M M') F]
  rw [map_sum, Polynomial.finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [B.reesMap_of_isWeightedHomogeneous (a := p.1) (b := p.2)
    (weightedHomogeneousComponent_isWeightedHomogeneous p F), Polynomial.coeff_C_mul_X_pow]

/-- For `F ∈ I'`, `F_{(a,b)}(x, G) ∈ I` for every bidegree: the coefficient of `u^b` in `Θ₀(F)`,
`∑_{a'} F_{(a',b)}(x, G)`, lies in `I`, and its homogeneous component of degree `a + b d` is
`F_{(a,b)}(x, G)` (`lem:pg-blowup-basic`(1)). -/
theorem subst_weightedHomogeneousComponent_mem {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F ∈ B.ideal) (p : ℕ × ℕ) :
    B.subst (weightedHomogeneousComponent (biWeight M M') p F) ∈ V.ideal := by
  obtain ⟨a, b⟩ := p
  have h1 := B.mem_ideal_iff_reesMap.1 hF b
  rw [coeff_reesMap] at h1
  have h2 := V.isHomogeneousIdeal _ h1 (a + b * B.d)
  rw [map_sum] at h2
  have h3 : ∀ q ∈ (weightSupport (biWeight M M') F).filter (fun q => b = q.2),
      homogeneousComponent (a + b * B.d)
          (B.subst (weightedHomogeneousComponent (biWeight M M') q F)) =
        if q = (a, b) then B.subst (weightedHomogeneousComponent (biWeight M M') q F) else 0 := by
    intro q hq
    have hb : b = q.2 := (Finset.mem_filter.1 hq).2
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2
      (B.isHomogeneous_subst (a := q.1) (b := q.2)
        (weightedHomogeneousComponent_isWeightedHomogeneous q F)))]
    by_cases hqa : q = (a, b)
    · rw [if_pos hqa, if_pos (by rw [hqa])]
    · rw [if_neg hqa, if_neg]
      intro h
      apply hqa
      rw [← hb] at h
      exact Prod.ext (Nat.add_right_cancel h).symm hb.symm
  rw [Finset.sum_congr rfl h3, Finset.sum_ite_eq'] at h2
  split_ifs at h2 with h
  · exact h2
  · rw [weightedHomogeneousComponent_eq_zero_of_notMem
      fun hm => h (Finset.mem_filter.2 ⟨hm, rfl⟩), map_zero]
    exact V.ideal.zero_mem

/-- `I'` contains the bihomogeneous components of its elements (`lem:pg-blowup-basic`(1)). -/
theorem weightedHomogeneousComponent_mem_ideal
    {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k} (hF : F ∈ B.ideal) (p : ℕ × ℕ) :
    weightedHomogeneousComponent (biWeight M M') p F ∈ B.ideal :=
  (B.mem_ideal_iff_of_isWeightedHomogeneous
    (weightedHomogeneousComponent_isWeightedHomogeneous p F)).2
    (B.subst_weightedHomogeneousComponent_mem hF p)

/-- `F ∈ I'` iff `F_{(a,b)}(x, G) ∈ I` for all bidegrees `(a, b)`. -/
theorem mem_ideal_iff {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k} :
    F ∈ B.ideal ↔
      ∀ p, B.subst (weightedHomogeneousComponent (biWeight M M') p F) ∈ V.ideal := by
  refine ⟨fun hF p => B.subst_weightedHomogeneousComponent_mem hF p, fun h => ?_⟩
  rw [← sum_weightSupport (w := biWeight M M') F]
  exact Ideal.sum_mem _ fun p _ => (B.mem_ideal_iff_of_isWeightedHomogeneous
    (weightedHomogeneousComponent_isWeightedHomogeneous p F)).2 (h p)

/-- `I' ∩ R_M = I` (`lem:pg-blowup-basic`(1)): `Θ₀(f(x)) = f`. -/
theorem rename_inl_mem_ideal_iff (f : MvPolynomial (Fin (M + 1)) k) :
    rename Sum.inl f ∈ B.ideal ↔ f ∈ V.ideal := by
  have e : B.reesMap (rename Sum.inl f) = Polynomial.C f := by
    rw [reesMap, aeval_rename, Sum.elim_comp_inl]
    have h := (DFunLike.congr_fun (comp_aeval (X : Fin (M + 1) → MvPolynomial (Fin (M + 1)) k)
      (Polynomial.CAlgHom (R := k))) f).symm
    rw [AlgHom.comp_apply, aeval_X_left_apply] at h
    exact h
  rw [mem_ideal_iff_reesMap, e]
  refine ⟨fun h => by simpa using h 0, fun h n => ?_⟩
  rw [Polynomial.coeff_C]
  split_ifs
  · exact h
  · exact V.ideal.zero_mem

theorem X_inl_mem_ideal_iff (j : Fin (M + 1)) :
    (X (Sum.inl j) : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) ∈ B.ideal ↔
      (X j : MvPolynomial (Fin (M + 1)) k) ∈ V.ideal := by
  simpa using B.rename_inl_mem_ideal_iff (X j)

theorem X_inr_mem_ideal_iff (m : Fin (M' + 1)) :
    (X (Sum.inr m) : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) ∈ B.ideal ↔ B.G m ∈ V.ideal := by
  simpa using B.mem_ideal_iff_of_isWeightedHomogeneous
    (isWeightedHomogeneous_X k (biWeight M M') (Sum.inr m))

/-- `I'` does not contain all `xⱼ` (`lem:pg-blowup-basic`(1)). -/
theorem exists_X_inl_notMem_ideal :
    ∃ j, (X (Sum.inl j) : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) ∉ B.ideal := by
  obtain ⟨j, hj⟩ := V.exists_X_notMem
  exact ⟨j, fun h => hj ((B.X_inl_mem_ideal_iff j).1 h)⟩

/-- `I'` does not contain all `y_m` (`lem:pg-blowup-basic`(1)). -/
theorem exists_X_inr_notMem_ideal :
    ∃ m, (X (Sum.inr m) : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) ∉ B.ideal := by
  obtain ⟨m, hm⟩ := B.exists_notMem
  exact ⟨m, fun h => hm ((B.X_inr_mem_ideal_iff m).1 h)⟩

/-! ### The analytification `X'^an` and the map `μ` (`lem:pg-blowup-basic`(2)–(4)) -/

/-- The analytification `X'^an = V(I')^an ⊆ (ℙ^M × ℙ^{M'})^an` of the blowup (`def:pg-blowup`). -/
def an : Set (BiProjBerk k M M') := {v | ∀ F ∈ B.ideal, v.1.val F = 0}

theorem isClosed_an : IsClosed B.an :=
  BiProjBerk.isClosed_setOf_forall_val_eq_zero _

/-- `X'^an` is compact (`lem:pg-blowup-basic`(3)); it is Hausdorff, and second countable for
countable `k`, as a subspace of `(ℙ^M × ℙ^{M'})^an`. -/
instance instCompactSpaceAn : CompactSpace B.an :=
  isCompact_iff_compactSpace.1 B.isClosed_an.isCompact

example : T2Space B.an := inferInstance

example [Countable k] : SecondCountableTopology B.an := inferInstance

/-- Points of `(ℙ^M × ℙ^{M'})^an` are bigraded, so `v ∈ X'^an` iff `|F|_v = 0` for the
bihomogeneous `F` with `F(x, G) ∈ I`. -/
theorem mem_an_iff {v : BiProjBerk k M M'} :
    v ∈ B.an ↔ ∀ (p : ℕ × ℕ) (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k),
      F.IsWeightedHomogeneous (biWeight M M') p → B.subst F ∈ V.ideal → v.1.val F = 0 := by
  refine ⟨fun hv p F hF hFI => hv F ((B.mem_ideal_iff_of_isWeightedHomogeneous hF).2 hFI),
    fun h F hF => ?_⟩
  rw [v.val_eq_sup]
  refine le_antisymm (Finset.sup_le fun p _ => ?_) zero_le
  rw [h p _ (weightedHomogeneousComponent_isWeightedHomogeneous p F)
    (B.subst_weightedHomogeneousComponent_mem hF p)]

theorem val_eq_zero_of_mem (v : B.an) {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F ∈ B.ideal) : (v : BiProjBerk k M M').1.val F = 0 :=
  v.2 F hF

/-- The blowup map `μ : X'^an → X^an`, the restriction of seminorms to `R_M ⊆ R_{M,M'}`
(`def:pg-blowup`, `lem:pg-blowup-basic`(4)). -/
def proj (v : B.an) : V.an :=
  ⟨BiProjBerk.fst v.1, fun f hf => v.2 _ ((B.rename_inl_mem_ideal_iff f).2 hf)⟩

theorem proj_val_apply (v : B.an) (f : MvPolynomial (Fin (M + 1)) k) :
    (B.proj v : ProjBerk k M).1.val f = (v : BiProjBerk k M M').1.val (rename Sum.inl f) :=
  rfl

theorem coe_proj (v : B.an) : (B.proj v : ProjBerk k M) = BiProjBerk.fst (v : BiProjBerk k M M') :=
  rfl

/-- `μ` is continuous (`lem:pg-blowup-basic`(4)). -/
@[fun_prop]
theorem continuous_proj : Continuous B.proj :=
  (BiProjBerk.continuous_fst.comp continuous_subtype_val).subtype_mk _

/-- The trivial point `⋆' ∈ X'^an`: `|F| = 0` for `F ∈ I'` and `|F| = 1` otherwise, the trivial
valuation of `R_{M,M'} / I'` (`lem:pg-blowup-basic`(2)). -/
def triv : B.an :=
  ⟨BiProjBerk.trivQuot B.ideal (fun _ hF p => B.weightedHomogeneousComponent_mem_ideal hF p)
      B.exists_X_inl_notMem_ideal B.exists_X_inr_notMem_ideal,
    fun _ hF => BiProjBerk.trivQuot_val_of_mem
      (fun _ hF p => B.weightedHomogeneousComponent_mem_ideal hF p)
      B.exists_X_inl_notMem_ideal B.exists_X_inr_notMem_ideal hF⟩

theorem triv_val_of_mem {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k} (hF : F ∈ B.ideal) :
    (B.triv : BiProjBerk k M M').1.val F = 0 :=
  B.triv.2 F hF

theorem triv_val_of_notMem {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F ∉ B.ideal) : (B.triv : BiProjBerk k M M').1.val F = 1 :=
  BiProjBerk.trivQuot_val_of_notMem (fun _ hF p => B.weightedHomogeneousComponent_mem_ideal hF p)
    B.exists_X_inl_notMem_ideal B.exists_X_inr_notMem_ideal hF

/-- `μ(⋆') = ⋆` (`lem:pg-blowup-basic`(2)). -/
theorem proj_triv : B.proj B.triv = V.triv := by
  refine Subtype.ext (ProjBerk.ext (Berk.ext_val fun f => ?_))
  change (B.triv : BiProjBerk k M M').1.val (rename Sum.inl f) = (V.triv : ProjBerk k M).1.val f
  by_cases hf : f ∈ V.ideal
  · rw [B.triv_val_of_mem ((B.rename_inl_mem_ideal_iff f).2 hf), V.triv.2 f hf]
  · rw [B.triv_val_of_notMem fun h => hf ((B.rename_inl_mem_ideal_iff f).1 h),
      V.triv_val_of_notMem hf]

/-! ### Graph points (`lem:pg-graph-point`) -/

/-- `|𝔞|_x = max_m |G_m|_x` for `x ∈ X^an`. -/
def centerAbs (x : V.an) : ℝ≥0 :=
  Finset.univ.sup fun m => (x : ProjBerk k M).1.val (B.G m)

theorem val_G_le_centerAbs (x : V.an) (m : Fin (M' + 1)) :
    (x : ProjBerk k M).1.val (B.G m) ≤ B.centerAbs x :=
  Finset.le_sup (f := fun m => (x : ProjBerk k M).1.val (B.G m)) (Finset.mem_univ m)

theorem centerAbs_ne_zero_iff (x : V.an) :
    B.centerAbs x ≠ 0 ↔ ∃ m, (x : ProjBerk k M).1.val (B.G m) ≠ 0 := by
  refine ⟨fun h => ?_, fun ⟨m, hm⟩ => ne_bot_of_le_ne_bot hm (B.val_G_le_centerAbs x m)⟩
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    fun m => (x : ProjBerk k M).1.val (B.G m)
  exact ⟨m, fun h' => h (by rw [centerAbs, hm, h'])⟩

theorem scaleX_subst (x : V.an) : BiProjBerk.scaleX B.subst (x : ProjBerk k M).1 = 1 := by
  simp only [BiProjBerk.scaleX, subst_X_inl]
  exact (x : ProjBerk k M).sup_val_X

theorem scaleY_subst (x : V.an) :
    BiProjBerk.scaleY B.subst (x : ProjBerk k M).1 = B.centerAbs x := by
  simp only [BiProjBerk.scaleY, subst_X_inr]
  rfl

/-- The **graph point** `γ(x) ∈ X'^an` of `x ∈ X^an` with `|𝔞|_x ≠ 0` (`lem:pg-graph-point`):
`|F|_{γ(x)} = |F(x, G)|_x / |𝔞|_x^b` for `F` bihomogeneous of bidegree `(a, b)`
(`graphPoint_val_of_isWeightedHomogeneous`), the rescaled pullback `BiProjBerk.ofComap` along the
substitution `F ↦ F(x, G)`. -/
def graphPoint (x : V.an) (hx : B.centerAbs x ≠ 0) : B.an :=
  ⟨BiProjBerk.ofComap B.subst (x : ProjBerk k M).1 (by rw [scaleX_subst]; exact one_ne_zero)
      (by rw [scaleY_subst]; exact hx),
    fun _ hF => BiProjBerk.ofComap_val_eq_zero _ _ fun p =>
      x.2 _ (B.subst_weightedHomogeneousComponent_mem hF p)⟩

variable {B}

theorem coe_graphPoint (x : V.an) (hx : B.centerAbs x ≠ 0) :
    (B.graphPoint x hx : BiProjBerk k M M') =
      BiProjBerk.ofComap B.subst (x : ProjBerk k M).1 (by rw [scaleX_subst]; exact one_ne_zero)
        (by rw [scaleY_subst]; exact hx) :=
  rfl

/-- `|F|_{γ(x)} = |F(x, G)|_x / |𝔞|_x^b` for `F` bihomogeneous of bidegree `(a, b)`
(`lem:pg-graph-point`). -/
theorem graphPoint_val_of_isWeightedHomogeneous (x : V.an) (hx : B.centerAbs x ≠ 0) {a b : ℕ}
    {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    (B.graphPoint x hx : BiProjBerk k M M').1.val F =
      (x : ProjBerk k M).1.val (B.subst F) / B.centerAbs x ^ b := by
  rw [coe_graphPoint, BiProjBerk.ofComap_val_of_isWeightedHomogeneous _ _ hF, scaleX_subst,
    scaleY_subst, one_pow, one_mul]

/-- `log|F|_{γ(x)} = log|F(x, G)|_x - b log|𝔞|_x` for `F` bihomogeneous of bidegree `(a, b)`. -/
theorem logAbs_graphPoint_of_isWeightedHomogeneous (x : V.an) (hx : B.centerAbs x ≠ 0)
    {a b : ℕ} {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    BiProjBerk.logAbs F (B.graphPoint x hx) =
      ProjBerk.logAbs (B.subst F) x - (b : EReal) * ENNReal.log (B.centerAbs x : ℝ≥0∞) := by
  rw [BiProjBerk.logAbs_def, graphPoint_val_of_isWeightedHomogeneous x hx hF, ProjBerk.logAbs_def,
    ENNReal.coe_div (pow_ne_zero _ hx), div_eq_mul_inv, ENNReal.log_mul_add, ENNReal.log_inv,
    ENNReal.coe_pow, ENNReal.log_pow, sub_eq_add_neg]

/-- `μ(γ(x)) = x` (`lem:pg-graph-point`): both are graded and agree on forms. -/
theorem proj_graphPoint (x : V.an) (hx : B.centerAbs x ≠ 0) : B.proj (B.graphPoint x hx) = x := by
  refine Subtype.ext (ProjBerk.ext_of_isHomogeneous fun c f hf => ?_)
  rw [coe_proj, coe_graphPoint, BiProjBerk.fst_ofComap_val_of_isHomogeneous _ _ hf,
    subst_rename_inl, scaleX_subst, one_pow, div_one]

end ProjSubvariety.BlowupCenter

end EnvelopeProperty
