import EnvelopeProperty.Cartier.Exchange
import EnvelopeProperty.Cartier.Finiteness

/-!
# `p`-bases of discrete valuation rings essentially of finite type

Let `k` be a perfect field of characteristic `p` and `R` a DVR essentially of finite type over `k`
with uniformizer `ϖ` and fraction field `F`. Then `R` has a `p`-basis `u = (ϖ, x_1, …, x_r)`: `R`
is free over `R^p` with basis the monomials `ϖ^{a_0} x^{a'}`, `a ∈ [0,p)^{r+1}`, where the `x_i`
lift a `p`-basis of the residue field `κ` (Kunz's theorem for this regular local ring, proved by
hand). Consequently it is also a `p`-basis of `F`, so `r + 1` is the size of any `p`-basis of `F`
(for `F = k(y_1, …, y_m)` this is `m`), and the Cartier operator `Φ_u` maps `R` into `R`.

## Steps

* `exists_isPBasis_of_surjective`: a field spanned over its `p`-th powers by finitely many
  monomials has a finite `p`-basis (a maximal `p`-independent family; adjoining `t ∉ κ^p(x)` keeps
  independence because `X^p - t^p` is irreducible over `κ^p(x)`).
* `exists_isPBasis_cons_uniformizer`: the lifted family `(ϖ, x)` spans `R/ϖ^p R` over `κ^p` by the
  `ϖ`-adic filtration, hence spans `R` over `R^p` by Nakayama (`R` is finite over `R^p`); it is
  independent by a descent on the `ϖ`-adic order of the coefficients.
* `exists_isPBasis_of_essFiniteType`: such a `p`-basis indexed by the index type of a given
  `p`-basis `y` of `F`.

This is item 4 of the CO lane and the input "regular top forms are preserved" in the proof of FHX
Lemma 3.3 (`lem:divisorial-trace-estimate`).
-/

noncomputable section

open scoped NNReal ENNReal Topology

namespace EnvelopeProperty.Cartier

open Finset Module

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Reindexing -/

section Reindex

variable {A : Type*} [CommRing A] [CharP A p]

theorem mono_comp_equiv' {σ τ : Type*} [Fintype σ] [Fintype τ] (u : τ → A) (e : σ ≃ τ)
    (n : σ → ℕ) : mono (u ∘ e) n = mono u (n ∘ e.symm) := by
  unfold mono
  exact Fintype.prod_equiv e _ _ fun i => by simp

/-- Reindexing a `p`-basis along an equivalence of index types. -/
theorem IsPBasis.comp_equiv {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    {u : τ → A} (hu : IsPBasis p u) (e : σ ≃ τ) : IsPBasis p (u ∘ e) := by
  let E : Box σ p ≃ Box τ p := Equiv.arrowCongr e (Equiv.refl _)
  have h : ∀ c : Box σ p → A, pSum p (u ∘ e) c = pSum p u (c ∘ E.symm) := by
    intro c
    rw [pSum_apply, pSum_apply]
    refine Fintype.sum_equiv E _ _ fun a => ?_
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [mono_comp_equiv']
    rfl
  constructor
  · intro c d hcd
    rw [h, h] at hcd
    have := hu.injective hcd
    funext a
    have := congr_fun this (E a)
    simpa using this
  · intro f
    obtain ⟨c, rfl⟩ := hu.surjective f
    exact ⟨c ∘ E, by rw [h]; congr 1; funext b; simp⟩

omit [CharP A p] hp in
@[simp]
theorem Box.toNat_cons_zero {r : ℕ} (n : Fin p) (b : Box (Fin r) p) :
    Box.toNat (Fin.cons n b : Box (Fin (r + 1)) p) 0 = n :=
  rfl

omit [CharP A p] hp in
@[simp]
theorem Box.tail_toNat_cons {r : ℕ} (n : Fin p) (b : Box (Fin r) p) :
    Fin.tail (Box.toNat (Fin.cons n b : Box (Fin (r + 1)) p)) = b.toNat :=
  rfl

omit [CharP A p] hp in
theorem consEquiv_apply' {r : ℕ} (n : Fin p) (b : Box (Fin r) p) :
    (Fin.consEquiv fun _ => Fin p) (n, b) = (Fin.cons n b : Box (Fin (r + 1)) p) :=
  rfl

/-- Monomials of `Fin.cons t x`. -/
theorem mono_cons {r : ℕ} (t : A) (x : Fin r → A) (n : Fin (r + 1) → ℕ) :
    mono (Fin.cons t x : Fin (r + 1) → A) n = t ^ n 0 * mono x (Fin.tail n) := by
  rw [mono, Fin.prod_univ_succ]
  rfl

end Reindex

/-! ### Existence of `p`-bases of fields finite over their `p`-th powers -/

section FieldExistence

variable {K : Type*} [Field K] [CharP K p]

/-- The subfield `K^p(x)` spanned over `K^p` by the monomials of `x`. -/
def pClosure {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → K) : Subfield K where
  carrier := AddMonoidHom.mrange (pSum p x)
  zero_mem' := (AddMonoidHom.mrange (pSum p x)).zero_mem
  add_mem' := (AddMonoidHom.mrange (pSum p x)).add_mem
  neg_mem' := by
    rintro _ ⟨c, rfl⟩
    exact ⟨-c, map_neg _ _⟩
  one_mem' := by
    have := mono_mem_range_pSum p x 0
    rwa [mono_zero] at this
  mul_mem' hx hy := mul_mem_range_pSum p x hx hy
  inv_mem' z hz := by
    have h : z⁻¹ = z⁻¹ ^ p * z ^ (p - 1) := by
      by_cases hz0 : z = 0
      · simp [hz0, zero_pow hp.out.ne_zero]
      · have hp1 : p = p - 1 + 1 := (Nat.sub_add_cancel hp.out.one_lt.le).symm
        calc z⁻¹ = z⁻¹ * (z⁻¹ * z) ^ (p - 1) := by rw [inv_mul_cancel₀ hz0, one_pow, mul_one]
          _ = z⁻¹ ^ (p - 1 + 1) * z ^ (p - 1) := by rw [mul_pow, pow_succ]; ring
          _ = z⁻¹ ^ p * z ^ (p - 1) := by rw [← hp1]
    rw [h]
    refine pow_mul_mem_range_pSum p x _ ?_
    clear h
    induction p - 1 with
    | zero => simpa using mono_mem_range_pSum p x 0
    | succ n ih => rw [pow_succ]; exact mul_mem_range_pSum p x ih hz

theorem mem_pClosure {ι : Type*} [Fintype ι] [DecidableEq ι] {x : ι → K} {z : K} :
    z ∈ pClosure (p := p) x ↔ ∃ c, pSum p x c = z :=
  Iff.rfl

/-- If `t ∉ L` and `t^p ∈ L` then `1, t, …, t^{p-1}` are linearly independent over `L`. -/
theorem linearIndependent_pow_of_not_mem (L : Subfield K) {t : K} (ht : t ∉ L)
    (htp : t ^ p ∈ L) : LinearIndependent L (fun i : Fin p => t ^ (i : ℕ)) := by
  have hirr : Irreducible (Polynomial.X ^ p - Polynomial.C (⟨t ^ p, htp⟩ : L)) := by
    refine X_pow_sub_C_irreducible_of_prime hp.out fun b hb => ht ?_
    have hb' : (b : K) ^ p = t ^ p := congrArg Subtype.val hb
    have : ((b : K) - t) ^ p = 0 := by rw [sub_pow_char, hb', sub_self]
    have hbt : (b : K) = t := sub_eq_zero.1 (pow_eq_zero_iff hp.out.ne_zero |>.1 this)
    rw [← hbt]
    exact b.2
  have hmin : Polynomial.X ^ p - Polynomial.C (⟨t ^ p, htp⟩ : L) = minpoly L t := by
    refine minpoly.eq_of_irreducible_of_monic hirr ?_ (Polynomial.monic_X_pow_sub_C _
      hp.out.ne_zero)
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [sub_eq_zero]
    rfl
  have hdeg : (minpoly L t).natDegree = p := by
    rw [← hmin, Polynomial.natDegree_X_pow_sub_C]
  have key : ∀ n (_ : (minpoly L t).natDegree = n),
      LinearIndependent L fun i : Fin n => t ^ (i : ℕ) := by
    rintro n rfl
    exact linearIndependent_pow t
  exact key p hdeg

/-- The monomials of a `p`-independent family are linearly independent over `K^p`. -/
theorem linearIndependent_of_injective_pSum {ι : Type*} [Fintype ι] [DecidableEq ι] {x : ι → K}
    (hx : Function.Injective (pSum p x)) :
    LinearIndependent (pthPowers (F := K) p) (fun a : Box ι p => mono x a.toNat) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  choose c hc using fun b => exists_pow_eq_of_mem_pthPowers (g b).2
  have h0 : pSum p x c = 0 := by
    rw [pSum_apply, ← hg]
    refine sum_congr rfl fun b _ => ?_
    rw [Subfield.smul_def, smul_eq_mul, hc b]
  have := hx (h0.trans (map_zero _).symm)
  have hca : c a = 0 := congr_fun this a
  apply Subtype.ext
  rw [← hc a, hca, zero_pow hp.out.ne_zero]
  rfl

/-- Adjoining an element outside `K^p(x)` to a `p`-independent family keeps it `p`-independent. -/
theorem injective_pSum_cons {r : ℕ} {x : Fin r → K} (hx : Function.Injective (pSum p x))
    {t : K} (ht : t ∉ pClosure (p := p) x) :
    Function.Injective (pSum p (Fin.cons t x : Fin (r + 1) → K)) := by
  set L := pClosure (p := p) x
  have htp : t ^ p ∈ L := by
    have := pow_mul_mem_range_pSum p x t (mono_mem_range_pSum p x 0)
    rwa [mono_zero, mul_one] at this
  have hli := linearIndependent_pow_of_not_mem L ht htp
  rw [injective_iff_map_eq_zero]
  intro c hc
  -- split off the first digit
  let κ : Fin p → K := fun n => pSum p x fun b => c (Fin.cons n b)
  have hκL : ∀ n, κ n ∈ L := fun n => ⟨_, rfl⟩
  have hrel : ∑ n : Fin p, (⟨κ n, hκL n⟩ : L) • t ^ (n : ℕ) = 0 := by
    rw [← hc, pSum_apply, ← (Fin.consEquiv fun _ => Fin p).sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl fun n _ => ?_
    rw [Subfield.smul_def, smul_eq_mul]
    show (pSum p x fun b => c (Fin.cons n b)) * t ^ (n : ℕ) = _
    rw [pSum_apply, sum_mul]
    refine sum_congr rfl fun b _ => ?_
    rw [consEquiv_apply', mono_cons, Box.toNat_cons_zero, Box.tail_toNat_cons]
    ring
  have hκ0 : ∀ n, κ n = 0 := fun n =>
    congrArg Subtype.val (Fintype.linearIndependent_iff.1 hli _ hrel n)
  funext a
  have h1 : (fun b => c (Fin.cons (a 0) b)) = 0 :=
    hx ((hκ0 (a 0)).trans (map_zero _).symm)
  have := congr_fun h1 (Fin.tail a)
  simpa [Fin.cons_self_tail] using this

/-- A field spanned over its `p`-th powers by the monomials of a finite family has a finite
`p`-basis. -/
theorem exists_isPBasis_of_surjective {n : ℕ} {s : Fin n → K}
    (hs : Function.Surjective (pSum p s)) : ∃ (r : ℕ) (x : Fin r → K), IsPBasis p x := by
  classical
  let Kp := pthPowers (F := K) p
  -- `K` is finite-dimensional over `K^p`
  have hspan : Submodule.span Kp (Set.range fun a : Box (Fin n) p => mono s a.toNat) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨c, rfl⟩ := hs z
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun a => ⟨c a ^ p, pow_mem_pthPowers _⟩, ?_⟩
    rw [pSum_apply]
    refine sum_congr rfl fun a _ => ?_
    rw [Subfield.smul_def, smul_eq_mul]
  have hfin : Module.Finite Kp K := by
    rw [Module.finite_def, ← hspan]
    exact Submodule.fg_span (Set.finite_range _)
  have hrank : finrank Kp K ≤ p ^ n := by
    have := finrank_range_le_card (R := Kp) (fun a : Box (Fin n) p => mono s a.toNat)
    rw [Set.finrank, hspan, finrank_top, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin] at this
    exact this
  -- `p`-independent families have size `≤ n`
  let P : ℕ → Prop := fun r => ∃ x : Fin r → K, Function.Injective (pSum p x)
  have hbound : ∀ r, P r → r ≤ n := by
    rintro r ⟨x, hx⟩
    have := (linearIndependent_of_injective_pSum hx).fintype_card_le_finrank
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at this
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 (this.trans hrank)
  have hP0 : P 0 := by
    refine ⟨Fin.elim0, fun c d hcd => ?_⟩
    funext a
    have ha : (univ : Finset (Box (Fin 0) p)) = {a} := by
      ext b
      simp only [mem_univ, mem_singleton, true_iff]
      exact funext fun i => i.elim0
    rw [pSum_apply, pSum_apply, ha, sum_singleton, sum_singleton] at hcd
    simp only [mono, univ_eq_empty, prod_empty, mul_one] at hcd
    exact frobenius_inj K p hcd
  set r := Nat.findGreatest P n
  obtain ⟨x, hx⟩ : P r := Nat.findGreatest_spec (Nat.zero_le n) hP0
  refine ⟨r, x, hx, fun z => ?_⟩
  by_contra hz
  push Not at hz
  have hnotmem : z ∉ pClosure (p := p) x := fun ⟨c, hc⟩ => hz c hc
  have hP1 : P (r + 1) := ⟨_, injective_pSum_cons hx hnotmem⟩
  have hr1 : r + 1 ≤ n := hbound _ hP1
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self r) hr1 hP1

end FieldExistence

/-! ### The `p`-basis of a DVR -/

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharP R p]

theorem charP_residueField : CharP (IsLocalRing.ResidueField R) p := by
  rw [CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (IsLocalRing.residue R), CharP.cast_eq_zero,
    map_zero]

/-- **The `p`-basis of a DVR.** If `R` is spanned over `R^p` by the monomials of a finite family,
then for every uniformizer `ϖ` there are `x_1, …, x_r ∈ R` such that `(ϖ, x_1, …, x_r)` is a
`p`-basis of `R`. -/
theorem exists_isPBasis_cons_uniformizer {n : ℕ} {s : Fin n → R}
    (hs : Function.Surjective (pSum p s)) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ (r : ℕ) (x : Fin r → R), IsPBasis p (Fin.cons ϖ x : Fin (r + 1) → R) := by
  classical
  have := charP_residueField (R := R) (p := p)
  set κ := IsLocalRing.ResidueField R
  set res := IsLocalRing.residue R
  have hres : Function.Surjective res := IsLocalRing.residue_surjective
  -- a `p`-basis of the residue field
  have hsκ : Function.Surjective (pSum p (res ∘ s)) := by
    intro z
    obtain ⟨w, rfl⟩ := hres z
    obtain ⟨c, rfl⟩ := hs w
    exact ⟨res ∘ c, (map_pSum p res s c).symm⟩
  obtain ⟨r, xb, hxb⟩ := exists_isPBasis_of_surjective hsκ
  choose x hx using fun i => hres (xb i)
  have hxres : res ∘ x = xb := funext hx
  refine ⟨r, x, ?_⟩
  set u : Fin (r + 1) → R := Fin.cons ϖ x
  have hmax : ∀ z : R, res z = 0 ↔ ϖ ∣ z := by
    intro z
    rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  -- reduction modulo `ϖ`
  have hlift : ∀ z : R, ∃ c : Box (Fin r) p → R, ∃ z' : R, z = pSum p x c + ϖ * z' := by
    intro z
    obtain ⟨cb, hcb⟩ := hxb.surjective (res z)
    choose c hc using fun b => hres (cb b)
    have : ϖ ∣ z - pSum p x c := by
      rw [← hmax, map_sub, map_pSum, hxres, show res ∘ c = cb from funext hc, hcb, sub_self]
    obtain ⟨z', hz'⟩ := this
    exact ⟨c, z', by rw [← hz']; ring⟩
  set M := AddMonoidHom.mrange (pSum p u)
  -- the `ϖ`-adic filtration: `R = M + ϖ^j R`
  have hfilt : ∀ j : ℕ, ∀ z : R, ∃ m ∈ M, ∃ z' : R, z = m + ϖ ^ j * z' := by
    intro j
    induction j with
    | zero => intro z; exact ⟨0, M.zero_mem, z, by simp⟩
    | succ j ih =>
      intro z
      obtain ⟨m, hm, z', rfl⟩ := ih z
      obtain ⟨c, z'', rfl⟩ := hlift z'
      refine ⟨m + ϖ ^ j * pSum p x c, M.add_mem hm ?_, z'', by ring⟩
      rw [pSum_apply, mul_sum]
      refine M.sum_mem fun b _ => ?_
      rw [show ϖ ^ j * (c b ^ p * mono x b.toNat) =
        c b ^ p * mono u (Fin.cons j b.toNat) by rw [mono_cons]; simp; ring]
      exact pow_mul_mem_range_pSum p u _ (mono_mem_range_pSum p u _)
  -- Nakayama over `R^p`
  let S : Subring R := (frobenius R p).range
  have hpowS : ∀ c : R, c ^ p ∈ S := fun c => ⟨c, frobenius_def p c⟩
  let N : Submodule S R := Submodule.span S (Set.range fun a : Box (Fin (r + 1)) p => mono u a.toNat)
  have hMN : ∀ m ∈ M, m ∈ N := by
    rintro _ ⟨c, rfl⟩
    rw [pSum_apply]
    refine N.sum_mem fun a _ => ?_
    have : c a ^ p * mono u a.toNat = (⟨c a ^ p, hpowS _⟩ : S) • mono u a.toNat := rfl
    rw [this]
    exact N.smul_mem _ (Submodule.subset_span ⟨a, rfl⟩)
  have htopFG : (⊤ : Submodule S R).FG := by
    refine ⟨(univ.image fun a : Box (Fin n) p => mono s a.toNat), eq_top_iff.2 fun z _ => ?_⟩
    obtain ⟨c, rfl⟩ := hs z
    rw [coe_image, coe_univ, Set.image_univ, pSum_apply]
    refine Submodule.sum_mem _ fun a _ => ?_
    have : c a ^ p * mono s a.toNat = (⟨c a ^ p, hpowS _⟩ : S) • mono s a.toNat := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  let I : Ideal S := Ideal.span {⟨ϖ ^ p, hpowS ϖ⟩}
  have hIJ : I ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_jacobson_bot]
    rintro ⟨_, v, rfl⟩
    have hunit : IsUnit (ϖ * v + 1) := by
      have h := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(ϖ * v)) (by
        rw [← IsLocalRing.mem_maximalIdeal, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
        exact Dvd.intro (-v) (by ring))
      rwa [sub_neg_eq_add, add_comm] at h
    obtain ⟨w, hw⟩ := hunit.exists_right_inv
    refine IsUnit.of_mul_eq_one ⟨w ^ p, hpowS w⟩ ?_
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_add, Subring.coe_one, frobenius_def]
    rw [← mul_pow, show (ϖ * v) ^ p + 1 = (ϖ * v + 1) ^ p by rw [add_pow_char, one_pow],
      ← mul_pow, hw, one_pow]
  have hNN : (⊤ : Submodule S R) ≤ N ⊔ I • ⊤ := by
    intro z _
    obtain ⟨m, hm, z', rfl⟩ := hfilt p z
    refine Submodule.add_mem_sup (hMN m hm) ?_
    have : ϖ ^ p * z' = (⟨ϖ ^ p, hpowS ϖ⟩ : S) • z' := rfl
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.subset_span rfl) trivial
  have htop := Submodule.le_of_le_smul_of_le_jacobson_bot htopFG hIJ hNN
  constructor
  · -- independence: descent on the `ϖ`-adic order of the coefficients
    have hstep : ∀ c : Box (Fin (r + 1)) p → R, pSum p u c = 0 → ∀ a, ϖ ∣ c a := by
      intro c hc
      -- `S_n = ∑_b c_{(n,b)}^p x^b`
      let Sn : Fin p → R := fun m => pSum p x fun b => c (Fin.cons m b)
      have hsplit : pSum p u c = ∑ m : Fin p, ϖ ^ (m : ℕ) * Sn m := by
        rw [pSum_apply, ← (Fin.consEquiv fun _ => Fin p).sum_comp, Fintype.sum_prod_type]
        refine sum_congr rfl fun m _ => ?_
        show _ = ϖ ^ (m : ℕ) * pSum p x (fun b => c (Fin.cons m b))
        rw [pSum_apply, mul_sum]
        refine sum_congr rfl fun b _ => ?_
        rw [consEquiv_apply', mono_cons, Box.toNat_cons_zero, Box.tail_toNat_cons]
        ring
      -- by strong induction on the first digit
      have hdig : ∀ m : ℕ, ∀ (hm : m < p), ∀ b, ϖ ∣ c (Fin.cons ⟨m, hm⟩ b) := by
        intro m
        induction m using Nat.strong_induction_on with
        | _ m ih =>
          intro hm b
          -- `ϖ^{m+1}` divides every term except `ϖ^m S_m`
          have hothers : ϖ ^ (m + 1) ∣ ∑ l ∈ univ.erase (⟨m, hm⟩ : Fin p), ϖ ^ (l : ℕ) * Sn l := by
            refine dvd_sum fun l hl => ?_
            rcases lt_or_gt_of_ne (Fin.val_ne_of_ne (ne_of_mem_erase hl)) with hlt | hgt <;>
              simp only at *
            · -- lower digits: all coefficients are divisible by `ϖ`, so `S_l ∈ ϖ^p R`
              have hdivS : ϖ ^ p ∣ Sn l := by
                refine dvd_sum fun b' _ => ?_
                obtain ⟨d, hd⟩ := ih l hlt l.2 b'
                have hd' : c (Fin.cons l b') = ϖ * d := hd
                show ϖ ^ p ∣ c (Fin.cons l b') ^ p * mono x b'.toNat
                rw [hd', mul_pow]
                exact Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _
              exact Dvd.dvd.mul_left ((pow_dvd_pow ϖ (by omega)).trans hdivS) _
            · exact Dvd.dvd.mul_right (pow_dvd_pow ϖ (by omega)) _
          have hm' : ϖ ^ (m + 1) ∣ ϖ ^ m * Sn ⟨m, hm⟩ := by
            have h0 := hsplit.symm.trans hc
            rw [← add_sum_erase _ _ (mem_univ (⟨m, hm⟩ : Fin p))] at h0
            rw [eq_neg_of_add_eq_zero_left h0]
            exact (dvd_neg).2 hothers
          rw [pow_succ] at hm'
          have hdivS : ϖ ∣ Sn ⟨m, hm⟩ :=
            (mul_dvd_mul_iff_left (pow_ne_zero m hϖ.ne_zero)).1 hm'
          rw [← hmax] at hdivS
          rw [map_pSum, hxres] at hdivS
          have := hxb.injective (hdivS.trans (map_zero _).symm)
          rw [← hmax]
          exact congr_fun this b
      intro a
      have := hdig (a 0) (a 0).2 (Fin.tail a)
      simpa [Fin.cons_self_tail] using this
    have hdesc : ∀ k : ℕ, ∀ c : Box (Fin (r + 1)) p → R, pSum p u c = 0 → ∀ a, ϖ ^ k ∣ c a := by
      intro k
      induction k with
      | zero => intro c _ a; simp
      | succ k ih =>
        intro c hc a
        choose d hd using hstep c hc
        have hd0 : pSum p u d = 0 := by
          have : pSum p u c = ϖ ^ p * pSum p u d := by
            rw [← pSum_smul]
            congr 1
            funext b
            rw [hd b]
            rfl
          rw [this] at hc
          exact (mul_eq_zero.1 hc).resolve_left (pow_ne_zero _ hϖ.ne_zero)
        rw [hd a, pow_succ']
        exact mul_dvd_mul_left ϖ (ih d hd0 a)
    rw [injective_iff_map_eq_zero]
    intro c hc
    funext a
    by_contra hca
    obtain ⟨m, v, hmv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hca hϖ
    obtain ⟨d, hd⟩ := hdesc (m + 1) c hc a
    have : ϖ ∣ (v : R) := by
      have h1 : (v : R) * ϖ ^ m = ϖ * d * ϖ ^ m := by
        rw [← hmv, hd]; ring
      exact ⟨d, mul_right_cancel₀ (pow_ne_zero m hϖ.ne_zero) h1⟩
    exact hϖ.not_isUnit (isUnit_of_dvd_unit this v.isUnit)
  · -- spanning
    intro z
    have hz : z ∈ N := htop trivial
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
    choose c hc using fun a => (g a).2
    refine ⟨c, ?_⟩
    rw [pSum_apply, ← hg]
    refine sum_congr rfl fun a _ => ?_
    show c a ^ p * mono u a.toNat = (g a : R) * mono u a.toNat
    rw [← hc a, frobenius_def]

end DVR

/-! ### Assembling: DVRs essentially of finite type over a perfect field -/

section EssFiniteType

variable {R F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharP R p] [Field F]
  [Algebra R F] [IsFractionRing R F] [CharP F p]

/-- **`p`-bases of a DVR essentially of finite type** (over a perfect field `k` of characteristic
`p`). Given a `p`-basis `y` of the fraction field `F`, there is a `p`-basis `u` of `R`, indexed by
the same type, containing the uniformizer `ϖ`. -/
theorem exists_isPBasis_of_essFiniteType (k : Type*) [Field k] [CharP k p] [PerfectRing k p]
    [Algebra k R] [Algebra.EssFiniteType k R] {σ : Type*} [Fintype σ] [DecidableEq σ]
    {y : σ → F} (hy : IsPBasis p y) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ u : σ → R, IsPBasis p u ∧ ϖ ∈ Set.range u := by
  obtain ⟨n, s, hs⟩ := exists_surjective_pSum p k R
  obtain ⟨r, x, hu⟩ := exists_isPBasis_cons_uniformizer hs hϖ
  have huF := hu.map_of_isFractionRing (K := F)
  have hcard : Fintype.card σ = Fintype.card (Fin (r + 1)) := (huF.card_eq hy)
  let e : σ ≃ Fin (r + 1) := Fintype.equivOfCardEq hcard
  refine ⟨(Fin.cons ϖ x : Fin (r + 1) → R) ∘ e, hu.comp_equiv e, e.symm 0, ?_⟩
  simp

end EssFiniteType

end EnvelopeProperty.Cartier
