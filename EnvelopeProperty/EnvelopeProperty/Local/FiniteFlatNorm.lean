/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.EtaleFibre
import EnvelopeProperty.Local.Regularizable

/-!
# Norms of regularizable functions along finite free étale morphisms

Let `k` be a field with the trivial absolute value, `B → A` a homomorphism of `k`-algebras making
`A` a finite free étale `B`-algebra, and `π = π^an : (Spec A)^an → (Spec B)^an`. For a function
`u` on `(Spec A)^an` its **norm** is
`N_π u (s) = ∑_{π(y) = s} m_y(π) u(y)`,
where `m_y(π)` is the multiplicity of `y` in its fibre (`Berk.fibreMult`, the residue degree of
the fibre algebra at `y`). This file proves Fang–Han–Xia, *The envelope property for unibranch
projective varieties*, Lemma 5.13 (`lem:finite-flat-norm`), in the finite free étale form of the
blueprint remark `rmk:finite-flat-norm-etale`: `N_π` maps regularizable functions to
regularizable functions.

* **FS functions** (`exists_normFun_finsetSup_fsTerm`, `exists_normFun_eval_eq`). For
  `u = max_t (a_t log|f_t| + b_t)` with `a_t ∈ ℚ_{>0}`, choose `N > 0` with `N a_t ∈ ℕ`; with
  `b_t = f_t^{N a_t}` and `λ_t = N b_t`, `N u(y) = log max_t |b_t|_y e^{λ_t}`. The norm identity at a
  point (`Berk.wgaussValuation_map_normForm`) gives, with `P = ∑_α c_α X^α` the norm form of
  `∑_t X_t b_t` (coefficients in `B`),
  `N · N_π u = max_α (log|c_α| + ∑_t α_t λ_t)`,
  a finite maximum of terms `a log|c| + b` with `a = N⁻¹ > 0` and `b ∈ ℚ`.
* **Regularizable functions** (`IsRegularizable.normFun`). On a normal affine variety
  `Spec B`, if `u_j ∈ FS(Spec A)` decrease to `u ∈ ℛ(Spec A)`, then `N_π u_j ∈ ℛ(Spec B)`
  (FHX Lemma 5.11(3), `isRegularizable_finsetSup_fsTerm`) decrease to `N_π u` (finite sums with
  positive weights of decreasing sequences), which is finite at the trivial valuation (the only
  point over `v_triv` is `v_triv`, `Berk.eq_triv_of_comap_eq_triv`, and `u(v_triv) ≠ -∞`); FHX
  Lemma 5.11(2) (`IsRegularizable.of_antitone`) concludes.

The base change property `(N_π u) ∘ r = N_{π_F}(u ∘ r)` of the source lemma is not treated here.

## Main definitions

* `EnvelopeProperty.normFun u`: the norm `N_π u` of `u : (Spec A)^an → [-∞, ∞]`.

## Main results

* `EnvelopeProperty.exists_normFun_eval_eq`: the norm of an FS function is a finite maximum of
  terms `a log|c| + b` with `c ∈ B`, `a ∈ ℚ_{>0}`, `b ∈ ℚ`; `normFun_eval_ne_bot`: it is finite.
* `EnvelopeProperty.FSData.isRegularizable_normFun`: the norm of an FS function is regularizable.
* `EnvelopeProperty.IsRegularizable.normFun`: **FHX Lemma 5.13** (finite free étale case).
-/

open scoped NNReal ENNReal Topology

open MvPolynomial

noncomputable section

namespace EnvelopeProperty

open Berk

/-! ### Auxiliary facts on `log`, `EReal` sums and denominators -/

section aux

/-- `log` of a finite supremum in `ℝ≥0`. -/
theorem log_coe_nnreal_finsetSup {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0) :
    ENNReal.log ((s.sup f : ℝ≥0) : ℝ≥0∞) = s.sup fun i => ENNReal.log (f i : ℝ≥0∞) :=
  Finset.apply_sup_eq_sup_comp_of_linearOrder (g := fun a : ℝ≥0 => ENNReal.log (a : ℝ≥0∞))
    (fun _ _ h => ENNReal.log_monotone (ENNReal.coe_le_coe.2 h)) (by simp)

/-- `log` of a finite product in `ℝ≥0`. -/
theorem log_coe_nnreal_finsetProd {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0) :
    ENNReal.log ((∏ i ∈ s, f i : ℝ≥0) : ℝ≥0∞) = ∑ i ∈ s, ENNReal.log (f i : ℝ≥0∞) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ENNReal.coe_mul, ENNReal.log_mul_add, ih]

theorem log_coe_nnreal_pow (a : ℝ≥0) (n : ℕ) :
    ENNReal.log ((a ^ n : ℝ≥0) : ℝ≥0∞) = ((n : ℝ) : EReal) * ENNReal.log (a : ℝ≥0∞) := by
  rw [ENNReal.coe_pow, ENNReal.log_pow, EReal.coe_natCast]

theorem log_coe_nnreal_of_coe_eq_exp {a : ℝ≥0} {z : ℝ} (h : (a : ℝ) = Real.exp z) :
    ENNReal.log (a : ℝ≥0∞) = (z : EReal) := by
  rw [← ENNReal.ofReal_coe_nnreal, h, ENNReal.log_ofReal_of_pos (Real.exp_pos z), Real.log_exp]

/-- Multiplication by a nonnegative real distributes over finite sums in `EReal`. -/
theorem ereal_coe_mul_finsetSum {ι : Type*} (s : Finset ι) (F : ι → EReal) {c : ℝ}
    (hc : 0 ≤ c) : (c : EReal) * ∑ i ∈ s, F i = ∑ i ∈ s, (c : EReal) * F i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hc) (EReal.coe_ne_top c), ih]

theorem ereal_coe_mul_add_coe {c : ℝ} (hc : 0 ≤ c) (a : EReal) (b : ℝ) :
    (c : EReal) * (a + (b : EReal)) = (c : EReal) * a + ((c * b : ℝ) : EReal) := by
  rw [EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hc) (EReal.coe_ne_top c),
    EReal.coe_mul]

/-- A finite sum of extended reals `≠ -∞` is `≠ -∞`. -/
theorem ereal_finsetSum_ne_bot {ι : Type*} (s : Finset ι) (F : ι → EReal)
    (h : ∀ i ∈ s, F i ≠ ⊥) : ∑ i ∈ s, F i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Ne, EReal.add_eq_bot_iff, not_or]
    exact ⟨h a (Finset.mem_insert_self a s), ih fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

/-- A finite sum of extended reals `≠ +∞` is `≠ +∞`. -/
theorem ereal_finsetSum_ne_top {ι : Type*} (s : Finset ι) (F : ι → EReal)
    (h : ∀ i ∈ s, F i ≠ ⊤) : ∑ i ∈ s, F i ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact EReal.add_ne_top (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The infimum of a finite positive combination of decreasing sequences (not `+∞`) is the
combination of the infima. -/
theorem iInf_finsetSum_coe_mul_of_antitone {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 < c i) (a : ι → ℕ → EReal) (ha : ∀ i ∈ s, Antitone (a i))
    (ha0 : ∀ i ∈ s, a i 0 ≠ ⊤) :
    ⨅ j, ∑ i ∈ s, (c i : EReal) * a i j = ∑ i ∈ s, (c i : EReal) * ⨅ j, a i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have hc' : ∀ i ∈ s, 0 < c i := fun i hi => hc i (Finset.mem_insert_of_mem hi)
    have ha' : ∀ i ∈ s, Antitone (a i) := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have ha0' : ∀ i ∈ s, a i 0 ≠ ⊤ := fun i hi => ha0 i (Finset.mem_insert_of_mem hi)
    have hxs := Finset.mem_insert_self x s
    simp only [Finset.sum_insert hx]
    have h1 : Antitone fun j => (c x : EReal) * a x j := fun _ _ h =>
      mul_le_mul_of_nonneg_left (ha x hxs h) (by exact_mod_cast (hc x hxs).le)
    have h2 : Antitone fun j => ∑ i ∈ s, (c i : EReal) * a i j := fun _ _ h =>
      Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (ha' i hi h) (by exact_mod_cast (hc' i hi).le)
    rw [iInf_add_of_antitone h1 h2 (ereal_coe_mul_ne_top (hc x hxs).le (ha0 x hxs))
      (ereal_finsetSum_ne_top _ _ fun i hi => ereal_coe_mul_ne_top (hc' i hi).le (ha0' i hi)),
      iInf_coe_mul_of_antitone (ha x hxs) (hc x hxs), ih hc' ha' ha0']

/-- **Clearing denominators**: finitely many positive rationals `a_i` have a common positive
multiple `N` with `N a_i ∈ ℕ`. -/
theorem exists_nat_mul_eq_of_pos {ι : Type*} (s : Finset ι) (a : ι → ℚ)
    (ha : ∀ i ∈ s, 0 < a i) : ∃ N : ℕ, 0 < N ∧ ∃ n : ι → ℕ, ∀ i ∈ s, (n i : ℚ) = N * a i := by
  refine ⟨∏ i ∈ s, (a i).den, Finset.prod_pos fun i _ => (a i).den_pos,
    fun i => (∏ i ∈ s, (a i).den) / (a i).den * (a i).num.toNat, fun i hi => ?_⟩
  obtain ⟨c, hc⟩ : (a i).den ∣ ∏ i ∈ s, (a i).den := Finset.dvd_prod_of_mem _ hi
  have hnum : (((a i).num.toNat : ℕ) : ℚ) = (a i).num := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_pos.2 (ha i hi)).le]
  dsimp only
  rw [hc, Nat.mul_div_cancel_left _ (a i).den_pos, Nat.cast_mul, hnum, Nat.cast_mul,
    ← Rat.mul_den_eq_num]
  ring

theorem univ_sup_subtype_val {ι β : Type*} [SemilatticeSup β] [OrderBot β] (s : Finset ι)
    (G : ι → β) : (Finset.univ : Finset s).sup (fun j => G j.1) = s.sup G := by
  rw [Finset.univ_eq_attach, Finset.sup_attach]

end aux

/-! ### The trivial valuation in finite morphisms -/

namespace Berk

variable {k : Type*} [Field k] {B A : Type*} [CommRing B] [CommRing A] [Algebra k B]
  [Algebra k A] [Algebra B A] [IsScalarTower k B A]

/-- **The only point over the trivial valuation is the trivial valuation** (FHX, proof of
`lem:finite-flat-norm`). Let `A` be a domain integral over the domain `B` and `π(y) = v_triv`.
Then `|a|_y ≤ 1` for all `a` (integral equation estimate), and for `a ≠ 0` some `b ≠ 0` in `B`
is a multiple `c a` (`Ideal.comap_ne_bot_of_integral_mem`), so `|c|_y |a|_y = |b| = 1` forces
`|a|_y = 1`. -/
theorem eq_triv_of_comap_eq_triv [IsDomain B] [IsDomain A] [Algebra.IsIntegral B A]
    {y : Berk k A} (hy : comap (IsScalarTower.toAlgHom k B A) y = triv) : y = triv := by
  have hval : ∀ b : B, b ≠ 0 → y.val (algebraMap B A b) = 1 := fun b hb => by
    have := congrArg (fun z : Berk k B => z.val b) hy
    simp only [comap_val_apply, IsScalarTower.toAlgHom_apply] at this
    rw [this, triv_val_of_ne_zero hb]
  have hle : ∀ a : A, y.val a ≤ 1 := fun a => by
    obtain ⟨p, hp, hpa⟩ := Algebra.IsIntegral.isIntegral (R := B) a
    refine Valuation.le_of_monic_eval₂_eq_zero y.val (algebraMap B A) hp hpa le_rfl
      fun i _ => ?_
    by_cases hc : p.coeff i = 0
    · simp [hc]
    · exact (hval _ hc).le
  refine Berk.ext (Valuation.ext fun a => ?_)
  by_cases ha : a = 0
  · simp [ha]
  rw [triv_val_of_ne_zero ha]
  have hI := Ideal.comap_ne_bot_of_integral_mem ha (Ideal.mem_span_singleton_self a)
    (Algebra.IsIntegral.isIntegral (R := B) a)
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hb
  obtain ⟨c, hc⟩ := hb
  have h1 : y.val c * y.val a = 1 := by rw [← map_mul, hc, hval b hb0]
  refine le_antisymm (hle a) (not_lt.1 fun hlt => ?_)
  have := mul_lt_one_of_nonneg_of_lt_one_right (hle c) zero_le hlt
  rw [h1] at this
  exact lt_irrefl _ this

end Berk

/-! ### The norm of a function -/

section normFun

variable {k : Type*} [Field k] {B A : Type*} [CommRing B] [CommRing A] [Algebra k B]
  [Algebra k A] [Algebra B A] [IsScalarTower k B A]

/-- The **norm** `N_π u (s) = ∑_{π(y) = s} m_y(π) u(y)` of a function `u` on `(Spec A)^an` along
`π : (Spec A)^an → (Spec B)^an`, for `A` finite over `B` (FHX `lem:finite-flat-norm`), with the
multiplicities `m_y(π) = Berk.fibreMult B y`. -/
def normFun [Module.Finite B A] (u : Berk k A → EReal) (s : Berk k B) : EReal :=
  ∑ y ∈ (finite_preimage_singleton (A := A) s).toFinset, ((fibreMult B y : ℝ) : EReal) * u y

/-- `N_π` is monotone. -/
theorem normFun_mono [Module.Finite B A] {u v : Berk k A → EReal} (h : ∀ y, u y ≤ v y)
    (s : Berk k B) : normFun u s ≤ normFun v s :=
  Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (by positivity)

omit [Algebra B A] [IsScalarTower k B A] in
theorem log_abs_pow_mul_expRadius {ι : Type*} (y : Berk k A) (f : A) (n : ℕ) (lam : ι → ℝ)
    (j : ι) :
    ENNReal.log ((y.val (f ^ n) * expRadius lam j : ℝ≥0) : ℝ≥0∞) =
      ((n : ℝ) : EReal) * logAbs f y + (lam j : EReal) := by
  rw [ENNReal.coe_mul, ENNReal.log_mul_add, map_pow, log_coe_nnreal_pow,
    log_coe_nnreal_of_coe_eq_exp (coe_expRadius lam j), logAbs_def]

omit [Algebra B A] [IsScalarTower k B A] in
/-- If `N a_t = n_t ∈ ℕ`, then `N max_t (a_t log|f_t| + b_t) = log max_t |f_t^{n_t}| e^{N b_t}`. -/
theorem natCast_mul_finsetSup_fsTerm (s : Finset (A × ℚ × ℚ)) {N : ℕ} {n : A × ℚ × ℚ → ℕ}
    (hn : ∀ t ∈ s, (n t : ℚ) = N * t.2.1) (hN : 0 < N) (y : Berk k A) :
    ((N : ℝ) : EReal) * (s.sup fun t => fsTerm t y) =
      ENNReal.log ((Finset.univ.sup fun j : s => y.val (j.1.1 ^ n j.1) *
        expRadius (fun j : s => (((N : ℚ) * j.1.2.2 : ℚ) : ℝ)) j : ℝ≥0) : ℝ≥0∞) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [log_coe_nnreal_finsetSup, FSData.coe_mul_sup _ _ hNR]
  simp only [log_abs_pow_mul_expRadius]
  rw [univ_sup_subtype_val s (fun t => ((n t : ℝ) : EReal) * logAbs t.1 y +
    ((((N : ℚ) * t.2.2 : ℚ) : ℝ) : EReal))]
  refine Finset.sup_congr rfl fun t ht => ?_
  have hn' : (n t : ℝ) = N * t.2.1 := by exact_mod_cast hn t ht
  rw [fsTerm_def, ereal_coe_mul_add_coe hNR.le, ← mul_assoc, ← EReal.coe_mul, hn']
  push_cast
  ring_nf

/-- **Norms of finite maxima of terms `a log|f| + b`** (FHX, proof of `lem:finite-flat-norm`,
finite free étale case). If `u = max_{t ∈ s} (a_t log|f_t| + b_t)` with `a_t ∈ ℚ_{>0}`, then
`N_π u = max_{t ∈ T} (a_t log|c_t| + b_t)` for a finite set `T` of terms with `c_t ∈ B`,
`a_t ∈ ℚ_{>0}`, `b_t ∈ ℚ`: with `N a_t = n_t ∈ ℕ`, `T` consists of the terms
`(c_α, N⁻¹, N⁻¹ ∑_t α_t N b_t)`, `c_α` the coefficients of the norm form of
`∑_t X_t f_t^{n_t}` (`Berk.wgaussValuation_map_normForm`). -/
theorem exists_normFun_finsetSup_fsTerm [Infinite k] [Module.Free B A] [Module.Finite B A]
    [Algebra.Etale B A] (s : Finset (A × ℚ × ℚ)) (hs : ∀ t ∈ s, 0 < t.2.1) :
    ∃ T : Finset (B × ℚ × ℚ), (∀ t ∈ T, 0 < t.2.1) ∧
      ∀ x : Berk k B, normFun (fun y => s.sup fun t => fsTerm t y) x =
        T.sup fun t => fsTerm t x := by
  classical
  obtain ⟨N, hN, n, hn⟩ := exists_nat_mul_eq_of_pos s (fun t => t.2.1) hs
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let b : s → A := fun j => j.1.1 ^ n j.1
  let lam : s → ℚ := fun j => N * j.1.2.2
  let r : s → ℝ≥0 := expRadius fun j => (lam j : ℝ)
  let P : MvPolynomial s B := normForm B b
  let q : (s →₀ ℕ) → ℚ := fun α => α.sum fun j m => (m : ℚ) * lam j
  refine ⟨P.support.image fun α => (P.coeff α, (N : ℚ)⁻¹, (N : ℚ)⁻¹ * q α), ?_, fun x => ?_⟩
  · simp only [Finset.mem_image]
    rintro _ ⟨α, -, rfl⟩
    positivity
  have hkey : ∀ y : Berk k A, (s.sup fun t => fsTerm t y) =
      (((N : ℝ)⁻¹ : ℝ) : EReal) *
        ENNReal.log ((Finset.univ.sup fun j => y.val (b j) * r j : ℝ≥0) : ℝ≥0∞) := by
    intro y
    rw [← natCast_mul_finsetSup_fsTerm s hn hN y, ← mul_assoc, ← EReal.coe_mul,
      inv_mul_cancel₀ hNR.ne', EReal.coe_one, one_mul]
  simp only [normFun, hkey]
  rw [Finset.sum_congr rfl fun y _ => mul_left_comm _ _ _,
    ← ereal_coe_mul_finsetSum _ _ (inv_nonneg.2 hNR.le),
    Finset.sum_congr rfl fun y _ => (log_coe_nnreal_pow _ _).symm,
    ← log_coe_nnreal_finsetProd, ← wgaussValuation_map_normForm b r x,
    wgaussValuation_eq_sup_of_subset _ r _ (support_map_subset _ _),
    log_coe_nnreal_finsetSup, FSData.coe_mul_sup _ _ (inv_pos.2 hNR), Finset.sup_image]
  refine Finset.sup_congr rfl fun α _ => ?_
  simp only [Function.comp_apply, coeff_map, NormedField.valuation_apply, nnnorm_toH]
  rw [ENNReal.coe_mul, ENNReal.log_mul_add,
    log_coe_nnreal_of_coe_eq_exp (coe_monoWeight_expRadius _ α),
    ereal_coe_mul_add_coe (inv_nonneg.2 hNR.le), fsTerm_def]
  have h1 : (((N : ℚ)⁻¹ : ℚ) : ℝ) = (N : ℝ)⁻¹ := by push_cast; ring
  have h2 : (((N : ℚ)⁻¹ * q α : ℚ) : ℝ) =
      (N : ℝ)⁻¹ * α.sum fun j m => (m : ℝ) * (lam j : ℝ) := by
    simp only [q, Finsupp.sum]
    push_cast
    ring
  dsimp only
  rw [h1, h2, logAbs_def]

/-- **Norms of FS functions** (FHX, proof of `lem:finite-flat-norm`, finite free étale case): for
`g ∈ FS(Spec A)`, `N_π g = max_{t ∈ T} (a_t log|c_t| + b_t)` for a finite set `T` of terms with
`c_t ∈ B`, `a_t ∈ ℚ_{>0}`, `b_t ∈ ℚ` (the constant term of `g` is the term `log|1| + b₀`). -/
theorem exists_normFun_eval_eq [Infinite k] [Module.Free B A] [Module.Finite B A]
    [Algebra.Etale B A] (g : FSData k A) :
    ∃ T : Finset (B × ℚ × ℚ), (∀ t ∈ T, 0 < t.2.1) ∧
      ∀ x : Berk k B, normFun g.eval x = T.sup fun t => fsTerm t x := by
  classical
  have hs : ∀ t ∈ insert ((1 : A), (1 : ℚ), g.const) g.terms, 0 < t.2.1 := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact one_pos
    · exact g.pos t ht
  obtain ⟨T, hT, hTeq⟩ := exists_normFun_finsetSup_fsTerm (k := k) (B := B) _ hs
  refine ⟨T, hT, fun x => ?_⟩
  rw [← hTeq]
  congr 1
  funext y
  rw [Finset.sup_insert, fsTerm_one, FSData.eval_def]

/-- The norm of an FS function is finite: it is a positive combination of finite values. -/
theorem normFun_eval_ne_bot [Module.Finite B A] (g : FSData k A) (x : Berk k B) :
    normFun g.eval x ≠ ⊥ :=
  ereal_finsetSum_ne_bot _ _ fun y _ =>
    coe_mul_ne_bot (by exact_mod_cast one_le_fibreMult y) (g.eval_ne_bot y)

/-- **The norm of an FS function is regularizable** (FHX, proof of `lem:finite-flat-norm`):
it is a finite maximum of terms `a log|c| + b`, `a > 0`, not identically `-∞`
(FHX Lemma 5.11(3), `isRegularizable_finsetSup_fsTerm`). -/
theorem FSData.isRegularizable_normFun [Infinite k] [Algebra.FiniteType k B] [Module.Free B A]
    [Module.Finite B A] [Algebra.Etale B A] [Nonempty (Berk k B)] (g : FSData k A) :
    IsRegularizable (normFun (B := B) g.eval) := by
  obtain ⟨T, hT, hTeq⟩ := exists_normFun_eval_eq (B := B) g
  refine (isRegularizable_finsetSup_fsTerm hT ⟨Classical.arbitrary _, ?_⟩).congr
    fun s => (hTeq s).symm
  rw [← hTeq]
  exact normFun_eval_ne_bot _ _

end normFun

universe u v

/-- **FHX Lemma 5.13** (`lem:finite-flat-norm`), finite free étale case
(`rmk:finite-flat-norm-etale`). Let `Spec B` be a normal affine variety over the algebraically
closed field `k`, and `A` a domain which is a finite free étale `B`-algebra. Then the norm
`N_π u = ∑_{π(y) = ·} m_y(π) u(y)` of a regularizable function `u` on `(Spec A)^an` is
regularizable on `(Spec B)^an`.

Proof: if FS functions `g_j` decrease to `u`, the norms `N_π g_j` are regularizable
(`FSData.isRegularizable_normFun`) and decrease to `N_π u`
(`iInf_finsetSum_coe_mul_of_antitone`); `N_π u` is finite at `v_triv`, as the only point over
`v_triv` is `v_triv` (`Berk.eq_triv_of_comap_eq_triv`) and `u(v_triv) ≠ -∞`
(`IsRegularizable.triv_ne_bot`); conclude by FHX Lemma 5.11(2) (`IsRegularizable.of_antitone`). -/
theorem IsRegularizable.normFun {k : Type u} [Field k] [IsAlgClosed k]
    [WuRegularization.{u, v} k] {B : Type v} [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] [IsIntegrallyClosed B] {A : Type*} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Module.Free B A] [Module.Finite B A]
    [Algebra.Etale B A] {u : Berk k A → EReal} (hu : IsRegularizable u) :
    IsRegularizable (EnvelopeProperty.normFun (B := B) u) := by
  have htriv := hu.triv_ne_bot
  have : Nonempty (Berk k B) := ⟨triv⟩
  obtain ⟨-, g, hg, hgu⟩ := hu
  have hreg : ∀ j, IsRegularizable (EnvelopeProperty.normFun (B := B) (g j).eval) :=
    fun j => (g j).isRegularizable_normFun
  have hmono : ∀ s : Berk k B, Antitone fun j => EnvelopeProperty.normFun (g j).eval s :=
    fun s _ _ hij => normFun_mono (fun y => hg y hij) s
  have hinf : ∀ s : Berk k B,
      ⨅ j, EnvelopeProperty.normFun (g j).eval s = EnvelopeProperty.normFun u s := fun s => by
    simp only [EnvelopeProperty.normFun, hgu]
    exact iInf_finsetSum_coe_mul_of_antitone _ _
      (fun y _ => by exact_mod_cast one_le_fibreMult y) (fun y j => (g j).eval y)
      (fun y _ => hg y) (fun y _ => (g 0).eval_ne_top y)
  have hne : EnvelopeProperty.normFun u (triv : Berk k B) ≠ ⊥ := by
    refine ereal_finsetSum_ne_bot _ _ fun y hy => ?_
    have hy' : y ∈ comap (IsScalarTower.toAlgHom k B A) ⁻¹' {triv} :=
      (Set.Finite.mem_toFinset _).1 hy
    rw [eq_triv_of_comap_eq_triv hy']
    exact coe_mul_ne_bot (by exact_mod_cast one_le_fibreMult _) htriv
  refine (IsRegularizable.of_antitone hreg hmono ⟨triv, ?_⟩).congr hinf
  rw [hinf]
  exact hne

end EnvelopeProperty
