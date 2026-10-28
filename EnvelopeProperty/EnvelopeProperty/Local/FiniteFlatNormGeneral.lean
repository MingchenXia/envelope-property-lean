/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.FlatFibre
import EnvelopeProperty.Local.FiniteFlatNorm
import EnvelopeProperty.Local.GluingCover

/-!
# Norms of regularizable functions along finite flat morphisms

Let `k` be a field with the trivial absolute value, `B → A` a homomorphism of `k`-algebras making
`A` a finite `B`-module, and `π = π^an : (Spec A)^an → (Spec B)^an`. For a function `u` on
`(Spec A)^an` its **norm** is
`N_π u (s) = ∑_{π(y) = s} m_y(π) u(y)`,
where `m_y(π) = dim_{H(s)} (H(s) ⊗_B A)_{m_y}` is the multiplicity of `y` in its fibre
(`Berk.flatFibreMult`). This file proves Fang–Han–Xia, *The envelope property for unibranch
projective varieties*, Lemma 5.13 (`lem:finite-flat-norm`) for a finite flat morphism
`π : Y → S` of affine varieties with `S` normal (normality of `Y` is not needed), without the
base change compatibility: `N_π` maps `ℛ(Y)` to `ℛ(S)`
(`EnvelopeProperty.IsRegularizable.flatNormFun`). As the gluing proposition FHX 5.20(2) is used,
`k` is assumed countable there; the finite free case
(`EnvelopeProperty.IsRegularizable.flatNormFun_of_free`) needs no countability.

* **FS functions.** For `u = max_t (a_t log|f_t| + b_t)` with `a_t ∈ ℚ_{>0}`, choose `N > 0` with
  `N a_t ∈ ℕ`; with `b_t = f_t^{N a_t}` and `λ_t = N b_t`, `N u(y) = log max_t |b_t|_y e^{λ_t}`.
  If `P = ∑_α c_α X^α` is a polynomial over a ring `B'`, with a map
  `F : (Spec B')^an → (Spec B)^an`, such that
  `max_α |c_α|_x r^α = ∏_{π(y) = F(x)} (max_j |b_j|_y r_j)^{m_y(π)}` for all `x` and all radii
  (`EnvelopeProperty.HasFlatNormForms`), then
  `N · (N_π u) ∘ F = max_α (log|c_α| + ∑_t α_t λ_t)`, a finite maximum of terms `a log|c| + b`
  with `c ∈ B'`, `a = N⁻¹`, `b ∈ ℚ` (`EnvelopeProperty.exists_flatNormFun_finsetSup_fsTerm_of`).
  The norm form provides `P` for `B' = B`, `F = id` when `A` is free over `B`
  (`Berk.wgaussValuation_normForm_flat`), and for `B' = B_h`, `F` the inclusion of the principal
  open `(Spec B_h)^an`, when `B_h ⊗_B A` is free over `B_h` (`Berk.wgaussValuation_normForm_away`).
* **Regularizable functions** (`EnvelopeProperty.IsRegularizable.flatNormFun_comp_of`). On a
  normal affine variety `Spec B'`, if `u_j ∈ FS(Spec A)` decrease to `u ∈ ℛ(Spec A)`, then
  `(N_π u_j) ∘ F ∈ ℛ(Spec B')` (FHX Lemma 5.11(3)) decrease to `(N_π u) ∘ F`, which is finite at
  the trivial valuation (the only point over `v_triv` is `v_triv`); FHX Lemma 5.11(2) concludes.
  This gives the **finite free case** (`EnvelopeProperty.IsRegularizable.flatNormFun_of_free`).
* **The finite flat case** (`EnvelopeProperty.IsRegularizable.flatNormFun`). A finite flat module
  over the noetherian ring `B` is free on a principal neighbourhood of every prime
  (`EnvelopeProperty.exists_free_localizationAway`), so `N_π u` is regularizable on principal
  opens `(Spec B_h)^an` covering `(Spec B)^an`. It is upper semicontinuous (a local property) and
  has logarithmic growth (`u ≤ C g ∘ π + C'` for `g ∈ FS(S)` by FHX Lemma 5.8(2), and the sums
  of the multiplicities are bounded), so FHX Proposition 5.20(2)
  (`EnvelopeProperty.IsRegularizable.of_cover_principal`) applies.

In the finite free étale case `N_π` agrees with `EnvelopeProperty.normFun`
(`EnvelopeProperty.flatNormFun_eq_normFun`). The base change property
`(N_π u) ∘ r = N_{π_F}(u ∘ r)` of the source lemma is not treated here.

## Main definitions

* `EnvelopeProperty.flatNormFun u`: the norm `N_π u` of `u : (Spec A)^an → [-∞, ∞]`.
* `EnvelopeProperty.HasFlatNormForms F`: the norm forms of `A` over `B'` along `F`.

## Main results

* `EnvelopeProperty.exists_flatNormFun_eval_eq_of`, `EnvelopeProperty.exists_flatNormFun_eval_eq`:
  norms of FS functions are finite maxima of terms `a log|c| + b`.
* `EnvelopeProperty.IsRegularizable.flatNormFun_of_free`: FHX Lemma 5.13, finite free case.
* `EnvelopeProperty.IsRegularizable.flatNormFun`: **FHX Lemma 5.13** (finite flat case).
-/

open scoped NNReal ENNReal Topology TensorProduct

open MvPolynomial Topology

noncomputable section

namespace EnvelopeProperty

open Berk

/-- Upper semicontinuity transfers along open embeddings. -/
theorem upperSemicontinuousAt_of_isOpenEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {e : X → Y} (he : IsOpenEmbedding e) {f : Y → EReal} {x : X}
    (hf : UpperSemicontinuousAt (f ∘ e) x) : UpperSemicontinuousAt f (e x) := by
  intro c hc
  rw [← he.map_nhds_eq]
  exact Filter.eventually_map.2 (hf c hc)

/-- The coercion `ℝ → [-∞, ∞]` commutes with finite sums. -/
theorem ereal_coe_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

section flatNormFun

variable {k : Type*} [Field k] {B A : Type*} [CommRing B] [CommRing A] [Algebra k B]
  [Algebra k A] [Algebra B A] [IsScalarTower k B A]

/-- The **norm** `N_π u (s) = ∑_{π(y) = s} m_y(π) u(y)` of a function `u` on `(Spec A)^an` along
`π : (Spec A)^an → (Spec B)^an`, for `A` finite over `B` (FHX `lem:finite-flat-norm`), with the
multiplicities `m_y(π) = dim_{H(s)} (H(s) ⊗_B A)_{m_y}` (`Berk.flatFibreMult`). -/
def flatNormFun [Module.Finite B A] (u : Berk k A → EReal) (s : Berk k B) : EReal :=
  ∑ y ∈ (finite_preimage_singleton (A := A) s).toFinset, ((flatFibreMult B y : ℝ) : EReal) * u y

/-- `N_π` is monotone. -/
theorem flatNormFun_mono [Module.Finite B A] {u v : Berk k A → EReal} (h : ∀ y, u y ≤ v y)
    (s : Berk k B) : flatNormFun u s ≤ flatNormFun v s :=
  Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (by positivity)

/-- In the finite free étale case, `N_π` is the norm `EnvelopeProperty.normFun` of
`rmk:finite-flat-norm-etale` (the multiplicities are the residue degrees). -/
theorem flatNormFun_eq_normFun [Module.Free B A] [Module.Finite B A] [Algebra.Etale B A]
    (u : Berk k A → EReal) (s : Berk k B) : flatNormFun (B := B) u s = normFun (B := B) u s := by
  simp only [flatNormFun, normFun, flatFibreMult_eq_fibreMult]

/-- The norm of an FS function is finite: it is a positive combination of finite values. -/
theorem flatNormFun_eval_ne_bot [Module.Finite B A] (g : FSData k A) (x : Berk k B) :
    flatNormFun g.eval x ≠ ⊥ :=
  ereal_finsetSum_ne_bot _ _ fun y _ =>
    coe_mul_ne_bot (by exact_mod_cast one_le_flatFibreMult y) (g.eval_ne_bot y)

variable (A) in
/-- **Norm forms along `F`.** For a map `F : (Spec B')^an → (Spec B)^an`, `F` *admits norm forms*
for `A` if for every finite family `b_j ∈ A` (indexed by a finite set of terms) there is a
polynomial `P = ∑_α c_α X^α` with coefficients in `B'` such that
`max_α |c_α|_x r^α = ∏_{π(y) = F(x)} (max_j |b_j|_y r_j)^{m_y(π)}` for all radii `r_j ≥ 0` and all
`x ∈ (Spec B')^an`. The norm form `N(∑_j X_j b_j)` gives such `P` for `F = id` when `A` is free
over `B` (`Berk.wgaussValuation_normForm_flat`), and for the inclusion of a principal open
`(Spec B_h)^an` when `B_h ⊗_B A` is free over `B_h` (`Berk.wgaussValuation_normForm_away`). -/
def HasFlatNormForms [Module.Finite B A] {B' : Type*} [CommRing B'] [Algebra k B']
    (F : Berk k B' → Berk k B) : Prop :=
  ∀ (s : Finset (A × ℚ × ℚ)) (b : s → A), ∃ P : MvPolynomial s B',
    ∀ (r : s → ℝ≥0) (x : Berk k B'), wgaussValuation x.val r P =
      ∏ y ∈ (finite_preimage_singleton (A := A) (F x)).toFinset,
        (Finset.univ.sup fun j => y.val (b j) * r j) ^ flatFibreMult B y

/-- For `A` finite free over `B`, the identity admits norm forms. -/
theorem hasFlatNormForms_id [Infinite k] [Module.Free B A] [Module.Finite B A] :
    HasFlatNormForms A (id : Berk k B → Berk k B) :=
  fun _ b => ⟨normForm B b, fun r x => wgaussValuation_normForm_flat b r x⟩

/-- If `B_h ⊗_B A` is free over `B_h`, the inclusion `(Spec B_h)^an → (Spec B)^an` admits norm
forms. -/
theorem hasFlatNormForms_awayComap [Infinite k] [Module.Finite B A] (h : B)
    [Module.Free (Localization.Away h) (Localization.Away h ⊗[B] A)] :
    HasFlatNormForms A (awayComap (k := k) h) :=
  fun _ b => ⟨normForm (Localization.Away h) fun j => (1 : Localization.Away h) ⊗ₜ[B] b j,
    fun r x => wgaussValuation_normForm_away h b r x⟩

/-- **Norms of finite maxima of terms `a log|f| + b`** (FHX, proof of `lem:finite-flat-norm`).
If `F : (Spec B')^an → (Spec B)^an` admits norm forms for `A` and
`u = max_{t ∈ s} (a_t log|f_t| + b_t)` with `a_t ∈ ℚ_{>0}`, then
`(N_π u) ∘ F = max_{t ∈ T} (a_t log|c_t| + b_t)` for a finite set `T` of terms with `c_t ∈ B'`,
`a_t ∈ ℚ_{>0}`, `b_t ∈ ℚ`: with `N a_t = n_t ∈ ℕ`, `T` consists of the terms
`(c_α, N⁻¹, N⁻¹ ∑_t α_t N b_t)`, `c_α` the coefficients of a norm form of `∑_t X_t f_t^{n_t}`. -/
theorem exists_flatNormFun_finsetSup_fsTerm_of [Module.Finite B A] {B' : Type*} [CommRing B']
    [Algebra k B'] {F : Berk k B' → Berk k B} (hN : HasFlatNormForms A F)
    (s : Finset (A × ℚ × ℚ)) (hs : ∀ t ∈ s, 0 < t.2.1) :
    ∃ T : Finset (B' × ℚ × ℚ), (∀ t ∈ T, 0 < t.2.1) ∧
      ∀ x : Berk k B', flatNormFun (fun y => s.sup fun t => fsTerm t y) (F x) =
        T.sup fun t => fsTerm t x := by
  classical
  obtain ⟨N, hN0, n, hn⟩ := exists_nat_mul_eq_of_pos s (fun t => t.2.1) hs
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  let b : s → A := fun j => j.1.1 ^ n j.1
  let lam : s → ℚ := fun j => N * j.1.2.2
  let r : s → ℝ≥0 := expRadius fun j => (lam j : ℝ)
  obtain ⟨P, hP⟩ := hN s b
  let q : (s →₀ ℕ) → ℚ := fun α => α.sum fun j m => (m : ℚ) * lam j
  refine ⟨P.support.image fun α => (P.coeff α, (N : ℚ)⁻¹, (N : ℚ)⁻¹ * q α), ?_, fun x => ?_⟩
  · simp only [Finset.mem_image]
    rintro _ ⟨α, -, rfl⟩
    positivity
  have hkey : ∀ y : Berk k A, (s.sup fun t => fsTerm t y) =
      (((N : ℝ)⁻¹ : ℝ) : EReal) *
        ENNReal.log ((Finset.univ.sup fun j => y.val (b j) * r j : ℝ≥0) : ℝ≥0∞) := by
    intro y
    rw [← natCast_mul_finsetSup_fsTerm s hn hN0 y, ← mul_assoc, ← EReal.coe_mul,
      inv_mul_cancel₀ hNR.ne', EReal.coe_one, one_mul]
  simp only [flatNormFun, hkey]
  rw [Finset.sum_congr rfl fun y _ => mul_left_comm _ _ _,
    ← ereal_coe_mul_finsetSum _ _ (inv_nonneg.2 hNR.le),
    Finset.sum_congr rfl fun y _ => (log_coe_nnreal_pow _ _).symm,
    ← log_coe_nnreal_finsetProd, ← hP r x, wgaussValuation_apply,
    log_coe_nnreal_finsetSup, FSData.coe_mul_sup _ _ (inv_pos.2 hNR), Finset.sup_image]
  refine Finset.sup_congr rfl fun α _ => ?_
  simp only [Function.comp_apply]
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

/-- **Norms of FS functions** (FHX, proof of `lem:finite-flat-norm`): if `F` admits norm forms
for `A`, then for `g ∈ FS(Spec A)`, `(N_π g) ∘ F = max_{t ∈ T} (a_t log|c_t| + b_t)` for a
finite set `T` of terms with `c_t ∈ B'`, `a_t ∈ ℚ_{>0}`, `b_t ∈ ℚ`. -/
theorem exists_flatNormFun_eval_eq_of [Module.Finite B A] {B' : Type*} [CommRing B']
    [Algebra k B'] {F : Berk k B' → Berk k B} (hN : HasFlatNormForms A F) (g : FSData k A) :
    ∃ T : Finset (B' × ℚ × ℚ), (∀ t ∈ T, 0 < t.2.1) ∧
      ∀ x : Berk k B', flatNormFun g.eval (F x) = T.sup fun t => fsTerm t x := by
  classical
  have hs : ∀ t ∈ insert ((1 : A), (1 : ℚ), g.const) g.terms, 0 < t.2.1 := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact one_pos
    · exact g.pos t ht
  obtain ⟨T, hT, hTeq⟩ := exists_flatNormFun_finsetSup_fsTerm_of hN _ hs
  refine ⟨T, hT, fun x => ?_⟩
  rw [← hTeq]
  congr 1
  funext y
  rw [Finset.sup_insert, fsTerm_one, FSData.eval_def]

/-- **Norms of FS functions along a finite free morphism** (FHX, proof of
`lem:finite-flat-norm`): for `A` finite free over `B` and `g ∈ FS(Spec A)`,
`N_π g = max_{t ∈ T} (a_t log|c_t| + b_t)` with `c_t ∈ B`, `a_t ∈ ℚ_{>0}`, `b_t ∈ ℚ`. -/
theorem exists_flatNormFun_eval_eq [Infinite k] [Module.Free B A] [Module.Finite B A]
    (g : FSData k A) :
    ∃ T : Finset (B × ℚ × ℚ), (∀ t ∈ T, 0 < t.2.1) ∧
      ∀ x : Berk k B, flatNormFun g.eval x = T.sup fun t => fsTerm t x :=
  exists_flatNormFun_eval_eq_of (hasFlatNormForms_id (k := k)) g

/-- **The norm of an FS function is regularizable** along `F` (FHX, proof of
`lem:finite-flat-norm`): it is a finite maximum of terms `a log|c| + b`, `a > 0`, not
identically `-∞` (FHX Lemma 5.11(3), `isRegularizable_finsetSup_fsTerm`). -/
theorem FSData.isRegularizable_flatNormFun_of [Module.Finite B A] {B' : Type*} [CommRing B']
    [Algebra k B'] [Algebra.FiniteType k B'] [Nonempty (Berk k B')] {F : Berk k B' → Berk k B}
    (hN : HasFlatNormForms A F) (g : FSData k A) :
    IsRegularizable fun x => flatNormFun (B := B) g.eval (F x) := by
  obtain ⟨T, hT, hTeq⟩ := exists_flatNormFun_eval_eq_of hN g
  refine (isRegularizable_finsetSup_fsTerm hT ⟨Classical.arbitrary _, ?_⟩).congr
    fun s => (hTeq s).symm
  rw [← hTeq]
  exact flatNormFun_eval_ne_bot _ _

end flatNormFun

universe u v

/-- **Regularizability of norms along maps admitting norm forms** (FHX, proof of
`lem:finite-flat-norm`). Let `Spec B'` be a normal affine variety over the algebraically closed
field `k`, `A` a domain finite over the domain `B`, and `F : (Spec B')^an → (Spec B)^an` a map
admitting norm forms for `A` with `F(v_triv) = v_triv`. Then for `u ∈ ℛ(Spec A)`, the function
`(N_π u) ∘ F` is regularizable on `(Spec B')^an`.

Proof: if FS functions `g_j` decrease to `u`, the functions `(N_π g_j) ∘ F` are regularizable
(`FSData.isRegularizable_flatNormFun_of`) and decrease to `(N_π u) ∘ F`
(`iInf_finsetSum_coe_mul_of_antitone`); `(N_π u)(F(v_triv)) = (N_π u)(v_triv)` is finite, as the
only point over `v_triv` is `v_triv` (`Berk.eq_triv_of_comap_eq_triv`) and `u(v_triv) ≠ -∞`
(`IsRegularizable.triv_ne_bot`); conclude by FHX Lemma 5.11(2) (`IsRegularizable.of_antitone`). -/
theorem IsRegularizable.flatNormFun_comp_of {k : Type u} [Field k] [IsAlgClosed k]
    [WuRegularization.{u, v} k] {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]
    {A : Type*} [CommRing A] [IsDomain A] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
    [Module.Finite B A] {B' : Type v} [CommRing B'] [IsDomain B'] [Algebra k B']
    [Algebra.FiniteType k B'] [IsIntegrallyClosed B'] {F : Berk k B' → Berk k B}
    (hF : F triv = triv) (hN : HasFlatNormForms A F) {u : Berk k A → EReal}
    (hu : IsRegularizable u) : IsRegularizable fun x => flatNormFun (B := B) u (F x) := by
  have htriv := hu.triv_ne_bot
  have : Nonempty (Berk k B') := ⟨triv⟩
  obtain ⟨-, g, hg, hgu⟩ := hu
  have hreg : ∀ j, IsRegularizable fun x => flatNormFun (B := B) (g j).eval (F x) :=
    fun j => (g j).isRegularizable_flatNormFun_of hN
  have hmono : ∀ x : Berk k B', Antitone fun j => flatNormFun (B := B) (g j).eval (F x) :=
    fun x _ _ hij => flatNormFun_mono (fun y => hg y hij) _
  have hinf : ∀ x : Berk k B',
      ⨅ j, flatNormFun (B := B) (g j).eval (F x) = flatNormFun u (F x) := fun x => by
    simp only [flatNormFun, hgu]
    exact iInf_finsetSum_coe_mul_of_antitone _ _
      (fun y _ => by exact_mod_cast one_le_flatFibreMult y) (fun y j => (g j).eval y)
      (fun y _ => hg y) (fun y _ => (g 0).eval_ne_top y)
  have hne : flatNormFun u (F triv) ≠ ⊥ := by
    rw [hF]
    refine ereal_finsetSum_ne_bot _ _ fun y hy => ?_
    have hy' : y ∈ comap (IsScalarTower.toAlgHom k B A) ⁻¹' {triv} :=
      (Set.Finite.mem_toFinset _).1 hy
    rw [eq_triv_of_comap_eq_triv hy']
    exact coe_mul_ne_bot (by exact_mod_cast one_le_flatFibreMult _) htriv
  refine (IsRegularizable.of_antitone hreg hmono ⟨triv, ?_⟩).congr hinf
  rw [hinf]
  exact hne

/-- **FHX Lemma 5.13** (`lem:finite-flat-norm`), finite free case. Let `Spec B` be a normal affine
variety over the algebraically closed field `k`, and `A` a domain which is a finite free
`B`-algebra. Then the norm `N_π u = ∑_{π(y) = ·} m_y(π) u(y)` of a regularizable function `u` on
`(Spec A)^an` is regularizable on `(Spec B)^an`. -/
theorem IsRegularizable.flatNormFun_of_free {k : Type u} [Field k] [IsAlgClosed k]
    [WuRegularization.{u, v} k] {B : Type v} [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] [IsIntegrallyClosed B] {A : Type*} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Module.Free B A] [Module.Finite B A]
    {u : Berk k A → EReal} (hu : IsRegularizable u) :
    IsRegularizable (flatNormFun (B := B) u) :=
  hu.flatNormFun_comp_of (F := id) rfl hasFlatNormForms_id

/-- **The norm of a function of logarithmic growth has logarithmic growth** (for `A` finite over
`B` of finite type): if `u ≤ g` with `g ∈ FS(Spec A)`, then `g ≤ C h ∘ π + C'` for the standard
FS function `h ≥ 0` of `Spec B` (FHX Lemma 5.8(2)), and the multiplicities over each point add
up to at most `n`, the number of generators of the `B`-module `A`; so
`N_π u ≤ n C h + n |C'|`. -/
theorem hasLogGrowth_flatNormFun {k : Type*} [Field k] {B A : Type*} [CommRing B] [CommRing A]
    [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Algebra.FiniteType k B]
    [Module.Finite B A] {u : Berk k A → EReal} (g : FSData k A) (hug : ∀ y, u y ≤ g.eval y) :
    HasLogGrowth (flatNormFun (B := B) u) := by
  obtain ⟨C, C', hC, hCg⟩ := FSData.exists_eval_le_comap_of_isIntegral' g (FSData.std k B)
  obtain ⟨n, hn⟩ := exists_sum_flatFibreMult_le (k := k) (B := B) (A := A)
  refine (((FSData.std k B).hasLogGrowth.smul (c := n * C) (by positivity)).add_const
    (n * |C'|)).mono fun s => ?_
  set e := (FSData.std k B).evalReal s with he
  have he0 : 0 ≤ e := FSData.evalReal_std_nonneg k B s
  set M : ℝ := C * e + |C'| with hM
  have hM0 : 0 ≤ M := add_nonneg (mul_nonneg hC he0) (abs_nonneg _)
  have hle : ∀ y ∈ (finite_preimage_singleton (A := A) s).toFinset, u y ≤ (M : EReal) := by
    intro y hy
    have hy0 : y ∈ comap (IsScalarTower.toAlgHom k B A) ⁻¹' {s} :=
      (Set.Finite.mem_toFinset _).1 hy
    have hy' : comap (IsScalarTower.toAlgHom k B A) y = s := hy0
    refine (hug y).trans ((hCg y).trans ?_)
    rw [hy', ← (FSData.std k B).coe_evalReal s, ← he, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_le_coe_iff, hM]
    linarith [le_abs_self C']
  calc flatNormFun u s
      ≤ ∑ y ∈ (finite_preimage_singleton (A := A) s).toFinset,
          ((flatFibreMult B y : ℝ) : EReal) * (M : EReal) :=
        Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_left (hle y hy) (by positivity)
    _ = ((∑ y ∈ (finite_preimage_singleton (A := A) s).toFinset,
          (flatFibreMult B y : ℝ)) * M : ℝ) := by
        rw [Finset.sum_mul, ereal_coe_finsetSum]
        simp only [EReal.coe_mul]
    _ ≤ ((n : ℝ) * M : ℝ) := by
        rw [EReal.coe_le_coe_iff]
        refine mul_le_mul_of_nonneg_right ?_ hM0
        exact_mod_cast hn s
    _ = ((n * C : ℝ) : EReal) * (FSData.std k B).eval s + ((n * |C'| : ℝ) : EReal) := by
        rw [← (FSData.std k B).coe_evalReal s, ← he, ← EReal.coe_mul, ← EReal.coe_add, hM]
        congr 1
        ring

/-- **FHX Lemma 5.13** (`lem:finite-flat-norm`). Let `π : Y = Spec A → S = Spec B` be a finite flat
morphism of affine varieties over the (countable) algebraically closed field `k`, with `S`
normal. Then the norm `N_π u = ∑_{π(y) = ·} m_y(π) u(y)`, with the multiplicities
`m_y(π) = dim_{H(s)} (H(s) ⊗_B A)_{m_y}`, of a regularizable function `u` on `Y^an` is
regularizable on `S^an`.

Proof: every point `x ∈ S^an` lies in a principal open `(Spec B_h)^an` over which `A` is free
(`exists_free_localizationAway`, at the prime `supp x`); there `(N_π u) ∘ ι` is regularizable
(`IsRegularizable.flatNormFun_comp_of` with the norm forms over `B_h`). Hence `N_π u` is upper
semicontinuous (a local property), and it has logarithmic growth
(`hasLogGrowth_flatNormFun`); conclude by FHX Proposition 5.20(2)
(`IsRegularizable.of_cover_principal`). -/
theorem IsRegularizable.flatNormFun {k : Type u} [Field k] [IsAlgClosed k] [Countable k]
    [WuRegularization.{u, v} k] {B : Type v} [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] [IsIntegrallyClosed B] {A : Type*} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Module.Finite B A] [Module.Flat B A]
    {u : Berk k A → EReal} (hu : IsRegularizable u) :
    IsRegularizable (flatNormFun (B := B) u) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hloc : ∀ x : Berk k B, ∃ h : B, h ≠ 0 ∧ x.val h ≠ 0 ∧
      IsRegularizable fun y => EnvelopeProperty.flatNormFun (B := B) u (awayComap h y) := by
    intro x
    obtain ⟨h, hh, hfree⟩ := exists_free_localizationAway (B := B) (A := A) x.val.supp
    have hxh : x.val h ≠ 0 := hh
    have hh0 : h ≠ 0 := fun h0 => hxh (by rw [h0, map_zero])
    have := isDomain_localizationAway hh0
    have : IsIntegrallyClosed (Localization.Away h) :=
      isIntegrallyClosed_of_isLocalization (Localization.Away h) (Submonoid.powers h)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hh0)
    exact ⟨h, hh0, hxh, hu.flatNormFun_comp_of (awayComap_triv h)
      (hasFlatNormForms_awayComap h)⟩
  have husc : UpperSemicontinuous (EnvelopeProperty.flatNormFun (B := B) u) := by
    intro x
    obtain ⟨h, -, hxh, hreg⟩ := hloc x
    rw [← awayComap_awayLift h x hxh]
    exact upperSemicontinuousAt_of_isOpenEmbedding (isOpenEmbedding_awayComap h)
      (hreg.upperSemicontinuous _)
  obtain ⟨-, g, -, hgu⟩ := hu
  have hlog : HasLogGrowth (EnvelopeProperty.flatNormFun (B := B) u) :=
    hasLogGrowth_flatNormFun (g 0) fun y => by rw [hgu y]; exact iInf_le _ 0
  exact IsRegularizable.of_cover_principal husc hlog hloc

end EnvelopeProperty
