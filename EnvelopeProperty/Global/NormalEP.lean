/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.Siu

/-!
# Homogeneous slices and the envelope property on normal models

Let `𝒳 = (K, S, z)` be an integral multiprojective model of rank `r` over an
algebraically closed trivially valued field `k` (`EnvelopeProperty.MultiModel`).
This module proves the homogeneous-slice criterion and the envelope property
at every real class from the envelope property at positive classes, following
FHX Proposition 7.5 and Corollary 7.6 (`prop:homogeneous-slices`, `cor:normal-EP`).
The corresponding blueprint nodes are `prop:nn-homogeneous-slices` and
`cor:nn-normal-ep`.

## Main statements

* `MultiModel.hasEnvelopeProperty_of_isPSHHom_uscReg_iSup` (**`prop:nn-homogeneous-slices`**): for
  every `θ ∈ ℝ^r`, if `(sup_i ψ_i)^⋆ ∈ PSH_hom(𝒳, θ)` for every nonempty increasing net `(ψ_i)` in
  `PSH_hom(𝒳, θ)`, then `EP_𝒳(θ)`.
* `MultiModel.isPSHHom_uscReg_iSup_of_isNormal`: on a normal model with the envelope property at
  positive classes, `(sup_i ψ_i)^⋆ ∈ PSH_hom(𝒳, θ)` for every nonempty family in `PSH_hom(𝒳, θ)`,
  every `θ ∈ ℝ^r` (by Siu division, `thm:nn-homogeneous-siu`).
* `MultiModel.hasEnvelopeProperty_of_isNormal_of_forall_pos` (**`cor:nn-normal-ep`**): on a normal
  model with the envelope property at positive classes, `EP_𝒳(θ)` for **every** `θ ∈ ℝ^r`.

The envelope property at positive classes (`thm:gl-normal-ample-ep`, FHX Theorem 6.1) enters only
through its conclusion, as the explicit hypothesis
`hample: ∀ η: Fin r → ℝ, (∀ c, 0 < η c) → X.HasEnvelopeProperty η`.

## Proof of `prop:nn-homogeneous-slices`

* `hasEnvelopeProperty_of_monotone`: a bounded family in `PSH(𝒳, θ)` is replaced by the increasing
  net of its finite maxima; a constant normalizes `sup_i φ_i(⋆) = 0`.
* For `λ < 0` the regularized slices `ψ_λ = (sup_{φ_i(⋆) > λ} (φ̂_i)_λ)^⋆` lie in `PSH_hom(𝒳, θ)`
  (`isPSHHom_uscReg_iSup_legendreSlice`, `thm:gl-homog-decomposition`) and decrease in `λ`
  (`uscReg_iSup_legendreSlice_antitone`); `Ψ = (sup_n ψ_{-n-1})^⋆ ∈ PSH_hom(𝒳, θ)` dominates them.
* `EnvelopeProperty.SliceGrid`: the dyadic grid `j 2^{-n}`, `-n 2^n ≤ j < 0`, with the index sets
  `SliceGrid.index n: Finset (Option ℤ)` (`none` for the term `Ψ - n`), the functions
  `SliceGrid.term` and the constants `SliceGrid.const` of
  `U_n = max {Ψ - n, max_j (ψ_{j 2^{-n}} + (j + 1) 2^{-n})}`; termwise domination
  (`SliceGrid.dominated`), `f ≤ U_n` (`SliceGrid.le_sup`, with
  `le_of_forall_uscReg_iSup_legendreSlice_add_le`) and `U_n ≤ max (-n, f^⋆ + 2^{-n})`
  (`SliceGrid.sup_le_max`).
* `isPSH_uscReg_iSup_of_homogeneous_slices`: `U = inf_n U_n` is `θ`-psh by
  `thm:nn-hom-max-diagonal` (`MultiModel.isPSH_of_dominated_homMax_seq`), and `U = f^⋆`.

## Deviations from the blueprint

* `prop:nn-homogeneous-slices`: the nets of the hypothesis are indexed by nonempty directed
  preorders in the universe of `𝒳^an`. The grid points are indexed by integers, `a = j 2^{-n}`,
  `h_n = 2^{-n}`, and the level `n = 0` (`U_0 = Ψ`) is included. The lower bound `f ≤ U_n` is proved
  for each `φ_i` from `φ_i = sup_{λ < φ_i(⋆)} ((φ̂_i)_λ + λ)`, without first interchanging the
  suprema.
* `cor:nn-normal-ep`: the homogeneous step is proved for arbitrary nonempty families (not only
  increasing nets). The identification `(sup_i ψ_i)^⋆ = Ψ₀` (where `χ = e_E + Ψ₀`) uses the
  comparison theorem twice with the usc majorant `(sup_i ψ_i)^⋆ + e_E` of `χ`, instead of the
  locality of usc regularization on `Ω = {e_E > -∞}` (`lem:gl-usc-local`(2)).
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Real translates in `EReal` -/

/-- Adding a real constant commutes with suprema in `EReal`. -/
theorem ereal_iSup_add_coe {ι : Sort*} (a : ι → EReal) (c : ℝ) :
    (⨆ i, a i) + (c : EReal) = ⨆ i, (a i + (c : EReal)) :=
  Monotone.map_iSup_of_continuousAt (f := fun x : EReal => x + (c : EReal))
    (ProjBerk.continuous_ereal_add_coe c).continuousAt (fun _ _ h => add_le_add_left h _)
    (EReal.bot_add _)

/-- The usc regularization commutes with real translates: `(g + c)^⋆ = g^⋆ + c`. -/
theorem uscReg_add_coe {T : Type*} [TopologicalSpace T] (g : T → EReal) (c : ℝ) :
    uscReg (fun x => g x + (c : EReal)) = fun x => uscReg g x + (c : EReal) := by
  funext x
  exact (uscReg_restrict_apply isOpen_univ (fun y => g y + (c : EReal)) ⟨x, mem_univ x⟩).symm.trans
    (uscReg_add_continuous (Ω := univ) isOpen_univ g (e := fun _ => c) continuous_const
      ⟨x, mem_univ x⟩)

/-- If `x ≤ max (-n, y + 2^{-n})` for every `n`, then `x ≤ y` in `EReal`. -/
theorem ereal_le_of_forall_le_max_neg_add {x y : EReal}
    (h : ∀ n : ℕ, x ≤ max ((-(n : ℝ) : ℝ) : EReal) (y + ((1 / 2 ^ n : ℝ) : EReal))) : x ≤ y := by
  induction y using EReal.rec with
  | bot =>
    refine le_of_eq ((EReal.eq_bot_iff_forall_lt _).2 fun z => ?_)
    obtain ⟨n, hn⟩ := exists_nat_gt (-z)
    have h' := h n
    rw [EReal.bot_add, max_eq_left bot_le] at h'
    exact h'.trans_lt (EReal.coe_lt_coe_iff.2 (by linarith))
  | top => exact le_top
  | coe y =>
    refine ProjBerk.ereal_le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨n₁, hn₁⟩ := exists_nat_gt (-y)
    obtain ⟨n₂, hn₂⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    have hpow : (1 / 2 : ℝ) ^ max n₁ n₂ ≤ (1 / 2) ^ n₂ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right _ _)
    have h3 : (1 : ℝ) / 2 ^ max n₁ n₂ < ε := by
      rw [← one_div_pow]
      exact hpow.trans_lt hn₂
    have hn₁' : (n₁ : ℝ) ≤ (max n₁ n₂ : ℕ) := by exact_mod_cast le_max_left _ _
    refine (h (max n₁ n₂)).trans (max_le ?_ ?_)
    · rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.2 (by linarith)
    · rw [← EReal.coe_add, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.2 (by linarith)

/-! ### The dyadic grid of `prop:nn-homogeneous-slices` -/

namespace SliceGrid

/-- The index set of level `n`: `none` (for the term `Ψ - n`) and `some j` for the grid points
`j 2^{-n}`, `-n 2^n ≤ j < 0`, of `[-n, 0)`. -/
def index (n : ℕ) : Finset (Option ℤ) :=
  insert none ((Finset.Ico (-((n : ℤ) * 2 ^ n)) 0).image some)

/-- The functions of level `n`: `Ψ` for `none` and `ψ_{j 2^{-n}}` for `some j`. -/
def term {V : Type*} (Ψ : V → EReal) (ψ : ℝ → V → EReal) (n : ℕ) (k : Option ℤ) : V → EReal :=
  k.elim Ψ fun j => ψ ((j : ℝ) / 2 ^ n)

/-- The constants of level `n`: `-n` for `none` and `(j + 1) 2^{-n}` for `some j`. -/
def const (n : ℕ) (k : Option ℤ) : ℝ :=
  k.elim (-(n : ℝ)) fun j => ((j : ℝ) + 1) / 2 ^ n

theorem mem_index {n : ℕ} {k : Option ℤ} :
    k ∈ index n ↔ k = none ∨ ∃ j : ℤ, -((n : ℤ) * 2 ^ n) ≤ j ∧ j < 0 ∧ k = some j := by
  constructor
  · intro hk
    rcases Finset.mem_insert.1 hk with h | h
    · exact Or.inl h
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
      exact Or.inr ⟨j, hj1, hj2, rfl⟩
  · rintro (rfl | ⟨j, hj1, hj2, rfl⟩)
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_Ico.2 ⟨hj1, hj2⟩))

theorem none_mem_index (n : ℕ) : none ∈ index n :=
  mem_index.2 (Or.inl rfl)

theorem some_mem_index {n : ℕ} {j : ℤ} (h1 : -((n : ℤ) * 2 ^ n) ≤ j) (h2 : j < 0) :
    some j ∈ index n :=
  mem_index.2 (Or.inr ⟨j, h1, h2, rfl⟩)

theorem const_nonpos {n : ℕ} {k : Option ℤ} (hk : k ∈ index n) : const n k ≤ 0 := by
  rcases mem_index.1 hk with rfl | ⟨j, -, hj, rfl⟩
  · exact neg_nonpos.2 (Nat.cast_nonneg n)
  · have : (j : ℝ) + 1 ≤ 0 := by
      have : j + 1 ≤ 0 := hj
      exact_mod_cast this
    exact div_nonpos_of_nonpos_of_nonneg this (by positivity)

variable {V : Type*} {Ψ : V → EReal} {ψ : ℝ → V → EReal}

/-- The grid points of `term` are negative. -/
theorem term_some_neg {n : ℕ} {j : ℤ} (hj : j < 0) : (j : ℝ) / 2 ^ n < 0 :=
  div_neg_of_neg_of_pos (by exact_mod_cast hj) (by positivity)

/-- **Termwise domination** for the nested dyadic grids (proof of `prop:nn-homogeneous-slices`):
if `λ ↦ ψ_λ` is decreasing and `ψ_λ ≤ Ψ` for `λ < 0`, then every term of level `n' ≥ n` is
dominated by a term of level `n`, functions and constants alike. -/
theorem dominated (hanti : ∀ lam lam' : ℝ, lam ≤ lam' → ψ lam' ≤ ψ lam)
    (hΨ : ∀ lam : ℝ, lam < 0 → ψ lam ≤ Ψ) (n n' : ℕ) (hnn' : n ≤ n') (k' : Option ℤ)
    (hk' : k' ∈ index n') : ∃ k ∈ index n,
      (∀ v, term Ψ ψ n' k' v ≤ term Ψ ψ n k v) ∧ const n' k' ≤ const n k := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hnn'
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have h2p : (0 : ℝ) < 2 ^ p := by positivity
  rcases mem_index.1 hk' with rfl | ⟨j', hj'1, hj'2, rfl⟩
  · refine ⟨none, none_mem_index n, fun v => le_rfl, ?_⟩
    show -((n + p : ℕ) : ℝ) ≤ -(n : ℝ)
    exact neg_le_neg (by exact_mod_cast Nat.le_add_right n p)
  · by_cases hcase : j' < -((n : ℤ) * 2 ^ (n + p))
    · -- dominated by `Ψ - n`
      refine ⟨none, none_mem_index n, fun v => hΨ _ (term_some_neg hj'2) v, ?_⟩
      show ((j' : ℝ) + 1) / 2 ^ (n + p) ≤ -(n : ℝ)
      rw [div_le_iff₀ (by positivity)]
      have h1 : j' + 1 ≤ -((n : ℤ) * 2 ^ (n + p)) := hcase
      have h2 : (j' : ℝ) + 1 ≤ -((n : ℝ) * 2 ^ (n + p)) := by exact_mod_cast h1
      linarith
    · -- dominated by the grid point `j 2^{-n} ≤ j' 2^{-n-p}` below it
      replace hcase := not_lt.1 hcase
      have hfl := Int.floor_le ((j' : ℝ) / 2 ^ p)
      have hfl' := Int.lt_floor_add_one ((j' : ℝ) / 2 ^ p)
      set j : ℤ := ⌊(j' : ℝ) / 2 ^ p⌋ with hj
      have hj1 : -((n : ℤ) * 2 ^ n) ≤ j := by
        rw [hj, Int.le_floor, le_div_iff₀ h2p]
        have : ((-((n : ℤ) * 2 ^ (n + p)) : ℤ) : ℝ) ≤ j' := by exact_mod_cast hcase
        push_cast at this ⊢
        rw [pow_add] at this
        linarith
      have hj2 : j < 0 := by
        rw [hj, Int.floor_lt]
        push_cast
        exact div_neg_of_neg_of_pos (by exact_mod_cast hj'2) h2p
      refine ⟨some j, some_mem_index hj1 hj2, fun v => ?_, ?_⟩
      · show ψ ((j' : ℝ) / 2 ^ (n + p)) v ≤ ψ ((j : ℝ) / 2 ^ n) v
        refine hanti _ _ ?_ v
        rw [pow_add, div_le_div_iff₀ h2n (by positivity)]
        rw [le_div_iff₀ h2p] at hfl
        nlinarith
      · show ((j' : ℝ) + 1) / 2 ^ (n + p) ≤ ((j : ℝ) + 1) / 2 ^ n
        rw [div_lt_iff₀ h2p] at hfl'
        have h2 : j' < (j + 1) * 2 ^ p := by exact_mod_cast hfl'
        have h3 : j' + 1 ≤ (j + 1) * 2 ^ p := h2
        have h4 : (j' : ℝ) + 1 ≤ ((j : ℝ) + 1) * 2 ^ p := by exact_mod_cast h3
        rw [pow_add, div_le_div_iff₀ (by positivity) h2n]
        nlinarith

/-- **Lower bound**: `ψ_λ + λ ≤ max_k (term_k + const_k)` at every level `n`, for `λ < 0`. -/
theorem le_sup (hanti : ∀ lam lam' : ℝ, lam ≤ lam' → ψ lam' ≤ ψ lam)
    (hΨ : ∀ lam : ℝ, lam < 0 → ψ lam ≤ Ψ) {lam : ℝ} (hlam : lam < 0) (n : ℕ) (v : V) :
    ψ lam v + (lam : EReal) ≤ (index n).sup fun k => term Ψ ψ n k v + (const n k : EReal) := by
  by_cases hcase : lam < -(n : ℝ)
  · refine le_trans ?_ (Finset.le_sup (f := fun k => term Ψ ψ n k v + (const n k : EReal))
      (none_mem_index n))
    show ψ lam v + (lam : EReal) ≤ Ψ v + ((-(n : ℝ) : ℝ) : EReal)
    exact add_le_add (hΨ lam hlam v) (EReal.coe_le_coe_iff.2 hcase.le)
  · replace hcase := not_lt.1 hcase
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have hfl := Int.floor_le (lam * 2 ^ n)
    have hfl' := Int.lt_floor_add_one (lam * 2 ^ n)
    set j : ℤ := ⌊lam * 2 ^ n⌋ with hj
    have hj1 : -((n : ℤ) * 2 ^ n) ≤ j := by
      rw [hj, Int.le_floor]
      push_cast
      nlinarith
    have hj2 : j < 0 := by
      rw [hj, Int.floor_lt]
      push_cast
      exact mul_neg_of_neg_of_pos hlam h2n
    refine le_trans ?_ (Finset.le_sup (f := fun k => term Ψ ψ n k v + (const n k : EReal))
      (some_mem_index hj1 hj2))
    show ψ lam v + (lam : EReal) ≤ ψ ((j : ℝ) / 2 ^ n) v + ((((j : ℝ) + 1) / 2 ^ n : ℝ) : EReal)
    refine add_le_add (hanti _ _ ?_ v) (EReal.coe_le_coe_iff.2 ?_)
    · rw [div_le_iff₀ h2n]
      exact hfl
    · rw [le_div_iff₀ h2n]
      exact hfl'.le

/-- **Upper bound**: if `Ψ ≤ 0` and `ψ_λ + λ ≤ F` for `λ < 0`, then
`max_k (term_k + const_k) ≤ max (-n, F + 2^{-n})` at level `n`. -/
theorem sup_le_max (hΨ0 : ∀ v, Ψ v ≤ 0) {F : V → EReal}
    (hF : ∀ lam : ℝ, lam < 0 → ∀ v, ψ lam v + (lam : EReal) ≤ F v) (n : ℕ) (v : V) :
    ((index n).sup fun k => term Ψ ψ n k v + (const n k : EReal)) ≤
      max ((-(n : ℝ) : ℝ) : EReal) (F v + ((1 / 2 ^ n : ℝ) : EReal)) := by
  refine Finset.sup_le fun k hk => ?_
  rcases mem_index.1 hk with rfl | ⟨j, -, hj, rfl⟩
  · refine le_max_of_le_left ?_
    show Ψ v + ((-(n : ℝ) : ℝ) : EReal) ≤ ((-(n : ℝ) : ℝ) : EReal)
    calc Ψ v + ((-(n : ℝ) : ℝ) : EReal) ≤ 0 + ((-(n : ℝ) : ℝ) : EReal) :=
          add_le_add (hΨ0 v) le_rfl
      _ = ((-(n : ℝ) : ℝ) : EReal) := zero_add _
  · refine le_max_of_le_right ?_
    show ψ ((j : ℝ) / 2 ^ n) v + ((((j : ℝ) + 1) / 2 ^ n : ℝ) : EReal) ≤
      F v + ((1 / 2 ^ n : ℝ) : EReal)
    have hsplit : ((j : ℝ) + 1) / 2 ^ n = (j : ℝ) / 2 ^ n + 1 / 2 ^ n := by ring
    rw [hsplit, EReal.coe_add, ← add_assoc]
    exact add_le_add (hF _ (term_some_neg hj) v) le_rfl

end SliceGrid

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r}

/-- **The envelope property from increasing nets.** If `(sup_i φ_i)^⋆ ∈ PSH(𝒳, θ)` for every
increasing net `(φ_i)` in `PSH(𝒳, θ)` bounded above (indexed by a nonempty directed preorder in the
universe of `𝒳^an`), then `EP_𝒳(θ)`: a family `S` is replaced by the net of its finite maxima,
indexed by the nonempty finite subsets of `S` (`thm:gl-fs-system-theory`(1)). -/
theorem hasEnvelopeProperty_of_monotone {θ : Fin r → ℝ}
    (h : ∀ (ι : Type u) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      (φ : ι → X.an → EReal), (∀ i, X.IsPSH θ (φ i)) → Monotone φ →
        (∃ C : ℝ, ∀ i v, φ i v ≤ C) → X.IsPSH θ (uscReg fun v => ⨆ i, φ i v)) :
    X.HasEnvelopeProperty θ := by
  classical
  intro S hSne hS hbdd
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨u₀, hu₀⟩ := hSne
  let ι := {F : Finset (X.an → EReal) // F.Nonempty ∧ ∀ u ∈ F, u ∈ S}
  have : IsDirected ι (· ≤ ·) := ⟨fun F G => ⟨⟨F.1 ∪ G.1, F.2.1.mono Finset.subset_union_left,
    fun u hu => (Finset.mem_union.1 hu).elim (F.2.2 u) (G.2.2 u)⟩,
    Finset.subset_union_left, Finset.subset_union_right⟩⟩
  have hsing : ∀ u ∈ S, ({u} : Finset (X.an → EReal)).Nonempty ∧
      ∀ w ∈ ({u} : Finset (X.an → EReal)), w ∈ S := fun u hu =>
    ⟨Finset.singleton_nonempty u, fun w hw => (Finset.mem_singleton.1 hw) ▸ hu⟩
  have : Nonempty ι := ⟨⟨{u₀}, hsing u₀ hu₀⟩⟩
  let φ : ι → X.an → EReal := fun F v => F.1.sup' F.2.1 fun u => u v
  have hφ : ∀ F, X.IsPSH θ (φ F) := fun F =>
    FSSystemC.isPSH_finset_sup' (F := X.fsSystem) F.2.1 fun u hu => hS u (F.2.2 u hu)
  have hmono : Monotone φ := fun F G hFG v => Finset.sup'_mono _ hFG F.2.1
  have hbdd' : ∃ C : ℝ, ∀ F v, φ F v ≤ C :=
    ⟨C, fun F v => Finset.sup'_le _ _ fun u hu => hC u (F.2.2 u hu) v⟩
  have heq : (fun v => ⨆ u ∈ S, u v) = fun v => ⨆ F, φ F v := by
    funext v
    refine le_antisymm (iSup₂_le fun u hu => ?_) (iSup_le fun F => Finset.sup'_le _ _ fun u hu =>
      le_iSup₂ (f := fun (u : X.an → EReal) (_ : u ∈ S) => u v) u (F.2.2 u hu))
    refine le_iSup_of_le (⟨{u}, hsing u hu⟩ : ι) ?_
    simp only [φ, Finset.sup'_singleton, le_refl]
  rw [heq]
  exact h ι φ hφ hmono hbdd'

/-- The regularized slice `ψ_λ = (sup_{φ_i(⋆) > λ} (φ̂_i)_λ)^⋆` of an increasing net `(φ_i)` in
`PSH(𝒳, θ)` lies in `PSH_hom(𝒳, θ)` when the indices with `φ_i(⋆) > λ` exist, provided increasing
nets in `PSH_hom(𝒳, θ)` have `θ`-psh regularized suprema (`thm:gl-homog-decomposition`: the slices
`(φ̂_i)_λ` lie in `PSH_hom(𝒳, θ)` and increase with `i`). -/
theorem isPSHHom_uscReg_iSup_legendreSlice {θ : Fin r → ℝ}
    (H : ∀ (ι : Type u) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      (ψ : ι → X.an → EReal), (∀ i, X.IsPSHHom θ (ψ i)) → Monotone ψ →
        X.IsPSHHom θ (uscReg fun v => ⨆ i, ψ i v))
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] {φ : ι → X.an → EReal}
    (hφ : ∀ i, X.IsPSH θ (φ i)) (hmono : Monotone φ) (lam : ℝ) (i₀ : ι)
    (hi₀ : (lam : EReal) < φ i₀ X.triv) :
    X.IsPSHHom θ (uscReg fun v =>
      ⨆ i : {i : ι // (lam : EReal) < φ i X.triv}, X.legendreSlice (φ i.1) lam v) := by
  have : Nonempty {i : ι // (lam : EReal) < φ i X.triv} := ⟨⟨i₀, hi₀⟩⟩
  have : IsDirected {i : ι // (lam : EReal) < φ i X.triv} (· ≤ ·) := ⟨fun i j => by
    obtain ⟨l, hil, hjl⟩ := directed_of (· ≤ ·) i.1 j.1
    exact ⟨⟨l, i.2.trans_le (hmono hil X.triv)⟩, hil, hjl⟩⟩
  have h1 : ∀ i : {i : ι // (lam : EReal) < φ i X.triv},
      X.IsPSHHom θ (X.legendreSlice (φ i.1) lam) :=
    fun i => (hφ i.1).isPSHHom_legendreSlice i.2.le
  have h2 : Monotone fun i : {i : ι // (lam : EReal) < φ i X.triv} =>
      X.legendreSlice (φ i.1) lam :=
    fun i j hij => legendreSlice_mono (hmono hij) lam
  exact H {i : ι // (lam : EReal) < φ i X.triv} _ h1 h2


/-- The regularized slices `ψ_λ = (sup_{φ_i(⋆) > λ} (φ̂_i)_λ)^⋆` decrease in `λ`. -/
theorem uscReg_iSup_legendreSlice_antitone {ι : Type*} (φ : ι → X.an → EReal) {lam lam' : ℝ}
    (h : lam ≤ lam') :
    (uscReg fun v => ⨆ i : {i : ι // (lam' : EReal) < φ i X.triv},
      X.legendreSlice (φ i.1) lam' v) ≤
    uscReg fun v => ⨆ i : {i : ι // (lam : EReal) < φ i X.triv},
      X.legendreSlice (φ i.1) lam v := by
  refine uscReg_mono fun v => iSup_le fun i => ?_
  exact (legendreSlice_antitone (φ i.1) h v).trans
    (le_iSup (fun j : {i : ι // (lam : EReal) < φ i X.triv} => X.legendreSlice (φ j.1) lam v)
      ⟨i.1, lt_of_le_of_lt (EReal.coe_le_coe_iff.2 h) i.2⟩)

/-- `ψ_λ + λ ≤ (sup_i φ_i)^⋆` for the regularized slices `ψ_λ` (`legendreSlice_add_le`). -/
theorem uscReg_iSup_legendreSlice_add_le {ι : Type*} (φ : ι → X.an → EReal) (lam : ℝ)
    (v : X.an) :
    (uscReg fun v => ⨆ i : {i : ι // (lam : EReal) < φ i X.triv},
      X.legendreSlice (φ i.1) lam v) v + (lam : EReal) ≤ uscReg (fun v => ⨆ i, φ i v) v := by
  have h1 : (fun w => (⨆ i : {i : ι // (lam : EReal) < φ i X.triv},
      X.legendreSlice (φ i.1) lam w) + (lam : EReal)) ≤ fun w => ⨆ i, φ i w := fun w => by
    show (⨆ i : {i : ι // (lam : EReal) < φ i X.triv}, X.legendreSlice (φ i.1) lam w) +
      (lam : EReal) ≤ ⨆ i, φ i w
    rw [ereal_iSup_add_coe]
    exact iSup_le fun i =>
      (legendreSlice_add_le (φ i.1) lam w).trans (le_iSup (fun i => φ i w) i.1)
  have h2 := uscReg_mono h1 v
  rwa [uscReg_add_coe] at h2

/-- **Reconstruction from the regularized slices** (`thm:gl-homog-decomposition`): if `φ_i ≤ 0`
at `⋆` and `ψ_λ + λ ≤ U` for every `λ < 0`, then `φ_i ≤ U`, since
`φ_i = sup_{λ < φ_i(⋆)} ((φ̂_i)_λ + λ)` and `(φ̂_i)_λ ≤ ψ_λ` for `λ < φ_i(⋆)`. -/
theorem le_of_forall_uscReg_iSup_legendreSlice_add_le {θ : Fin r → ℝ} {ι : Type*}
    {φ : ι → X.an → EReal} (hφ : ∀ i, X.IsPSH θ (φ i)) (hb0 : ∀ i, φ i X.triv ≤ 0) (i : ι)
    (v : X.an) {U : EReal}
    (hU : ∀ lam : ℝ, lam < 0 → (uscReg fun v => ⨆ i : {i : ι // (lam : EReal) < φ i X.triv},
      X.legendreSlice (φ i.1) lam v) v + (lam : EReal) ≤ U) : φ i v ≤ U := by
  rw [(hφ i).eq_iSup_legendreSlice v]
  refine iSup₂_le fun lam hlam => ?_
  have hlam0 : lam < 0 := by
    have := hlam.trans_le (hb0 i)
    exact_mod_cast this
  refine le_trans (add_le_add ?_ le_rfl) (hU lam hlam0)
  exact (le_iSup (fun j : {i : ι // (lam : EReal) < φ i X.triv} =>
    X.legendreSlice (φ j.1) lam v) ⟨i, hlam⟩).trans (le_uscReg (fun v =>
      ⨆ i : {i : ι // (lam : EReal) < φ i X.triv}, X.legendreSlice (φ i.1) lam v) v)

variable [IsAlgClosed k]

/-- **Envelopes from homogeneous slices, normalized form** (the proof of
`prop:nn-homogeneous-slices`). Assume `(sup_i ψ_i)^⋆ ∈ PSH_hom(𝒳, θ)` for every nonempty
increasing net `(ψ_i)` in `PSH_hom(𝒳, θ)`. If `(φ_i)` is an increasing net in `PSH(𝒳, θ)` with
`sup_i φ_i(⋆) = 0`, then `(sup_i φ_i)^⋆ ∈ PSH(𝒳, θ)`. With the slices
`ψ_λ = (sup_{φ_i(⋆) > λ} (φ̂_i)_λ)^⋆`, `Ψ = (sup_n ψ_{-n-1})^⋆` and the dyadic grid `j 2^{-n}`,
`-n 2^n ≤ j < 0` (`EnvelopeProperty.SliceGrid`), the functions
`U_n = max {Ψ - n, max_j (ψ_{j 2^{-n}} + (j + 1) 2^{-n})}` satisfy termwise domination, and
`U = inf_n U_n = (sup_i φ_i)^⋆` is `θ`-psh by `thm:nn-hom-max-diagonal`. -/
theorem isPSH_uscReg_iSup_of_homogeneous_slices {θ : Fin r → ℝ}
    (H : ∀ (ι : Type u) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      (ψ : ι → X.an → EReal), (∀ i, X.IsPSHHom θ (ψ i)) → Monotone ψ →
        X.IsPSHHom θ (uscReg fun v => ⨆ i, ψ i v))
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] {φ : ι → X.an → EReal}
    (hφ : ∀ i, X.IsPSH θ (φ i)) (hmono : Monotone φ) (hsup : ⨆ i, φ i X.triv = 0) :
    X.IsPSH θ (uscReg fun v => ⨆ i, φ i v) := by
  classical
  have hb0 : ∀ i, φ i X.triv ≤ 0 := fun i => hsup ▸ le_iSup (fun i => φ i X.triv) i
  -- the regularized slices `ψ_λ`
  let ψ : ℝ → X.an → EReal := fun lam => uscReg fun v =>
    ⨆ i : {i : ι // (lam : EReal) < φ i X.triv}, X.legendreSlice (φ i.1) lam v
  have hψP : ∀ lam : ℝ, lam < 0 → X.IsPSHHom θ (ψ lam) := by
    intro lam hlam
    have hlt : (lam : EReal) < ⨆ i, φ i X.triv := by
      rw [hsup]
      exact_mod_cast hlam
    obtain ⟨i₀, hi₀⟩ := lt_iSup_iff.1 hlt
    exact isPSHHom_uscReg_iSup_legendreSlice H hφ hmono lam i₀ hi₀
  have hψanti : ∀ lam lam' : ℝ, lam ≤ lam' → ψ lam' ≤ ψ lam := fun lam lam' h =>
    uscReg_iSup_legendreSlice_antitone φ h
  -- `Ψ = (sup_n ψ_{-n-1})^⋆ ≥ ψ_λ` for `λ < 0`
  let Ψ : X.an → EReal := uscReg fun v => ⨆ n : ULift.{u} ℕ, ψ (-((n.down : ℝ) + 1)) v
  have hΨP : X.IsPSHHom θ Ψ := H (ULift.{u} ℕ) (fun n => ψ (-((n.down : ℝ) + 1)))
    (fun n => hψP _ (by have := n.down.cast_nonneg (α := ℝ); linarith))
    (fun n n' h => hψanti _ _ (by
      have h' : n.down ≤ n'.down := h
      have : (n.down : ℝ) ≤ n'.down := by exact_mod_cast h'
      linarith))
  have hψΨ : ∀ lam : ℝ, lam < 0 → ψ lam ≤ Ψ := by
    intro lam hlam v
    obtain ⟨n, hn⟩ := exists_nat_ge (-lam)
    exact (hψanti _ _ (by linarith) v).trans
      ((le_iSup (fun n : ULift.{u} ℕ => ψ (-((n.down : ℝ) + 1)) v) (ULift.up n)).trans
        (le_uscReg (fun v => ⨆ n : ULift.{u} ℕ, ψ (-((n.down : ℝ) + 1)) v) v))
  -- `U = inf_n U_n` is `θ`-psh (`thm:nn-hom-max-diagonal`)
  let U : X.an → EReal := fun v => ⨅ n, (SliceGrid.index n).sup fun k =>
    SliceGrid.term Ψ ψ n k v + (SliceGrid.const n k : EReal)
  have hlow : ∀ n v, (⨆ i, φ i v) ≤ (SliceGrid.index n).sup fun k =>
      SliceGrid.term Ψ ψ n k v + (SliceGrid.const n k : EReal) := fun n v =>
    iSup_le fun i => le_of_forall_uscReg_iSup_legendreSlice_add_le hφ hb0 i v fun lam hlam =>
      SliceGrid.le_sup hψanti hψΨ hlam n v
  have hUpsh : X.IsPSH θ U := by
    refine isPSH_of_dominated_homMax_seq (θs := fun _ => θ) tendsto_const_nhds SliceGrid.index
      (SliceGrid.term Ψ ψ) SliceGrid.const (fun n k hk => ?_)
      (fun n k hk => SliceGrid.const_nonpos hk) (SliceGrid.dominated hψanti hψΨ)
      (fun v => rfl) ⟨X.triv, ?_⟩
    · rcases SliceGrid.mem_index.1 hk with rfl | ⟨j, -, hj, rfl⟩
      · exact hΨP
      · exact hψP _ (SliceGrid.term_some_neg hj)
    · have h : (⨆ i, φ i X.triv) ≤ U X.triv := le_iInf fun n => hlow n X.triv
      rw [hsup] at h
      exact ne_bot_of_le_ne_bot EReal.zero_ne_bot h
  -- `U = (sup_i φ_i)^⋆`
  have hUf : ∀ v, U v ≤ uscReg (fun v => ⨆ i, φ i v) v := fun v =>
    ereal_le_of_forall_le_max_neg_add fun n => (iInf_le _ n).trans
      (SliceGrid.sup_le_max (fun v => hΨP.nonpos v)
        (fun lam _ v => uscReg_iSup_legendreSlice_add_le φ lam v) n v)
  have hfU : uscReg (fun v => ⨆ i, φ i v) = U := le_antisymm
    (uscReg_le_of_le (FSSystemC.IsPSH.upperSemicontinuous hUpsh) fun v =>
      le_iInf fun n => hlow n v) fun v => hUf v
  rw [hfU]
  exact hUpsh

/-- **Envelopes from homogeneous slices for every class** (**`prop:nn-homogeneous-slices`**; FHX
Proposition 7.5, `prop:homogeneous-slices`, in usc form, for
all classes). Let `θ ∈ ℝ^r`. If
`(sup_i ψ_i)^⋆ ∈ PSH_hom(𝒳, θ)` for every nonempty increasing net `(ψ_i)` in `PSH_hom(𝒳, θ)`, then
`EP_𝒳(θ)`. A bounded family is replaced by the increasing net of its finite maxima
(`hasEnvelopeProperty_of_monotone`) and normalized by a constant to `sup_i φ_i(⋆) = 0`
(`isPSH_uscReg_iSup_of_homogeneous_slices`). -/
theorem hasEnvelopeProperty_of_isPSHHom_uscReg_iSup {θ : Fin r → ℝ}
    (H : ∀ (ι : Type u) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      (ψ : ι → X.an → EReal), (∀ i, X.IsPSHHom θ (ψ i)) → Monotone ψ →
        X.IsPSHHom θ (uscReg fun v => ⨆ i, ψ i v)) :
    X.HasEnvelopeProperty θ := by
  refine hasEnvelopeProperty_of_monotone fun ι _ _ _ φ hφ hmono hbdd => ?_
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  -- `B = sup_i φ_i(⋆)` is finite
  set B : EReal := ⨆ i, φ i X.triv with hB
  have hBbot : B ≠ ⊥ := ne_bot_of_le_ne_bot (hφ i₀).apply_triv_ne_bot
    (le_iSup (fun i => φ i X.triv) i₀)
  have hBtop : B ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top C) (iSup_le fun i => hC i X.triv)
  set β : ℝ := B.toReal with hβdef
  have hβ : (β : EReal) = B := EReal.coe_toReal hBtop hBbot
  -- normalize to `sup_i φ_i(⋆) = 0`
  have hφ' : ∀ i, X.IsPSH θ fun v => φ i v + ((-β : ℝ) : EReal) := fun i => (hφ i).add_const (-β)
  have hmono' : Monotone fun i v => φ i v + ((-β : ℝ) : EReal) := fun i j h v =>
    add_le_add (hmono h v) le_rfl
  have hsup' : ⨆ i, (φ i X.triv + ((-β : ℝ) : EReal)) = 0 := by
    rw [← ereal_iSup_add_coe, ← hB, ← hβ, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  have h := isPSH_uscReg_iSup_of_homogeneous_slices H hφ' hmono' hsup'
  have heq : (uscReg fun v => ⨆ i, φ i v) =
      fun v => (uscReg fun v => ⨆ i, (φ i v + ((-β : ℝ) : EReal))) v + (β : EReal) := by
    rw [← uscReg_add_coe]
    congr 1
    funext v
    rw [← ereal_iSup_add_coe, ProjBerk.ereal_add_neg_add_coe]
  rw [heq]
  exact h.add_const β

/-- **Increasing limits of homogeneous psh functions on normal models** (the step of
`cor:nn-normal-ep`; FHX Corollary 7.6, `cor:normal-EP`). Let
`𝒳` be normal over an algebraically
closed field with the envelope property at every positive class (`hample`). For every `θ ∈ ℝ^r`
and every nonempty family `(ψ_i)` in `PSH_hom(𝒳, θ)`, `(sup_i ψ_i)^⋆ ∈ PSH_hom(𝒳, θ)`. With a
monomial `s_E` of degree `N 𝟙` (`θ + N 𝟙` positive) and `e_E = log |s_E|`,
`χ = (sup_i (ψ_i + e_E))^⋆ ∈ PSH_hom(𝒳, θ + N 𝟙)` by the envelope property, `χ ≤ e_E`, and Siu
division (`thm:nn-homogeneous-siu`) gives `χ = e_E + Ψ₀`, `Ψ₀ ∈ PSH_hom(𝒳, θ)`; by the comparison
theorem `Ψ₀ = (sup_i ψ_i)^⋆`. -/
theorem isPSHHom_uscReg_iSup_of_isNormal (hX : X.IsNormal)
    (hample : ∀ η : Fin r → ℝ, (∀ c, 0 < η c) → X.HasEnvelopeProperty η)
    {θ : Fin r → ℝ} {ι : Sort*} [Nonempty ι] {ψ : ι → X.an → EReal}
    (hψ : ∀ i, X.IsPSHHom θ (ψ i)) : X.IsPSHHom θ (uscReg fun v => ⨆ i, ψ i v) := by
  classical
  -- `N` with `θ + N 𝟙` positive and a monomial `s_E` of degree `N 𝟙`
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ c, |θ c|)
  have hNθ : ∀ c, 0 < θ c + ((N : ℚ) : ℝ) := fun c => by
    have h1 : |θ c| ≤ ∑ c, |θ c| :=
      Finset.single_le_sum (f := fun c => |θ c|) (fun c _ => abs_nonneg _) (Finset.mem_univ c)
    have h2 := neg_abs_le (θ c)
    push_cast
    linarith
  obtain ⟨s, hs, hs1⟩ := X.exists_finset_sections_logSecAbs_eq_zero N
  obtain ⟨sE, hsEs, -⟩ := hs1 X.triv
  obtain ⟨hsE, hsE0⟩ := hs sE hsEs
  set dN : Fin r → ℤ := fun _ => (N : ℤ) with hdN
  set eE : X.an → EReal := fun v => X.logSecAbs v.1 dN sE with heE
  have heEP : X.IsPSHHom (fun c => ((dN c : ℚ) : ℝ)) eE :=
    ⟨isPSH_logSecAbs hsE hsE0, fun t ht v => logSecAbs_rpow t ht v dN sE⟩
  have heEcont : Continuous eE := (X.continuous_logSecAbs dN sE).comp continuous_subtype_val
  have heE0 : ∀ v, eE v ≤ 0 := fun v => logSecAbs_le_zero v.2.2 dN sE
  have heEtop : ∀ v, eE v ≠ ⊤ := fun v => logSecAbs_ne_top _ _ _
  have hfin : ∀ v, X.IsDivisorial v → ∃ E : ℝ, eE v = E := fun v hv =>
    ⟨(eE v).toReal, (EReal.coe_toReal (heEtop v) (hv.logSecAbs_ne_bot hsE hsE0)).symm⟩
  -- `χ = (sup_i (ψ_i + e_E))^⋆ ∈ PSH_hom(𝒳, θ + N 𝟙)`
  set η : Fin r → ℝ := fun c => θ c + ((N : ℚ) : ℝ) with hη
  have hψE : ∀ i, X.IsPSHHom η fun v => ψ i v + eE v := fun i => by
    have h := (hψ i).add heEP
    have hcl : (θ + fun c => ((dN c : ℚ) : ℝ)) = η := by
      funext c
      simp [hη, hdN]
    rw [hcl] at h
    exact h
  set χ : X.an → EReal := uscReg fun v => ⨆ i, (ψ i v + eE v) with hχdef
  have hχ : X.IsPSHHom η χ :=
    ⟨FSSystemC.HasEnvelopeProperty.isPSH_uscReg_iSup (F := X.fsSystem) (hample η hNθ)
      (fun i => (hψE i).1) ⟨0, fun i v => by
        exact_mod_cast (add_le_add ((hψ i).nonpos v) (heE0 v)).trans_eq (add_zero 0)⟩,
      IsScaleHomogeneous.uscReg_iSup fun i => (hψE i).2⟩
  have hχle : ∀ v, χ v ≤ eE v := uscReg_le_of_le heEcont.upperSemicontinuous fun v =>
    iSup_le fun i => (add_le_add ((hψ i).nonpos v) le_rfl).trans_eq (zero_add _)
  -- Siu division: `χ = e_E + Ψ₀`
  obtain ⟨Ψ₀, hΨ₀, hχeq⟩ := IsPSHHom.exists_isPSHHom_eq_add_of_le_logSecAbs (e := fun _ => (N : ℚ))
    hX hample one_pos (fun c => by simp [hdN]) hsE hsE0 hχ
    (fun v => by rw [Nat.cast_one, inv_one, EReal.coe_one, one_mul]; exact hχle v)
  have hχeq' : ∀ v, χ v = eE v + Ψ₀ v := fun v => by
    rw [hχeq v, Nat.cast_one, inv_one, EReal.coe_one, one_mul]
  -- `G = (sup_i ψ_i)^⋆ = Ψ₀`
  set G : X.an → EReal := uscReg fun v => ⨆ i, ψ i v with hG
  have hG0 : ∀ v, G v ≤ 0 :=
    uscReg_le_of_le upperSemicontinuous_const fun v => iSup_le fun i => (hψ i).nonpos v
  have hGusc : UpperSemicontinuous G := upperSemicontinuous_uscReg _
  have hψG : ∀ i v, ψ i v ≤ G v := fun i v =>
    (le_iSup (fun i => ψ i v) i).trans (le_uscReg (fun v => ⨆ i, ψ i v) v)
  -- `χ ≤ G + e_E` everywhere (`G + e_E` is usc)
  have hχG : ∀ v, χ v ≤ G v + eE v := by
    refine uscReg_le_of_le ?_ fun v => iSup_le fun i => add_le_add (hψG i v) le_rfl
    exact fun v => UpperSemicontinuousAt.add' (hGusc v) heEcont.continuousAt.upperSemicontinuousAt
      (EReal.continuousAt_add (Or.inl (ne_top_of_le_ne_top EReal.zero_ne_top (hG0 v)))
        (Or.inr (heEtop v)))
  have hΨ₀G : Ψ₀ ≤ G := hΨ₀.1.le_of_forall_isDivisorial_le hGusc
    (fun v => ne_top_of_le_ne_top EReal.zero_ne_top (hG0 v)) fun v hv => by
      obtain ⟨E, hE⟩ := hfin v hv
      have h := hχG v
      rw [hχeq' v, hE, add_comm (G v)] at h
      exact ereal_le_of_coe_add_le_coe_add h
  have hGΨ₀ : G ≤ Ψ₀ := uscReg_le_of_le (FSSystemC.IsPSH.upperSemicontinuous hΨ₀.1) fun v =>
    iSup_le fun i => (hψ i).1.le_of_forall_isDivisorial_le
      (FSSystemC.IsPSH.upperSemicontinuous hΨ₀.1) (FSSystemC.IsPSH.ne_top hΨ₀.1)
      (fun w hw => by
        obtain ⟨E, hE⟩ := hfin w hw
        have h : ψ i w + eE w ≤ χ w :=
          (le_iSup (fun i => ψ i w + eE w) i).trans (le_uscReg (fun v => ⨆ i, (ψ i v + eE v)) w)
        rw [hχeq' w, hE, add_comm (ψ i w)] at h
        exact ereal_le_of_coe_add_le_coe_add h) v
  rw [show G = Ψ₀ from le_antisymm hGΨ₀ hΨ₀G]
  exact hΨ₀

/-- **The envelope property at every class on normal models** (**`cor:nn-normal-ep`**; FHX
Corollary 7.6, `cor:normal-EP`, for all classes). Let `𝒳`
be a normal model over an algebraically closed field with the envelope property at every positive
class (`hample`, the conclusion of `thm:gl-normal-ample-ep`). Then `EP_𝒳(θ)` holds for **every**
`θ ∈ ℝ^r`. -/
theorem hasEnvelopeProperty_of_isNormal_of_forall_pos (hX : X.IsNormal)
    (hample : ∀ η : Fin r → ℝ, (∀ c, 0 < η c) → X.HasEnvelopeProperty η) (θ : Fin r → ℝ) :
    X.HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_isPSHHom_uscReg_iSup fun _ _ _ _ _ hψ _ =>
    isPSHHom_uscReg_iSup_of_isNormal hX hample hψ

end MultiModel

end EnvelopeProperty
