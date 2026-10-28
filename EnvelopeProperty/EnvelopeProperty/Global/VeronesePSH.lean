/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.MorphismsPSH
import EnvelopeProperty.Global.Veronese

/-!
# Sections, Fubini–Study and psh functions on Segre–Veronese models

This file implements the parts of the blueprint node `lem:gl-veronese` of `global.tex`
(subsection `subsec:gl-model`) that concern sections, Fubini–Study functions, psh functions and
the envelope property, for the formalization of Fang–Han–Xia, *The envelope property for
unibranch projective varieties* (revision `832e086`, used in FHX `thm:normal-ample-EP`). The
point-level part (the homeomorphism `𝒳^an ≃ 𝒳_(a)^an`, `MultiModel.veroneseHomeomorph`) and
normality are in `EnvelopeProperty.Global.Veronese`.

Let `𝒳` be a model of rank `r ≥ 1`, `a ∈ ℕ^r` positive, `𝒳_(a)` the Segre–Veronese model
(`MultiModel.veronese`) and `e : 𝒳^an ≃ 𝒳_(a)^an` the restriction homeomorphism.

* Multi-indices: a multi-index `β` of `𝒳_(a)` (in the coordinates `z̃^{β_j} U`, `β_j ∈ Mon(a)`)
  gives the multi-index `∑_j β(j) β_j` of `𝒳` (`MultiModel.veroneseMon`), with
  `z̃^β(𝒳_(a)) = z̃^{veroneseMon β}(𝒳)` (`MultiModel.zCoeff_veronese`); it maps
  `Mon_{𝒳_(a)}(n)` onto `Mon_𝒳(n a)` (`MultiModel.exists_veroneseMon_eq`, from
  `Mon(A + B) = Mon(A) + Mon(B)`).
* Sections (`lem:gl-veronese`, `R_n(𝒳_(a)) = R_{n a}(𝒳)`): for `d ∈ ℤ^1`, the degree `n` is
  admissible on `𝒳_(a)` iff `n a` is admissible on `𝒳` in degree `d₀ a`
  (`MultiModel.isAdmissible_veronese_iff`), hence
  `MultiModel.mem_veronese_sections_iff : f ∈ R_d(𝒳_(a)) ↔ f ∈ R_{d₀ a}(𝒳)`, with the same values
  `|f|_{e(v)} = |f|_v` (`MultiModel.secAbs_veroneseAnMap`).
* Fubini–Study functions (`MultiModel.isFS_veronese_iff`, `MultiModel.isFinFS_veronese_iff`):
  `ψ ∈ 𝓗(𝒳_(a), q)` iff `ψ ∘ e ∈ 𝓗(𝒳, q₀ a)`, for `q ∈ ℚ^1` (and the same for `𝓗_fin`). Data of class `q₀ a` on `𝒳` with `m` and degree `m q₀ a`
  give data of class `q` on `𝒳_(a)` with `a₀ m` and the powers `f_t^{a₀}` (the degree
  `m q₀ ∈ a₀⁻¹ ℤ` need not be integral).
* Psh functions (`MultiModel.isPSH_veronese_iff`, `PSH(𝒳_(a), t) = PSH(𝒳, t a)` for every real
  `t`): an approximant of class `b_α → t a` on `𝒳` lies in `𝓗(𝒳, λ_α a)` with
  `λ_α = max_c b_{α,c} / a_c → t` (FS2).
* The envelope property (`MultiModel.hasEnvelopeProperty_veronese_iff`):
  `EP_{𝒳_(a)}(t) ↔ EP_𝒳(t a)`, by `FSSystemC.hasEnvelopeProperty_iff_of_isPSH_comp_iff`.
-/

open scoped NNReal ENNReal Topology

open Topology Filter MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}

/- `veroneseM = |Mon(a)| - 1` is a concrete `Finset` computation; unfolding it (e.g. while
checking membership in `Mon_{𝒳_(a)}(n)`) makes `whnf` run away. -/
attribute [local irreducible] veroneseM

/-! ### Degrees -/

/-- The degree `d₀ a ∈ ℤ^r` of `𝒳` corresponding to the degree `d ∈ ℤ^1` of `𝒳_(a)`. -/
def veroneseDeg (a : Fin r →₀ ℕ) (d : Fin 1 → ℤ) : Fin r → ℤ :=
  fun c => d 0 * a c

theorem veroneseDeg_apply (a : Fin r →₀ ℕ) (d : Fin 1 → ℤ) (c : Fin r) :
    veroneseDeg a d c = d 0 * a c :=
  rfl

theorem addDeg_veroneseDeg {a : Fin r →₀ ℕ} {d : Fin 1 → ℤ} {n : ℕ} (h : 0 ≤ d 0 + n) :
    addDeg (veroneseDeg a d) (n • a) = addDeg d (Finsupp.single 0 n) 0 • a := by
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h
  ext c
  simp only [addDeg_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_eq_same,
    veroneseDeg_apply]
  rw [show d 0 * (a c : ℤ) + ((n * a c : ℕ) : ℤ) = ((m * a c : ℕ) : ℤ) by
    push_cast
    linear_combination (a c : ℤ) * hm, hm, Int.toNat_natCast, Int.toNat_natCast]

theorem nonneg_of_veroneseDeg [NeZero r] {a : Fin r →₀ ℕ} (ha : ∀ c, 0 < a c) {d : Fin 1 → ℤ}
    {n : ℕ} (h : ∀ c, 0 ≤ veroneseDeg a d c + ((n • a) c : ℤ)) : 0 ≤ d 0 + n := by
  by_contra hneg
  push Not at hneg
  have h0 := h 0
  rw [veroneseDeg_apply, Finsupp.smul_apply, smul_eq_mul, Nat.cast_mul] at h0
  have : (d 0 + n) * (a 0 : ℤ) < 0 := mul_neg_of_neg_of_pos hneg (by exact_mod_cast ha 0)
  linarith

theorem veroneseDeg_nonneg {a : Fin r →₀ ℕ} {d : Fin 1 → ℤ} {n : ℕ} (h : 0 ≤ d 0 + n) (c : Fin r) :
    0 ≤ veroneseDeg a d c + ((n • a) c : ℤ) := by
  rw [veroneseDeg_apply, Finsupp.smul_apply, smul_eq_mul, Nat.cast_mul]
  calc (0 : ℤ) ≤ (d 0 + n) * a c := mul_nonneg h (Nat.cast_nonneg _)
    _ = _ := by ring

/-! ### Multi-indices of the Segre–Veronese model -/

section Segre

variable [NeZero r] (X : MultiModel k K r) {a : Fin r →₀ ℕ} (ha : ∀ c, 0 < a c)

/-- The multi-index `∑_j β(j) β_j` of `𝒳` underlying the monomial `z̃^β` of `𝒳_(a)` in the
Segre coordinates `z̃^{β_j} U`, `β_j ∈ Mon(a)`. -/
def veroneseMon (β : (X.veronese ha).CoordIndex →₀ ℕ) : X.CoordIndex →₀ ℕ :=
  β.sum fun i n => n • (X.monEnum a i.2).1

theorem veroneseMon_zero : X.veroneseMon ha 0 = 0 :=
  Finsupp.sum_zero_index

theorem veroneseMon_add (β γ : (X.veronese ha).CoordIndex →₀ ℕ) :
    X.veroneseMon ha (β + γ) = X.veroneseMon ha β + X.veroneseMon ha γ :=
  Finsupp.sum_add_index' (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

theorem veroneseMon_single (i : (X.veronese ha).CoordIndex) (n : ℕ) :
    X.veroneseMon ha (Finsupp.single i n) = n • (X.monEnum a i.2).1 :=
  Finsupp.sum_single_index (zero_smul _ _)

/-- `z̃^β(𝒳_(a)) = z̃^{∑_j β(j) β_j}(𝒳)`. -/
theorem zCoeff_veronese (β : (X.veronese ha).CoordIndex →₀ ℕ) :
    (X.veronese ha).zCoeff β = X.zCoeff (X.veroneseMon ha β) := by
  induction β using Finsupp.induction with
  | zero => rw [zCoeff_zero, veroneseMon_zero, zCoeff_zero]
  | single_add i n β _ _ ih =>
    rw [zCoeff_add, veroneseMon_add, zCoeff_add, ih, zCoeff_single, veroneseMon_single,
      zCoeff_nsmul]
    rfl

/-- The degree of `∑_j β(j) β_j` is `(∑_j β(j)) a`. -/
theorem monDeg_veroneseMon (β : (X.veronese ha).CoordIndex →₀ ℕ) :
    X.monDeg (X.veroneseMon ha β) = (X.veronese ha).monDeg β 0 • a := by
  induction β using Finsupp.induction with
  | zero => rw [veroneseMon_zero, monDeg_zero, monDeg_zero, Finsupp.coe_zero, Pi.zero_apply,
      zero_smul]
  | single_add i n β _ _ ih =>
    obtain ⟨c, j⟩ := i
    obtain rfl := Fin.fin_one_eq_zero c
    rw [veroneseMon_add, monDeg_add, ih, veroneseMon_single,
      (X.mem_monSet).1 (nsmul_mem_monSet (X.monEnum a j).2 n), monDeg_add, Finsupp.add_apply,
      monDeg_single, Finsupp.single_eq_same, add_smul]

theorem veroneseMon_mem_monSet {β : (X.veronese ha).CoordIndex →₀ ℕ} {n : ℕ}
    (hβ : β ∈ (X.veronese ha).monSet (Finsupp.single 0 n)) :
    X.veroneseMon ha β ∈ X.monSet (n • a) := by
  rw [X.mem_monSet, monDeg_veroneseMon, ((X.veronese ha).mem_monSet).1 hβ,
    Finsupp.single_eq_same]

/-- Every `γ ∈ Mon_𝒳(n a)` is `∑_j β(j) β_j` for some `β ∈ Mon_{𝒳_(a)}(n)`. -/
theorem exists_veroneseMon_eq {n : ℕ} {γ : X.CoordIndex →₀ ℕ} (hγ : γ ∈ X.monSet (n • a)) :
    ∃ β ∈ (X.veronese ha).monSet (Finsupp.single 0 n), X.veroneseMon ha β = γ := by
  induction n generalizing γ with
  | zero =>
    rw [zero_smul, X.monSet_zero, Finset.mem_singleton] at hγ
    refine ⟨0, ?_, by rw [veroneseMon_zero, hγ]⟩
    rw [Finsupp.single_zero, (X.veronese ha).monSet_zero]
    exact Finset.mem_singleton_self _
  | succ n ih =>
    rw [succ_nsmul] at hγ
    obtain ⟨γ₁, h₁, γ₂, h₂, rfl⟩ := X.exists_add_of_mem_monSet_add hγ
    obtain ⟨β₁, hβ₁, rfl⟩ := ih h₁
    refine ⟨β₁ + Finsupp.single (⟨0, (X.monEnum a).symm ⟨γ₂, h₂⟩⟩ :
      (X.veronese ha).CoordIndex) 1, ?_, ?_⟩
    · rw [(X.veronese ha).mem_monSet, monDeg_add, ((X.veronese ha).mem_monSet).1 hβ₁,
        monDeg_single, Finsupp.single_add]
    · rw [veroneseMon_add, veroneseMon_single, one_smul]
      change _ + ((X.monEnum a) ((X.monEnum a).symm ⟨γ₂, h₂⟩)).1 = _
      rw [Equiv.apply_symm_apply]

/-- `max_{β ∈ Mon_{𝒳_(a)}(n)} g(∑_j β(j) β_j) = max_{γ ∈ Mon_𝒳(n a)} g(γ)`. -/
theorem sup_veroneseMon (n : ℕ) (g : (X.CoordIndex →₀ ℕ) → ℝ≥0) :
    ((X.veronese ha).monSet (Finsupp.single 0 n)).sup (fun β => g (X.veroneseMon ha β)) =
      (X.monSet (n • a)).sup g := by
  classical
  change ((X.veronese ha).monSet (Finsupp.single 0 n)).sup (g ∘ X.veroneseMon ha) = _
  rw [← Finset.sup_image]
  congr 1
  ext γ
  rw [Finset.mem_image]
  exact ⟨fun ⟨β, hβ, h⟩ => h ▸ X.veroneseMon_mem_monSet ha hβ,
    fun h => X.exists_veroneseMon_eq ha h⟩

end Segre

/-! ### Sections (`lem:gl-veronese`: `R_n(𝒳_(a)) = R_{n a}(𝒳)`) -/

section Sections

variable [NeZero r] (X : MultiModel k K r) {a : Fin r →₀ ℕ} (ha : ∀ c, 0 < a c)

/-- The degree `n` is admissible for `f` on `𝒳_(a)` in degree `d ∈ ℤ^1` iff `n a` is admissible
for `f` on `𝒳` in degree `d₀ a`. -/
theorem isAdmissible_veronese_iff {d : Fin 1 → ℤ} {n : ℕ} {f : K} :
    (X.veronese ha).IsAdmissible d (Finsupp.single 0 n) f ↔
      X.IsAdmissible (veroneseDeg a d) (n • a) f := by
  constructor
  · rintro ⟨h1, h2⟩
    have h0 : 0 ≤ d 0 + n := by simpa using h1 0
    refine ⟨veroneseDeg_nonneg h0, fun γ hγ => ?_⟩
    obtain ⟨β, hβ, rfl⟩ := X.exists_veroneseMon_eq ha hγ
    have h := h2 β hβ
    rw [zCoeff_veronese, mem_veronese_piece_iff'] at h
    rw [addDeg_veroneseDeg h0]
    exact h
  · rintro ⟨h1, h2⟩
    have h0 := nonneg_of_veroneseDeg ha h1
    refine ⟨fun c => ?_, fun β hβ => ?_⟩
    · obtain rfl := Fin.fin_one_eq_zero c
      simpa using h0
    · have h := h2 _ (X.veroneseMon_mem_monSet ha hβ)
      rw [zCoeff_veronese, mem_veronese_piece_iff']
      rw [addDeg_veroneseDeg h0] at h
      exact h

omit [NeZero r] in
include ha in
/-- An admissible degree of `f ∈ R_{d₀ a}(𝒳)` can be taken of the form `n a`. -/
theorem exists_isAdmissible_veronese {d : Fin 1 → ℤ} {f : K}
    (hf : f ∈ X.sections (veroneseDeg a d)) :
    ∃ n : ℕ, X.IsAdmissible (veroneseDeg a d) (n • a) f := by
  obtain ⟨b, hb⟩ := hf
  exact ⟨_, hb.mono (le_sum_nsmul ha b)⟩

/-- **`R_d(𝒳_(a)) = R_{d₀ a}(𝒳)`** (`lem:gl-veronese`). -/
theorem mem_veronese_sections_iff {d : Fin 1 → ℤ} {f : K} :
    f ∈ (X.veronese ha).sections d ↔ f ∈ X.sections (veroneseDeg a d) := by
  constructor
  · rintro ⟨b, hb⟩
    rw [fin_one_eq_single b] at hb
    exact ((X.isAdmissible_veronese_iff ha).1 hb).mem_sections
  · intro hf
    obtain ⟨n, hn⟩ := X.exists_isAdmissible_veronese ha hf
    exact ((X.isAdmissible_veronese_iff ha).2 hn).mem_sections

/-- `|f U^u|_{e(v)} = |f T^{u₀ a}|_v` on homogeneous elements. -/
theorem homNorm_veroneseAnMap (v : X.an) (u : Fin 1 →₀ ℕ) (g : K) :
    (X.veronese ha).homNorm (X.veroneseAnMap ha v).1 u g = X.homNorm v.1 (u 0 • a) g := by
  by_cases hg : g ∈ (X.veronese ha).piece u
  · rw [homNorm_of_mem _ hg, homNorm_of_mem _ ((X.mem_veronese_piece_iff' ha).1 hg),
      veroneseAnMap_val_ofPiece]
  · rw [homNorm_of_notMem _ hg,
      homNorm_of_notMem _ fun h => hg ((X.mem_veronese_piece_iff' ha).2 h)]

/-- **Values of sections** (`lem:gl-veronese`): `|f|_{e(v)} = |f|_v` for `f ∈ R_d(𝒳_(a))`
(both sides vanish for `f ∉ R_d(𝒳_(a)) = R_{d₀ a}(𝒳)`). -/
theorem secAbs_veroneseAnMap (v : X.an) (d : Fin 1 → ℤ) (f : K) :
    (X.veronese ha).secAbs (X.veroneseAnMap ha v).1 d f = X.secAbs v.1 (veroneseDeg a d) f := by
  by_cases hf : f ∈ X.sections (veroneseDeg a d)
  · obtain ⟨n, hn⟩ := X.exists_isAdmissible_veronese ha hf
    have h0 := nonneg_of_veroneseDeg ha hn.1
    rw [secAbs_eq (X.veroneseAnMap ha v).2.2 ((X.isAdmissible_veronese_iff ha).2 hn),
      secAbs_eq v.2.2 hn, secAbsAt, secAbsAt]
    refine (Finset.sup_congr rfl fun β _ => ?_).trans (X.sup_veroneseMon ha n _)
    rw [homNorm_veroneseAnMap, zCoeff_veronese, ← addDeg_veroneseDeg h0]
  · rw [secAbs_of_notMem _ hf,
      secAbs_of_notMem _ fun h => hf ((X.mem_veronese_sections_iff ha).1 h)]

theorem logSecAbs_veroneseAnMap (v : X.an) (d : Fin 1 → ℤ) (f : K) :
    (X.veronese ha).logSecAbs (X.veroneseAnMap ha v).1 d f =
      X.logSecAbs v.1 (veroneseDeg a d) f := by
  rw [logSecAbs, logSecAbs, secAbs_veroneseAnMap]

theorem termVal_veroneseAnMap (v : X.an) (d : Fin 1 → ℤ) (t : K × ℝ) :
    (X.veronese ha).termVal d t (X.veroneseAnMap ha v) = X.termVal (veroneseDeg a d) t v := by
  rw [termVal_def, termVal_def, logSecAbs_veroneseAnMap]

end Sections

/-! ### Fubini–Study functions -/

section FS

variable [NeZero r] (X : MultiModel k K r) {a : Fin r →₀ ℕ} (ha : ∀ c, 0 < a c)

/-- Fubini–Study data of class `q ∈ ℚ^1` on `𝒳_(a)` as data of class `q₀ a` on `𝒳`: the same
`m`, sections and constants, in degree `(m q₀) a`. -/
def fsDataOfVeronese {q : Fin 1 → ℚ} (D : (X.veronese ha).FSData q) :
    X.FSData fun c => q 0 * a c where
  m := D.m
  m_pos := D.m_pos
  deg := veroneseDeg a D.deg
  deg_eq c := by rw [veroneseDeg_apply, Int.cast_mul, D.deg_eq 0, Int.cast_natCast]; ring
  terms := D.terms
  mem_sections t ht := (X.mem_veronese_sections_iff ha).1 (D.mem_sections t ht)

theorem eval_fsDataOfVeronese {q : Fin 1 → ℚ} (D : (X.veronese ha).FSData q) (v : X.an) :
    (X.fsDataOfVeronese ha D).eval v = D.eval (X.veroneseAnMap ha v) := by
  rw [FSData.eval_def, FSData.eval_def]
  refine congrArg _ (Finset.sup_congr rfl fun t _ => ?_)
  rw [termVal_veroneseAnMap]
  rfl

/-- For data of class `q₀ a` on `𝒳` (degree `m q₀ a ∈ ℤ^r`): `a₀ (m q₀ a) = (m q₀ a)_0 a`. -/
theorem veroneseDeg_deg {q : Fin 1 → ℚ} (D : X.FSData fun c => q 0 * a c) :
    veroneseDeg a (fun _ => D.deg 0) = a 0 • D.deg := by
  funext c
  have h1 := D.deg_eq 0
  have h2 := D.deg_eq c
  have : (((D.deg 0 * a c : ℤ)) : ℚ) = ((a 0 * D.deg c : ℤ) : ℚ) := by
    push_cast
    rw [h1, h2]
    ring
  rw [veroneseDeg_apply, Pi.smul_apply, nsmul_eq_mul]
  exact_mod_cast this

/-- Fubini–Study data of class `q₀ a` on `𝒳` as data of class `q` on `𝒳_(a)`: `m` becomes
`a₀ m` and the sections `f_t` become `f_t^{a₀}` (`MultiModel.scaleTerms`), of degree
`(a₀ m q₀) = (m q₀ a)_0 ∈ ℤ`. -/
def veroneseFSData {q : Fin 1 → ℚ} (D : X.FSData fun c => q 0 * a c) :
    (X.veronese ha).FSData q where
  m := a 0 * D.m
  m_pos := Nat.mul_pos (ha 0) D.m_pos
  deg := fun _ => D.deg 0
  deg_eq c := by
    obtain rfl := Fin.fin_one_eq_zero c
    rw [D.deg_eq 0]
    push_cast
    ring
  terms := scaleTerms (a 0) D.terms
  mem_sections t ht := by
    rw [mem_veronese_sections_iff, veroneseDeg_deg]
    exact scaleTerms_mem_sections D.mem_sections t ht

theorem eval_veroneseFSData {q : Fin 1 → ℚ} (D : X.FSData fun c => q 0 * a c) (v : X.an) :
    (X.veroneseFSData ha D).eval (X.veroneseAnMap ha v) = D.eval v := by
  rw [FSData.eval_def, FSData.eval_def]
  change ((((a 0 * D.m : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * (scaleTerms (a 0) D.terms).sup
    (fun t => (X.veronese ha).termVal (fun _ => D.deg 0) t (X.veroneseAnMap ha v)) = _
  have h : (fun t => (X.veronese ha).termVal (fun _ => D.deg 0) t (X.veroneseAnMap ha v)) =
      fun t => X.termVal (a 0 • D.deg) t v :=
    funext fun t => by rw [termVal_veroneseAnMap, veroneseDeg_deg]
  rw [h, sup_scaleTerms (ha 0) D.mem_sections v, ← mul_assoc, ← EReal.coe_mul]
  congr 3
  have : (a 0 : ℝ) ≠ 0 := by exact_mod_cast (ha 0).ne'
  have : (D.m : ℝ) ≠ 0 := D.m_ne_zero
  push_cast
  field_simp

/-- **Fubini–Study functions** (`lem:gl-veronese`): `ψ ∈ 𝓗(𝒳_(a), q)` iff
`ψ ∘ e ∈ 𝓗(𝒳, q₀ a)`, for `q ∈ ℚ^1`. -/
theorem isFS_veronese_iff {q : Fin 1 → ℚ} {ψ : (X.veronese ha).an → EReal} :
    (X.veronese ha).IsFS q ψ ↔ X.IsFS (fun c => q 0 * a c) (ψ ∘ X.veroneseHomeomorph ha) := by
  constructor
  · rintro ⟨D, ⟨t, ht, ht0⟩, hψ⟩
    exact ⟨X.fsDataOfVeronese ha D, ⟨t, ht, ht0⟩, fun v => by
      rw [Function.comp_apply, hψ, eval_fsDataOfVeronese, veroneseHomeomorph_apply]⟩
  · rintro ⟨D, ⟨t, ht, ht0⟩, hψ⟩
    refine ⟨X.veroneseFSData ha D, ⟨(t.1 ^ a 0, (a 0 : ℝ) * t.2),
      mem_scaleTerms.2 ⟨t, ht, rfl⟩, pow_ne_zero _ ht0⟩, fun y => ?_⟩
    obtain ⟨v, rfl⟩ := (X.veroneseHomeomorph ha).surjective y
    rw [veroneseHomeomorph_apply, eval_veroneseFSData, ← hψ, Function.comp_apply,
      veroneseHomeomorph_apply]

/-- **Finite Fubini–Study functions**: `ψ ∈ 𝓗_fin(𝒳_(a), q)` iff `ψ ∘ e ∈ 𝓗_fin(𝒳, q₀ a)`. -/
theorem isFinFS_veronese_iff {q : Fin 1 → ℚ} {ψ : (X.veronese ha).an → EReal} :
    (X.veronese ha).IsFinFS q ψ ↔
      X.IsFinFS (fun c => q 0 * a c) (ψ ∘ X.veroneseHomeomorph ha) := by
  rw [isFinFS_iff, isFinFS_iff]
  constructor
  · rintro ⟨D, hrat, hne, hψ⟩
    refine ⟨X.fsDataOfVeronese ha D, hrat, fun v => ?_, fun v => ?_⟩
    · rw [eval_fsDataOfVeronese]
      exact hne _
    · rw [Function.comp_apply, hψ, eval_fsDataOfVeronese, veroneseHomeomorph_apply]
  · rintro ⟨D, hrat, hne, hψ⟩
    refine ⟨X.veroneseFSData ha D, isRational_scaleTerms hrat (a 0), fun y => ?_, fun y => ?_⟩
    · obtain ⟨v, rfl⟩ := (X.veroneseHomeomorph ha).surjective y
      rw [veroneseHomeomorph_apply, eval_veroneseFSData]
      exact hne v
    · obtain ⟨v, rfl⟩ := (X.veroneseHomeomorph ha).surjective y
      rw [veroneseHomeomorph_apply, eval_veroneseFSData, ← hψ, Function.comp_apply,
        veroneseHomeomorph_apply]

end FS

/-! ### Psh functions and the envelope property -/

section PSH

variable [NeZero r] (X : MultiModel k K r) {a : Fin r →₀ ℕ} (ha : ∀ c, 0 < a c)

/-- `PSH(𝒳_(a), θ) ⊆ PSH(𝒳, θ₀ a)` (via `e`): push the decreasing nets of classes `q_α → θ` to
classes `q_{α,0} a → θ₀ a`. -/
theorem IsPSH.comp_veroneseHomeomorph {θ : Fin 1 → ℝ} {u : (X.veronese ha).an → EReal}
    (hu : (X.veronese ha).IsPSH θ u) :
    X.IsPSH (fun c => θ 0 * a c) (u ∘ X.veroneseHomeomorph ha) := by
  have hne := MultiModel.IsPSH.apply_triv_ne_bot hu
  obtain ⟨-, husc, ι, hpre, hdir, hnon, q, f, hf, hq, hanti, hinf⟩ := hu
  refine ⟨⟨X.triv, by rw [Function.comp_apply, veroneseHomeomorph_triv]; exact hne⟩,
    husc.comp (X.veroneseHomeomorph ha).continuous, ι, hpre, hdir, hnon,
    fun i c => q i 0 * a c, fun i => f i ∘ X.veroneseHomeomorph ha,
    fun i => (X.isFS_veronese_iff ha).1 (hf i), ?_, fun v => hanti _, fun v => hinf _⟩
  refine tendsto_pi_nhds.2 fun c => ?_
  have h0 : Tendsto (fun i => (q i 0 : ℝ)) atTop (𝓝 (θ 0)) := tendsto_pi_nhds.1 hq 0
  simpa only [Rat.cast_mul, Rat.cast_natCast] using h0.mul_const (a c : ℝ)

/-- `PSH(𝒳, θ₀ a) ⊆ PSH(𝒳_(a), θ)` (via `e`): an approximant of class `b_α → θ₀ a` lies in
`𝓗(𝒳, λ_α a)` with `λ_α = max_c b_{α,c} / a_c → θ₀` (FS2). -/
theorem isPSH_of_comp_veroneseHomeomorph {θ : Fin 1 → ℝ} {u : (X.veronese ha).an → EReal}
    (hu : X.IsPSH (fun c => θ 0 * a c) (u ∘ X.veroneseHomeomorph ha)) :
    (X.veronese ha).IsPSH θ u := by
  have hne := MultiModel.IsPSH.apply_triv_ne_bot hu
  obtain ⟨-, husc, ι, hpre, hdir, hnon, b, f, hf, hb, hanti, hinf⟩ := hu
  let lam : ι → ℚ := fun i => Finset.univ.sup' Finset.univ_nonempty fun c => b i c / a c
  have hle : ∀ i, b i ≤ fun c => lam i * a c := fun i c => by
    have hlc : b i c / a c ≤ lam i := Finset.le_sup' (fun c => b i c / a c) (Finset.mem_univ c)
    have hac : (0 : ℚ) < a c := by exact_mod_cast ha c
    calc b i c = b i c / a c * a c := by field_simp
      _ ≤ lam i * a c := mul_le_mul_of_nonneg_right hlc hac.le
  have hlam : ∀ i, (lam i : ℝ) = Finset.univ.sup' Finset.univ_nonempty
      fun c => (b i c : ℝ) / a c := fun i => by
    rw [Finset.apply_sup'_eq_sup'_comp _ (fun x : ℚ => (x : ℝ)) fun x y => Rat.cast_max x y]
    refine Finset.sup'_congr _ rfl fun c _ => ?_
    simp only [Function.comp_apply, Rat.cast_div, Rat.cast_natCast]
  have husc' : UpperSemicontinuous u := by
    have h := husc.comp (X.veroneseHomeomorph ha).symm.continuous
    have e1 : (u ∘ X.veroneseHomeomorph ha) ∘ (X.veroneseHomeomorph ha).symm = u :=
      funext fun y => by simp
    rwa [e1] at h
  refine ⟨⟨(X.veronese ha).triv, ?_⟩, husc', ι, hpre, hdir, hnon, fun i _ => lam i,
    fun i => f i ∘ (X.veroneseHomeomorph ha).symm, fun i => ?_, ?_,
    fun y => hanti ((X.veroneseHomeomorph ha).symm y), fun y => ?_⟩
  · rw [← veroneseHomeomorph_triv]
    exact hne
  · change (X.veronese ha).IsFS _ _
    rw [isFS_veronese_iff]
    have e1 : (f i ∘ (X.veroneseHomeomorph ha).symm) ∘ X.veroneseHomeomorph ha = f i :=
      funext fun v => by simp
    rw [e1]
    exact (hf i).mono_class (hle i)
  · refine tendsto_pi_nhds.2 fun c => ?_
    obtain rfl := Fin.fin_one_eq_zero c
    have hc : ∀ c ∈ (Finset.univ : Finset (Fin r)),
        Tendsto (fun i => (b i c : ℝ) / a c) atTop (𝓝 (θ 0)) := fun c _ => by
      have h := (tendsto_pi_nhds.1 hb c).div_const (a c : ℝ)
      rwa [mul_div_cancel_right₀ _ (by exact_mod_cast (ha c).ne')] at h
    have h := Filter.Tendsto.finset_sup'_nhds_apply (g := fun _ => θ 0) Finset.univ_nonempty hc
    rw [Finset.sup'_const] at h
    simpa only [hlam] using h
  · have h := hinf ((X.veroneseHomeomorph ha).symm y)
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply] at h
    exact h

/-- **`PSH(𝒳_(a), θ) = PSH(𝒳, θ₀ a)`** (`lem:gl-veronese`, for every `θ ∈ ℝ^1`): `u` is
`θ`-psh on `𝒳_(a)` iff `u ∘ e` is `θ₀ a`-psh on `𝒳`. -/
theorem isPSH_veronese_iff {θ : Fin 1 → ℝ} {u : (X.veronese ha).an → EReal} :
    (X.veronese ha).IsPSH θ u ↔ X.IsPSH (fun c => θ 0 * a c) (u ∘ X.veroneseHomeomorph ha) :=
  ⟨IsPSH.comp_veroneseHomeomorph X ha, isPSH_of_comp_veroneseHomeomorph X ha⟩

/-- **`EP_{𝒳_(a)}(θ) ↔ EP_𝒳(θ₀ a)`** (`lem:gl-veronese`, for every `θ ∈ ℝ^1`). -/
theorem hasEnvelopeProperty_veronese_iff {θ : Fin 1 → ℝ} :
    (X.veronese ha).HasEnvelopeProperty θ ↔ X.HasEnvelopeProperty fun c => θ 0 * a c :=
  (FSSystemC.hasEnvelopeProperty_iff_of_isPSH_comp_iff (X.veroneseHomeomorph ha)
    fun _ => (X.isPSH_veronese_iff ha).symm).symm

/-- **`EP_{𝒳_(a)}(t) ↔ EP_𝒳(t a)`** for a real `t`. -/
theorem hasEnvelopeProperty_veronese_iff_smul {t : ℝ} :
    (X.veronese ha).HasEnvelopeProperty (fun _ => t) ↔
      X.HasEnvelopeProperty (t • fun c => (a c : ℝ)) :=
  X.hasEnvelopeProperty_veronese_iff ha

end PSH

end MultiModel

end EnvelopeProperty
