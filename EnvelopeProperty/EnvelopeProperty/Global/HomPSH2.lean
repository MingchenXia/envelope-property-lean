/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.MultDiagonal
import EnvelopeProperty.Global.HomShilov
import EnvelopeProperty.Global.Homogeneous

/-!
# PSH2 for homogeneous functions at every class

Let `𝒳 = (K, S, z)` be an integral multiprojective model of rank `r` over an algebraically closed
trivially valued field `k` (`EnvelopeProperty.MultiModel`, `def:gl-model`). This file implements
the blueprint nodes `thm:nn-psh2-hom` and `thm:nn-hom-max-diagonal` of the chapter `nonnef.tex`
(subsection `subsec:nn-psh2-hom`, "Decreasing limits of homogeneous psh functions") of the
formalization of Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX,
revisions `832e086` and of 2026-10-28; numbers below are those of the revision of 2026-10-28).

## Context

Revision `832e086` of FHX uses the decreasing-limit property PSH2 (Boucksom–Jonsson, *Global
pluripotential theory over a trivially valued field* (BJ22), Theorem 4.5, `thm:psh12`; FHX
`prop:BJ-package`(1)) at possibly non-nef classes, in the last step of FHX Theorem 7.2
(`thm:homogeneous-Siu`) and for the limit `U` in FHX Proposition 7.5 (`prop:homogeneous-slices`,
Proposition 7.4 in revision `832e086`). BJ22 derives PSH2 from its Lemma 4.6 (`lem:PSH`), whose
statement is false (`prop:nn-bj-lemma46-false`, `Global/Lemma46Counterexample.lean`). The revision
of 2026-10-28 replaces these uses by its Lemma 2.3 (`lem:homogeneous-decreasing-stability`, which is
`MultiModel.isPSHHom_of_antitone` on models) and Lemma 7.4 (`lem:homogeneous-carrier-limit`). This
file proves the two instances of PSH2 that FHX needs there, for **every** class `θ ∈ ℝ^r`, from
the multiplicative diagonal lemma (`lem:nn-mult-diagonal`, `Global/MultDiagonal.lean`) and the
homogeneous comparison at finitely many Rees points (`lem:nn-hom-shilov`, `Global/HomShilov.lean`).
Nothing here depends on BJ22 Theorem 6.21 or Lemma 4.6.

## Main statements

* `MultiModel.IsPSHHom.exists_isHomFS_approx` (the common step of the proofs of (A) and (B)): for
  `ψ ∈ PSH_hom(𝒳, θ)`, finitely many `G_j ∈ 𝓗_hom(𝒳, b_j)` with `ψ ≤ G_j`, a rational
  `γ ∈ (0, 1)`, `η > 0`, a point `x` and a real `M > ψ(x)`, some `F ∈ 𝓗_hom(𝒳, a)` with
  `|a - θ| < η` satisfies `ψ ≤ F`, `F(x) < M` and `F ≤ γ G_j` on `𝒳^an` for all `j`. `F` is a term of
  a homogeneous Fubini–Study net of `ψ` (`cor:gl-pshhom`, `MultiModel.IsPSHHom.exists_isHomFS_net`):
  on the finite comparison sets `Σ_{G_j}` of `lem:nn-hom-shilov` one has
  `ψ ≤ G_j < γ G_j` (as `G_j ∈ (-∞, 0)` there), so a late term of the net is `< γ G_j` on
  `Σ_{G_j}`, hence `≤ γ G_j` everywhere (`MultiModel.IsHomFS.exists_finset_le_of_le`).
* `MultiModel.exists_isHomFS_net_of_antitone`, `MultiModel.isPSHHom_of_antitone`
  (**`thm:nn-psh2-hom`**): if `(ψᵢ)_{i ∈ I}` is a decreasing net with `ψᵢ ∈ PSH_hom(𝒳, θᵢ)` and
  `θᵢ → θ ∈ ℝ^r`, then `ψ = infᵢ ψᵢ ∈ PSH_hom(𝒳, θ)`, and `ψ` is the limit of a decreasing net
  in `𝓗_hom(𝒳, a_β)` with `a_β → θ`. `MultiModel.isPSHHom_of_antitone_seq` is the case of
  sequences, and `MultiModel.isPSHHom_of_tendsto_class` the case of a constant sequence:
  `⋂ₙ PSH_hom(𝒳, θₙ) ⊆ PSH_hom(𝒳, θ)` for `θₙ → θ` (the last step of FHX Theorem 7.2).
* `EnvelopeProperty.antitone_finset_sup_add_of_dominated`, `MultiModel.isPSH_of_dominated_homMax`
  (**`thm:nn-hom-max-diagonal`**): let `θᵢ → θ` be a net in `ℝ^r`, and for each `i` let `Kᵢ` be a
  finite set, `ψ_{i,k} ∈ PSH_hom(𝒳, θᵢ)` and `c_{i,k} ≤ 0` (`k ∈ Kᵢ`), with *termwise
  domination*: for `i ≤ i'` and `k' ∈ K_{i'}` some `k ∈ Kᵢ` has `ψ_{i',k'} ≤ ψ_{i,k}` and
  `c_{i',k'} ≤ c_{i,k}`. Then `Uᵢ = max_{k ∈ Kᵢ} (ψ_{i,k} + c_{i,k})` is decreasing, and
  `U = infᵢ Uᵢ ∈ PSH(𝒳, θ)` unless `U ≡ -∞`. `MultiModel.isPSH_of_dominated_homMax_seq` is the
  case of sequences.

The sets `Kᵢ` are finsets `Ks i` of a fixed type `κ`, and the maxima are `Finset.sup` in `EReal`.

## Deviations from the blueprint

* `thm:nn-psh2-hom`: the blueprint's sets `𝒜ᵢ = {(a, F) : F ∈ 𝓗_hom(𝒳, a), F ≥ ψᵢ}` and its
  verification of (A) and (B) are used verbatim; (A) and (B) are both derived from
  `MultiModel.IsPSHHom.exists_isHomFS_approx` (with no comparison function, respectively with the
  two functions `F₁, F₂`). The decreasing net of the conclusion is the net `(1 - κ) F` of
  `exists_antitone_net_of_multCompatible`, as in the blueprint; `ψ = infᵢ ψᵢ` is taken as the
  limit, and `ψ ≢ -∞` is not a hypothesis (it follows from `ψᵢ(⋆) = 0`).
* `thm:nn-hom-max-diagonal`: the sets `Kᵢ` are not assumed nonempty. If some `Kᵢ` were empty, then
  `Uᵢ ≡ -∞` and `U ≡ -∞`; so under the hypothesis `U ≢ -∞` all `Kᵢ` are nonempty, which is what
  the proof uses. The common class of finitely many approximants is the coordinatewise maximum of
  their classes (as in the blueprint), `EnvelopeProperty.exists_rat_ge_forall_dist_lt`.
* Index types of nets live in the universe of `𝒳^an` (as in `MultiModel.IsPSH`).
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Auxiliary facts -/

/-- **Common classes.** If finitely many rational classes `a_k`, `k ∈ s ≠ ∅`, lie within `η` of
`θ` (sup norm), so does their coordinatewise maximum `b ≥ a_k`. -/
theorem exists_rat_ge_forall_dist_lt {κ : Type*} {r : ℕ} (s : Finset κ) (hs : s.Nonempty)
    (a : κ → Fin r → ℚ) (θ : Fin r → ℝ) {η : ℝ}
    (h : ∀ k ∈ s, dist (fun c => (a k c : ℝ)) θ < η) :
    ∃ b : Fin r → ℚ, (∀ k ∈ s, a k ≤ b) ∧ dist (fun c => (b c : ℝ)) θ < η := by
  obtain ⟨k₀, hk₀⟩ := id hs
  have hη : 0 < η := dist_nonneg.trans_lt (h k₀ hk₀)
  refine ⟨s.sup' hs a, fun k hk => Finset.le_sup' a hk, ?_⟩
  rw [dist_pi_lt_iff hη]
  intro c
  obtain ⟨k₁, hk₁, heq⟩ := Finset.exists_mem_eq_sup' hs (fun k => a k c)
  have hc : (s.sup' hs a) c = a k₁ c := by rw [Finset.sup'_apply, heq]
  change dist ((s.sup' hs a c : ℚ) : ℝ) (θ c) < η
  rw [hc]
  exact (dist_le_pi_dist (fun c => (a k₁ c : ℝ)) θ c).trans_lt (h k₁ hk₁)

/-- `L < γ L` for `L ∈ (-∞, 0)` and a real `γ < 1`. -/
theorem ereal_lt_coe_mul_of_neg {γ : ℝ} (hγ1 : γ < 1) {L : EReal} (hL : L ≠ ⊥) (hL0 : L < 0) :
    L < (γ : EReal) * L := by
  induction L using EReal.rec with
  | bot => exact absurd rfl hL
  | top => exact absurd hL0 (not_lt.2 le_top)
  | coe l =>
    rw [← EReal.coe_mul, EReal.coe_lt_coe_iff]
    rw [← EReal.coe_zero, EReal.coe_lt_coe_iff] at hL0
    nlinarith

/-- `x < M - c ↔ x + c < M` in `EReal`, for real `M` and `c`. -/
theorem ereal_lt_coe_sub_iff {x : EReal} {M c : ℝ} :
    x < ((M - c : ℝ) : EReal) ↔ x + (c : EReal) < (M : EReal) := by
  induction x using EReal.rec with
  | bot => simp only [EReal.bot_lt_coe, EReal.bot_add]
  | top => simp only [not_top_lt, EReal.top_add_coe]
  | coe x =>
    rw [← EReal.coe_add, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    constructor <;> intro h <;> linarith

/-- **Termwise domination of translated maxima.** If `0 ≤ γ ≤ 1`, every `k ∈ s` is assigned some
`k̃ ∈ t` with `d_{k̃} ≤ 0`, `c_k ≤ d_{k̃}` and `F_k ≤ γ G_{k̃}`, then
`max_{k ∈ s} (F_k + c_k) ≤ γ max_{k ∈ t} (G_k + d_k)` (`c ≤ d ≤ γ d` as `d ≤ 0`). -/
theorem finset_sup_add_le_coe_mul {κ : Type*} {s t : Finset κ} {F G : κ → EReal}
    {c d : κ → ℝ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (kk : κ → κ)
    (hkk : ∀ k ∈ s, kk k ∈ t) (hd : ∀ k ∈ t, d k ≤ 0) (hc : ∀ k ∈ s, c k ≤ d (kk k))
    (hF : ∀ k ∈ s, F k ≤ (γ : EReal) * G (kk k)) :
    (s.sup fun k => F k + (c k : EReal)) ≤ (γ : EReal) * t.sup fun k => G k + (d k : EReal) := by
  refine Finset.sup_le fun k hk => ?_
  have hdk := hd (kk k) (hkk k hk)
  have hcd : (c k : EReal) ≤ (γ : EReal) * (d (kk k) : EReal) := by
    rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
    nlinarith [hc k hk]
  calc F k + (c k : EReal) ≤ (γ : EReal) * G (kk k) + (γ : EReal) * (d (kk k) : EReal) :=
        add_le_add (hF k hk) hcd
    _ = (γ : EReal) * (G (kk k) + (d (kk k) : EReal)) := (ProjBerk.ereal_coe_mul_add hγ0 _ _).symm
    _ ≤ (γ : EReal) * t.sup fun k => G k + (d k : EReal) :=
        ProjBerk.ereal_coe_mul_monotone hγ0
          (Finset.le_sup (f := fun k => G k + (d k : EReal)) (hkk k hk))

/-- **Termwise domination makes translated maxima decrease** (first assertion of
`thm:nn-hom-max-diagonal`): if for `i ≤ i'` every term `ψ_{i',k'} + c_{i',k'}` of `U_{i'}` is
bounded by a term `ψ_{i,k} + c_{i,k}` of `Uᵢ` (`ψ_{i',k'} ≤ ψ_{i,k}`, `c_{i',k'} ≤ c_{i,k}`), then
`Uᵢ = max_{k ∈ Kᵢ} (ψ_{i,k} + c_{i,k})` is decreasing in `i`. -/
theorem antitone_finset_sup_add_of_dominated {ι : Type*} [Preorder ι] {κ : Type*} {V : Type*}
    (Ks : ι → Finset κ) (ψ : ι → κ → V → EReal) (c : ι → κ → ℝ)
    (hdom : ∀ i i', i ≤ i' → ∀ k' ∈ Ks i', ∃ k ∈ Ks i,
      (∀ v, ψ i' k' v ≤ ψ i k v) ∧ c i' k' ≤ c i k) (v : V) :
    Antitone fun i => (Ks i).sup fun k => ψ i k v + (c i k : EReal) := by
  intro i i' h
  refine Finset.sup_le fun k' hk' => ?_
  obtain ⟨k, hk, hψ, hc⟩ := hdom i i' h k' hk'
  exact (add_le_add (hψ v) (EReal.coe_le_coe_iff.2 hc)).trans
    (Finset.le_sup (f := fun k => ψ i k v + (c i k : EReal)) hk)

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r}

/-- `𝓗(𝒳, a)` is stable under nonempty finite maxima (`lem:gl-fs-system`). -/
theorem IsFS.finset_sup {a : Fin r → ℚ} {κ : Type*} {s : Finset κ} (hs : s.Nonempty)
    {f : κ → X.an → EReal} (hf : ∀ k ∈ s, X.IsFS a (f k)) :
    X.IsFS a fun v => s.sup fun k => f k v := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton k => simpa only [Finset.sup_singleton] using hf k (Finset.mem_singleton_self k)
  | cons k s hk hs ih =>
    simp only [Finset.sup_cons]
    exact (hf k (Finset.mem_cons_self k s)).max (ih fun j hj => hf j (Finset.mem_cons_of_mem hj))

variable [IsAlgClosed k]

/-! ### The approximation step -/

/-- **The approximation step** of `thm:nn-psh2-hom` and `thm:nn-hom-max-diagonal`. Let
`ψ ∈ PSH_hom(𝒳, θ)` and let `s` be a finite set of pairs `(b, G)` with `G ∈ 𝓗_hom(𝒳, b)` and
`ψ ≤ G`. For every rational `γ ∈ (0, 1)`, `η > 0`, `x ∈ 𝒳^an` and real `M > ψ(x)` there is
`F ∈ 𝓗_hom(𝒳, a)` with `ψ ≤ F`, `|a - θ| < η`, `F(x) < M` and `F ≤ γ G` on `𝒳^an` for every
`(b, G) ∈ s`. `F` is a late term of a homogeneous Fubini–Study net of `ψ` (`cor:gl-pshhom`): on the
finite sets `Σ_G` of `lem:nn-hom-shilov`, `ψ ≤ G < γ G` since `G ∈ (-∞, 0)` there. -/
theorem IsPSHHom.exists_isHomFS_approx {θ : Fin r → ℝ} {ψ : X.an → EReal}
    (hψ : X.IsPSHHom θ ψ) (s : Finset ((Fin r → ℚ) × (X.an → EReal)))
    (hs : ∀ p ∈ s, X.IsHomFS p.1 p.2 ∧ ∀ v, ψ v ≤ p.2 v) {γ : ℚ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {η : ℝ} (hη : 0 < η) (x : X.an) {M : ℝ} (hM : ψ x < (M : EReal)) :
    ∃ (a : Fin r → ℚ) (F : X.an → EReal), X.IsHomFS a F ∧ (∀ v, ψ v ≤ F v) ∧
      dist (fun c => (a c : ℝ)) θ < η ∧ F x < (M : EReal) ∧
        ∀ p ∈ s, ∀ v, F v ≤ ((γ : ℝ) : EReal) * p.2 v := by
  obtain ⟨ι, _, _, _, a, f, hf, ha, hanti, hlim⟩ := hψ.exists_isHomFS_net
  choose! S hS using fun p (hp : p ∈ s) => (hs p hp).1.exists_finset_le_of_le
  -- pointwise, the net is eventually below every bound above `ψ`
  have hev : ∀ v (L : EReal), ψ v < L → ∀ᶠ i in atTop, f i v < L := by
    intro v L h
    rw [hlim v] at h
    obtain ⟨i₀, hi₀⟩ := iInf_lt_iff.1 h
    exact eventually_atTop.2 ⟨i₀, fun i hi => (hanti v hi).trans_lt hi₀⟩
  -- on the finite comparison sets, `ψ ≤ G < γ G`
  have h₁ : ∀ᶠ i in atTop, ∀ p ∈ s, ∀ v ∈ S p, f i v < ((γ : ℝ) : EReal) * p.2 v := by
    refine (eventually_all_finset s).2 fun p hp => (eventually_all_finset (S p)).2 fun v hv =>
      hev v _ ?_
    obtain ⟨hb, hn⟩ := (hS p hp).1 v hv
    exact ((hs p hp).2 v).trans_lt (ereal_lt_coe_mul_of_neg (by exact_mod_cast hγ1) hb.ne' hn)
  obtain ⟨i, hi₁, hi₂, hi₃⟩ := (h₁.and ((hev x M hM).and (Metric.tendsto_nhds.1 ha η hη))).exists
  refine ⟨a i, f i, hf i, fun v => ?_, hi₃, hi₂, fun p hp =>
    (hS p hp).2 (a i) (f i) γ hγ0 (hf i) fun v hv => (hi₁ p hp v hv).le⟩
  rw [hlim v]
  exact iInf_le _ i

/-! ### PSH2 for homogeneous functions (`thm:nn-psh2-hom`) -/

/-- **PSH2 for homogeneous functions**, net form (**`thm:nn-psh2-hom`**): let `(ψᵢ)_{i ∈ I}` be a
decreasing net with `ψᵢ ∈ PSH_hom(𝒳, θᵢ)` and `θᵢ → θ ∈ ℝ^r` (any `θ`). Then `ψ = infᵢ ψᵢ` is
the limit of a decreasing net `F_β ∈ 𝓗_hom(𝒳, a_β)` with `a_β → θ`. This is the multiplicative
diagonal lemma (`lem:nn-mult-diagonal`) for `𝒜ᵢ = {(a, F) : F ∈ 𝓗_hom(𝒳, a), F ≥ ψᵢ}`; the
approximants `(1 - κ) F` lie in `𝓗_hom(𝒳, (1 - κ) a)` (`lem:nn-hom-fs-operations`(3)). -/
theorem exists_isHomFS_net_of_antitone {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] {θs : ι → Fin r → ℝ} {θ : Fin r → ℝ} (hθ : Tendsto θs atTop (𝓝 θ))
    {ψ : ι → X.an → EReal} (hψ : ∀ i, X.IsPSHHom (θs i) (ψ i))
    (hanti : ∀ v, Antitone fun i => ψ i v) {w : X.an → EReal} (hw : ∀ v, w v = ⨅ i, ψ i v) :
    ∃ (D : Type u) (_ : Preorder D) (_ : IsDirected D (· ≤ ·)) (_ : Nonempty D)
      (a : D → Fin r → ℚ) (f : D → X.an → EReal), (∀ d, X.IsHomFS (a d) (f d)) ∧
        Tendsto (fun d c => (a d c : ℝ)) atTop (𝓝 θ) ∧ (∀ v, Antitone fun d => f d v) ∧
          ∀ v, w v = ⨅ d, f d v := by
  classical
  have : Nonempty X.an := ⟨X.triv⟩
  let A : ι → Set ((Fin r → ℚ) × (X.an → EReal)) :=
    fun i => {p | X.IsHomFS p.1 p.2 ∧ ∀ v, ψ i v ≤ p.2 v}
  have hA : ∀ i, ∀ p ∈ A i, (∀ v, ψ i v ≤ p.2 v) ∧ ∀ v, p.2 v ≤ 0 :=
    fun i p hp => ⟨hp.2, hp.1.le_zero⟩
  -- (A)
  have happrox : ∀ i x (M : ℝ), ψ i x < (M : EReal) → ∀ η : ℝ, 0 < η →
      ∃ p ∈ A i, dist (fun c => (p.1 c : ℝ)) (θs i) < η ∧ p.2 x < (M : EReal) := by
    intro i x M hM η hη
    obtain ⟨a, F, hF, hle, hdist, hx, -⟩ := (hψ i).exists_isHomFS_approx ∅
      (fun p hp => absurd hp (Finset.notMem_empty p)) (γ := 1 / 2) (by norm_num) (by norm_num)
      hη x hM
    exact ⟨(a, F), ⟨hF, hle⟩, hdist, hx⟩
  -- (B)
  have hcompat : ∀ i₁ i₂ i, i₁ ≤ i → i₂ ≤ i → ∀ p₁ ∈ A i₁, ∀ p₂ ∈ A i₂, ∀ γ : ℚ, 0 < γ →
      γ < 1 → ∀ η : ℝ, 0 < η → ∃ p ∈ A i, dist (fun c => (p.1 c : ℝ)) (θs i) < η ∧
        (∀ x, p.2 x ≤ ((γ : ℝ) : EReal) * p₁.2 x) ∧ ∀ x, p.2 x ≤ ((γ : ℝ) : EReal) * p₂.2 x := by
    intro i₁ i₂ i h₁ h₂ p₁ hp₁ p₂ hp₂ γ hγ0 hγ1 η hη
    have hs : ∀ p ∈ ({p₁, p₂} : Finset _), X.IsHomFS p.1 p.2 ∧ ∀ v, ψ i v ≤ p.2 v := by
      intro p hp
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact ⟨hp₁.1, fun v => (hanti v h₁).trans (hp₁.2 v)⟩
      · rw [Finset.mem_singleton.1 hp]
        exact ⟨hp₂.1, fun v => (hanti v h₂).trans (hp₂.2 v)⟩
    have hM : ψ i X.triv < ((1 : ℝ) : EReal) :=
      ((hψ i).nonpos _).trans_lt (by rw [EReal.coe_one]; exact zero_lt_one)
    obtain ⟨a, F, hF, hle, hdist, -, hγ⟩ :=
      (hψ i).exists_isHomFS_approx {p₁, p₂} hs hγ0 hγ1 hη X.triv hM
    exact ⟨(a, F), ⟨hF, hle⟩, hdist, hγ p₁ (Finset.mem_insert_self _ _),
      hγ p₂ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
  obtain ⟨D, _, _, _, idx, p, κ, hmem, hκ, hcl, hanti', hlim⟩ :=
    exists_antitone_net_of_multCompatible (fun i v => (hψ i).nonpos v) hθ hw hA happrox hcompat
  exact ⟨D, inferInstance, inferInstance, inferInstance, fun d => (1 - κ d) • (p d).1,
    fun d v => (((1 - κ d : ℚ) : ℝ) : EReal) * (p d).2 v,
    fun d => (hmem d).1.smul (sub_pos.2 (hκ d).2), hcl, hanti', hlim⟩

/-- **PSH2 for homogeneous functions** (**`thm:nn-psh2-hom`**): if `(ψᵢ)` is a decreasing net
with `ψᵢ ∈ PSH_hom(𝒳, θᵢ)` and `θᵢ → θ ∈ ℝ^r` (any `θ`), then `ψ = infᵢ ψᵢ ∈ PSH_hom(𝒳, θ)`.
Homogeneity of `ψ` holds because scaling commutes with infima; `ψ(⋆) = 0`. -/
theorem isPSHHom_of_antitone {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {θs : ι → Fin r → ℝ} {θ : Fin r → ℝ} (hθ : Tendsto θs atTop (𝓝 θ))
    {ψ : ι → X.an → EReal} (hψ : ∀ i, X.IsPSHHom (θs i) (ψ i))
    (hanti : ∀ v, Antitone fun i => ψ i v) {w : X.an → EReal} (hw : ∀ v, w v = ⨅ i, ψ i v) :
    X.IsPSHHom θ w := by
  obtain ⟨D, _, _, _, a, f, hf, ha, hanti', hlim⟩ :=
    exists_isHomFS_net_of_antitone hθ hψ hanti hw
  have hw0 : w X.triv = 0 := by
    rw [hw]
    exact (iInf_congr fun i => (hψ i).apply_triv_eq_zero).trans iInf_const
  refine ⟨FSSystemC.isPSH_of_iInf (F := X.fsSystem) ⟨X.triv, by rw [hw0]; exact EReal.zero_ne_bot⟩
    a f (fun d => (hf d).isFS) ha hanti' hlim, fun t ht v => ?_⟩
  rw [hw, hw, ereal_coe_mul_iInf ht]
  exact iInf_congr fun i => (hψ i).2 t ht v

/-- **PSH2 for homogeneous functions**, decreasing sequences (`thm:nn-psh2-hom`). -/
theorem isPSHHom_of_antitone_seq {θs : ℕ → Fin r → ℝ} {θ : Fin r → ℝ}
    (hθ : Tendsto θs atTop (𝓝 θ)) {ψ : ℕ → X.an → EReal} (hψ : ∀ n, X.IsPSHHom (θs n) (ψ n))
    (hanti : ∀ v, Antitone fun n => ψ n v) {w : X.an → EReal} (hw : ∀ v, w v = ⨅ n, ψ n v) :
    X.IsPSHHom θ w := by
  have hdown : Tendsto (ULift.down : ULift.{u} ℕ → ℕ) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨ULift.up b, fun a ha => ha⟩
  refine isPSHHom_of_antitone (ι := ULift.{u} ℕ) (ψ := fun n => ψ n.down) (hθ.comp hdown)
    (fun n => hψ n.down) (fun v _ _ h => hanti v h) fun v => ?_
  rw [hw v]
  exact (Equiv.ulift.iInf_comp (g := fun n => ψ n v)).symm

/-- **Homogeneous psh functions at a limit class** (`thm:nn-psh2-hom` for a constant sequence; the
last step of FHX Theorem 7.2, `thm:homogeneous-Siu`): if `ψ ∈ PSH_hom(𝒳, θₙ)` for all `n` and
`θₙ → θ ∈ ℝ^r`, then `ψ ∈ PSH_hom(𝒳, θ)`. -/
theorem isPSHHom_of_tendsto_class {θs : ℕ → Fin r → ℝ} {θ : Fin r → ℝ}
    (hθ : Tendsto θs atTop (𝓝 θ)) {ψ : X.an → EReal} (hψ : ∀ n, X.IsPSHHom (θs n) ψ) :
    X.IsPSHHom θ ψ :=
  isPSHHom_of_antitone_seq hθ hψ (fun _ _ _ _ => le_rfl) fun _ => iInf_const.symm

/-! ### Decreasing limits of maxima of homogeneous psh functions (`thm:nn-hom-max-diagonal`) -/

/-- **Decreasing limits of maxima of homogeneous psh functions** (**`thm:nn-hom-max-diagonal`**).
Let `θᵢ → θ` be a net in `ℝ^r` (any `θ`). For each `i` let `Kᵢ = Ks i` be a finite set and, for
`k ∈ Kᵢ`, `ψ_{i,k} ∈ PSH_hom(𝒳, θᵢ)` and `c_{i,k} ≤ 0`; put
`Uᵢ = max_{k ∈ Kᵢ} (ψ_{i,k} + c_{i,k})`. Assume *termwise domination*: for `i ≤ i'` and
`k' ∈ K_{i'}` some `k ∈ Kᵢ` has `ψ_{i',k'} ≤ ψ_{i,k}` and `c_{i',k'} ≤ c_{i,k}` (so `(Uᵢ)` is
decreasing, `antitone_finset_sup_add_of_dominated`). If `U = infᵢ Uᵢ ≢ -∞`, then
`U ∈ PSH(𝒳, θ)`. The proof is the multiplicative diagonal lemma (`lem:nn-mult-diagonal`) for
`𝒜ᵢ = {(b, max_{k ∈ Kᵢ} (F_k + c_{i,k})) : F_k ∈ 𝓗_hom(𝒳, b), F_k ≥ ψ_{i,k}}`, with (B) verified
termwise through the homogeneous comparison at Rees points (`lem:nn-hom-shilov`). -/
theorem isPSH_of_dominated_homMax {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {θs : ι → Fin r → ℝ} {θ : Fin r → ℝ} (hθ : Tendsto θs atTop (𝓝 θ)) {κ : Type*}
    (Ks : ι → Finset κ) (ψ : ι → κ → X.an → EReal) (c : ι → κ → ℝ)
    (hψ : ∀ i, ∀ k ∈ Ks i, X.IsPSHHom (θs i) (ψ i k)) (hc : ∀ i, ∀ k ∈ Ks i, c i k ≤ 0)
    (hdom : ∀ i i', i ≤ i' → ∀ k' ∈ Ks i', ∃ k ∈ Ks i,
      (∀ v, ψ i' k' v ≤ ψ i k v) ∧ c i' k' ≤ c i k)
    {w : X.an → EReal} (hw : ∀ v, w v = ⨅ i, (Ks i).sup fun k => ψ i k v + (c i k : EReal))
    (hfin : ∃ v, w v ≠ ⊥) : X.IsPSH θ w := by
  classical
  set U : ι → X.an → EReal := fun i v => (Ks i).sup fun k => ψ i k v + (c i k : EReal) with hU
  -- all `Kᵢ` are nonempty, since otherwise `U ≤ Uᵢ ≡ -∞`
  have hne : ∀ i, (Ks i).Nonempty := by
    intro i
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    obtain ⟨v, hv⟩ := hfin
    refine hv (le_bot_iff.1 ((hw v).le.trans ((iInf_le _ i).trans ?_)))
    rw [h, Finset.sup_empty]
  -- `ψ_{i,k} + c_{i,k} ≤ 0`
  have hle0 : ∀ i, ∀ k ∈ Ks i, ∀ (G : X.an → EReal), (∀ v, G v ≤ 0) → ∀ v,
      G v + (c i k : EReal) ≤ 0 := by
    intro i k hk G hG v
    have hc' : (c i k : EReal) ≤ 0 := by exact_mod_cast hc i k hk
    simpa only [add_zero] using add_le_add (hG v) hc'
  have hU0 : ∀ i v, U i v ≤ 0 := fun i v =>
    Finset.sup_le fun k hk => hle0 i k hk (ψ i k) (hψ i k hk).nonpos v
  let A : ι → Set ((Fin r → ℚ) × (X.an → EReal)) := fun i => {p | ∃ G : κ → X.an → EReal,
    (∀ k ∈ Ks i, X.IsHomFS p.1 (G k) ∧ ∀ v, ψ i k v ≤ G k v) ∧
      ∀ v, p.2 v = (Ks i).sup fun k => G k v + (c i k : EReal)}
  have hA : ∀ i, ∀ p ∈ A i, X.IsFS p.1 p.2 ∧ (∀ x, U i x ≤ p.2 x) ∧ ∀ x, p.2 x ≤ 0 := by
    rintro i p ⟨G, hG, hp⟩
    refine ⟨?_, fun v => ?_, fun v => ?_⟩
    · rw [show p.2 = fun v => (Ks i).sup fun k => G k v + (c i k : EReal) from funext hp]
      exact IsFS.finset_sup (hne i) fun k hk =>
        FSSystemC.IsFS.add_const (F := X.fsSystem) (hG k hk).1.isFS (c i k)
    · rw [hp v]
      exact Finset.sup_mono_fun fun k hk => add_le_add ((hG k hk).2 v) le_rfl
    · rw [hp v]
      exact Finset.sup_le fun k hk => hle0 i k hk (G k) (hG k hk).1.le_zero v
  -- (A): approximate each term at `x`, then pass to a common class
  have happrox : ∀ i x (M : ℝ), U i x < (M : EReal) → ∀ η : ℝ, 0 < η →
      ∃ p ∈ A i, dist (fun c => (p.1 c : ℝ)) (θs i) < η ∧ p.2 x < (M : EReal) := by
    intro i x M hM η hη
    have hk : ∀ k ∈ Ks i, ψ i k x < ((M - c i k : ℝ) : EReal) := fun k hk =>
      ereal_lt_coe_sub_iff.2
        ((Finset.le_sup (f := fun k => ψ i k x + (c i k : EReal)) hk).trans_lt hM)
    choose! a F hF using fun k (hki : k ∈ Ks i) => (hψ i k hki).exists_isHomFS_approx ∅
      (fun p hp => absurd hp (Finset.notMem_empty p)) (γ := 1 / 2) (by norm_num) (by norm_num)
      hη x (hk k hki)
    obtain ⟨b, hab, hb⟩ := exists_rat_ge_forall_dist_lt (Ks i) (hne i) a (θs i)
      fun k hk => (hF k hk).2.2.1
    refine ⟨(b, fun v => (Ks i).sup fun k => F k v + (c i k : EReal)),
      ⟨F, fun k hk => ⟨(hF k hk).1.mono_class (hab k hk), (hF k hk).2.1⟩, fun v => rfl⟩, hb, ?_⟩
    exact (Finset.sup_lt_iff (EReal.bot_lt_coe M)).2 fun k hk =>
      ereal_lt_coe_sub_iff.1 (hF k hk).2.2.2.1
  -- (B): dominate termwise, through the comparison at Rees points
  have hcompat : ∀ i₁ i₂ i, i₁ ≤ i → i₂ ≤ i → ∀ p₁ ∈ A i₁, ∀ p₂ ∈ A i₂, ∀ γ : ℚ, 0 < γ →
      γ < 1 → ∀ η : ℝ, 0 < η → ∃ p ∈ A i, dist (fun c => (p.1 c : ℝ)) (θs i) < η ∧
        (∀ x, p.2 x ≤ ((γ : ℝ) : EReal) * p₁.2 x) ∧ ∀ x, p.2 x ≤ ((γ : ℝ) : EReal) * p₂.2 x := by
    rintro i₁ i₂ i h₁ h₂ p₁ ⟨G₁, hG₁, hp₁⟩ p₂ ⟨G₂, hG₂, hp₂⟩ γ hγ0 hγ1 η hη
    obtain ⟨k₀, hk₀⟩ := hne i
    have : Nonempty κ := ⟨k₀⟩
    choose! k₁ hk₁ using fun k' (hk' : k' ∈ Ks i) => hdom i₁ i h₁ k' hk'
    choose! k₂ hk₂ using fun k' (hk' : k' ∈ Ks i) => hdom i₂ i h₂ k' hk'
    have hs : ∀ k' ∈ Ks i, ∀ q ∈ ({(p₁.1, G₁ (k₁ k')), (p₂.1, G₂ (k₂ k'))} : Finset _),
        X.IsHomFS q.1 q.2 ∧ ∀ v, ψ i k' v ≤ q.2 v := by
      intro k' hk' q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact ⟨(hG₁ _ (hk₁ k' hk').1).1,
          fun v => ((hk₁ k' hk').2.1 v).trans ((hG₁ _ (hk₁ k' hk').1).2 v)⟩
      · rw [Finset.mem_singleton.1 hq]
        exact ⟨(hG₂ _ (hk₂ k' hk').1).1,
          fun v => ((hk₂ k' hk').2.1 v).trans ((hG₂ _ (hk₂ k' hk').1).2 v)⟩
    have hM : ∀ k' ∈ Ks i, ψ i k' X.triv < ((1 : ℝ) : EReal) := fun k' hk' =>
      ((hψ i k' hk').nonpos _).trans_lt (by rw [EReal.coe_one]; exact zero_lt_one)
    choose! a F hF using fun k' (hk' : k' ∈ Ks i) =>
      (hψ i k' hk').exists_isHomFS_approx _ (hs k' hk') hγ0 hγ1 hη X.triv (hM k' hk')
    obtain ⟨b, hab, hb⟩ := exists_rat_ge_forall_dist_lt (Ks i) (hne i) a (θs i)
      fun k hk => (hF k hk).2.2.1
    have hγ0' : (0 : ℝ) ≤ (γ : ℝ) := by exact_mod_cast hγ0.le
    have hγ1' : (γ : ℝ) ≤ 1 := by exact_mod_cast hγ1.le
    refine ⟨(b, fun v => (Ks i).sup fun k => F k v + (c i k : EReal)),
      ⟨F, fun k hk => ⟨(hF k hk).1.mono_class (hab k hk), (hF k hk).2.1⟩, fun v => rfl⟩, hb,
      fun v => ?_, fun v => ?_⟩
    · rw [hp₁ v]
      exact finset_sup_add_le_coe_mul hγ0' hγ1' k₁ (fun k' hk' => (hk₁ k' hk').1)
        (hc i₁) (fun k' hk' => (hk₁ k' hk').2.2)
        fun k' hk' => (hF k' hk').2.2.2.2 _ (Finset.mem_insert_self _ _) v
    · rw [hp₂ v]
      exact finset_sup_add_le_coe_mul hγ0' hγ1' k₂ (fun k' hk' => (hk₂ k' hk').1)
        (hc i₂) (fun k' hk' => (hk₂ k' hk').2.2)
        fun k' hk' => (hF k' hk').2.2.2.2 _
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) v
  exact X.fsSystem.isPSH_of_multCompatible hU0 hθ hw hfin hA happrox hcompat

/-- **Decreasing limits of maxima of homogeneous psh functions**, sequences
(`thm:nn-hom-max-diagonal`). -/
theorem isPSH_of_dominated_homMax_seq {θs : ℕ → Fin r → ℝ} {θ : Fin r → ℝ}
    (hθ : Tendsto θs atTop (𝓝 θ)) {κ : Type*} (Ks : ℕ → Finset κ) (ψ : ℕ → κ → X.an → EReal)
    (c : ℕ → κ → ℝ) (hψ : ∀ n, ∀ k ∈ Ks n, X.IsPSHHom (θs n) (ψ n k))
    (hc : ∀ n, ∀ k ∈ Ks n, c n k ≤ 0)
    (hdom : ∀ n n', n ≤ n' → ∀ k' ∈ Ks n', ∃ k ∈ Ks n,
      (∀ v, ψ n' k' v ≤ ψ n k v) ∧ c n' k' ≤ c n k)
    {w : X.an → EReal} (hw : ∀ v, w v = ⨅ n, (Ks n).sup fun k => ψ n k v + (c n k : EReal))
    (hfin : ∃ v, w v ≠ ⊥) : X.IsPSH θ w := by
  have hdown : Tendsto (ULift.down : ULift.{u} ℕ → ℕ) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨ULift.up b, fun a ha => ha⟩
  refine isPSH_of_dominated_homMax (ι := ULift.{u} ℕ) (hθ.comp hdown) (fun n => Ks n.down)
    (fun n => ψ n.down) (fun n => c n.down) (fun n => hψ n.down) (fun n => hc n.down)
    (fun n n' h => hdom n.down n'.down h) (fun v => ?_) hfin
  rw [hw v]
  exact (Equiv.ulift.iInf_comp (g := fun n => (Ks n).sup fun k => ψ n k v + (c n k : EReal))).symm

end MultiModel

end EnvelopeProperty
