/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.NormalEP

/-!
# PSH2 below a homogeneous majorant

Let `𝒳 = (K, S, z)` be an integral multiprojective model of rank `r` over an algebraically closed
trivially valued field `k` (`EnvelopeProperty.MultiModel`, `def:gl-model`). This file implements the
blueprint chapter `psh2-homogeneous-majorant.tex` (section `sec:psh2-hom-majorant`) of the
formalization of Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX,
revisions `832e086` and of 2026-10-28; numbers below are those of the revision of 2026-10-28).

## Context

In revision `832e086`, FHX Proposition 2.1(1) (`prop:BJ-package`) states the decreasing-limit
property PSH2 at every class, citing Boucksom–Jonsson, *Global pluripotential theory over a
trivially valued field* (BJ22), Theorem 4.5 (`thm:psh12`), whose proof rests on the false BJ22
Lemma 4.6 (`lem:PSH`; `prop:nn-bj-lemma46-false`); the revision of 2026-10-28 restricts it to nef
classes and homogeneous nets (FHX Remark 2.2, `rem:BJ-decreasing-limits`). The project proves
PSH2 at nef limit classes, for homogeneous nets and dominated homogeneous maxima
(`Global/HomPSH2.lean`) and under the envelope property at the limit class (`thm:nn-psh2-of-ep`).
This file isolates the remaining input: a decreasing limit `u` of `θᵢ`-psh functions, `θᵢ → θ`, is
`θ`-psh as soon as one homogeneous `θ`-psh function `Ψ` dominates all Legendre slices `û_λ`,
`λ < u(⋆)`, i.e. the slope of `u` at infinity. The proof is the dyadic-grid argument of FHX
Proposition 7.5 (`prop:homogeneous-slices`, Proposition 7.4 in revision `832e086`;
`MultiModel.isPSH_uscReg_iSup_of_homogeneous_slices`), with `Ψ` given instead of produced by the
envelope property. FHX Lemma 7.4 (`lem:homogeneous-carrier-limit`) on models is a corollary
(`Global/HomogeneousCarrierLimit.lean`).

## Main statements

* `MultiModel.eq_iSup_legendreSlice_of_scaleFun_convex` (`lem:hm-convex-ray-reconstruction`):
  Legendre reconstruction `u = sup_{λ < u(⋆)} (û_λ + λ)` for every `u < +∞` with `u ≤ u(⋆) ∈ ℝ`
  whose scaling rays `t ↦ (t · u)(v)` satisfy the convexity inequality; with
  `MultiModel.scaleFun_ne_bot_of_scaleFun_convex` and
  `MultiModel.convexOn_rayFun_of_scaleFun_convex`.
* `MultiModel.isPSHHom_legendreSlice_of_antitone` (`lem:hm-limit-slices`): for a decreasing net
  `uᵢ ∈ PSH(𝒳, θᵢ)`, `θᵢ → θ`, with limit `u`, `û_λ ∈ PSH_hom(𝒳, θ)` for `λ < u(⋆)`.
* `MultiModel.isPSH_of_antitone_of_homMajorant` (**`thm:hm-psh2-hom-majorant`**, "Prop R"): if
  moreover `u ≢ -∞` and some `Ψ ∈ PSH_hom(𝒳, θ)` satisfies `û_λ ≤ Ψ` for all `λ < u(⋆)`, then
  `u ∈ PSH(𝒳, θ)`.
* `MultiModel.exists_homMajorant_of_hasEnvelopeProperty` (`cor:hm-majorant-of-ep`): under
  `EP_𝒳(θ)` the majorant exists, `Ψ = (sup_{λ < u(⋆)} û_λ)^⋆`; so the theorem contains
  `MultiModel.isPSH_of_antitone_of_hasEnvelopeProperty`.
* `MultiModel.isPSH_of_antitone_of_isPSH_zero` (`cor:hm-majorant-zero`): PSH2 at every class `θ`
  with `0 ∈ PSH(𝒳, θ)` (majorant `Ψ = 0`).

## Implementation notes

The reconstruction lemma is proved for arbitrary functions with convex rays rather than for
decreasing limits only, so that this file depends only on `Global/NormalEP.lean` (and not on the
main theorem, which `Global/EPDecreasingLimits.lean` imports). The convexity of the rays of a
decreasing limit is the private lemma `scaleFun_convex_of_iInf`.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty
namespace MultiModel

universe u

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r}

/-! ### Legendre reconstruction along convex rays (`lem:hm-convex-ray-reconstruction`) -/

section ConvexRays

variable {u : X.an → EReal}

/-- Along a scaling ray satisfying the convexity inequality, finiteness at one `t₀ > 0` forces
finiteness at every `t > 0` (`lem:hm-convex-ray-reconstruction`(1)): write `t₀` as a convex
combination of `t` and `t₀² / t` with a positive weight on `t`. -/
theorem scaleFun_ne_bot_of_scaleFun_convex {v : X.an}
    (hconv : ∀ {t₁ t₂ t : ℝ} (h₁ : 0 < t₁) (h₂ : 0 < t₂) (ht : 0 < t) {α β : ℝ}, 0 ≤ α → 0 ≤ β →
      α + β = 1 → t = α * t₁ + β * t₂ →
        X.scaleFun t ht u v ≤
          (α : EReal) * X.scaleFun t₁ h₁ u v + (β : EReal) * X.scaleFun t₂ h₂ u v)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hv : X.scaleFun t₀ ht₀ u v ≠ ⊥) (t : ℝ) (ht : 0 < t) :
    X.scaleFun t ht u v ≠ ⊥ := by
  intro hbot
  have hα : 0 < t₀ / (t + t₀) := div_pos ht₀ (by linarith)
  have hβ : 0 ≤ t / (t + t₀) := (div_pos ht (by linarith)).le
  have h₂ : 0 < t₀ ^ 2 / t := by positivity
  have hsum : t₀ / (t + t₀) + t / (t + t₀) = 1 := by
    rw [← add_div, add_comm, div_self (by linarith)]
  have hc := hconv ht h₂ ht₀ hα.le hβ hsum (by field_simp)
  rw [hbot, EReal.coe_mul_bot_of_pos hα, EReal.bot_add, le_bot_iff] at hc
  exact hv hc

/-- A scaling ray satisfying the convexity inequality and finite at `t = 1` is a real convex
function on `(0, ∞)` (`lem:hm-convex-ray-reconstruction`(1)). -/
theorem convexOn_rayFun_of_scaleFun_convex (htop : ∀ v, u v ≠ ⊤) {v : X.an}
    (hconv : ∀ {t₁ t₂ t : ℝ} (h₁ : 0 < t₁) (h₂ : 0 < t₂) (ht : 0 < t) {α β : ℝ}, 0 ≤ α → 0 ≤ β →
      α + β = 1 → t = α * t₁ + β * t₂ →
        X.scaleFun t ht u v ≤
          (α : EReal) * X.scaleFun t₁ h₁ u v + (β : EReal) * X.scaleFun t₂ h₂ u v)
    (hv : u v ≠ ⊥) :
    ConvexOn ℝ (Ioi 0) fun t => (X.rayFun u v t).toReal := by
  have hv1 : X.scaleFun 1 one_pos u v ≠ ⊥ := by rwa [scaleFun_one]
  have hfin : ∀ (t : ℝ) (ht : 0 < t), X.scaleFun t ht u v ≠ ⊥ :=
    scaleFun_ne_bot_of_scaleFun_convex hconv one_pos hv1
  have htop' : ∀ (t : ℝ) (ht : 0 < t), X.scaleFun t ht u v ≠ ⊤ := fun t ht =>
    ProjBerk.ereal_coe_mul_ne_top ht.le (htop _)
  refine ⟨convex_Ioi 0, fun x hx y hy α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  have hxy : 0 < α * x + β * y := by
    rcases hα.lt_or_eq with hα' | rfl
    · positivity
    · rw [zero_add] at hαβ
      subst hαβ
      simpa using hy'
  have hc := hconv hx' hy' hxy hα hβ hαβ rfl
  rw [rayFun_of_pos _ v hxy, rayFun_of_pos _ v hx', rayFun_of_pos _ v hy',
    ← EReal.coe_le_coe_iff, EReal.coe_toReal (htop' _ hxy) (hfin _ hxy), EReal.coe_add,
    EReal.coe_mul, EReal.coe_mul, EReal.coe_toReal (htop' _ hx') (hfin _ hx'),
    EReal.coe_toReal (htop' _ hy') (hfin _ hy')]
  exact hc

/-- **Legendre reconstruction along convex rays** (`lem:hm-convex-ray-reconstruction`(2); BJ22
`thm:homogpsh`, FHX `eq:Legendre-reconstruction`). Let `u : 𝒳^an → [-∞, ∞)` with
`u ≤ u(⋆) ∈ ℝ`, whose scaling rays `t ↦ (t · u)(v)` satisfy the convexity inequality. Then
`u = sup_{λ < u(⋆)} (û_λ + λ)` pointwise. This needs no plurisubharmonicity of `u`; it applies to
decreasing limits of psh functions before they are known to be psh. -/
theorem eq_iSup_legendreSlice_of_scaleFun_convex (htop : ∀ v, u v ≠ ⊤)
    (hconv : ∀ (v : X.an) {t₁ t₂ t : ℝ} (h₁ : 0 < t₁) (h₂ : 0 < t₂) (ht : 0 < t) {α β : ℝ},
      0 ≤ α → 0 ≤ β → α + β = 1 → t = α * t₁ + β * t₂ →
        X.scaleFun t ht u v ≤
          (α : EReal) * X.scaleFun t₁ h₁ u v + (β : EReal) * X.scaleFun t₂ h₂ u v)
    (hle : ∀ v, u v ≤ u X.triv) (hb : u X.triv ≠ ⊥) (v : X.an) :
    u v = ⨆ (lam : ℝ) (_ : (lam : EReal) < u X.triv), X.legendreSlice u lam v + (lam : EReal) := by
  refine le_antisymm ?_ (iSup₂_le fun lam _ => legendreSlice_add_le u lam v)
  by_cases hv : u v = ⊥
  · rw [hv]
    exact bot_le
  have hv1 : X.scaleFun 1 one_pos u v ≠ ⊥ := by rwa [scaleFun_one]
  have hfin : ∀ (t : ℝ) (ht : 0 < t), X.scaleFun t ht u v ≠ ⊥ :=
    scaleFun_ne_bot_of_scaleFun_convex (hconv v) one_pos hv1
  have htop' : ∀ (t : ℝ) (ht : 0 < t), X.scaleFun t ht u v ≠ ⊤ := fun t ht =>
    ProjBerk.ereal_coe_mul_ne_top ht.le (htop _)
  set G : ℝ → ℝ := fun t => (X.rayFun u v t).toReal with hG
  have hGt : ∀ (t : ℝ) (ht : 0 < t), (G t : EReal) = X.scaleFun t ht u v := fun t ht => by
    rw [hG]
    simp only
    rw [rayFun_of_pos u v ht, EReal.coe_toReal (htop' t ht) (hfin t ht)]
  obtain ⟨c, hc⟩ := exists_subgradient_one_of_convexOn_Ioi
    (convexOn_rayFun_of_scaleFun_convex htop (hconv v) hv)
  set b : ℝ := (u X.triv).toReal
  have hbb : (b : EReal) = u X.triv := EReal.coe_toReal (htop _) hb
  rw [← hbb]
  -- `G t ≤ t b`
  have hGb : ∀ t : ℝ, 0 < t → G t ≤ t * b := fun t ht => by
    have hbound : X.scaleFun t ht u v ≤ (t : EReal) * u X.triv :=
      ProjBerk.ereal_coe_mul_monotone ht.le (hle _)
    rw [← hbb, ← hGt t ht, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hbound
    exact hbound
  -- the subgradient is `≤ b`
  have hcb : c ≤ b := by
    by_contra hcb
    rw [not_le] at hcb
    set t : ℝ := Max.max 1 ((c - G 1) / (c - b) + 1) with ht
    have htpos : 0 < t := lt_of_lt_of_le one_pos (le_max_left _ _)
    have h₁ : (c - G 1) / (c - b) < t := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
    rw [div_lt_iff₀ (by linarith)] at h₁
    have h₂ := hc t htpos
    have h₃ := hGb t htpos
    nlinarith
  have hG1 : (G 1 : EReal) = u v := by rw [hGt 1 one_pos, scaleFun_one]
  refine ProjBerk.ereal_le_of_forall_pos_le_add fun ε hε => ?_
  have hlam : ((c - ε : ℝ) : EReal) < (b : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)
  refine le_trans ?_ (add_le_add (le_iSup₂ (f := fun (lam : ℝ) (_ : (lam : EReal) < (b : EReal)) =>
    X.legendreSlice u lam v + (lam : EReal)) (c - ε) hlam) le_rfl)
  -- `û_{c - ε}(v) ≥ G 1 - c`
  have hslice : ((G 1 - c : ℝ) : EReal) ≤ X.legendreSlice u (c - ε) v := by
    refine le_iInf₂ fun t ht => ?_
    have hx := hfin t ht
    have hx' := htop' t ht
    rw [scaleFun_apply] at hx hx' ⊢
    have hxb : u (X.rpow t⁻¹ (inv_pos.2 ht) v) ≠ ⊥ := fun h0 => hx (by
      rw [h0, EReal.coe_mul_bot_of_pos ht])
    have hxt : u (X.rpow t⁻¹ (inv_pos.2 ht) v) ≠ ⊤ := htop _
    have hGt' := hGt t ht
    rw [scaleFun_apply] at hGt'
    lift u (X.rpow t⁻¹ (inv_pos.2 ht) v) to ℝ using ⟨hxt, hxb⟩ with x hx''
    rw [← EReal.coe_mul, EReal.coe_eq_coe_iff] at hGt'
    rw [← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    have := hc t ht
    nlinarith
  rw [← hG1]
  calc (G 1 : EReal) = ((G 1 - c : ℝ) : EReal) + ((c - ε : ℝ) : EReal) + (ε : EReal) := by
        rw [← EReal.coe_add, ← EReal.coe_add]
        congr 1
        ring
    _ ≤ X.legendreSlice u (c - ε) v + ((c - ε : ℝ) : EReal) + (ε : EReal) :=
      add_le_add (add_le_add hslice le_rfl) le_rfl

end ConvexRays

/-! ### Decreasing limits of psh functions -/

section DecreasingLimits

/-- A nontrivial infimum of psh functions is `< +∞`, satisfies the maximum principle, and is
finite at `⋆`. -/
private theorem iInf_isPSH_facts {ι : Type*} [Nonempty ι] {θs : ι → Fin r → ℝ}
    {ψ : ι → X.an → EReal} (hψ : ∀ i, X.IsPSH (θs i) (ψ i)) {w : X.an → EReal}
    (hw : ∀ v, w v = ⨅ i, ψ i v) (hne : ∃ v, w v ≠ ⊥) :
    (∀ v, w v ≠ ⊤) ∧ (∀ v, w v ≤ w X.triv) ∧ w X.triv ≠ ⊥ := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have htop : ∀ v, w v ≠ ⊤ := fun v => by
    rw [hw]
    exact ne_top_of_le_ne_top (FSSystemC.IsPSH.ne_top (hψ i₀) v) (iInf_le _ i₀)
  have hle : ∀ v, w v ≤ w X.triv := fun v => by
    rw [hw v, hw X.triv]
    exact le_iInf fun i => (iInf_le _ i).trans ((hψ i).le_apply_triv v)
  refine ⟨htop, hle, ?_⟩
  obtain ⟨v, hv⟩ := hne
  exact ne_bot_of_le_ne_bot hv (hle v)

/-- The convexity inequality along scaling rays passes to decreasing limits of psh functions with
varying classes (`lem:nn-ray-limit`(1)). -/
private theorem scaleFun_convex_of_iInf {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] {θs : ι → Fin r → ℝ} {ψ : ι → X.an → EReal} (hψ : ∀ i, X.IsPSH (θs i) (ψ i))
    (hanti : ∀ v, Antitone fun i => ψ i v) {w : X.an → EReal} (hw : ∀ v, w v = ⨅ i, ψ i v)
    (hwtop : ∀ v, w v ≠ ⊤) (v : X.an) {t₁ t₂ t : ℝ} (h₁ : 0 < t₁) (h₂ : 0 < t₂) (ht : 0 < t)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) (hteq : t = α * t₁ + β * t₂) :
    X.scaleFun t ht w v ≤
      (α : EReal) * X.scaleFun t₁ h₁ w v + (β : EReal) * X.scaleFun t₂ h₂ w v := by
  have hw' : w = fun v => ⨅ i, ψ i v := funext hw
  have htop : ∀ (s : ℝ) (hs : 0 < s), X.scaleFun s hs w v ≠ ⊤ := fun s hs =>
    ProjBerk.ereal_coe_mul_ne_top hs.le (hwtop _)
  have hlim : ∀ (s : ℝ) (hs : 0 < s),
      Tendsto (fun i => X.scaleFun s hs (ψ i) v) atTop (𝓝 (X.scaleFun s hs w v)) := by
    intro s hs
    rw [hw', scaleFun_iInf]
    exact tendsto_atTop_iInf fun i j hij => scaleFun_mono hs (fun x => hanti x hij) v
  have hsum := ProjBerk.tendsto_ereal_add
    (ProjBerk.tendsto_ereal_coe_mul (hlim t₁ h₁) α)
    (ProjBerk.tendsto_ereal_coe_mul (hlim t₂ h₂) β)
    (ProjBerk.ereal_coe_mul_ne_top hα (htop _ _))
    (ProjBerk.ereal_coe_mul_ne_top hβ (htop _ _))
  refine ge_of_tendsto hsum (Eventually.of_forall fun i => ?_)
  calc
    X.scaleFun t ht w v ≤ X.scaleFun t ht (ψ i) v :=
      scaleFun_mono ht (fun x => (hw x).trans_le (iInf_le _ i)) v
    _ ≤ _ := (hψ i).scaleFun_convex v h₁ h₂ ht hα hβ hαβ hteq

variable [IsAlgClosed k]

/-- **Slices of a decreasing limit** (`lem:hm-limit-slices`): if `(uᵢ)` is a decreasing net with
`uᵢ ∈ PSH(𝒳, θᵢ)`, `θᵢ → θ` (any `θ ∈ ℝ^r`) and limit `w`, then `ŵ_λ ∈ PSH_hom(𝒳, θ)` for every
real `λ < w(⋆)`: the slices `(ûᵢ)_λ ∈ PSH_hom(𝒳, θᵢ)` decrease to `ŵ_λ`, and PSH2 holds for
homogeneous nets (`thm:nn-psh2-hom`, `MultiModel.isPSHHom_of_antitone`). -/
theorem isPSHHom_legendreSlice_of_antitone {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] {θs : ι → Fin r → ℝ} {θ : Fin r → ℝ} (hθ : Tendsto θs atTop (𝓝 θ))
    {ψ : ι → X.an → EReal} (hψ : ∀ i, X.IsPSH (θs i) (ψ i))
    (hanti : ∀ v, Antitone fun i => ψ i v) {w : X.an → EReal} (hw : ∀ v, w v = ⨅ i, ψ i v)
    {lam : ℝ} (hlam : (lam : EReal) < w X.triv) : X.IsPSHHom θ (X.legendreSlice w lam) := by
  have hψslice : ∀ i, X.IsPSHHom (θs i) (X.legendreSlice (ψ i) lam) := fun i =>
    (hψ i).isPSHHom_legendreSlice (hlam.le.trans ((hw X.triv).trans_le (iInf_le _ i)))
  refine isPSHHom_of_antitone hθ hψslice
    (fun v i j hij => legendreSlice_mono (fun x => hanti x hij) lam v) fun v => ?_
  -- homogenization commutes with infima, and so does the real translate by `-λ`
  rw [show w = fun v => ⨅ i, ψ i v from funext hw]
  simp only [legendreSlice_def, ereal_sub_coe_eq_add_coe_neg, ereal_iInf_add_coe]
  exact congrFun (homogenization_iInf _) v

/-! ### PSH2 below a homogeneous majorant (`thm:hm-psh2-hom-majorant`) -/

/-- **PSH2 below a homogeneous majorant** (**`thm:hm-psh2-hom-majorant`**). Let `(uᵢ)` be a
decreasing net with `uᵢ ∈ PSH(𝒳, θᵢ)` and `θᵢ → θ ∈ ℝ^r` (any `θ`), with limit `w ≢ -∞`. If some
`Ψ ∈ PSH_hom(𝒳, θ)` dominates every Legendre slice `ŵ_λ`, `λ < w(⋆)` (equivalently, the slope of
`w` at infinity), then `w ∈ PSH(𝒳, θ)`.

With `b = w(⋆)` and the shifted slices `φ_μ = ŵ_{b + μ} ∈ PSH_hom(𝒳, θ)` (`μ < 0`), the functions
`U_n = max {Ψ - n, max_j (φ_{j 2^{-n}} + (j + 1) 2^{-n})}` on the dyadic grid of FHX
Proposition 7.5 (`prop:homogeneous-slices`, `EnvelopeProperty.SliceGrid`) satisfy termwise
domination, so `U = inf_n U_n` is `θ`-psh (`thm:nn-hom-max-diagonal`); Legendre reconstruction of
`w` (`eq_iSup_legendreSlice_of_scaleFun_convex`) gives `U = w - b`. -/
theorem isPSH_of_antitone_of_homMajorant {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] {θs : ι → Fin r → ℝ} {θ : Fin r → ℝ} (hθ : Tendsto θs atTop (𝓝 θ))
    {ψ : ι → X.an → EReal} (hψ : ∀ i, X.IsPSH (θs i) (ψ i))
    (hanti : ∀ v, Antitone fun i => ψ i v) {w : X.an → EReal} (hw : ∀ v, w v = ⨅ i, ψ i v)
    (hne : ∃ v, w v ≠ ⊥) {Ψ : X.an → EReal} (hΨ : X.IsPSHHom θ Ψ)
    (hmaj : ∀ lam : ℝ, (lam : EReal) < w X.triv → ∀ v, X.legendreSlice w lam v ≤ Ψ v) :
    X.IsPSH θ w := by
  classical
  obtain ⟨hwtop, hwle, hwb⟩ := iInf_isPSH_facts hψ hw hne
  set b : ℝ := (w X.triv).toReal
  have hb : (b : EReal) = w X.triv := EReal.coe_toReal (hwtop _) hwb
  -- Legendre reconstruction of the limit
  have hrec : ∀ v, w v = ⨆ (lam : ℝ) (_ : (lam : EReal) < w X.triv),
      X.legendreSlice w lam v + (lam : EReal) := fun v =>
    eq_iSup_legendreSlice_of_scaleFun_convex hwtop
      (fun v => scaleFun_convex_of_iInf hψ hanti hw hwtop v) hwle hwb v
  -- the shifted slices `φ_μ = ŵ_{b + μ}`, `μ < 0`
  let φ : ℝ → X.an → EReal := fun μ => X.legendreSlice w (μ + b)
  have hμ : ∀ μ : ℝ, μ < 0 → ((μ + b : ℝ) : EReal) < w X.triv := fun μ hμ' => by
    rw [← hb, EReal.coe_lt_coe_iff]
    linarith
  have hφP : ∀ μ : ℝ, μ < 0 → X.IsPSHHom θ (φ μ) := fun μ hμ' =>
    isPSHHom_legendreSlice_of_antitone hθ hψ hanti hw (hμ μ hμ')
  have hφanti : ∀ μ μ' : ℝ, μ ≤ μ' → φ μ' ≤ φ μ := fun μ μ' h =>
    legendreSlice_antitone w (by linarith : μ + b ≤ μ' + b)
  have hφΨ : ∀ μ : ℝ, μ < 0 → φ μ ≤ Ψ := fun μ hμ' v => hmaj _ (hμ μ hμ') v
  -- the dyadic approximants `U_n` and their limit `U`
  let Un : ℕ → X.an → EReal := fun n v => (SliceGrid.index n).sup fun k =>
    SliceGrid.term Ψ φ n k v + (SliceGrid.const n k : EReal)
  let U : X.an → EReal := fun v => ⨅ n, Un n v
  -- lower bound `w - b ≤ U_n`
  have hlow : ∀ n v, w v + ((-b : ℝ) : EReal) ≤ Un n v := by
    intro n v
    rw [hrec v]
    simp only [ereal_iSup_add_coe]
    refine iSup₂_le fun lam hlam => ?_
    obtain ⟨μ, rfl⟩ : ∃ μ : ℝ, lam = μ + b := ⟨lam - b, by ring⟩
    have hμ0 : μ < 0 := by
      rw [← hb, EReal.coe_lt_coe_iff] at hlam
      linarith
    calc X.legendreSlice w (μ + b) v + ((μ + b : ℝ) : EReal) + ((-b : ℝ) : EReal)
        = φ μ v + (μ : EReal) := by
          show _ = X.legendreSlice w (μ + b) v + (μ : EReal)
          rw [add_assoc, ← EReal.coe_add, show μ + b + -b = μ by ring]
      _ ≤ Un n v := SliceGrid.le_sup hφanti hφΨ hμ0 n v
  -- upper bound `U ≤ w - b`
  have hF : ∀ μ : ℝ, μ < 0 → ∀ v, φ μ v + (μ : EReal) ≤ w v + ((-b : ℝ) : EReal) := by
    intro μ _ v
    calc φ μ v + (μ : EReal)
        = X.legendreSlice w (μ + b) v + ((μ + b : ℝ) : EReal) + ((-b : ℝ) : EReal) := by
          show X.legendreSlice w (μ + b) v + (μ : EReal) = _
          rw [add_assoc, ← EReal.coe_add, show μ + b + -b = μ by ring]
      _ ≤ w v + ((-b : ℝ) : EReal) := add_le_add (legendreSlice_add_le w (μ + b) v) le_rfl
  have hUle : ∀ v, U v ≤ w v + ((-b : ℝ) : EReal) := fun v =>
    ereal_le_of_forall_le_max_neg_add fun n => (iInf_le _ n).trans
      (SliceGrid.sup_le_max (fun v => hΨ.nonpos v) hF n v)
  -- `U` is `θ`-psh (`thm:nn-hom-max-diagonal`)
  have hUpsh : X.IsPSH θ U := by
    refine isPSH_of_dominated_homMax_seq (θs := fun _ => θ) tendsto_const_nhds SliceGrid.index
      (SliceGrid.term Ψ φ) SliceGrid.const (fun n k hk => ?_)
      (fun n k hk => SliceGrid.const_nonpos hk) (SliceGrid.dominated hφanti hφΨ)
      (fun v => rfl) ⟨X.triv, ?_⟩
    · rcases SliceGrid.mem_index.1 hk with rfl | ⟨j, -, hj, rfl⟩
      · exact hΨ
      · exact hφP _ (SliceGrid.term_some_neg hj)
    · have h : w X.triv + ((-b : ℝ) : EReal) ≤ U X.triv := le_iInf fun n => hlow n X.triv
      rw [← hb, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at h
      exact ne_bot_of_le_ne_bot EReal.zero_ne_bot h
  -- `w = U + b`
  have hUw : ∀ v, U v = w v + ((-b : ℝ) : EReal) := fun v =>
    le_antisymm (hUle v) (le_iInf fun n => hlow n v)
  have hw' : w = fun v => U v + (b : EReal) := by
    funext v
    show w v = U v + (b : EReal)
    rw [hUw v, add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]
  rw [hw']
  exact hUpsh.add_const b

/-- **Majorants from the envelope property** (`cor:hm-majorant-of-ep`): under `EP_𝒳(θ)`, the
slices of a nontrivial decreasing limit as in `isPSH_of_antitone_of_homMajorant` have the
homogeneous `θ`-psh majorant `Ψ = (sup_{λ < w(⋆)} ŵ_λ)^⋆`. Together with
`isPSH_of_antitone_of_homMajorant` this recovers `isPSH_of_antitone_of_hasEnvelopeProperty`. -/
theorem exists_homMajorant_of_hasEnvelopeProperty {θ : Fin r → ℝ}
    (hEP : X.HasEnvelopeProperty θ) {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] {θs : ι → Fin r → ℝ} (hθ : Tendsto θs atTop (𝓝 θ))
    {ψ : ι → X.an → EReal} (hψ : ∀ i, X.IsPSH (θs i) (ψ i))
    (hanti : ∀ v, Antitone fun i => ψ i v) {w : X.an → EReal} (hw : ∀ v, w v = ⨅ i, ψ i v)
    (hne : ∃ v, w v ≠ ⊥) :
    ∃ Ψ : X.an → EReal, X.IsPSHHom θ Ψ ∧
      ∀ lam : ℝ, (lam : EReal) < w X.triv → ∀ v, X.legendreSlice w lam v ≤ Ψ v := by
  obtain ⟨hwtop, -, hwb⟩ := iInf_isPSH_facts hψ hw hne
  let Λ := {lam : ℝ // (lam : EReal) < w X.triv}
  have : Nonempty Λ := by
    obtain ⟨lam, -, hlam⟩ := EReal.lt_iff_exists_real_btwn.1 (bot_lt_iff_ne_bot.2 hwb)
    exact ⟨⟨lam, hlam⟩⟩
  have hslice : ∀ lam : Λ, X.IsPSHHom θ (X.legendreSlice w lam.1) := fun lam =>
    isPSHHom_legendreSlice_of_antitone hθ hψ hanti hw lam.2
  refine ⟨uscReg fun v => ⨆ lam : Λ, X.legendreSlice w lam.1 v,
    ⟨FSSystemC.HasEnvelopeProperty.isPSH_uscReg_iSup hEP (fun lam => (hslice lam).isPSH)
      ⟨0, fun lam v => ((hslice lam).nonpos v).trans_eq EReal.coe_zero.symm⟩,
      IsScaleHomogeneous.uscReg_iSup fun lam => (hslice lam).isScaleHomogeneous⟩,
    fun lam hlam v => ?_⟩
  exact (le_iSup (fun lam : Λ => X.legendreSlice w lam.1 v) ⟨lam, hlam⟩).trans
    (le_uscReg (fun v => ⨆ lam : Λ, X.legendreSlice w lam.1 v) v)

/-- **PSH2 at classes carrying the constant `0`** (`cor:hm-majorant-zero`): if `0 ∈ PSH(𝒳, θ)`,
then every nontrivial decreasing limit of `θᵢ`-psh functions with `θᵢ → θ` is `θ`-psh. The majorant
of `isPSH_of_antitone_of_homMajorant` is `Ψ = 0`, since `ŵ_λ ∈ PSH_hom(𝒳, θ)` is `≤ 0`. -/
theorem isPSH_of_antitone_of_isPSH_zero {θ : Fin r → ℝ} (h0 : X.IsPSH θ fun _ => 0)
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] {θs : ι → Fin r → ℝ}
    (hθ : Tendsto θs atTop (𝓝 θ)) {ψ : ι → X.an → EReal} (hψ : ∀ i, X.IsPSH (θs i) (ψ i))
    (hanti : ∀ v, Antitone fun i => ψ i v) {w : X.an → EReal} (hw : ∀ v, w v = ⨅ i, ψ i v)
    (hne : ∃ v, w v ≠ ⊥) : X.IsPSH θ w :=
  isPSH_of_antitone_of_homMajorant hθ hψ hanti hw hne (Ψ := fun _ => 0)
    ⟨h0, fun _ _ _ => (mul_zero _).symm⟩
    fun _ hlam v => (isPSHHom_legendreSlice_of_antitone hθ hψ hanti hw hlam).nonpos v

end DecreasingLimits

end MultiModel
end EnvelopeProperty
