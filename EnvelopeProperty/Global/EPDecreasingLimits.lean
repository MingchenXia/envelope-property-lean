/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.MainTheorem

/-!
# Decreasing psh limits under the envelope property

This file proves that on a model `𝒳` with the envelope property at a class `θ ∈ ℝ^r`, the limit
`w` of a decreasing net `ψᵢ ∈ PSH(𝒳, θᵢ)` with `θᵢ → θ` lies in `PSH(𝒳, θ)` unless `w ≡ -∞`
(`MultiModel.isPSH_of_antitone_of_hasEnvelopeProperty`); the envelope property is used only at
the limiting class. The proof writes `w` as the supremum of its translated Legendre slices, which
are homogeneous psh functions of class `θ`. Blueprint: `lem:nn-ray-limit`, `thm:nn-psh2-of-ep`
(`nonnef.tex`, with the details in `ep-decreasing-limits.tex`).

On a unibranch model this is FHX Corollary 8.4 (`cor:unibranch-decreasing-stability`):
`MultiModel.isPSH_of_antitone_of_isUnibranch_of_forall_countable` assumes the three inputs
`LocalPositivity`, `BlowupFibreConstancy` and `SmoothEnvelopeCharZero` at the countable
algebraically closed subfields of `k`, as
`MultiModel.hasEnvelopeProperty_of_isUnibranch_of_forall_countable` does;
`EnvelopeProperty/MainTheorem.lean` states it without hypotheses
(`MultiModel.isPSH_of_antitone_of_isUnibranch`).
-/

open scoped NNReal ENNReal Topology
open Set Topology Filter

noncomputable section

namespace EnvelopeProperty
namespace MultiModel

universe u

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r}

section Rays

variable {ι : Type u} {θs : ι → Fin r → ℝ} {ψ : ι → X.an → EReal}
  (hψ : ∀ i, X.IsPSH (θs i) (ψ i))

include hψ

/-- An infimum of psh functions has no value `+∞`. -/
theorem iInf_psh_ne_top [Nonempty ι] (v : X.an) : (⨅ i, ψ i v) ≠ ⊤ := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  exact ne_top_of_le_ne_top (FSSystemC.IsPSH.ne_top (hψ i) v) (iInf_le _ i)

/-- The maximum principle survives arbitrary infima. -/
theorem iInf_psh_le_triv (v : X.an) : (⨅ i, ψ i v) ≤ ⨅ i, ψ i X.triv := by
  exact le_iInf fun i => (iInf_le _ i).trans ((hψ i).le_apply_triv v)

/-- A nontrivial infimum is finite at the trivial valuation. -/
theorem iInf_psh_triv_ne_bot (hne : ∃ v, (⨅ i, ψ i v) ≠ ⊥) :
    (⨅ i, ψ i X.triv) ≠ ⊥ := by
  obtain ⟨v, hv⟩ := hne
  exact ne_bot_of_le_ne_bot hv (iInf_psh_le_triv hψ v)

variable [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  (hanti : ∀ v, Antitone fun i => ψ i v)

include hanti

/-- Convexity of scaling rays passes to a decreasing psh net, with varying classes. -/
theorem scaleFun_iInf_psh_convex (v : X.an) {t₁ t₂ t : ℝ}
    (h₁ : 0 < t₁) (h₂ : 0 < t₂) (ht : 0 < t) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hteq : t = α * t₁ + β * t₂) :
    X.scaleFun t ht (fun v => ⨅ i, ψ i v) v ≤
      (α : EReal) * X.scaleFun t₁ h₁ (fun v => ⨅ i, ψ i v) v +
        (β : EReal) * X.scaleFun t₂ h₂ (fun v => ⨅ i, ψ i v) v := by
  have htop : ∀ (s : ℝ) (hs : 0 < s),
      X.scaleFun s hs (fun v => ⨅ i, ψ i v) v ≠ ⊤ := fun s hs =>
    ProjBerk.ereal_coe_mul_ne_top hs.le (iInf_psh_ne_top hψ _)
  have hlim : ∀ (s : ℝ) (hs : 0 < s),
      Tendsto (fun i => X.scaleFun s hs (ψ i) v) atTop
        (𝓝 (X.scaleFun s hs (fun v => ⨅ i, ψ i v) v)) := by
    intro s hs
    rw [scaleFun_iInf]
    exact tendsto_atTop_iInf fun i j hij =>
      scaleFun_mono hs (fun w => hanti w hij) v
  have hsum := ProjBerk.tendsto_ereal_add
    (ProjBerk.tendsto_ereal_coe_mul (hlim t₁ h₁) α)
    (ProjBerk.tendsto_ereal_coe_mul (hlim t₂ h₂) β)
    (ProjBerk.ereal_coe_mul_ne_top hα (htop _ _))
    (ProjBerk.ereal_coe_mul_ne_top hβ (htop _ _))
  refine ge_of_tendsto hsum (Eventually.of_forall fun i => ?_)
  calc
    X.scaleFun t ht (fun v => ⨅ i, ψ i v) v ≤ X.scaleFun t ht (ψ i) v :=
      scaleFun_mono ht (fun _ => iInf_le _ i) v
    _ ≤ _ := (hψ i).scaleFun_convex v h₁ h₂ ht hα hβ hαβ hteq

/-- Finiteness at one point of a limiting ray forces finiteness everywhere on it. -/
theorem scaleFun_iInf_psh_ne_bot {v : X.an} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hv : X.scaleFun t₀ ht₀ (fun v => ⨅ i, ψ i v) v ≠ ⊥)
    (t : ℝ) (ht : 0 < t) :
    X.scaleFun t ht (fun v => ⨅ i, ψ i v) v ≠ ⊥ := by
  intro hbot
  have hα : 0 < t₀ / (t + t₀) := div_pos ht₀ (by linarith)
  have hβ : 0 ≤ t / (t + t₀) := (div_pos ht (by linarith)).le
  have h₂ : 0 < t₀ ^ 2 / t := by positivity
  have hsum : t₀ / (t + t₀) + t / (t + t₀) = 1 := by
    rw [← add_div, add_comm, div_self (by linarith)]
  have hconv := scaleFun_iInf_psh_convex hψ hanti v ht h₂ ht₀ hα.le hβ hsum
    (by field_simp)
  rw [hbot, EReal.coe_mul_bot_of_pos hα, EReal.bot_add, le_bot_iff] at hconv
  exact hv hconv

/-- The real-valued part of a non-bottom limiting ray is convex. -/
theorem convexOn_rayFun_iInf_psh {v : X.an} (hv : (⨅ i, ψ i v) ≠ ⊥) :
    ConvexOn ℝ (Ioi 0) fun t => (X.rayFun (fun v => ⨅ i, ψ i v) v t).toReal := by
  have hv1 : X.scaleFun 1 one_pos (fun v => ⨅ i, ψ i v) v ≠ ⊥ := by
    rwa [scaleFun_one]
  have hfin : ∀ (t : ℝ) (ht : 0 < t),
      X.scaleFun t ht (fun v => ⨅ i, ψ i v) v ≠ ⊥ :=
    scaleFun_iInf_psh_ne_bot hψ hanti one_pos hv1
  have htop : ∀ (t : ℝ) (ht : 0 < t),
      X.scaleFun t ht (fun v => ⨅ i, ψ i v) v ≠ ⊤ := fun t ht =>
    ProjBerk.ereal_coe_mul_ne_top ht.le (iInf_psh_ne_top hψ _)
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
  have hconv := scaleFun_iInf_psh_convex hψ hanti v hx' hy' hxy hα hβ hαβ rfl
  rw [rayFun_of_pos _ v hxy, rayFun_of_pos _ v hx', rayFun_of_pos _ v hy',
    ← EReal.coe_le_coe_iff, EReal.coe_toReal (htop _ hxy) (hfin _ hxy), EReal.coe_add,
    EReal.coe_mul, EReal.coe_mul, EReal.coe_toReal (htop _ hx') (hfin _ hx'),
    EReal.coe_toReal (htop _ hy') (hfin _ hy')]
  exact hconv

/-- Legendre reconstruction holds for a nontrivial decreasing psh limit before
knowing that the limit itself is psh. -/
theorem iInf_psh_eq_iSup_legendreSlice (hne : ∃ v, (⨅ i, ψ i v) ≠ ⊥) (v : X.an) :
    (⨅ i, ψ i v) = ⨆ (lam : ℝ) (_ : (lam : EReal) < ⨅ i, ψ i X.triv),
      X.legendreSlice (fun v => ⨅ i, ψ i v) lam v + (lam : EReal) := by
  let u : X.an → EReal := fun v => ⨅ i, ψ i v
  change u v = ⨆ (lam : ℝ) (_ : (lam : EReal) < u X.triv),
    X.legendreSlice u lam v + (lam : EReal)
  refine le_antisymm ?_ (iSup₂_le fun lam _ => legendreSlice_add_le u lam v)
  by_cases hv : u v = ⊥
  · rw [hv]
    exact bot_le
  have hv1 : X.scaleFun 1 one_pos u v ≠ ⊥ := by rwa [scaleFun_one]
  have hfin : ∀ (t : ℝ) (ht : 0 < t), X.scaleFun t ht u v ≠ ⊥ :=
    scaleFun_iInf_psh_ne_bot hψ hanti one_pos hv1
  have htop : ∀ (t : ℝ) (ht : 0 < t), X.scaleFun t ht u v ≠ ⊤ := fun t ht =>
    ProjBerk.ereal_coe_mul_ne_top ht.le (iInf_psh_ne_top hψ _)
  set G : ℝ → ℝ := fun t => (X.rayFun u v t).toReal with hG
  have hGt : ∀ (t : ℝ) (ht : 0 < t), (G t : EReal) = X.scaleFun t ht u v := fun t ht => by
    rw [hG]
    simp only
    rw [rayFun_of_pos u v ht, EReal.coe_toReal (htop t ht) (hfin t ht)]
  obtain ⟨c, hc⟩ := exists_subgradient_one_of_convexOn_Ioi
    (convexOn_rayFun_iInf_psh hψ hanti hv)
  have hub : u X.triv ≠ ⊥ := iInf_psh_triv_ne_bot hψ hne
  have hut : u X.triv ≠ ⊤ := iInf_psh_ne_top hψ _
  lift u X.triv to ℝ using ⟨hut, hub⟩ with b hb
  have hGb : ∀ t : ℝ, 0 < t → G t ≤ t * b := fun t ht => by
    have hbound : X.scaleFun t ht u v ≤ (t : EReal) * u X.triv :=
      ProjBerk.ereal_coe_mul_monotone ht.le (iInf_psh_le_triv hψ _)
    rw [← hb, ← hGt t ht, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hbound
    exact hbound
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
  have hslice : ((G 1 - c : ℝ) : EReal) ≤ X.legendreSlice u (c - ε) v := by
    refine le_iInf₂ fun t ht => ?_
    have hx := hfin t ht
    have hx' := htop t ht
    rw [scaleFun_apply] at hx hx' ⊢
    have hxb : u (X.rpow t⁻¹ (inv_pos.2 ht) v) ≠ ⊥ := fun h0 => hx (by
      rw [h0, EReal.coe_mul_bot_of_pos ht])
    have hxt : u (X.rpow t⁻¹ (inv_pos.2 ht) v) ≠ ⊤ := iInf_psh_ne_top hψ _
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

end Rays

/-- Legendre slices commute with arbitrary pointwise infima, including real translation. -/
theorem legendreSlice_iInf {ι : Sort*} (ψ : ι → X.an → EReal) (lam : ℝ) :
    X.legendreSlice (fun v => ⨅ i, ψ i v) lam =
      fun v => ⨅ i, X.legendreSlice (ψ i) lam v := by
  simp only [legendreSlice_def, ereal_sub_coe_eq_add_coe_neg, ereal_iInf_add_coe]
  exact homogenization_iInf _

section EnvelopeProperty

variable [IsAlgClosed k]
  {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  {θs : ι → Fin r → ℝ} {θ : Fin r → ℝ} {ψ : ι → X.an → EReal}

/-- **PSH2 under the envelope property**, at any real class: a nontrivial decreasing
net of psh functions with converging classes has a psh limit. The envelope property
is needed only at the limiting class. -/
theorem isPSH_of_antitone_of_hasEnvelopeProperty
    (hEP : X.HasEnvelopeProperty θ) (hθ : Tendsto θs atTop (𝓝 θ))
    (hψ : ∀ i, X.IsPSH (θs i) (ψ i)) (hanti : ∀ v, Antitone fun i => ψ i v)
    {w : X.an → EReal} (hw : ∀ v, w v = ⨅ i, ψ i v)
    (hne : ∃ v, w v ≠ ⊥) : X.IsPSH θ w := by
  have hne' : ∃ v, (⨅ i, ψ i v) ≠ ⊥ := by simpa only [← hw] using hne
  have hwt : w X.triv ≠ ⊤ := by rw [hw]; exact iInf_psh_ne_top hψ _
  have hwb : w X.triv ≠ ⊥ := by rw [hw]; exact iInf_psh_triv_ne_bot hψ hne'
  let b : ℝ := (w X.triv).toReal
  have hb : (b : EReal) = w X.triv := EReal.coe_toReal hwt hwb
  let Λ := {lam : ℝ // lam < b}
  have : Nonempty Λ := ⟨⟨b - 1, by linarith⟩⟩
  have hbound : ∀ v, w v ≤ (b : EReal) := fun v => calc
    w v = ⨅ i, ψ i v := hw v
    _ ≤ ⨅ i, ψ i X.triv := iInf_psh_le_triv hψ v
    _ = w X.triv := (hw X.triv).symm
    _ = (b : EReal) := hb.symm
  have hslice : ∀ lam : Λ, X.IsPSHHom θ (X.legendreSlice w lam) := by
    intro lam
    have hψslice : ∀ i, X.IsPSHHom (θs i) (X.legendreSlice (ψ i) lam) := by
      intro i
      apply (hψ i).isPSHHom_legendreSlice
      calc
        (lam : EReal) ≤ (b : EReal) := EReal.coe_le_coe_iff.2 lam.2.le
        _ = w X.triv := hb
        _ = ⨅ i, ψ i X.triv := hw X.triv
        _ ≤ ψ i X.triv := iInf_le _ i
    refine isPSHHom_of_antitone hθ hψslice
      (fun v i j hij => legendreSlice_mono (fun x => hanti x hij) lam v) ?_
    intro v
    rw [show w = fun v => ⨅ i, ψ i v from funext hw, legendreSlice_iInf]
  have hreconstruct : ∀ v, w v = ⨆ lam : Λ, X.legendreSlice w lam v + (lam : EReal) := by
    intro v
    have h := iInf_psh_eq_iSup_legendreSlice hψ hanti hne' v
    rw [← hw v] at h
    simp only [show (fun v => ⨅ i, ψ i v) = w from (funext hw).symm, ← hw X.triv, ← hb,
      EReal.coe_lt_coe_iff] at h
    simpa only [Λ, iSup_subtype] using h
  have hpsh := FSSystemC.HasEnvelopeProperty.isPSH_uscReg_iSup hEP
    (fun lam : Λ => (hslice lam).isPSH.add_const lam)
    ⟨b, fun lam v => (legendreSlice_add_le w lam v).trans (hbound v)⟩
  have hwusc : UpperSemicontinuous w := by
    rw [show w = fun v => ⨅ i, ψ i v from funext hw]
    exact upperSemicontinuous_iInf fun i => FSSystemC.IsPSH.upperSemicontinuous (hψ i)
  rwa [show (fun v => ⨆ lam : Λ, X.legendreSlice w lam v + (lam : EReal)) = w from
    (funext hreconstruct).symm, uscReg_eq_self hwusc] at hpsh

/-- **FHX Corollary 8.4** (`cor:unibranch-decreasing-stability`) under the three inputs at the
countable subfields: on a unibranch model, the limit of a decreasing net `ψᵢ ∈ PSH(𝒳, θᵢ)` with
`θᵢ → θ`, if not identically `-∞`, lies in `PSH(𝒳, θ)`. The envelope property at `θ` is
`hasEnvelopeProperty_of_isUnibranch_of_forall_countable`. -/
theorem isPSH_of_antitone_of_isUnibranch_of_forall_countable
    (hLP : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      LocalPositivity k₀)
    (hFC : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀],
      BlowupFibreConstancy k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      [CharZero k₀], SmoothEnvelopeCharZero k₀)
    (hX : X.IsUnibranch) (hθ : Tendsto θs atTop (𝓝 θ))
    (hψ : ∀ i, X.IsPSH (θs i) (ψ i)) (hanti : ∀ v, Antitone fun i => ψ i v)
    {w : X.an → EReal} (hw : ∀ v, w v = ⨅ i, ψ i v) (hne : ∃ v, w v ≠ ⊥) :
    X.IsPSH θ w :=
  isPSH_of_antitone_of_hasEnvelopeProperty
    (hasEnvelopeProperty_of_isUnibranch_of_forall_countable hLP hFC h₀ hX θ) hθ hψ hanti hw hne

end EnvelopeProperty

end MultiModel
end EnvelopeProperty
