/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.ComparisonShilov

/-!
# Divisorial comparison on `(ℙⁿ)^an` and the increasing-net criterion

This file proves, on the model `ProjBerk k n` of `(ℙⁿ)^an` over an algebraically closed, trivially
valued field `k` (`EnvelopeProperty.Projective.Basic`), the divisorial comparison theorem of
Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field* (BJ22,
Theorem 4.22, with Corollary 4.23) and the criterion for the envelope property by
increasing nets used by Fang–Han–Xia, *The envelope property for unibranch projective varieties*
(FHX, Proposition 2.4, `prop:EP-criterion`; the direction
"convergence of increasing nets ⇒ envelope property"). Divisorial points are those of
`def:pn-div` (`ProjBerk.IsDivisorial`). The blueprint nodes (`bj22.tex`) are `lem:bj-sup-pl`,
`thm:bj-divisorial-comparison` and `prop:bj-ep-criterion`.

## Main results

* `ProjBerk.IsRatPL.exists_finset_iSup_sub_eq` (`lem:bj-sup-pl`, BJ22 Lemma 4.26): for every
  rational PL function `f` there is a finite set `Σ` of divisorial points (containing `v_triv`)
  with `sup (u - f) = max_Σ (u - f)` for all `θ` and all `u ∈ PSH(θ)`; the comparison form is
  `ProjBerk.IsRatPL.exists_finset_le_of_le`. Writing `f = φ₁ - ψ₁` with `φ₁, ψ₁` finite rational
  FS functions, `Σ` is the Shilov set of `φ₁` (`ProjBerk.IsFiniteRatFS.exists_finset_iSup_sub_eq`),
  applied to `u_α + ψ₁` for a decreasing net `u_α ∈ H_ℚ(a_α)` with limit `u`
  (`ProjBerk.IsPSH.exists_finiteRatFS_net`); the maximum over the finite set `Σ` passes to the
  limit.
* `ProjBerk.IsPSH.le_of_forall_isDivisorial_le` (`thm:bj-divisorial-comparison`): if
  `u ∈ PSH(θ)`, `h` is usc with values in `[-∞, ∞)` and `u ≤ h` on `(ℙⁿ)^div`, then `u ≤ h`;
  `ProjBerk.IsPSH.eq_of_forall_isDivisorial_eq`: a psh function is determined by its values on
  `(ℙⁿ)^div`.
* `ProjBerk.IsPSH.eq_uscReg_iSup` (`prop:bj-ep-criterion`, second claim): if `U ∈ PSH(θ)`
  agrees with `sup_i uᵢ` on `(ℙⁿ)^div` for a bounded-above family in `PSH(θ)`, then
  `U = (sup_i uᵢ)^⋆`.
* `ProjBerk.hasEnvelopeProperty_of_forall_monotone` (`prop:bj-ep-criterion`): if every
  bounded-above increasing net in `PSH(θ)` admits `U ∈ PSH(θ)` equal to its supremum on
  `(ℙⁿ)^div`, then `θ` has the envelope property.

## Deviations from the blueprint

* The second claim of `prop:bj-ep-criterion` holds for arbitrary bounded-above families; neither
  monotonicity nor directedness is used. The nets in the hypothesis of
  `hasEnvelopeProperty_of_forall_monotone` are indexed by types in the universe of `k`.
* The converse (`rmk:bj-ep-criterion-converse`: envelope property ⇒ convergence on `(ℙⁿ)^div`,
  which needs BJ22 Theorem 5.6) is not formalized.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

namespace ProjBerk

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

/-! ### Suprema against PL functions (`lem:bj-sup-pl`) -/

/-- **Suprema against PL functions** (`lem:bj-sup-pl`, BJ22 Lemma 4.26): for every rational PL
function `f` there is a finite set `Σ ⊆ (ℙⁿ)^div` containing `v_triv` such that
`sup (u - f) = max_Σ (u - f)` for every `θ` and every `u ∈ PSH(θ)`. -/
theorem IsRatPL.exists_finset_iSup_sub_eq {f : ProjBerk k n → ℝ} (hf : IsRatPL f) :
    ∃ S : Finset (ProjBerk k n), triv ∈ S ∧ (∀ w ∈ S, w.IsDivisorial) ∧
      ∀ (θ : ℝ) (u : ProjBerk k n → EReal), IsPSH θ u →
        ⨆ v, (u v - (f v : EReal)) = S.sup fun v => u v - (f v : EReal) := by
  classical
  obtain ⟨a, b, φ₁, ψ₁, hφ₁, hψ₁, hf⟩ := hf
  obtain ⟨S, hS, hSdiv, hsup⟩ := hφ₁.exists_finset_iSup_sub_eq
  refine ⟨S, hS, hSdiv, fun θ u hu => le_antisymm (iSup_le fun v => ?_)
    (Finset.sup_le fun w _ => le_iSup (fun v => u v - (f v : EReal)) w)⟩
  obtain ⟨ι, _, _, _, c, uα, huα, -, -, -, hanti, -, hinf⟩ := hu.exists_finiteRatFS_net
  -- `u_α - f = (u_α + ψ₁) - φ₁`
  have hid : ∀ α v, uα α v - (f v : EReal) = (uα α v + ψ₁ v) - φ₁ v := fun α v => by
    obtain ⟨x, hx⟩ : ∃ x : ℝ, φ₁ v = x :=
      ⟨_, (EReal.coe_toReal (hφ₁.isFS.ne_top v) (hφ₁.2 v)).symm⟩
    obtain ⟨y, hy⟩ : ∃ y : ℝ, ψ₁ v = y :=
      ⟨_, (EReal.coe_toReal (hψ₁.isFS.ne_top v) (hψ₁.2 v)).symm⟩
    rw [hf v, hx, hy, EReal.toReal_coe, EReal.toReal_coe]
    calc uα α v - ((x - y : ℝ) : EReal) = uα α v + ((y - x : ℝ) : EReal) := by
          rw [sub_eq_add_neg, ← EReal.coe_neg, neg_sub]
      _ = uα α v + (y : EReal) - (x : EReal) := by
          rw [sub_eq_add_neg (uα α v + _), add_assoc, ← EReal.coe_neg, ← EReal.coe_add,
            sub_eq_add_neg]
  -- the Shilov lemma for `u_α + ψ₁ ∈ H^gf_ℚ(a_α + b)`
  have hS' : ∀ α v, uα α v - (f v : EReal) ≤ S.sup fun w => uα α w - (f w : EReal) := by
    intro α v
    have h := hsup (c α + b) (fun v => uα α v + ψ₁ v) ((huα α).isRatFS.add hψ₁.isRatFS)
    simp only [← hid] at h
    rw [← h]
    exact le_iSup (fun v => uα α v - (f v : EReal)) v
  -- pass to the limit in the maximum over the finite set `Σ`
  by_contra hlt
  push Not at hlt
  obtain ⟨c', hc1, hc2⟩ := exists_between hlt
  have hex : ∀ w ∈ S, ∃ α, uα α w - (f w : EReal) < c' := by
    intro w hw
    have h1 : u w - (f w : EReal) < c' :=
      (Finset.le_sup (f := fun v => u v - (f v : EReal)) hw).trans_lt hc1
    rw [hinf w, sub_eq_add_neg, ← EReal.coe_neg, ereal_iInf_add_coe] at h1
    obtain ⟨α, hα⟩ := iInf_lt_iff.1 h1
    exact ⟨α, by rwa [sub_eq_add_neg, ← EReal.coe_neg]⟩
  choose! α hα using hex
  obtain ⟨β, hβ⟩ := Finset.exists_le (S.image α)
  have h3 : (S.sup fun w => uα β w - (f w : EReal)) < c' := by
    rw [Finset.sup_lt_iff (bot_le.trans_lt hc1)]
    intro w hw
    refine lt_of_le_of_lt ?_ (hα w hw)
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact add_le_add_left (hanti w (hβ _ (Finset.mem_image_of_mem α hw))) _
  have h4 : u v - (f v : EReal) ≤ uα β v - (f v : EReal) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, hinf v]
    exact add_le_add_left (iInf_le _ β) _
  exact absurd ((h4.trans (hS' β v)).trans_lt h3) (not_lt.2 hc2.le)

/-- `lem:bj-sup-pl`, comparison form: for every rational PL function `f` there is a finite set
`Σ ⊆ (ℙⁿ)^div` containing `v_triv` such that every `u ∈ PSH(θ)` with `u ≤ f` on `Σ` satisfies
`u ≤ f` everywhere. -/
theorem IsRatPL.exists_finset_le_of_le {f : ProjBerk k n → ℝ} (hf : IsRatPL f) :
    ∃ S : Finset (ProjBerk k n), triv ∈ S ∧ (∀ w ∈ S, w.IsDivisorial) ∧
      ∀ (θ : ℝ) (u : ProjBerk k n → EReal), IsPSH θ u → (∀ w ∈ S, u w ≤ f w) →
        ∀ v, u v ≤ f v := by
  obtain ⟨S, hS, hSdiv, hsup⟩ := hf.exists_finset_iSup_sub_eq
  refine ⟨S, hS, hSdiv, fun θ u hu h v => ?_⟩
  have h1 : u v - (f v : EReal) ≤ 0 := by
    refine (le_iSup (fun v => u v - (f v : EReal)) v).trans ?_
    rw [hsup θ u hu]
    exact Finset.sup_le fun w hw => EReal.sub_nonpos.2 (h w hw)
  exact EReal.sub_nonpos.1 h1

/-- `lem:bj-sup-pl` applied to a PL function `f` with `u ≤ f` on `(ℙⁿ)^div`: then `u ≤ f`. -/
theorem IsPSH.le_of_forall_isDivisorial_le_isRatPL {θ : ℝ} {u : ProjBerk k n → EReal}
    (hu : IsPSH θ u) {f : ProjBerk k n → ℝ} (hf : IsRatPL f)
    (hle : ∀ v, v.IsDivisorial → u v ≤ f v) (v : ProjBerk k n) : u v ≤ f v := by
  obtain ⟨S, -, hSdiv, hcomp⟩ := hf.exists_finset_le_of_le
  exact hcomp θ u hu (fun w hw => hle w (hSdiv w hw)) v

/-! ### Divisorial comparison (`thm:bj-divisorial-comparison`) -/

/-- **Divisorial comparison** (`thm:bj-divisorial-comparison`, BJ22 Theorem 4.22): if
`u ∈ PSH(θ)` and `h : (ℙⁿ)^an → [-∞, ∞)` is usc with `u ≤ h` on the divisorial points, then
`u ≤ h` everywhere. For a rational PL function `ψ > h`, `u ≤ ψ` on `(ℙⁿ)^div`, hence everywhere
(`lem:bj-sup-pl`), and `h` is the infimum of such `ψ` (`lem:bj-usc-pl`). -/
theorem IsPSH.le_of_forall_isDivisorial_le {θ : ℝ} {u h : ProjBerk k n → EReal}
    (hu : IsPSH θ u) (hh : UpperSemicontinuous h) (htop : ∀ v, h v ≠ ⊤)
    (hle : ∀ v, v.IsDivisorial → u v ≤ h v) : u ≤ h :=
  le_of_forall_isRatPL_gt hh htop fun _ hψ hgt v =>
    hu.le_of_forall_isDivisorial_le_isRatPL hψ (fun w hw => (hle w hw).trans (hgt w).le) v

/-- A `θ`-psh function is determined by its restriction to the divisorial points
(`thm:bj-divisorial-comparison`, BJ22 Corollary 4.23). -/
theorem IsPSH.eq_of_forall_isDivisorial_eq {θ θ' : ℝ} {u u' : ProjBerk k n → EReal}
    (hu : IsPSH θ u) (hu' : IsPSH θ' u') (h : ∀ v, v.IsDivisorial → u v = u' v) : u = u' :=
  funext fun v => le_antisymm
    (hu.le_of_forall_isDivisorial_le hu'.upperSemicontinuous hu'.ne_top
      (fun w hw => (h w hw).le) v)
    (hu'.le_of_forall_isDivisorial_le hu.upperSemicontinuous hu.ne_top
      (fun w hw => (h w hw).ge) v)

/-! ### Increasing nets (`prop:bj-ep-criterion`) -/

/-- `prop:bj-ep-criterion`, second claim: if `U ∈ PSH(θ)` agrees on the divisorial points with
the supremum of a bounded-above family `uᵢ ∈ PSH(θ)`, then `U = (sup_i uᵢ)^⋆`. -/
theorem IsPSH.eq_uscReg_iSup {θ : ℝ} {ι : Sort*} {u : ι → ProjBerk k n → EReal}
    (hu : ∀ i, IsPSH θ (u i)) (hbdd : ∃ C : ℝ, ∀ i v, u i v ≤ C) {U : ProjBerk k n → EReal}
    (hU : IsPSH θ U) (hdiv : ∀ v, v.IsDivisorial → U v = ⨆ i, u i v) :
    U = uscReg fun v => ⨆ i, u i v := by
  obtain ⟨C, hC⟩ := hbdd
  have hle : ∀ i, u i ≤ U := fun i =>
    (hu i).le_of_forall_isDivisorial_le hU.upperSemicontinuous hU.ne_top fun v hv =>
      (hdiv v hv).symm ▸ le_iSup (fun i => u i v) i
  have hregC : ∀ v, uscReg (fun v => ⨆ i, u i v) v ≤ C :=
    uscReg_le_of_le (g := fun _ => (C : EReal)) continuous_const.upperSemicontinuous
      fun v => iSup_le fun i => hC i v
  refine le_antisymm (hU.le_of_forall_isDivisorial_le (upperSemicontinuous_uscReg _)
    (fun v => ne_top_of_le_ne_top (EReal.coe_ne_top C) (hregC v)) fun v hv => ?_)
    (uscReg_le_of_le (f := fun v => ⨆ i, u i v) hU.upperSemicontinuous
      fun v => iSup_le fun i => hle i v)
  rw [hdiv v hv]
  exact le_uscReg (fun v => ⨆ i, u i v) v

/-- **The envelope property via increasing nets** (`prop:bj-ep-criterion`, FHX
`prop:EP-criterion`, BJ22 Theorem 5.11): if every bounded-above increasing net in `PSH(θ)` admits
a `θ`-psh function agreeing with its supremum on the divisorial points, then `θ` has the envelope
property. For a bounded-above family `S`, the hypothesis is applied to the increasing net of
finite maxima `max(u₀, max_{u ∈ J} u)`, `J ⊆ S` finite, and `eq_uscReg_iSup` identifies the
resulting `θ`-psh function with `(sup S)^⋆`. -/
theorem hasEnvelopeProperty_of_forall_monotone {θ : ℝ}
    (H : ∀ (ι : Type u) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      (u : ι → ProjBerk k n → EReal), (∀ i, IsPSH θ (u i)) → (∀ v, Monotone fun i => u i v) →
        (∃ C : ℝ, ∀ i v, u i v ≤ C) →
          ∃ U, IsPSH θ U ∧ ∀ v, v.IsDivisorial → U v = ⨆ i, u i v) :
    HasEnvelopeProperty k n θ := by
  classical
  intro S hSne hS hbdd
  obtain ⟨u₀, hu₀⟩ := hSne
  obtain ⟨C, hC⟩ := hbdd
  -- the increasing net of finite maxima, indexed by the finite subsets of `S`
  set w : Finset S → ProjBerk k n → EReal := fun J v =>
    (insert ⟨u₀, hu₀⟩ J).sup' (Finset.insert_nonempty _ _) fun i => i.1 v with hw
  have hwpsh : ∀ J, IsPSH θ (w J) := fun J =>
    isPSH_finset_sup' (Finset.insert_nonempty _ _) fun i _ => hS i.1 i.2
  have hwmono : ∀ v, Monotone fun J => w J v := fun v J J' hJJ' =>
    Finset.sup'_mono _ (Finset.insert_subset_insert _ hJJ') _
  have hwC : ∃ C : ℝ, ∀ J v, w J v ≤ C :=
    ⟨C, fun J v => Finset.sup'_le _ _ fun i _ => hC i.1 i.2 v⟩
  obtain ⟨U, hU, hUdiv⟩ := H (Finset S) w hwpsh hwmono hwC
  have hsup : (fun v => ⨆ J, w J v) = fun v => ⨆ u ∈ S, u v := by
    funext v
    refine le_antisymm (iSup_le fun J => Finset.sup'_le _ _ fun i _ =>
      le_iSup₂ (f := fun (u : ProjBerk k n → EReal) (_ : u ∈ S) => u v) i.1 i.2) ?_
    refine iSup₂_le fun u hu => le_iSup_of_le ({⟨u, hu⟩} : Finset S) ?_
    show u v ≤ (insert ⟨u₀, hu₀⟩ ({⟨u, hu⟩} : Finset S)).sup' (Finset.insert_nonempty _ _)
      fun i => i.1 v
    exact Finset.le_sup' (fun i : S => i.1 v)
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self (⟨u, hu⟩ : S)))
  have hUeq := hU.eq_uscReg_iSup hwpsh hwC hUdiv
  rw [hsup] at hUeq
  rw [← hUeq]
  exact hU

end ProjBerk

end EnvelopeProperty
