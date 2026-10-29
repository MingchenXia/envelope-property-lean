/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietyShilov
import EnvelopeProperty.Projective.FSSystemPL

/-!
# Divisorial comparison on `X = V(I)`

Let `k` be an algebraically closed field with the trivial absolute value and `X = V(I) ⊆ ℙᴹ` a
projective subvariety (`EnvelopeProperty.ProjSubvariety`). This file proves the divisorial
comparison theorem of Boucksom–Jonsson, *Global pluripotential theory over a trivially valued
field* (BJ22, Theorem 4.22, suppsh) on `X^an`, in the form of the blueprint chapter
`smooth-general.tex` (subsection `subsec:sg-comparison`, nodes `lem:sg-sup-pl` and
`thm:sg-comparison`), with the divisorial points `ProjSubvariety.IsDivisorial` of `def:sg-div`.
It is the input of the envelope criterion used by Fang–Han–Xia, *The envelope property for
unibranch projective varieties*, Theorem 3.1 (`thm:smooth-EP`) for smooth `X`
(FHX `prop:BJ-package`).

## Main results

* `ProjSubvariety.separatesPoints_isPL` (**`lem:sg-pl-separate`** in the form used by
  `EnvelopeProperty.Projective.FSSystemPL`): `PL(X)` separates the points of `X^an`.
* **`lem:sg-sup-pl`** (BJ22 supPL): `ProjSubvariety.IsPL.exists_finset_iSup_sub_eq`: for every
  PL function `f` there is a finite set `Σ ⊆ X^div` containing `⋆` with
  `sup_{X^an} (u - f) = max_Σ (u - f)` for every `θ` and every `u ∈ PSH(X, θ)`; the comparison form
  is `ProjSubvariety.IsPL.exists_finset_le_of_le`. Writing `f = φ₁ - ψ₁`, `Σ` is the Shilov set of
  `φ₁` (`ProjSubvariety.IsFinFS.exists_finset_iSup_sub_eq`), applied to `u_α + ψ₁` for a decreasing
  net `u_α ∈ 𝓗_fin(a_α)` with limit `u` (`FSSystem.IsPSH.exists_isFinFS_net`).
* **`thm:sg-comparison`**: `ProjSubvariety.IsPSH.le_of_forall_isDivisorial_le`: if
  `u ∈ PSH(X, θ)`, `h : X^an → [-∞, ∞)` is usc and `u ≤ h` on `X^div`, then `u ≤ h`. The PL case is
  `ProjSubvariety.IsPSH.le_of_forall_isDivisorial_le_isPL`; the general case uses `lem:sg-pl`(3)
  (`FSSystem.le_of_forall_isPL_gt`) with `lem:sg-pl-separate`.
* `ProjSubvariety.IsPSH.eq_of_forall_isDivisorial_eq`: a psh function on `X^an` is determined by
  its values at the divisorial points.

## Deviations from the blueprint

None in the statements. `lem:sg-sup-pl` is proved for the PL functions `ProjSubvariety.IsPL` of
`FSSystemPL` (differences of finite Fubini–Study functions with rational weights).
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

namespace ProjSubvariety

universe u

variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}

/-! ### PL functions separate points (`lem:sg-pl-separate`) -/

variable (X) in
/-- **`lem:sg-pl-separate`** (BJ22 FSdense): `PL(X)` separates the points of `X^an`; this is
the hypothesis `hsep` of the density results of `EnvelopeProperty.Projective.FSSystemPL` for
`X.fsSystem`. A single finite Fubini–Study function already separates two given points
(`ProjSubvariety.exists_isFiniteFS_ne`). -/
theorem separatesPoints_isPL : {f : X.an → ℝ | X.IsPL f}.SeparatesPoints := by
  intro v w h
  obtain ⟨c, f, hf, hne⟩ := exists_isFiniteFS_ne h
  refine ⟨fun x => ((f x : EReal)).toReal, IsFinFS.isPL hf.isFinFS, ?_⟩
  simpa only [EReal.toReal_coe] using hne

variable [IsAlgClosed k]

/-! ### Suprema against PL functions (`lem:sg-sup-pl`) -/

/-- **Suprema against PL functions** (`lem:sg-sup-pl`, BJ22 supPL): for every PL function
`f` on `X^an` there is a finite set `Σ ⊆ X^div` containing `⋆` such that
`sup_{X^an} (u - f) = max_Σ (u - f)` for every `θ ∈ ℝ` and every `u ∈ PSH(X, θ)`. -/
theorem IsPL.exists_finset_iSup_sub_eq {f : X.an → ℝ} (hf : X.IsPL f) :
    ∃ S : Finset X.an, X.triv ∈ S ∧ (∀ w ∈ S, X.IsDivisorial w) ∧
      ∀ (θ : ℝ) (u : X.an → EReal), X.IsPSH θ u →
        ⨆ v, (u v - (f v : EReal)) = S.sup fun v => u v - (f v : EReal) := by
  classical
  obtain ⟨a, b, φ₁, ψ₁, hφ₁, hψ₁, hf⟩ := hf
  have hφ₁' : X.IsFinFS (a 0) φ₁ := hφ₁
  have hψ₁' : X.IsFinFS (b 0) ψ₁ := hψ₁
  obtain ⟨S, hS, hSdiv, hsup⟩ := hφ₁'.exists_finset_iSup_sub_eq
  refine ⟨S, hS, hSdiv, fun θ u hu => le_antisymm (iSup_le fun v => ?_)
    (Finset.sup_le fun w _ => le_iSup (fun v => u v - (f v : EReal)) w)⟩
  obtain ⟨ι, _, _, _, c, uα, huα, -, hanti, hinf⟩ :=
    FSSystem.IsPSH.exists_isFinFS_net (F := X.fsSystem) hu
  -- `u_α - f = (u_α + ψ₁) - φ₁`
  have hid : ∀ α v, uα α v - (f v : EReal) = (uα α v + ψ₁ v) - φ₁ v := fun α v => by
    obtain ⟨x, hx⟩ : ∃ x : ℝ, φ₁ v = x := ⟨_, (hφ₁'.coe_toReal v).symm⟩
    obtain ⟨y, hy⟩ : ∃ y : ℝ, ψ₁ v = y := ⟨_, (hψ₁'.coe_toReal v).symm⟩
    rw [hf v, hx, hy, EReal.toReal_coe, EReal.toReal_coe]
    calc uα α v - ((x - y : ℝ) : EReal) = uα α v + ((y - x : ℝ) : EReal) := by
          rw [sub_eq_add_neg, ← EReal.coe_neg, neg_sub]
      _ = uα α v + (y : EReal) - (x : EReal) := by
          rw [sub_eq_add_neg (uα α v + _), add_assoc, ← EReal.coe_neg, ← EReal.coe_add,
            sub_eq_add_neg]
  -- the Shilov lemma for `u_α + ψ₁ ∈ 𝓗_fin(X, a_α + b)`
  have hS' : ∀ α v, uα α v - (f v : EReal) ≤ S.sup fun w => uα α w - (f w : EReal) := by
    intro α v
    have hadd : X.IsFinFS (c α 0 + b 0) fun v => uα α v + ψ₁ v :=
      IsFinFS.add (huα α) hψ₁'
    obtain ⟨D, hD, -, hDeq⟩ := hadd
    have h := hsup (c α 0 + b 0) (fun v => uα α v + ψ₁ v) ⟨D, hD, hDeq⟩
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

/-- `lem:sg-sup-pl`, comparison form: for every PL function `f` on `X^an` there is a finite set
`Σ ⊆ X^div` containing `⋆` such that every `u ∈ PSH(X, θ)` with `u ≤ f` on `Σ` satisfies
`u ≤ f` on `X^an`. -/
theorem IsPL.exists_finset_le_of_le {f : X.an → ℝ} (hf : X.IsPL f) :
    ∃ S : Finset X.an, X.triv ∈ S ∧ (∀ w ∈ S, X.IsDivisorial w) ∧
      ∀ (θ : ℝ) (u : X.an → EReal), X.IsPSH θ u → (∀ w ∈ S, u w ≤ f w) →
        ∀ v, u v ≤ f v := by
  obtain ⟨S, hS, hSdiv, hsup⟩ := hf.exists_finset_iSup_sub_eq
  refine ⟨S, hS, hSdiv, fun θ u hu h v => ?_⟩
  have h1 : u v - (f v : EReal) ≤ 0 := by
    refine (le_iSup (fun v => u v - (f v : EReal)) v).trans ?_
    rw [hsup θ u hu]
    exact Finset.sup_le fun w hw => EReal.sub_nonpos.2 (h w hw)
  exact EReal.sub_nonpos.1 h1

/-- `lem:sg-sup-pl` applied to a PL function `f` with `u ≤ f` on `X^div`: then `u ≤ f`. -/
theorem IsPSH.le_of_forall_isDivisorial_le_isPL {θ : ℝ} {u : X.an → EReal} (hu : X.IsPSH θ u)
    {f : X.an → ℝ} (hf : X.IsPL f) (hle : ∀ v, X.IsDivisorial v → u v ≤ f v) (v : X.an) :
    u v ≤ f v := by
  obtain ⟨S, -, hSdiv, hcomp⟩ := hf.exists_finset_le_of_le
  exact hcomp θ u hu (fun w hw => hle w (hSdiv w hw)) v

/-! ### Divisorial comparison (`thm:sg-comparison`) -/

/-- **Divisorial comparison on `X`** (**`thm:sg-comparison`**, BJ22 suppsh): if
`u ∈ PSH(X, θ)` and `h : X^an → [-∞, ∞)` is usc with `u ≤ h` on the divisorial points of `X`, then
`u ≤ h` on `X^an`. For a PL function `ψ > h`, `u ≤ ψ` on `X^div`, hence everywhere
(`lem:sg-sup-pl`), and `h` is the infimum of such `ψ` (`lem:sg-pl`(3), which applies by
`lem:sg-pl-separate`). -/
theorem IsPSH.le_of_forall_isDivisorial_le {θ : ℝ} {u h : X.an → EReal} (hu : X.IsPSH θ u)
    (hh : UpperSemicontinuous h) (htop : ∀ v, h v ≠ ⊤)
    (hle : ∀ v, X.IsDivisorial v → u v ≤ h v) : u ≤ h :=
  FSSystem.le_of_forall_isPL_gt (F := X.fsSystem) (separatesPoints_isPL X) hh htop
    fun _ hψ hgt v =>
      hu.le_of_forall_isDivisorial_le_isPL hψ (fun w hw => (hle w hw).trans (hgt w).le) v

/-- A `θ`-psh function on `X^an` is determined by its values at the divisorial points of `X`
(`thm:sg-comparison`, BJ22 Hausdorff). -/
theorem IsPSH.eq_of_forall_isDivisorial_eq {θ θ' : ℝ} {u u' : X.an → EReal} (hu : X.IsPSH θ u)
    (hu' : X.IsPSH θ' u') (h : ∀ v, X.IsDivisorial v → u v = u' v) : u = u' :=
  funext fun v => le_antisymm
    (hu.le_of_forall_isDivisorial_le (FSSystem.IsPSH.upperSemicontinuous hu')
      (FSSystem.IsPSH.ne_top hu') (fun w hw => (h w hw).le) v)
    (hu'.le_of_forall_isDivisorial_le (FSSystem.IsPSH.upperSemicontinuous hu)
      (FSSystem.IsPSH.ne_top hu) (fun w hw => (h w hw).ge) v)

end ProjSubvariety

end EnvelopeProperty
