/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.Shilov
import EnvelopeProperty.Global.ModelPL

/-!
# Divisorial comparison on a model

Let `k` be an algebraically closed field with the trivial absolute value and
`𝒳 = (K, S, z)` an integral multiprojective model of rank `r` (`EnvelopeProperty.MultiModel`,
`def:gl-model`). This file proves the divisorial comparison theorem of Boucksom–Jonsson, *Global
pluripotential theory over a trivially valued field* (BJ22, Theorem 4.22,
Corollary 4.23) on `𝒳^an`, for **every** class `θ ∈ ℝ^r`, in the form of the blueprint nodes
`thm:gl-comparison` and `lem:gl-usc-local` of the global chapter `global.tex` (subsection
`subsec:gl-comparison`) of the formalization of Fang–Han–Xia, *The envelope property for unibranch
projective varieties* (FHX, `prop:BJ-package`(2)). It generalizes the rank-one
template `EnvelopeProperty.Projective.SubvarietyComparison` to `MultiModel`.

## Main results

* `MultiModel.IsPL.exists_finset_iSup_sub_eq` (BJ22 Lemma 4.26): for every PL function `f` there is
  a finite set `Σ ⊆ 𝒳^div` containing `⋆` with `sup_{𝒳^an} (u - f) = max_Σ (u - f)` for every
  `θ ∈ ℝ^r` and every `u ∈ PSH(𝒳, θ)`. Writing `f = φ₁ - ψ₁`, `Σ` is the Shilov set of `φ₁`
  (`MultiModel.IsFinFS.exists_finset_iSup_sub_eq`), applied to `u_α + ψ₁ ∈ 𝓗(a_α + b)` for the
  decreasing net `u_α ∈ 𝓗(a_α)` defining `u`; the comparison form is
  `MultiModel.IsPL.exists_finset_le_of_le`.
* **`thm:gl-comparison`**: `MultiModel.IsPSH.le_of_forall_isDivisorial_le`: if `u ∈ PSH(𝒳, θ)`,
  `h : 𝒳^an → [-∞, ∞)` is usc and `u ≤ h` on `𝒳^div`, then `u ≤ h`;
  `MultiModel.IsPSH.eq_of_forall_isDivisorial_eq`: psh functions (possibly of different classes)
  agreeing on `𝒳^div` are equal.
* **`lem:gl-usc-local`**: (1) `EnvelopeProperty.uscReg_restrict_apply`,
  `EnvelopeProperty.uscReg_apply_of_upperSemicontinuousOn`: usc regularization is local on open
  sets; (2) `EnvelopeProperty.uscReg_add_continuous`: `(g + e)^⋆ = g^⋆ + e` on `Ω` for continuous
  real `e` on `Ω`; (3) `MultiModel.IsPSH.le_of_forall_mem_le`,
  `MultiModel.IsPSH.eq_of_forall_mem_eq`: comparison on sets `Ω ⊇ 𝒳^div`.

## Deviations from the blueprint

* The proof of `thm:gl-comparison` does not pass to rational weights (the blueprint invokes the
  proof of `cor:gl-pshhom`): the Shilov lemma is proved for all Fubini–Study functions
  (`EnvelopeProperty.Global.Shilov`), so the defining net of `u` is used directly. No hypothesis on
  `θ` is needed (in particular `θ` need not lie in the model-nef cone).
* `lem:gl-usc-local`(3) holds for every set `Ω ⊇ 𝒳^div` (openness is not used).
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Locality of usc regularization (`lem:gl-usc-local`(1),(2)) -/

section UscLocal

variable {T : Type*} [TopologicalSpace T] {Ω : Set T}

/-- **`lem:gl-usc-local`(1)**: on an open set `Ω`, the usc regularization of the restriction is the
restriction of the usc regularization: `(g|_Ω)^⋆ = g^⋆|_Ω`. -/
theorem uscReg_restrict_apply {γ : Type*} [CompleteLinearOrder γ] (hΩ : IsOpen Ω) (g : T → γ)
    (x : Ω) : uscReg (fun y : Ω => g y) x = uscReg g x := by
  rw [uscReg, uscReg, ← map_nhds_subtype_coe_eq_nhds x.2 (hΩ.mem_nhds x.2)]
  rfl

/-- **`lem:gl-usc-local`(1)**: if `g|_Ω` is usc on the open set `Ω`, then `g^⋆ = g` on `Ω`. -/
theorem uscReg_apply_of_upperSemicontinuousOn {γ : Type*} [CompleteLinearOrder γ]
    (hΩ : IsOpen Ω) {g : T → γ} (hg : UpperSemicontinuousOn g Ω) {x : T} (hx : x ∈ Ω) :
    uscReg g x = g x := by
  have hg' : UpperSemicontinuous fun y : Ω => g y := upperSemicontinuousOn_iff_restrict.2 hg
  rw [← uscReg_restrict_apply hΩ g ⟨x, hx⟩, uscReg_eq_self hg']

/-- **`lem:gl-usc-local`(2)**: for a continuous real function `e` on the open set `Ω`,
`(g + e)^⋆ = g^⋆ + e` on `Ω`. -/
theorem uscReg_add_continuous (hΩ : IsOpen Ω) (g : T → EReal) {e : Ω → ℝ} (he : Continuous e)
    (x : Ω) : uscReg (fun y : Ω => g y + (e y : EReal)) x = uscReg g x + (e x : EReal) := by
  rw [← uscReg_restrict_apply hΩ g x]
  set g' : Ω → EReal := fun y => g y
  have hcont : ∀ (a : EReal) (b : ℝ), ContinuousAt (fun p : EReal × EReal => p.1 + p.2)
      (a, (b : EReal)) := fun a b =>
    EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot b)) (Or.inr (EReal.coe_ne_top b))
  have hecont : Continuous fun y => (e y : EReal) := continuous_coe_real_ereal.comp he
  have hnegcont : Continuous fun y => ((-e y : ℝ) : EReal) :=
    continuous_coe_real_ereal.comp he.neg
  refine le_antisymm ?_ ?_
  · -- `g' + e ≤ g'^⋆ + e`, which is usc
    refine uscReg_le_of_le ?_ (fun y => add_le_add (le_uscReg g' y) le_rfl) x
    exact (upperSemicontinuous_uscReg g').add' hecont.upperSemicontinuous
      fun y => hcont _ _
  · -- `g' = (g' + e) - e ≤ (g' + e)^⋆ - e`, which is usc
    have hle : uscReg g' ≤ fun y => uscReg (fun y => g' y + (e y : EReal)) y +
        ((-e y : ℝ) : EReal) := by
      refine uscReg_le_of_le ?_ fun y => ?_
      · exact (upperSemicontinuous_uscReg _).add' hnegcont.upperSemicontinuous
          fun y => hcont _ _
      · have h1 := le_uscReg (fun y => g' y + (e y : EReal)) y
        calc g' y = g' y + (e y : EReal) + ((-e y : ℝ) : EReal) := by
              rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
          _ ≤ _ := add_le_add h1 le_rfl
    have h2 := add_le_add (hle x) (le_refl (e x : EReal))
    rwa [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] at h2

end UscLocal

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r}

variable [IsAlgClosed k]

/-! ### Suprema against PL functions (BJ22 Lemma 4.26) -/

/-- **Suprema against PL functions** (BJ22 Lemma 4.26): for every PL function `f` on `𝒳^an` there
is a finite set `Σ ⊆ 𝒳^div` containing `⋆` such that `sup_{𝒳^an} (u - f) = max_Σ (u - f)` for
every `θ ∈ ℝ^r` and every `u ∈ PSH(𝒳, θ)`. -/
theorem IsPL.exists_finset_iSup_sub_eq {f : X.an → ℝ} (hf : X.IsPL f) :
    ∃ S : Finset X.an, X.triv ∈ S ∧ (∀ w ∈ S, X.IsDivisorial w) ∧
      ∀ (θ : Fin r → ℝ) (u : X.an → EReal), X.IsPSH θ u →
        ⨆ v, (u v - (f v : EReal)) = S.sup fun v => u v - (f v : EReal) := by
  classical
  obtain ⟨a, b, φ₁, ψ₁, -, -, hφ₁, hψ₁, hf⟩ := isPL_iff.1 hf
  obtain ⟨S, hS, hSdiv, hsup⟩ := hφ₁.exists_finset_iSup_sub_eq
  refine ⟨S, hS, hSdiv, fun θ u hu => le_antisymm (iSup_le fun v => ?_)
    (Finset.sup_le fun w _ => le_iSup (fun v => u v - (f v : EReal)) w)⟩
  obtain ⟨-, -, ι, _, _, _, c, uα, huα, -, hanti, hinf⟩ := hu
  have hφ₁r : ∀ v, ((φ₁ v).toReal : EReal) = φ₁ v := fun v =>
    EReal.coe_toReal ((FSSystemC.IsFinFS.isFS (F := X.fsSystem) hφ₁).ne_top v)
      (FSSystemC.IsFinFS.ne_bot (F := X.fsSystem) hφ₁ v)
  have hψ₁r : ∀ v, ((ψ₁ v).toReal : EReal) = ψ₁ v := fun v =>
    EReal.coe_toReal ((FSSystemC.IsFinFS.isFS (F := X.fsSystem) hψ₁).ne_top v)
      (FSSystemC.IsFinFS.ne_bot (F := X.fsSystem) hψ₁ v)
  -- `u_α - f = (u_α + ψ₁) - φ₁`
  have hid : ∀ α v, uα α v - (f v : EReal) = (uα α v + ψ₁ v) - φ₁ v := fun α v => by
    obtain ⟨x, hx⟩ : ∃ x : ℝ, φ₁ v = x := ⟨_, (hφ₁r v).symm⟩
    obtain ⟨y, hy⟩ : ∃ y : ℝ, ψ₁ v = y := ⟨_, (hψ₁r v).symm⟩
    rw [hf v, hx, hy, EReal.toReal_coe, EReal.toReal_coe]
    calc uα α v - ((x - y : ℝ) : EReal) = uα α v + ((y - x : ℝ) : EReal) := by
          rw [sub_eq_add_neg, ← EReal.coe_neg, neg_sub]
      _ = uα α v + (y : EReal) - (x : EReal) := by
          rw [sub_eq_add_neg (uα α v + _), add_assoc, ← EReal.coe_neg, ← EReal.coe_add,
            sub_eq_add_neg]
  -- the Shilov lemma for `u_α + ψ₁ ∈ 𝓗(a_α + b)`
  have hS' : ∀ α v, uα α v - (f v : EReal) ≤ S.sup fun w => uα α w - (f w : EReal) := by
    intro α v
    have hadd : X.IsFS (c α + b) fun v => uα α v + ψ₁ v :=
      FSSystemC.IsFS.add (F := X.fsSystem) (huα α) (FSSystemC.IsFinFS.isFS (F := X.fsSystem) hψ₁)
    have h := hsup (c α + b) (fun v => uα α v + ψ₁ v) hadd
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
    exact add_le_add (hanti w (hβ _ (Finset.mem_image_of_mem α hw))) le_rfl
  have h4 : u v - (f v : EReal) ≤ uα β v - (f v : EReal) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, hinf v]
    exact add_le_add (iInf_le _ β) le_rfl
  exact absurd ((h4.trans (hS' β v)).trans_lt h3) (not_lt.2 hc2.le)

/-- BJ22 Lemma 4.26, comparison form: for every PL function `f` on `𝒳^an` there is a finite set
`Σ ⊆ 𝒳^div` containing `⋆` such that every `u ∈ PSH(𝒳, θ)` with `u ≤ f` on `Σ` satisfies `u ≤ f`
on `𝒳^an`. -/
theorem IsPL.exists_finset_le_of_le {f : X.an → ℝ} (hf : X.IsPL f) :
    ∃ S : Finset X.an, X.triv ∈ S ∧ (∀ w ∈ S, X.IsDivisorial w) ∧
      ∀ (θ : Fin r → ℝ) (u : X.an → EReal), X.IsPSH θ u → (∀ w ∈ S, u w ≤ f w) →
        ∀ v, u v ≤ f v := by
  obtain ⟨S, hS, hSdiv, hsup⟩ := hf.exists_finset_iSup_sub_eq
  refine ⟨S, hS, hSdiv, fun θ u hu h v => ?_⟩
  have h1 : u v - (f v : EReal) ≤ 0 := by
    refine (le_iSup (fun v => u v - (f v : EReal)) v).trans ?_
    rw [hsup θ u hu]
    exact Finset.sup_le fun w hw => EReal.sub_nonpos.2 (h w hw)
  exact EReal.sub_nonpos.1 h1

/-- The PL case of `thm:gl-comparison`: if `u ≤ f` on `𝒳^div` for a PL function `f`, then
`u ≤ f`. -/
theorem IsPSH.le_of_forall_isDivisorial_le_isPL {θ : Fin r → ℝ} {u : X.an → EReal}
    (hu : X.IsPSH θ u) {f : X.an → ℝ} (hf : X.IsPL f)
    (hle : ∀ v, X.IsDivisorial v → u v ≤ f v) (v : X.an) : u v ≤ f v := by
  obtain ⟨S, -, hSdiv, hcomp⟩ := hf.exists_finset_le_of_le
  exact hcomp θ u hu (fun w hw => hle w (hSdiv w hw)) v

/-! ### Divisorial comparison (`thm:gl-comparison`) -/

/-- **Divisorial comparison** (**`thm:gl-comparison`**, BJ22 Theorem 4.22): if `θ ∈ ℝ^r`,
`u ∈ PSH(𝒳, θ)` and `h : 𝒳^an → [-∞, ∞)` is usc with `u ≤ h` on the divisorial points `𝒳^div`,
then `u ≤ h`. For a PL function `ψ > h`, `u ≤ ψ` on `𝒳^div`, hence everywhere (BJ22 Lemma 4.26),
and `h` is the infimum of such `ψ` (`lem:gl-pl`). -/
theorem IsPSH.le_of_forall_isDivisorial_le {θ : Fin r → ℝ} {u h : X.an → EReal}
    (hu : X.IsPSH θ u) (hh : UpperSemicontinuous h) (htop : ∀ v, h v ≠ ⊤)
    (hle : ∀ v, X.IsDivisorial v → u v ≤ h v) : u ≤ h :=
  le_of_forall_isPL_gt hh htop fun _ hψ hgt v =>
    hu.le_of_forall_isDivisorial_le_isPL hψ (fun w hw => (hle w hw).trans (hgt w).le) v

/-- **`thm:gl-comparison`**, uniqueness (BJ22 Corollary 4.23): psh functions on `𝒳^an`, possibly
of different classes, that agree on `𝒳^div` are equal. -/
theorem IsPSH.eq_of_forall_isDivisorial_eq {θ θ' : Fin r → ℝ} {u u' : X.an → EReal}
    (hu : X.IsPSH θ u) (hu' : X.IsPSH θ' u') (h : ∀ v, X.IsDivisorial v → u v = u' v) :
    u = u' :=
  funext fun v => le_antisymm
    (hu.le_of_forall_isDivisorial_le (FSSystemC.IsPSH.upperSemicontinuous hu')
      (FSSystemC.IsPSH.ne_top hu') (fun w hw => (h w hw).le) v)
    (hu'.le_of_forall_isDivisorial_le (FSSystemC.IsPSH.upperSemicontinuous hu)
      (FSSystemC.IsPSH.ne_top hu) (fun w hw => (h w hw).ge) v)

/-! ### Comparison on sets containing `𝒳^div` (`lem:gl-usc-local`(3)) -/

/-- **`lem:gl-usc-local`(3)**: if `Ω ⊇ 𝒳^div`, `u ∈ PSH(𝒳, θ)` and `h` is usc with `u ≤ h` on `Ω`,
then `u ≤ h`. -/
theorem IsPSH.le_of_forall_mem_le {θ : Fin r → ℝ} {u h : X.an → EReal} (hu : X.IsPSH θ u)
    (hh : UpperSemicontinuous h) (htop : ∀ v, h v ≠ ⊤) {Ω : Set X.an}
    (hΩ : ∀ v, X.IsDivisorial v → v ∈ Ω) (hle : ∀ v ∈ Ω, u v ≤ h v) : u ≤ h :=
  hu.le_of_forall_isDivisorial_le hh htop fun v hv => hle v (hΩ v hv)

/-- **`lem:gl-usc-local`(3)**: psh functions agreeing on a set `Ω ⊇ 𝒳^div` are equal. -/
theorem IsPSH.eq_of_forall_mem_eq {θ θ' : Fin r → ℝ} {u u' : X.an → EReal} (hu : X.IsPSH θ u)
    (hu' : X.IsPSH θ' u') {Ω : Set X.an} (hΩ : ∀ v, X.IsDivisorial v → v ∈ Ω)
    (h : ∀ v ∈ Ω, u v = u' v) : u = u' :=
  hu.eq_of_forall_isDivisorial_eq hu' fun v hv => h v (hΩ v hv)

end MultiModel

end EnvelopeProperty
