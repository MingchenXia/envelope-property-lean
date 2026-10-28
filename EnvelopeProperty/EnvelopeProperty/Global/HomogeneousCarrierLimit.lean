/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.PSH2HomogeneousMajorant

/-!
# Decreasing limits of maxima below a homogeneous carrier (FHX Lemma 7.4)

Let `𝒳 = (K, S, z)` be an integral multiprojective model of rank `r` over an algebraically closed
trivially valued field `k` (`EnvelopeProperty.MultiModel`, `def:gl-model`). This file implements
the blueprint node `lem:hm-carrier-limit` of the chapter `psh2-homogeneous-majorant.tex`.

Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX, revision of
2026-10-28, `references/fhx-envelope-20261028`), Lemma 7.4 (`lem:homogeneous-carrier-limit`):
*let `X` be an integral projective variety, `θ ∈ N¹(X)_ℝ` and `Ψ ∈ PSH_hom(X, θ)`. Suppose a
sequence `U_n` decreases pointwise and each `U_n` is a finite maximum
`U_n = max_a (q_{n,a} + c_{n,a})` with `q_{n,a} ∈ PSH_hom(X, θ)`, `q_{n,a} ≤ Ψ`, `c_{n,a} ∈ ℝ`,
including the term `Ψ - n`. If `u = lim_n U_n` is not identically `-∞`, then `u ∈ PSH(X, θ)`.*
FHX uses it for the limit `U` in Proposition 7.5 (`prop:homogeneous-slices`), in the general case
of Theorem 8.3 and in Corollary 8.4; the formalization of those statements does not use it
(`thm:nn-hom-max-diagonal`, `cor:nn-sandwich-diagonal` and `thm:nn-psh2-of-ep` take its place).

## Main statements

* `MultiModel.IsScaleHomogeneous.homogenization_add_coe_le`: for a homogeneous `Ψ` and a real
  `D ≥ 0`, the homogenization of `Ψ + D` is at most `Ψ` (`inf_{t > 0} (Ψ + tD) = Ψ`).
* `MultiModel.isPSH_of_homogeneous_carrier_limit` (**`lem:hm-carrier-limit`**): FHX Lemma 7.4 on
  models, for every `θ ∈ ℝ^r`.

## Implementation notes

The proof is not FHX's direct construction of a decreasing Fubini–Study net. It is a corollary of
PSH2 below a homogeneous majorant (`MultiModel.isPSH_of_antitone_of_homMajorant`,
`thm:hm-psh2-hom-majorant`): each `U_n` is `θ`-psh, and every Legendre slice of the limit is
`≤ Ψ`, because `U_0 - λ ≤ Ψ + D` with `D = max (max_a c_{0,a} - λ) 0` (`q_{0,a} ≤ Ψ`), and the
homogenization of `Ψ + D` is `≤ Ψ`. The carrier term `Ψ - n` of FHX is therefore not a hypothesis:
in FHX it makes `max_a p_{n,a,j} ≥ Ψ` for the approximants, which this proof does not need, and the
nonemptiness of the maxima follows from `u ≢ -∞`. The maxima are `Finset.sup` over finite sets
`Ks n` of a fixed type `κ`, as in `MultiModel.isPSH_of_dominated_homMax_seq`.
-/

open Filter

noncomputable section

namespace EnvelopeProperty
namespace MultiModel

universe u

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r}

/-- **Homogenization of a homogeneous function plus a constant.** If `Ψ` is homogeneous and
`D ≥ 0` is real, then `(Ψ + D)^ ≤ Ψ`: `t · (Ψ + D) = Ψ + tD` for `t > 0`, and `tD → 0` as
`t → 0`. -/
theorem IsScaleHomogeneous.homogenization_add_coe_le {Ψ : X.an → EReal}
    (hΨ : X.IsScaleHomogeneous Ψ) {D : ℝ} (hD : 0 ≤ D) :
    X.homogenization (fun v => Ψ v + (D : EReal)) ≤ Ψ := by
  intro v
  have hscale : ∀ (t : ℝ) (ht : 0 < t),
      X.homogenization (fun v => Ψ v + (D : EReal)) v ≤ Ψ v + ((t * D : ℝ) : EReal) := by
    intro t ht
    refine (homogenization_le_scaleFun _ t ht v).trans_eq ?_
    simp only [scaleFun_apply]
    rw [ProjBerk.ereal_coe_mul_add ht.le, ← EReal.coe_mul]
    congr 1
    exact congrFun (hΨ.scaleFun_eq t ht) v
  refine ProjBerk.ereal_le_of_forall_pos_le_add fun ε hε => ?_
  have hpos : 0 < ε / (D + 1) := div_pos hε (by linarith)
  refine (hscale _ hpos).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_))
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

variable [IsAlgClosed k]

/-- **FHX Lemma 7.4 on models** (**`lem:hm-carrier-limit`**; FHX `lem:homogeneous-carrier-limit`,
revision of 2026-10-28). Let `θ ∈ ℝ^r` (any class) and `Ψ ∈ PSH_hom(𝒳, θ)`. For each `n ∈ ℕ` let
`Ks n` be a finite set and, for `a ∈ Ks n`, `q n a ∈ PSH_hom(𝒳, θ)` with `q n a ≤ Ψ` and
`c n a ∈ ℝ`. If `U_n = max_{a ∈ Ks n} (q n a + c n a)` decreases in `n` and `w = inf_n U_n` is not
identically `-∞`, then `w ∈ PSH(𝒳, θ)`. FHX also requires the term `Ψ - n` among the
constituents of `U_n`; this is not needed here. The proof applies PSH2 below the homogeneous
majorant `Ψ` (`isPSH_of_antitone_of_homMajorant`): every Legendre slice of `w` is `≤ Ψ`. -/
theorem isPSH_of_homogeneous_carrier_limit {θ : Fin r → ℝ} {Ψ : X.an → EReal}
    (hΨ : X.IsPSHHom θ Ψ) {κ : Type*} (Ks : ℕ → Finset κ) (q : ℕ → κ → X.an → EReal)
    (c : ℕ → κ → ℝ) (hq : ∀ n, ∀ a ∈ Ks n, X.IsPSHHom θ (q n a))
    (hqΨ : ∀ n, ∀ a ∈ Ks n, ∀ v, q n a v ≤ Ψ v)
    (hanti : ∀ v, Antitone fun n => (Ks n).sup fun a => q n a v + (c n a : EReal))
    {w : X.an → EReal} (hw : ∀ v, w v = ⨅ n, (Ks n).sup fun a => q n a v + (c n a : EReal))
    (hne : ∃ v, w v ≠ ⊥) : X.IsPSH θ w := by
  classical
  -- the maxima are nonempty, since otherwise `w ≤ U_n ≡ -∞`
  have hKs : ∀ n, (Ks n).Nonempty := by
    intro n
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    obtain ⟨v, hv⟩ := hne
    refine hv (le_bot_iff.1 ((hw v).le.trans ((iInf_le _ n).trans ?_)))
    rw [h, Finset.sup_empty]
  -- each `U_n` is `θ`-psh
  have hUpsh : ∀ n, X.IsPSH θ fun v => (Ks n).sup fun a => q n a v + (c n a : EReal) := by
    intro n
    have h := FSSystemC.isPSH_finset_sup' (F := X.fsSystem) (hKs n)
      (w := fun a v => q n a v + (c n a : EReal)) fun a ha => (hq n a ha).isPSH.add_const (c n a)
    simpa only [Finset.sup'_eq_sup] using h
  -- every Legendre slice of `w` lies below `Ψ`
  have hmaj : ∀ lam : ℝ, (lam : EReal) < w X.triv → ∀ v, X.legendreSlice w lam v ≤ Ψ v := by
    intro lam _ v₀
    set C : ℝ := (Ks 0).sup' (hKs 0) (c 0) with hC
    set D : ℝ := max (C - lam) 0 with hD
    have hle : ∀ v, w v - (lam : EReal) ≤ Ψ v + (D : EReal) := by
      intro v
      have h1 : w v ≤ Ψ v + ((D + lam : ℝ) : EReal) := by
        refine ((hw v).le.trans (iInf_le _ 0)).trans (Finset.sup_le fun a ha => ?_)
        refine add_le_add (hqΨ 0 a ha v) (EReal.coe_le_coe_iff.2 ?_)
        have hca : c 0 a ≤ C := Finset.le_sup' (c 0) ha
        have hCD : C - lam ≤ D := le_max_left _ _
        linarith
      calc w v - (lam : EReal) ≤ Ψ v + ((D + lam : ℝ) : EReal) - (lam : EReal) :=
            EReal.sub_le_sub h1 le_rfl
        _ = Ψ v + (D : EReal) := by
            rw [ereal_sub_coe_eq_add_coe_neg, add_assoc, ← EReal.coe_add, add_neg_cancel_right]
    exact ((homogenization_mono (u := fun v => w v - (lam : EReal))
      (u' := fun v => Ψ v + (D : EReal)) hle).trans
      (hΨ.isScaleHomogeneous.homogenization_add_coe_le (le_max_right _ _))) v₀
  -- PSH2 below the majorant `Ψ`, along `ℕ` lifted to the universe of `k`
  refine isPSH_of_antitone_of_homMajorant (ι := ULift.{u} ℕ) (θs := fun _ => θ)
    tendsto_const_nhds
    (ψ := fun n v => (Ks n.down).sup fun a => q n.down a v + (c n.down a : EReal))
    (fun n => hUpsh n.down) (fun v n n' h => hanti v h) (fun v => ?_) hne hΨ hmaj
  rw [hw v]
  exact (Equiv.ulift.iInf_comp
    (g := fun n => (Ks n).sup fun a => q n a v + (c n a : EReal))).symm

end MultiModel
end EnvelopeProperty
