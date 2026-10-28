/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.WeightedNorm

/-!
# Finite descent of the envelope property

This file proves the blueprint node `thm:gl-finite-descent` of `global.tex` (subsection
`subsec:gl-ample`) for the formalization of Fang–Han–Xia, *The envelope property for unibranch
projective varieties* (FHX, §4, Theorem 4.2, `thm:finite-normal-descent`; revisions `832e086` and
of 2026-10-28):

**Theorem** (`MultiModel.FiniteHom.hasEnvelopeProperty`). Let `k` be algebraically closed,
`h : 𝒯 → 𝒳` a finite morphism of models (`MultiModel.FiniteHom`, `def:gl-maps`) with `𝒳`
normal, and `θ ∈ ℝ^r` any class (decision D-NN1). If `θ` has the envelope property on `𝒯`, it has
the envelope property on `𝒳`. **No normality of `𝒯` is assumed.**

## Proof (usc form, as in the blueprint)

Let `(φ_i) ⊆ PSH(𝒳, θ)` be a nonempty family bounded above and `g = sup_i φ_i`. The pullbacks
`φ_i ∘ h` are `θ`-psh on `𝒯` (`lem:gl-pullback`), so `F = (g ∘ h)^⋆ ∈ PSH(𝒯, θ)` by `EP_𝒯(θ)`. Let
`F_α ∈ 𝓗(𝒯, a_α)` decrease to `F`, `a_α → θ`, and `G_α = Av_h(F_α) ∈ 𝓗(𝒳, a_α)`
(`prop:gl-weighted-norm`, `MultiModel.FiniteHom.avFSData`); the `G_α` decrease
(`MultiModel.FiniteHom.eval_avFSData_le`), so `G = inf_α G_α` is usc. On `𝒳^div ⊆ 𝒳^val`,
`G_α(v) = d⁻¹ ∑_{h(w) = v} d(w/v) F_α(w)` (`MultiModel.FiniteHom.eval_avFSData`). Since
`g ∘ h ≤ F ≤ g^⋆ ∘ h`:

* `g(v) ≤ G(v)` on `𝒳^div` (each `F_α(w) ≥ F(w) ≥ g(v)`, and the weights add up to `d`,
  `lem:gl-finite-fibres`); by divisorial comparison (`thm:gl-comparison`) `φ_i ≤ G` everywhere,
  so `g ≤ G`, `G(⋆) > -∞`, and `g^⋆ ≤ G`;
* `G(v) ≤ g^⋆(v)` on `𝒳^div`: for real `c > g^⋆(v)` each of the finitely many `F(w)`, `w ↦ v`, is
  `< c`, so some `F_α(w) < c` for a common `α` (directedness), and then `G_α(v) ≤ c`;
* `G` is `θ`-psh (a decreasing limit of Fubini–Study functions with classes `a_α → θ`, finite at
  `⋆`), so `G ≤ g^⋆` everywhere by comparison.

Hence `g^⋆ = G ∈ PSH(𝒳, θ)`.

## Deviations from FHX

* FHX prove Theorem 4.2 through Proposition 2.4 (`prop:EP-criterion`, Proposition 2.2 in revision
  `832e086`: EP ⇔ convergence of increasing nets on `X^div`, which needs BJ22 Thm 5.6 and
  finiteness of psh functions on `X^div`); the usc form above avoids both (PLAN-68, literature
  issue 2).
* Revision `832e086` of FHX assumes `T` normal (it uses divisorial points of `T` over divisorial
  points of `X`); here the points over `v ∈ 𝒳^div` need not be divisorial, only of generic support,
  and normality of `𝒯` is never used (PLAN-68, literature issue 5; LITERATURE-ERRATA §3). The
  revision of 2026-10-28 assumes `T` integral only, as here.
-/

open scoped NNReal ENNReal Topology

open Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

namespace MultiModel

variable {k : Type u} [Field k] [IsAlgClosed k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r}

namespace FiniteHom

variable {E : Type u} [Field E] [Algebra K E] [Algebra k E] [IsScalarTower k K E]
  {T : MultiModel k E r} (h : FiniteHom T X)

include h in
/-- **Finite descent of the envelope property** (`thm:gl-finite-descent`, FHX Theorem 4.2,
`thm:finite-normal-descent`): for a finite morphism `h : 𝒯 → 𝒳` of models over an algebraically
closed field with `𝒳` normal and **any** class `θ ∈ ℝ^r`, `EP_𝒯(θ)` implies `EP_𝒳(θ)`. The model
`𝒯` need not be normal. -/
theorem hasEnvelopeProperty (hX : X.IsNormal) {θ : Fin r → ℝ} (hT : T.HasEnvelopeProperty θ) :
    X.HasEnvelopeProperty θ := by
  classical
  have := h.finiteDimensional
  intro S hS hSpsh' hSbdd
  have hSpsh : ∀ u ∈ S, X.IsPSH θ u := hSpsh'
  obtain ⟨C, hC⟩ := hSbdd
  set g : X.an → EReal := fun v => ⨆ u ∈ S, u v with hg
  -- the pulled-back family and `F = (g ∘ h)^⋆`
  set S' : Set (T.an → EReal) := (fun u => u ∘ h.anMap) '' S with hS'
  have hS'psh : ∀ u' ∈ S', T.IsPSH θ u' := by
    rintro _ ⟨u, hu, rfl⟩
    exact h.isPSH_comp (hSpsh u hu)
  have hF : T.IsPSH θ (uscReg fun w => ⨆ u' ∈ S', u' w) :=
    hT S' (hS.image _) hS'psh ⟨C, by rintro _ ⟨u, hu, rfl⟩ w; exact hC u hu _⟩
  set F : T.an → EReal := uscReg fun w => ⨆ u' ∈ S', u' w with hFdef
  have hgS' : ∀ w, (⨆ u' ∈ S', u' w) = g (h.anMap w) := fun w => by
    rw [hS', iSup_image]
    rfl
  have hgF : ∀ w, g (h.anMap w) ≤ F w := fun w => by
    rw [← hgS' w]
    exact le_uscReg (fun w => ⨆ u' ∈ S', u' w) w
  have hFg : ∀ w, F w ≤ uscReg g (h.anMap w) := by
    have hle : (fun w => ⨆ u' ∈ S', u' w) ≤ fun w => uscReg g (h.anMap w) := fun w => by
      show (⨆ u' ∈ S', u' w) ≤ uscReg g (h.anMap w)
      rw [hgS']
      exact le_uscReg g _
    exact uscReg_le_of_le ((upperSemicontinuous_uscReg g).comp h.continuous_anMap) hle
  -- a decreasing net of Fubini–Study functions converging to `F`
  obtain ⟨-, -, ι, _, _, _, a, f, hf, ha, hanti, hinf⟩ := hF
  have hf' : ∀ i, ∃ D : T.FSData (a i), (∃ t ∈ D.terms, t.1 ≠ 0) ∧ ∀ w, f i w = D.eval w := hf
  choose D hD0 hDf using hf'
  -- the weighted coefficient norms `G_α = Av_h(F_α)` and their limit `G`
  set G : ι → X.an → EReal := fun i => (h.avFSData hX (D i)).eval with hGdef
  set Gl : X.an → EReal := fun v => ⨅ i, G i v with hGldef
  set n := Module.finrank K E with hn
  have hn0 : 0 < n := Module.finrank_pos
  have hG : ∀ i (v : X.an) (hv : X.HasGenericSupport v.1), G i v =
      (((n : ℝ)⁻¹ : ℝ) : EReal) * ∑ w ∈ h.fibre v, ((T.fibreDeg K w : ℝ) : EReal) * f i w :=
    fun i v hv => by
      show (h.avFSData hX (D i)).eval v = _
      rw [h.eval_avFSData hX (D i) v hv]
      simp only [hDf]
      rfl
  have hdeg : ∀ (v : X.an) (_ : X.HasGenericSupport v.1), ∀ w ∈ h.fibre v,
      1 ≤ T.fibreDeg K w := fun v hv w hw =>
    one_le_fibreDeg (h.hasGenericSupport_of_anMap (by rw [(h.mem_fibre).1 hw]; exact hv))
  have hGanti : ∀ v, Antitone fun i => G i v := fun v i i' hii' =>
    h.eval_avFSData_le hX (D i') (D i) (hD0 i')
      (fun w => by rw [← hDf, ← hDf]; exact hanti w hii') v
  have hGusc : UpperSemicontinuous Gl :=
    upperSemicontinuous_iInf fun i => (h.avFSData hX (D i)).continuous_eval.upperSemicontinuous
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hGtop : ∀ v, Gl v ≠ ⊤ := fun v =>
    ne_top_of_le_ne_top ((h.avFSData hX (D i₀)).eval_ne_top v) (iInf_le _ i₀)
  -- lower bound on `𝒳^div`: `g ≤ G`
  have hlow : ∀ v, X.IsDivisorial v → g v ≤ Gl v := by
    intro v hv
    have hgv := hv.hasGenericSupport
    refine le_iInf fun i => ?_
    rw [hG i v hgv]
    calc g v = (((n : ℝ)⁻¹ : ℝ) : EReal) *
          ∑ w ∈ h.fibre v, ((T.fibreDeg K w : ℝ) : EReal) * g v :=
          (ereal_wavg_const _ _ (hdeg v hgv) (h.sum_fibreDeg v hgv) hn0 (g v)).symm
      _ ≤ _ := ereal_wavg_mono _ _ _ fun w hw => by
          calc g v = g (h.anMap w) := by rw [(h.mem_fibre).1 hw]
            _ ≤ F w := hgF w
            _ = ⨅ i, f i w := hinf w
            _ ≤ f i w := iInf_le _ i
  -- comparison: `φ_i ≤ G`, hence `g ≤ G` and `g^⋆ ≤ G`
  have hu_le : ∀ u ∈ S, u ≤ Gl := fun u hu =>
    (hSpsh u hu).le_of_forall_isDivisorial_le hGusc hGtop fun v hv =>
      (le_iSup₂ (f := fun u (_ : u ∈ S) => u v) u hu).trans (hlow v hv)
  have hg_le : g ≤ Gl := fun v => iSup₂_le fun u hu => hu_le u hu v
  have hgstar_le : uscReg g ≤ Gl := uscReg_le_of_le hGusc hg_le
  -- upper bound on `𝒳^div`: `G ≤ g^⋆`
  have hup : ∀ v, X.IsDivisorial v → Gl v ≤ uscReg g v := by
    intro v hv
    have hgv := hv.hasGenericSupport
    by_contra hlt
    push Not at hlt
    obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have hex : ∀ w ∈ h.fibre v, ∃ i, f i w < c := fun w hw => by
      have h1 : F w < c := (hFg w).trans_lt (by rw [(h.mem_fibre).1 hw]; exact hc1)
      rw [hinf w] at h1
      exact iInf_lt_iff.1 h1
    choose! α hα using hex
    obtain ⟨β, hβ⟩ := Finset.exists_le ((h.fibre v).image α)
    have h3 : G β v ≤ c := by
      rw [hG β v hgv]
      calc _ ≤ (((n : ℝ)⁻¹ : ℝ) : EReal) *
            ∑ w ∈ h.fibre v, ((T.fibreDeg K w : ℝ) : EReal) * (c : EReal) :=
            ereal_wavg_mono _ _ _ fun w hw =>
              (hanti w (hβ _ (Finset.mem_image_of_mem α hw))).trans (hα w hw).le
        _ = c := ereal_wavg_const _ _ (hdeg v hgv) (h.sum_fibreDeg v hgv) hn0 _
    exact absurd ((iInf_le _ β).trans h3) (not_le.2 hc2)
  -- `G` is `θ`-psh
  have hfin : ∃ v, Gl v ≠ ⊥ := by
    obtain ⟨u, hu⟩ := hS
    exact ⟨X.triv, ne_bot_of_le_ne_bot (hSpsh u hu).apply_triv_ne_bot (hu_le u hu X.triv)⟩
  have hGpsh : X.IsPSH θ Gl :=
    FSSystemC.isPSH_of_iInf (F := X.fsSystem) hfin a G
      (fun i => h.isFS_avFSData hX (D i) (hD0 i)) ha hGanti fun _ => rfl
  -- comparison: `G ≤ g^⋆`
  have hgstar_top : ∀ v, uscReg g v ≠ ⊤ := fun v =>
    ne_top_of_le_ne_top (EReal.coe_ne_top C)
      (uscReg_le_of_le upperSemicontinuous_const (fun v => iSup₂_le fun u hu => hC u hu v) v)
  have hGle : Gl ≤ uscReg g :=
    hGpsh.le_of_forall_isDivisorial_le (upperSemicontinuous_uscReg g) hgstar_top hup
  have heq : uscReg g = Gl := le_antisymm hgstar_le hGle
  change X.IsPSH θ (uscReg g)
  rw [heq]
  exact hGpsh

end FiniteHom

end MultiModel

end EnvelopeProperty
