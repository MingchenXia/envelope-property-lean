/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.FieldDescent
import EnvelopeProperty.Global.FiniteDescent
import EnvelopeProperty.Global.SmoothModelEP
import EnvelopeProperty.Global.Stein
import EnvelopeProperty.Global.FibreConstancyImport
import EnvelopeProperty.Projective.BlowupDescent

/-!
# Ample classes on normal models (FHX Theorem 6.1)

This file implements the blueprint nodes `prop:gl-ample-countable` and `thm:gl-normal-ample-ep` of
the global chapter `global.tex` (subsection `subsec:gl-ample`) of the formalization of Fang–Han–Xia,
*The envelope property for unibranch projective varieties* (FHX), Theorem 6.1
(`thm:normal-ample-EP`): *let `X` be a normal projective variety over `k`; then `EP_X(θ)` holds
for every ample class `θ ∈ N¹(X)_ℝ`*, in the model of `sec:global`
(`EnvelopeProperty.MultiModel`, `def:gl-model`) and for the positive classes `θ ∈ ℝ^r`
(`rmk:gl-model-comparison`: ampleness is used only through the sufficient condition "positive").
Step 2 (`prop:gl-ample-rational`, extension of scalars from countable subfields) is
`ProjSubvariety.hasEnvelopeProperty_one_of_forall_countable` (`Global/FieldDescent`).

## Main results

* `ProjSubvariety.Alteration.hasEnvelopeProperty_steinModel` and
  `ProjSubvariety.hasEnvelopeProperty_one_of_isProjNormal_of_countable`
  (**`prop:gl-ample-countable`**, FHX Step 1): for `k` countable and algebraically closed, under
  the imported `LocalPositivity k` (the hypothesis of Corollary
  5.26, `ProjSubvariety.isPSH_of_isPSH_comp_proj`),
  `BlowupFibreConstancy k` (`thm:gl-fibre-constancy`) and the characteristic-`0` import
  `SmoothEnvelopeCharZero k` of Theorem 3.1 (`h₀`), every projectively normal `X = V(I) ⊆ ℙᴺ` has
  `EP_X(1)`. De Jong's alterations are supplied internally by the proved model-form theorem.
* `MultiModel.eq_triv_of_rank_zero`, `MultiModel.hasEnvelopeProperty_of_rank_zero`: a model of rank
  `0` over an algebraically closed `k` has the single point `⋆`, and every class has the envelope
  property (the degenerate case `r = 0` of `thm:gl-normal-ample-ep`).
* `MultiModel.hasEnvelopeProperty_one_of_isNormal_of_forall_countable`: a normal model `𝒳` of rank
  `1` has `EP_𝒳(1)`, given `EP_{X₀}(1)` for projectively normal `X₀` over every countable
  algebraically closed field `k₀` (`hEP1`, the conclusion of `prop:gl-ample-countable`).
* `MultiModel.hasEnvelopeProperty_of_isNormal_of_pos` (**`thm:gl-normal-ample-ep`** from the
  conclusion `hEP1` of Step 1, FHX Step 3): every normal model `𝒳` of rank `r` over an
  algebraically closed `k` has `EP_𝒳(θ)` for every `θ ∈ ℝ^r` with positive coordinates. Its
  conclusion is the hypothesis `hample` of `MultiModel.hasEnvelopeProperty_of_isNormal_of_forall_pos`
  (`cor:nn-normal-ep`).
* `MultiModel.hasEnvelopeProperty_of_isNormal_of_pos_of_forall_countable`
  (**`thm:gl-normal-ample-ep`** under the imports of Step 1 for every countable algebraically
  closed field `k₀`): the combination of the two.

## Proof of `prop:gl-ample-countable`

Take an alteration `𝒴` of `X` (`ProjSubvariety.alteration`), its Stein factorization
`𝒴 → 𝒯 → 𝒳` (`Alteration.steinBeta`, `Alteration.steinHom`) and the data `T'`, `B`, `τ`, `ϑ`, `e`
of `lem:gl-stein`(3) (`Alteration.SteinBlowup`). For a nonempty family `(φ_i) ⊆ PSH(𝒯, 1)` bounded
above, `g = sup_i φ_i`: `φ_i ∘ β ∈ PSH(𝒴, (1, 0))` (`isPSH_comp_steinBeta`), so
`Φ = (g ∘ β)^⋆ ∈ PSH(𝒴, (1, 0))` by Theorem 3.1 on the smooth `𝒴`
(`hasEnvelopeProperty_of_isSmooth_of_nonneg`, `cor:gl-smooth-ep-nef`); `Φ ∘ ϑ⁻¹ ∈ PSH(B, (1/e, 0))`
(`SteinBlowup.isPSH_theta_iff`) is constant on the fibres of `μ` (`thm:gl-fibre-constancy`); as
`μ ∘ ϑ = τ ∘ β`, `Φ` is constant on the fibres of `β`, so `Φ = φ ∘ β`; Corollary 5.26 with
`a = 1/e` (`ProjSubvariety.isPSH_of_isPSH_comp_proj`, `thm:pg-psh-descent`) gives
`φ ∘ τ⁻¹ ∈ PSH(T', 1/e)`, i.e. `φ ∈ PSH(𝒯, 1)` (`SteinBlowup.isPSH_tau_iff`); and `φ = g^⋆` by
surjectivity of `β` (`steinBeta_surjective`). So `EP_𝒯(1)`; finite descent
(`FiniteHom.hasEnvelopeProperty`, `thm:gl-finite-descent`) gives `EP_𝒳(1)`, and the bridge
`hasEnvelopeProperty_iff_baseModel` (`lem:gl-bridge-psh`(1)) gives `EP_X(1)`.

## Proof of `thm:gl-normal-ample-ep`

By `lem:gl-ep-basic`(1) (`hasEnvelopeProperty_of_forall_rat_gt`, rational `q > θ`) and (2)
(`hasEnvelopeProperty_smul_iff`, `q = m⁻¹ a`) it suffices to treat `a ∈ ℕ^r` positive. The
Segre–Veronese model `𝒳_(a)` (`lem:gl-veronese`, `MultiModel.veronese`) is normal of rank `1`
(`isNormal_veronese`) with `EP_{𝒳_(a)}(1) ↔ EP_𝒳(a)` (`hasEnvelopeProperty_veronese_iff`). For a
normal model `𝒴` of rank `1`, a Veronese model `𝒴_(e)` is generated in degree `1`
(`exists_degOnePres_veronese`, from `lem:wu-veronese`; its degree-zero part is `k` since `k` is
algebraically closed) and normal; a presentation `w_0, …, w_N` gives a projectively normal
`V(I) ⊆ ℙᴺ` (`DegOnePres.isProjNormal_toProjSubvariety_iff`) with `EP_{V(I)}(1) ↔ EP_{𝒴_(e)}(1)`
(`DegOnePres.hasEnvelopeProperty_toProjSubvariety_iff`, `lem:gl-bridge-psh`(1)), and
`EP_{V(I)}(1)` holds by Step 2 (`prop:gl-ample-rational`) and `hEP1`. Then
`EP_𝒴(e) ↔ EP_{𝒴_(e)}(1)` (`lem:gl-veronese`) and `EP_𝒴(e) ↔ EP_𝒴(1)` (`lem:gl-ep-basic`(2)).

## Deviations from the blueprint

* `prop:gl-ample-countable`: `φ` is defined from `Φ` by `Function.extend` along `β` (fibre
  constancy says that `Φ` factors through `β`); the current hypothesis of Corollary 5.26 is
  `LocalPositivity k`; chart-regularizable nonflat norms are derived from it.
* `thm:gl-normal-ample-ep`: the blueprint passes from `𝒳_(a)` directly to "a Veronese of it, i.e.
  a projectively normal `V(I)`", leaving the rescaling of the class implicit; here the rank-one step
  (`hasEnvelopeProperty_one_of_isNormal_of_forall_countable`) is separate and the factor `e` of
  the second Veronese is removed by `lem:gl-ep-basic`(2). The theorem is proved from the conclusion
  `hEP1` of Step 1 (`hasEnvelopeProperty_of_isNormal_of_pos`) and then combined with Step 1
  (`hasEnvelopeProperty_of_isNormal_of_pos_of_forall_countable`).
* The case `r = 0` (not addressed in the blueprint, where models have `r ≥ 1` implicitly) is
  treated directly: `𝒳^an = {⋆}` (`S = k` by integrality over `k` and algebraic closedness), so
  the usc regularization of a bounded supremum is a real constant, which is psh.
-/

open scoped NNReal ENNReal Topology

open Topology Filter MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Step 1: countable fields (`prop:gl-ample-countable`) -/

namespace ProjSubvariety.Alteration

variable {k : Type u} [Field k] [IsAlgClosed k] {N : ℕ} {X : ProjSubvariety k N}
  (A : X.Alteration)

/-- **`EP_𝒯(1)` for the Stein model of an alteration** (the main step of
`prop:gl-ample-countable`, FHX Theorem 6.1, Step 1): let `k` be countable and algebraically
closed, `A` an alteration of `X = V(I)` with Stein factorization `𝒴 → 𝒯 → 𝒳`. Under the imports
of Corollary 5.26 (`LocalPositivity k`), fibre constancy
(`BlowupFibreConstancy k`) and Theorem 3.1 on the smooth `𝒴` (`h₀` in characteristic `0`), the
Stein model `𝒯` has the envelope property at the class `1`.

For `g = sup_i φ_i`: `Φ = (g ∘ β)^⋆ ∈ PSH(𝒴, (1, 0))` (smooth case), `Φ ∘ ϑ⁻¹ ∈ PSH(B, (1/e, 0))`
is constant on the fibres of `μ` (fibre constancy), hence `Φ = φ ∘ β`; Corollary 5.26 with
`a = 1/e` gives `φ ∈ PSH(𝒯, 1)`, and `φ = g^⋆` by surjectivity of `β`. -/
theorem hasEnvelopeProperty_steinModel [Countable k] [LocalPositivity k]
    [BlowupFibreConstancy k]
    (h₀ : ∀ [CharZero k], SmoothEnvelopeCharZero k) :
    A.steinModel.HasEnvelopeProperty fun _ => 1 := by
  obtain ⟨S⟩ := A.nonempty_steinBlowup
  intro F hF hpsh hbdd
  obtain ⟨C, hC⟩ := hbdd
  set g : A.steinModel.an → EReal := fun w => ⨆ u ∈ F, u w with hg
  -- `EP_𝒴((1, 0))` (Theorem 3.1 on the smooth model `𝒴`, `cor:gl-smooth-ep-nef`)
  have hEPY : A.model.HasEnvelopeProperty ![1, 0] :=
    MultiModel.hasEnvelopeProperty_of_isSmooth_of_nonneg h₀ A.isSmooth fun c => by
      refine Fin.cases ?_ (fun c => ?_) c
      · simp
      · obtain rfl := Fin.fin_one_eq_zero c
        simp
  -- the pulled-back family `φ_i ∘ β ⊆ PSH(𝒴, (1, 0))` (`lem:gl-stein`(2))
  set F' : Set (A.model.an → EReal) := (fun u => u ∘ A.steinBeta) '' F with hF'
  have hF'psh : ∀ u ∈ F', A.model.IsPSH ![1, 0] u := by
    rintro _ ⟨u, hu, rfl⟩
    have h := A.isPSH_comp_steinBeta (hpsh u hu)
    have e : MultiModel.steinDeg (fun _ : Fin 1 => (1 : ℝ)) = ![1, 0] := rfl
    rwa [e] at h
  have hsup : (fun y => ⨆ u ∈ F', u y) = g ∘ A.steinBeta := by
    funext y
    simp only [hF', Set.mem_image, iSup_exists, iSup_and, Function.comp_apply, hg]
    refine le_antisymm (iSup_le fun u => iSup_le fun v => iSup_le fun hv => iSup_le fun huv => ?_)
      (iSup₂_le fun v hv => le_iSup_of_le (v ∘ A.steinBeta) (le_iSup_of_le v
        (le_iSup_of_le hv (le_iSup_of_le rfl le_rfl))))
    subst huv
    exact le_iSup₂_of_le (f := fun (u : A.steinModel.an → EReal) (_ : u ∈ F) => u (A.steinBeta y))
      v hv le_rfl
  -- `Φ = (g ∘ β)^⋆ ∈ PSH(𝒴, (1, 0))`
  set Φ : A.model.an → EReal := uscReg (g ∘ A.steinBeta) with hΦdef
  have hΦ : A.model.IsPSH ![1, 0] Φ := by
    have h := hEPY F' (hF.image _) hF'psh ⟨C, by
      rintro _ ⟨u, hu, rfl⟩ y
      exact hC u hu _⟩
    rwa [hsup] at h
  -- transport to the blowup `B`: `Φ ∘ ϑ⁻¹ ∈ PSH(B, (1/e, 0))` (`lem:gl-stein`(3))
  have he : (0 : ℝ) < S.e := by exact_mod_cast S.e_pos
  set a : ℚ := 1 / S.e with hadef
  have ha : 0 < a := by
    have : (0 : ℚ) < S.e := by exact_mod_cast S.e_pos
    positivity
  have haR : ((a : ℚ) : ℝ) = 1 / S.e := by rw [hadef]; push_cast; ring
  have hea : (S.e : ℝ) * (1 / S.e) = 1 := mul_one_div_cancel he.ne'
  have hΦB : S.center.IsPSH ![(a : ℝ), 0] (Φ ∘ S.theta.symm) := by
    rw [S.isPSH_theta_iff (by rw [haR]; positivity) le_rfl]
    have h1 : (Φ ∘ S.theta.symm) ∘ S.theta = Φ := by
      funext y
      simp
    rw [h1, haR, hea]
    exact hΦ
  -- fibre constancy (`thm:gl-fibre-constancy`) and `μ ∘ ϑ = τ ∘ β`: `Φ` factors through `β`
  have hconst : Function.FactorsThrough Φ A.steinBeta := by
    intro y y' h
    have h1 := hΦB.apply_eq_of_proj_eq S.isProjNormal ha (y := S.theta y) (y' := S.theta y')
      (by rw [S.proj_theta, S.proj_theta, h])
    simpa using h1
  set φ : A.steinModel.an → EReal := Function.extend A.steinBeta Φ fun _ => ⊥ with hφdef
  have hφΦ : ∀ y, φ (A.steinBeta y) = Φ y := fun y => hconst.extend_apply _ y
  -- Corollary 5.26 on `T'` with `a = 1/e` (`thm:pg-psh-descent`)
  have hT' : S.target.IsPSH a (φ ∘ S.tau.symm) := by
    refine ProjSubvariety.isPSH_of_isPSH_comp_proj S.target S.isProjNormal S.center ha ?_
    have h1 : (φ ∘ S.tau.symm) ∘ S.center.proj = Φ ∘ S.theta.symm := by
      funext b
      obtain ⟨y, rfl⟩ := S.theta.surjective b
      simp [S.proj_theta, hφΦ]
    rw [h1]
    exact hΦB
  have hφ : A.steinModel.IsPSH (fun _ => 1) φ := by
    have h1 := (S.isPSH_tau_iff (by rw [haR]; positivity) _).1 hT'
    rw [haR, hea] at h1
    have h2 : (φ ∘ S.tau.symm) ∘ S.tau = φ := by
      funext w
      simp
    rwa [h2] at h1
  -- `φ = g^⋆`, by surjectivity of `β`
  have hβ := A.steinBeta_surjective
  have hφeq : uscReg g = φ := by
    refine le_antisymm (uscReg_le_of_le (FSSystemC.IsPSH.upperSemicontinuous hφ) fun w => ?_)
      fun w => ?_
    · obtain ⟨y, rfl⟩ := hβ w
      rw [hφΦ]
      exact le_uscReg (g ∘ A.steinBeta) y
    · obtain ⟨y, rfl⟩ := hβ w
      rw [hφΦ]
      exact uscReg_le_of_le ((upperSemicontinuous_uscReg g).comp A.continuous_steinBeta)
        (fun y => le_uscReg g (A.steinBeta y)) y
  change A.steinModel.IsPSH (fun _ => 1) (uscReg g)
  rw [hφeq]
  exact hφ

end ProjSubvariety.Alteration

namespace ProjSubvariety

variable {k : Type u} [Field k] [IsAlgClosed k] {N : ℕ}

/-- **Ample envelopes over countable fields** (**`prop:gl-ample-countable`**; FHX Theorem 6.1,
`thm:normal-ample-EP`, Step 1): let `k` be countable and algebraically closed, and assume the
imports of Corollary 5.26 (`LocalPositivity k`), fibre constancy (`BlowupFibreConstancy k`,
`thm:gl-fibre-constancy`) and, in characteristic `0`, Theorem 3.1 for smooth varieties (`h₀`,
`thm:import-sg-ep-char0`). Then every projectively normal `X = V(I) ⊆ ℙᴺ` has `EP_X(1)`.
De Jong's alterations are supplied internally by the proved model-form theorem.

`EP_𝒯(1)` for the Stein model of an alteration (`Alteration.hasEnvelopeProperty_steinModel`)
descends along the finite morphism `𝒯 → 𝒳` (`FiniteHom.hasEnvelopeProperty`,
`thm:gl-finite-descent`), and `EP_𝒳(1) ↔ EP_X(1)` (`lem:gl-bridge-psh`(1)). -/
theorem hasEnvelopeProperty_one_of_isProjNormal_of_countable [Countable k] [LocalPositivity k]
    [BlowupFibreConstancy k]
    (h₀ : ∀ [CharZero k], SmoothEnvelopeCharZero k) (X : ProjSubvariety k N)
    (hX : X.IsProjNormal) : X.HasEnvelopeProperty 1 := by
  have hT := X.alteration.hasEnvelopeProperty_steinModel h₀
  have hXm := X.alteration.steinHom.hasEnvelopeProperty (X.alteration.isNormal_baseModel hX) hT
  exact (X.alteration.hasEnvelopeProperty_iff_baseModel hX zero_le_one).2 hXm

end ProjSubvariety

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}

/-! ### Models of rank zero -/

section RankZero

/-- **A model of rank `0` is a point**: for `k` algebraically closed, every point of `𝒳^an` is the
trivial point `⋆`. Every homogeneous element lies in degree `0`, hence in `k`
(`exists_algebraMap_eq_of_mem_piece_zero`), where all points take the same values. -/
theorem eq_triv_of_rank_zero [IsAlgClosed k] (X : MultiModel k K 0) (v : X.an) : v = X.triv := by
  refine Subtype.ext (ext_of_ofPiece v.2.1 X.triv.2.1 fun a f hf => ?_)
  obtain rfl : a = 0 := Subsingleton.elim _ _
  obtain ⟨c, rfl⟩ := X.exists_algebraMap_eq_of_mem_piece_zero hf
  have hc : X.ofPiece hf = algebraMap k X.S c := X.ofPiece_algebraMap c
  rw [hc]
  by_cases hc0 : c = 0
  · simp [hc0]
  · rw [Berk.abs_algebraMap _ hc0, Berk.abs_algebraMap _ hc0]

/-- **The envelope property in rank `0`**: for `k` algebraically closed, every class of a model of
rank `0` has the envelope property, since `𝒳^an = {⋆}` (`eq_triv_of_rank_zero`) and real constants
are psh. -/
theorem hasEnvelopeProperty_of_rank_zero [IsAlgClosed k] (X : MultiModel k K 0)
    (θ : Fin 0 → ℝ) : X.HasEnvelopeProperty θ := by
  intro S hS hpsh hbdd
  obtain ⟨u₀, hu₀⟩ := hS
  obtain ⟨C, hC⟩ := hbdd
  set c : EReal := ⨆ u ∈ S, u X.triv with hc
  have hconst : (fun x => ⨆ u ∈ S, u x) = fun _ => c :=
    funext fun x => by rw [X.eq_triv_of_rank_zero x]
  have hc_top : c ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top C) (iSup₂_le fun u hu => hC u hu _)
  have hc_bot : c ≠ ⊥ :=
    ne_bot_of_le_ne_bot (IsPSH.apply_triv_ne_bot (hpsh u₀ hu₀))
      (le_iSup₂_of_le (f := fun (u : X.an → EReal) (_ : u ∈ S) => u X.triv) u₀ hu₀ le_rfl)
  rw [hconst, uscReg_eq_self upperSemicontinuous_const, ← EReal.coe_toReal hc_top hc_bot]
  exact X.isPSH_const (X.mem_nefCone_of_nonneg fun i => i.elim0) _

end RankZero

/-! ### Step 3: positive classes on normal models (`thm:gl-normal-ample-ep`) -/

section NormalAmple

variable [IsAlgClosed k]

/-- **The envelope property of `O(1)` on normal models of rank one** (the rank-one step of
`thm:gl-normal-ample-ep`): let `k` be algebraically closed and `𝒴` a normal model of rank `1`. If
`EP_{X₀}(1)` holds for every projectively normal `X₀ ⊆ ℙᴹ_{k₀}` over every countable algebraically
closed field `k₀` (`hEP1`, the conclusion of `prop:gl-ample-countable`), then
`EP_𝒴(1)`.

A Veronese model `𝒴_(e)` is generated in degree `1` (`exists_degOnePres_veronese`) and normal, so
a presentation gives a projectively normal `V(I)` with `EP_{V(I)}(1)` (`prop:gl-ample-rational`,
`ProjSubvariety.hasEnvelopeProperty_one_of_forall_countable`); then `EP_{𝒴_(e)}(1)`
(`lem:gl-bridge-psh`(1)), `EP_𝒴(e)` (`lem:gl-veronese`) and `EP_𝒴(1)` (`lem:gl-ep-basic`(2)). -/
theorem hasEnvelopeProperty_one_of_isNormal_of_forall_countable
    (hEP1 : ∀ (k₀ : Type u) [Field k₀] [IsAlgClosed k₀] [Countable k₀] {M : ℕ}
      (X₀ : ProjSubvariety k₀ M), X₀.IsProjNormal → X₀.HasEnvelopeProperty 1)
    {Y : MultiModel k K 1} (hY : Y.IsNormal) : Y.HasEnvelopeProperty fun _ => 1 := by
  obtain ⟨e, he, N, ⟨P⟩⟩ := Y.exists_degOnePres_veronese
  have he' : (0 : ℝ) < e := by
    have := he 0
    rw [Finsupp.single_eq_same] at this
    exact_mod_cast this
  have hV : P.toProjSubvariety.IsProjNormal :=
    P.isProjNormal_toProjSubvariety_iff.2 (Y.isNormal_veronese (ha := he) hY)
  have hEP : P.toProjSubvariety.HasEnvelopeProperty 1 :=
    P.toProjSubvariety.hasEnvelopeProperty_one_of_forall_countable hV
      fun k₀ _ _ _ X₀ hX₀ => hEP1 k₀ X₀ hX₀
  have h1 := (P.hasEnvelopeProperty_toProjSubvariety_iff hV zero_le_one).1 hEP
  have h2 := (Y.hasEnvelopeProperty_veronese_iff he).1 h1
  refine (hasEnvelopeProperty_smul_iff (Y.mem_nefCone_of_nonneg fun _ => zero_le_one) he').1 ?_
  convert h2 using 2 with c
  obtain rfl := Fin.fin_one_eq_zero c
  simp

/-- **Ample classes on normal models** (**`thm:gl-normal-ample-ep`**; FHX Theorem 6.1,
`thm:normal-ample-EP`, Step 3, for the positive classes `θ ∈ ℝ^r`): let `k` be algebraically closed
and `𝒳` a normal model of rank `r` over `k`. If `EP_{X₀}(1)` holds for every projectively normal
`X₀ ⊆ ℙᴹ_{k₀}` over every countable algebraically closed field `k₀` (`hEP1`, the conclusion of
`prop:gl-ample-countable`, FHX Step 1, in this form), then `EP_𝒳(θ)` holds for
every `θ ∈ ℝ^r` with positive coordinates. The conclusion is the hypothesis `hample` of
`MultiModel.hasEnvelopeProperty_of_isNormal_of_forall_pos` (`cor:nn-normal-ep`).

By `lem:gl-ep-basic`(1),(2) it suffices to treat positive `a ∈ ℕ^r`; the Segre–Veronese model
`𝒳_(a)` is normal of rank `1` with `EP_{𝒳_(a)}(1) ↔ EP_𝒳(a)` (`lem:gl-veronese`), and
`hasEnvelopeProperty_one_of_isNormal_of_forall_countable` applies. For `r = 0` see
`hasEnvelopeProperty_of_rank_zero`. -/
theorem hasEnvelopeProperty_of_isNormal_of_pos
    (hEP1 : ∀ (k₀ : Type u) [Field k₀] [IsAlgClosed k₀] [Countable k₀] {M : ℕ}
      (X₀ : ProjSubvariety k₀ M), X₀.IsProjNormal → X₀.HasEnvelopeProperty 1)
    {X : MultiModel k K r} (hX : X.IsNormal) {θ : Fin r → ℝ} (hθ : ∀ c, 0 < θ c) :
    X.HasEnvelopeProperty θ := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact X.hasEnvelopeProperty_of_rank_zero θ
  have : NeZero r := ⟨hr.ne'⟩
  refine hasEnvelopeProperty_of_forall_rat_gt (X.mem_nefCone_of_nonneg fun c => (hθ c).le)
    fun q hq => ?_
  have hqpos : ∀ c, (0 : ℚ) < q c := fun c => by
    have h : (0 : ℝ) < q c := (hθ c).trans (hq c)
    exact_mod_cast h
  have hq0 : 0 ≤ q := fun c => (hqpos c).le
  obtain ⟨m, hm, d, hd⟩ := exists_nat_mul_rat_vec_eq_nat_of_nonneg hq0
  set a : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm d
  have had : ∀ c, a c = d c := fun c => rfl
  have ha : ∀ c, 0 < a c := fun c => by
    have h2 : (0 : ℚ) < d c := by rw [hd c]; exact mul_pos (by exact_mod_cast hm) (hqpos c)
    rw [had c]
    exact_mod_cast h2
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hqa : (fun c => (q c : ℝ)) = (m : ℝ)⁻¹ • fun c => (a c : ℝ) := by
    funext c
    have := hd c
    rw [Pi.smul_apply, smul_eq_mul, had c]
    have h' : ((d c : ℚ) : ℝ) = (m : ℝ) * (q c : ℝ) := by exact_mod_cast this
    rw [show ((d c : ℕ) : ℝ) = ((d c : ℚ) : ℝ) by norm_cast, h', ← mul_assoc,
      inv_mul_cancel₀ hm'.ne', one_mul]
  rw [hqa, hasEnvelopeProperty_smul_iff (X.mem_nefCone_of_nonneg fun c => by positivity)
    (inv_pos.2 hm')]
  have h1 := hasEnvelopeProperty_one_of_isNormal_of_forall_countable hEP1
    (X.isNormal_veronese (ha := ha) hX)
  have h2 := (X.hasEnvelopeProperty_veronese_iff ha).1 h1
  simpa using h2

/-- **Ample classes on normal models under the imports of Step 1** (**`thm:gl-normal-ample-ep`**;
FHX Theorem 6.1, `thm:normal-ample-EP`, for the positive classes `θ ∈ ℝ^r`): let `k` be
algebraically closed and `𝒳` a normal model of rank `r` over `k`. Assume, for every countable
algebraically closed field `k₀`, the imports of Step 1: `LocalPositivity k₀`
(FHX Lemma 5.5), `BlowupFibreConstancy k₀` (`thm:gl-fibre-constancy`) and, in characteristic
`0`, `SmoothEnvelopeCharZero k₀` (`thm:import-sg-ep-char0`). Then `EP_𝒳(θ)` holds for every
`θ ∈ ℝ^r` with positive coordinates.

This combines Step 1 (`ProjSubvariety.hasEnvelopeProperty_one_of_isProjNormal_of_countable`)
over each `k₀` with `hasEnvelopeProperty_of_isNormal_of_pos` (Steps 2 and 3). -/
theorem hasEnvelopeProperty_of_isNormal_of_pos_of_forall_countable
    (hLP : ∀ (k₀ : Type u) [Field k₀] [IsAlgClosed k₀] [Countable k₀], LocalPositivity k₀)
    (hFC : ∀ (k₀ : Type u) [Field k₀] [IsAlgClosed k₀] [Countable k₀], BlowupFibreConstancy k₀)
    (h₀ : ∀ (k₀ : Type u) [Field k₀] [IsAlgClosed k₀] [Countable k₀] [CharZero k₀],
      SmoothEnvelopeCharZero k₀)
    {X : MultiModel k K r} (hX : X.IsNormal) {θ : Fin r → ℝ} (hθ : ∀ c, 0 < θ c) :
    X.HasEnvelopeProperty θ :=
  hasEnvelopeProperty_of_isNormal_of_pos (fun k₀ _ _ _ _ X₀ hX₀ => by
    have := hLP k₀
    have := hFC k₀
    exact X₀.hasEnvelopeProperty_one_of_isProjNormal_of_countable (h₀ k₀) hX₀) hX hθ

end NormalAmple

end MultiModel

end EnvelopeProperty
