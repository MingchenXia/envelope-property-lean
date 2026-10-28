/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.NonflatWeights
import EnvelopeProperty.Local.NonflatLocalApprox
import EnvelopeProperty.Local.ChartRegularizable
import EnvelopeProperty.Local.Hull

/-!
# Identification of the extended norm off the étale locus

This file formalizes `lem:nf-hull-approach` and `prop:nf-identification` of the blueprint chapter
`nonflat-route.tex`, the route to Fang–Han–Xia, *The envelope property for unibranch projective
varieties*, Proposition 5.22 (`prop:nonflat-norm`; revision 832e086, Section 5,
`sec:normal-local-regularization`; the proof of Proposition 5.22 in revision d64981e, last step
"identification off `S_0`") that does not use the subharmonic functions of FHX Lemma 5.21
(`lem:curves`).

## Setting

`π = Spec φ : Y = Spec A → S = Spec B` is finite and injective, `B ≅ k[x]_{h_S}` a principal open
of `𝔸ⁿ`, `h ∈ B` a good locus element (`IsNonflatGoodLocus`, `lem:nf-good-locus`), `S_0 = S_h`, and
`N_π u = nonflatNorm φ hφ h u` the norm with the weights of `def:nf-weights` (lane NF6). A rigid
datum `τ : ℋ(s) → F` gives the `F`-point `ξ` of `B_F = F ⊗_k B ≅ F[x]_{h_S}`, a line
`ι : B_F → Q = F[t]_p` through `ξ` (`t ↦ a + t w`), its normalized curve `R' = ∏_P D_P` with
`q : Spec R' → Spec Q`, `p : Spec R' → Spec A_F`, the point `ξ : t ↦ 0` of the line and the Gauss
points `ζ_r` of the discs `|t| ≤ r` (`nonflatEvalPoint`, `nonflatGaussPoint`, lane NF4).

## Main results

* **`lem:nf-hull-approach`**, for any `k`-algebra map `ι : B → Q` (in the application `B → B_F → Q`)
  and `s_r = ι^* ζ_r`: `nonflat_comap_nonflatGaussPoint_val_ne_zero` (`s_r ∈ S_0^an` for `r > 0`
  if `ι(h) ≠ 0`), `tendsto_comap_nonflatGaussPoint` (`s_r → ι^* ξ`),
  `eventually_mem_hull_comap_nonflatGaussPoint` (`ι^* ξ ∈ hull {s_r}` for small `r`, from the
  maximum modulus principle `|f(0)| ≤ |f|_{ζ_r}`), and the consequences
  `SatisfiesHullIneq.eventually_le_comap_nonflatGaussPoint` (`v(ι^* ξ) ≤ v(s_r)`) and
  `UpperSemicontinuous.eventually_comap_nonflatGaussPoint_lt` (`limsup v(s_r) ≤ v(ι^* ξ)`),
  packaged for `v ∈ ℛ(S)` as `IsRegularizable.nonflat_hull_approach`;
  `NonflatRigidEmbedding.comap_coordLine_nonflatEvalPoint` (`ι^* ξ = s` on the line through the
  rigid point).
* `nonflat_eq_flatNormFun_of_gaussRay`: the analytic core of `prop:nf-identification` on an
  abstract finite free cover `R` of the open line: if `U` is, near every point over `ξ`, a
  decreasing limit of functions of Fubini–Study type with a fixed denominator, upper
  semicontinuous there, and `N_q U(z) = v(ι^* z)` wherever `|c|_z ≠ 0` (`c ≠ 0`), then
  `v(ι^* ξ) = N_q U(ξ)` for every `v` satisfying the hull inequality and upper semicontinuous.
  It combines the two bounds of lane NF4 (`eventually_flatNormFun_nonflatEvalPoint_le`,
  `eventually_flatNormFun_nonflatGaussPoint_lt`) with the hull approach through the order lemma
  `nonflat_eq_of_squeeze`.
* On the normalized curve of a line through a rigid datum:
  `NonflatRigidEmbedding.exists_flatNormFun_line_eq_nonflatNorm` (`lem:nf-generic-fibre` in the form
  `N_q (u ∘ r ∘ p)(z) = N_π u(ι^* z)`, with `ι^* z ∈ S_0^an`, for `|c|_z ≠ 0`),
  `NonflatRigidEmbedding.exists_nonflatLocalApprox_line` (`lem:nf-local-approx` for `u ∘ r ∘ p`,
  the line admissible for `χ_{σ₀}(0)`) and `NonflatRigidEmbedding.eq_sum_rigidWeight_of_line`
  (the identification with the rigid weights of `τ`).
* **`prop:nf-identification`**: `IsChartRegularizable.eq_nonflatNorm`: if `u` is regularizable on
  the charts of a blowup (`IsChartRegularizable`) and `v ∈ ℛ(S)` agrees with `N_π u` on `S_0^an`,
  then `v = N_π u` on `S^an`; `IsChartRegularizable.eq_nonflatNorm_of_satisfiesHullIneq` is the
  pointwise form for every `v` satisfying the hull inequality and upper semicontinuous.

## Comparison with the blueprint

* The covering hypothesis of `prop:nf-identification` (regularizability of `u` on principal opens
  covering `Y^an \ Z^an`) is not needed: the local approximants of `lem:nf-local-approx` come from
  the blowup charts at every point of the normalized curve (lane NF5's Case B), as soon as the line
  is admissible for `h · χ_{σ₀}(0)` for some `0 ≠ σ₀` in the witness. It is still needed in
  `prop:nf-nonflat-norm` (`Local/NonflatNorm`), for the regularity of `N_π u` on `S_0`.
* Of `v ∈ ℛ(S)` only the hull inequality (`IsRegularizable.satisfiesHullIneq`) and upper
  semicontinuity are used.
* "For `0 < ε < ε₀`" is `∀ᶠ r in 𝓝 0` restricted to `r > 0`; the limits superior are stated as
  "for every `C > v(s)`, eventually `v(s_r) < C`".
* The upper bound needs `u ∘ r ∘ p < +∞` at the points over `ξ`; this follows from the local
  approximants (functions of FS type are `< +∞`).
* The identification is proved for the rigid weights of an arbitrary rigid datum and separating
  element (`NonflatRigidEmbedding.eq_sum_rigidWeight_of_line`); the canonical choices of
  `nonflatWeight` (`def:nf-weights`) are a special case. The point `s` need not lie off `S_0`.
-/

open scoped NNReal ENNReal Topology TensorProduct
open Polynomial Filter

noncomputable section

universe u

namespace EnvelopeProperty

open Berk AffineLine ReducedComponents

/-- `normalizationMapAlg K I` is the normalization map `normalizationMap I`. -/
theorem nonflat_normalizationMapAlg_apply {R K : Type*} [CommRing R] [CommRing K] [Algebra K R]
    (I : Ideal R) (x : R) : normalizationMapAlg K I x = normalizationMap I x := rfl

/-! ### Nonvanishing on every factor of the normalized curve -/

namespace AffineLine

variable {F σ B : Type u} [Field F] [CommRing B] [Algebra F B]
  (a b : σ → F) (j : σ) (g : MvPolynomial σ F) (hb : b j ≠ 0) (φ : Localization.Away g →ₐ[F] B)
  {k : Type*} [Field k] [Algebra k F] [Algebra k B] [IsScalarTower k F B]

include hb in
/-- **Elements of the base nonzero on the line are nonzero on every factor** of the normalized
curve `R' = ∏_P D_P` (`lem:nf-local-approx`): if `θ(x) = φ(r)` with `ι(r) ≠ 0` in `Q`, then the
image of `x` in `R'` is nonzero in every factor `D_P`, since `Q → D_P` is injective. -/
theorem nonflatLine_comp_apply_ne_zero [Fintype σ] [IsDomain B] (hg : g ≠ 0)
    (hline : subst a b g ≠ 0) (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ)
    {T : Type*} [CommRing T] [Algebra k T] (θ : T →ₐ[k] B) {x : T} {r : Localization.Away g}
    (hr : principalLineHom a b g r ≠ 0) (hx : θ x = φ r) :
    letI := φ.toRingHom.toAlgebra
    haveI := nonflatLine_isScalarTower_k_base (k := k) g φ
    haveI := nonflatLine_isScalarTower_k_base_curve (k := k) a b j g φ
    ∀ i, (((normalizationMapAlg (Localization.Away g)
      (linePreimageIdeal a b j g φ)).restrictScalars k).comp θ) x i ≠ 0 := by
  intro i
  change normalizationMap _ (θ x) i ≠ 0
  rw [hx, ← normalizedLineProductHom_principalLineHom a b j g hb φ r]
  exact (map_ne_zero_iff _ (normalizedComponentLineHom_injective a b j g hb φ i.1 i.2 hg hline hφ
    hiφ)).2 hr

end AffineLine

/-! ### An order lemma -/

/-- **Squeeze.** Let `N, V : ℝ_{≥0} → [-∞, ∞]` agree for small `r > 0`. If `N₀ ≤ N(r)` for small
`r` and `limsup_{r → 0} N(r) ≤ N₀` (for every `C > N₀`, eventually `N(r) < C`), and likewise
`v₀ ≤ V(r)` and `limsup V(r) ≤ v₀`, then `v₀ = N₀`. -/
theorem nonflat_eq_of_squeeze {N V : ℝ≥0 → EReal} {N₀ v₀ : EReal}
    (hNV : ∀ᶠ r in 𝓝 (0 : ℝ≥0), 0 < r → N r = V r)
    (hNlow : ∀ᶠ r in 𝓝 (0 : ℝ≥0), N₀ ≤ N r)
    (hNup : ∀ C, N₀ < C → ∀ᶠ r in 𝓝 (0 : ℝ≥0), N r < C)
    (hVlow : ∀ᶠ r in 𝓝 (0 : ℝ≥0), v₀ ≤ V r)
    (hVup : ∀ C, v₀ < C → ∀ᶠ r in 𝓝 (0 : ℝ≥0), V r < C) : v₀ = N₀ := by
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ≥0), 0 < r := self_mem_nhdsWithin
  apply le_antisymm
  · refine le_of_forall_gt_imp_ge_of_dense fun C hC => ?_
    obtain ⟨r, hr0, hr1, hr2, hr3⟩ := (hpos.and ((hNV.and ((hNup C hC).and hVlow)).filter_mono
      nhdsWithin_le_nhds)).exists
    exact (hr3.trans ((hr1 hr0).symm ▸ hr2).le)
  · refine le_of_forall_gt_imp_ge_of_dense fun C hC => ?_
    obtain ⟨r, hr0, hr1, hr2, hr3⟩ := (hpos.and ((hNV.and ((hVup C hC).and hNlow)).filter_mono
      nhdsWithin_le_nhds)).exists
    exact (hr3.trans ((hr1 hr0) ▸ hr2).le)

/-! ### Approach through the étale locus (`lem:nf-hull-approach`) -/

section HullApproach

variable {k : Type*} [Field k] {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra k F]
  (hF : ∀ c : k, c ≠ 0 → ‖algebraMap k F c‖ = 1) {p : F[X]} (hp : p.eval 0 ≠ 0)
  {B : Type*} [CommRing B] [Algebra k B] (ι : B →ₐ[k] OpenLineRing p)

/-- **`s_r ∈ S_0^an`** (`lem:nf-hull-approach`): for `r > 0` and `ι(e) ≠ 0`,
`|e|_{s_r} = |ι(e)|_{ζ_r} ≠ 0`, as `ζ_r` has zero kernel. -/
theorem nonflat_comap_nonflatGaussPoint_val_ne_zero {r : ℝ≥0} (hr : 0 < r) {e : B}
    (he : ι e ≠ 0) : (comap ι (nonflatGaussPoint hF p hp r)).val e ≠ 0 :=
  nonflatGaussPoint_val_ne_zero hF p hp hr he

/-- **`s_r → s`** (`lem:nf-hull-approach`): `s_r = ι^* ζ_r → ι^* ξ` as `r → 0`. -/
theorem tendsto_comap_nonflatGaussPoint :
    Tendsto (fun r => comap ι (nonflatGaussPoint hF p hp r)) (𝓝 0)
      (𝓝 (comap ι (nonflatEvalPoint hF p hp))) :=
  ((continuous_comap ι).tendsto _).comp (tendsto_nonflatGaussPoint_zero hF p hp)

/-- **`s ∈ hull {s_r}`** (`lem:nf-hull-approach`): for small `r` and every `f ∈ B`,
`|f|_{ι^* ξ} = |ι(f)(0)| ≤ |ι(f)|_{ζ_r} = |f|_{s_r}` (`exists_nonflatGaussPoint_maxModulus`). -/
theorem eventually_mem_hull_comap_nonflatGaussPoint :
    ∀ᶠ r in 𝓝 (0 : ℝ≥0), comap ι (nonflatEvalPoint hF p hp) ∈
      hull {comap ι (nonflatGaussPoint hF p hp r)} := by
  filter_upwards [eventually_nonflatGaussPoint_maxModulus hF p hp] with r hr
  intro f
  rw [iSup_singleton, logAbs_comap, logAbs_comap, logAbs_def, logAbs_def, ENNReal.log_le_log_iff,
    ENNReal.coe_le_coe]
  exact hr (ι f)

/-- **`v(s) ≤ v(s_r)`** for small `r` (`lem:nf-hull-approach`), for `v` satisfying the hull
inequality (`lem:hull-basic`), applied to the compact set `{s_r}`. -/
theorem SatisfiesHullIneq.eventually_le_comap_nonflatGaussPoint {v : Berk k B → EReal}
    (hv : SatisfiesHullIneq v) :
    ∀ᶠ r in 𝓝 (0 : ℝ≥0), v (comap ι (nonflatEvalPoint hF p hp)) ≤
      v (comap ι (nonflatGaussPoint hF p hp r)) := by
  filter_upwards [eventually_mem_hull_comap_nonflatGaussPoint hF hp ι] with r hr
  have h := hv _ isCompact_singleton _ hr
  rwa [iSup_singleton] at h

/-- **`limsup_{r → 0} v(s_r) ≤ v(s)`** (`lem:nf-hull-approach`) for `v` upper semicontinuous:
for every `C > v(ι^* ξ)`, eventually `v(s_r) < C`. -/
theorem UpperSemicontinuous.eventually_comap_nonflatGaussPoint_lt {v : Berk k B → EReal}
    (hv : UpperSemicontinuous v) {C : EReal} (hC : v (comap ι (nonflatEvalPoint hF p hp)) < C) :
    ∀ᶠ r in 𝓝 (0 : ℝ≥0), v (comap ι (nonflatGaussPoint hF p hp r)) < C :=
  (tendsto_comap_nonflatGaussPoint hF hp ι).eventually (hv _ C hC)

/-- **Approach through the étale locus** (`lem:nf-hull-approach`), for `v ∈ ℛ(S)`: with
`s_r = ι^* ζ_r`, `v(ι^* ξ) ≤ v(s_r)` for small `r`, and `limsup_{r → 0} v(s_r) ≤ v(ι^* ξ)`. -/
theorem IsRegularizable.nonflat_hull_approach {v : Berk k B → EReal} (hv : IsRegularizable v) :
    (∀ᶠ r in 𝓝 (0 : ℝ≥0), v (comap ι (nonflatEvalPoint hF p hp)) ≤
      v (comap ι (nonflatGaussPoint hF p hp r))) ∧
    ∀ C, v (comap ι (nonflatEvalPoint hF p hp)) < C →
      ∀ᶠ r in 𝓝 (0 : ℝ≥0), v (comap ι (nonflatGaussPoint hF p hp r)) < C :=
  ⟨hv.satisfiesHullIneq.eventually_le_comap_nonflatGaussPoint hF hp ι,
    fun _ hC => UpperSemicontinuous.eventually_comap_nonflatGaussPoint_lt hF hp ι
      hv.upperSemicontinuous hC⟩

end HullApproach

/-! ### The identification on an abstract finite free cover of the line -/

section AbstractIdentification

variable {k : Type*} [Field k] {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra k F]
  (hF : ∀ c : k, c ≠ 0 → ‖algebraMap k F c‖ = 1) {p : F[X]} (hp : p.eval 0 ≠ 0)
  {R : Type*} [CommRing R] [Algebra k R] [Algebra (OpenLineRing p) R]
  [IsScalarTower k (OpenLineRing p) R] {B : Type*} [CommRing B] [Algebra k B]

/-- **The identification on a finite free cover of the line** (`prop:nf-identification`, analytic
core). Let `F` be algebraically closed and nontrivially valued, `R` a finite free `Q`-algebra,
`Q = F[t]_p`, `ι : B → Q`, and `U` a function on `(Spec R)^an` that near every point `x` over
`ξ : t ↦ 0` is a decreasing limit of functions of FS type in some `R_g`, `|g|_x ≠ 0`, and is upper
semicontinuous at the points over `ξ`. Let `v` on `(Spec B)^an` satisfy the hull inequality and be
upper semicontinuous, and suppose `N_q U(z) = v(ι^* z)` wherever `|c|_z ≠ 0`, for some `c ≠ 0`.
Then `v(ι^* ξ) = N_q U(ξ)`.

Proof: `N_q U(ζ_r) = v(s_r)` for `r > 0`; `N_q U(ξ) ≤ N_q U(ζ_r)` and
`limsup N_q U(ζ_r) ≤ N_q U(ξ)` (lane NF4); `v(ι^* ξ) ≤ v(s_r)` and `limsup v(s_r) ≤ v(ι^* ξ)`
(`lem:nf-hull-approach`); conclude by `nonflat_eq_of_squeeze`. -/
theorem nonflat_eq_flatNormFun_of_gaussRay [IsAlgClosed F] (hκ : ∃ κ : F, 1 < ‖κ‖)
    [Module.Free (OpenLineRing p) R] [Module.Finite (OpenLineRing p) R]
    (ι : B →ₐ[k] OpenLineRing p) {U : Berk k R → EReal} {v : Berk k B → EReal}
    (hU : ∀ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp), ∃ g : R, x.val g ≠ 0 ∧
      ∃ G : ℕ → Berk k R → EReal, (∀ j, IsNonflatAwayFS g (G j)) ∧
        (∀ z, z.val g ≠ 0 → Antitone fun j => G j z) ∧ ∀ z, z.val g ≠ 0 → U z = ⨅ j, G j z)
    (hUusc : ∀ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp), UpperSemicontinuousAt U x)
    {c : OpenLineRing p} (hc : c ≠ 0)
    (hgen : ∀ z : Berk k (OpenLineRing p), z.val c ≠ 0 →
      flatNormFun (B := OpenLineRing p) U z = v (comap ι z))
    (hvhull : SatisfiesHullIneq v) (hvusc : UpperSemicontinuous v) :
    v (comap ι (nonflatEvalPoint hF p hp)) =
      flatNormFun (B := OpenLineRing p) U (nonflatEvalPoint hF p hp) := by
  have htop : ∀ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp), U x ≠ ⊤ := fun x hx => by
    obtain ⟨g, hxg, G, hG, -, hlim⟩ := hU x hx
    rw [hlim x hxg]
    exact ne_top_of_le_ne_top ((hG 0).ne_top hxg) (iInf_le _ 0)
  refine nonflat_eq_of_squeeze
    (N := fun r => flatNormFun (B := OpenLineRing p) U (nonflatGaussPoint hF p hp r))
    (V := fun r => v (comap ι (nonflatGaussPoint hF p hp r))) ?_
    (eventually_flatNormFun_nonflatEvalPoint_le hF hp hκ hU)
    (fun C hC => eventually_flatNormFun_nonflatGaussPoint_lt hF hp hκ hUusc htop hC)
    (hvhull.eventually_le_comap_nonflatGaussPoint hF hp ι)
    (fun C hC => UpperSemicontinuous.eventually_comap_nonflatGaussPoint_lt hF hp ι hvusc hC)
  exact Eventually.of_forall fun r hr => hgen _ (nonflatGaussPoint_val_ne_zero hF p hp hr hc)

end AbstractIdentification

/-! ### The identification on the normalized curve of a line through a rigid datum -/

section LineIdentification

variable {k : Type u} [Field k] [IsAlgClosed k] {A B : Type u} [CommRing A] [IsDomain A]
  [Algebra k A] [CommRing B] [IsDomain B] [Algebra k B] {s : Berk k B} {F : Type u}
  [NormedField F] [IsUltrametricDist F] [Algebra k F] [IsAlgClosed F]
  (τ : NonflatRigidEmbedding s F) {σ : Type u} [Fintype σ] {hS : MvPolynomial σ k}
  (E : B ≃ₐ[k] Localization.Away hS) (φ : B →ₐ[k] A)

set_option hygiene false in
/-- `g = h_S` over `F`. -/
local notation "gF" => MvPolynomial.map (algebraMap k F) hS

set_option hygiene false in
/-- The coordinates `a ∈ F^σ` of the rigid point `ξ`. -/
local notation "aξ" => nonflatLinePoint E τ.baseEval

set_option hygiene false in
/-- `φ_F : B_F = F[x]_{h_S} → A_F`. -/
local notation "φF" => nonflatCoordMap F E φ

set_option hygiene false in
/-- The open line ring `Q = F[t]_p`. -/
local notation "Qℓ" => OpenLineRing (subst aξ w gF)

set_option hygiene false in
/-- The normalized curve `R' = ∏_P D_P` of the line. -/
local notation "R'" => NormalizationProduct (linePreimageIdeal aξ w j gF φF)

set_option hygiene false in
/-- The normalization map `ρ : A_F → R'`. -/
local notation "ρℓ" => (normalizationMapAlg (Localization.Away gF)
  (linePreimageIdeal aξ w j gF φF)).restrictScalars k

set_option hygiene false in
/-- The map `ψ : A → A_F → R'`. -/
local notation "ψℓ" => (ρℓ).comp (Algebra.TensorProduct.includeRight : A →ₐ[k] F ⊗[k] A)

set_option hygiene false in
/-- The rigid point `ξ : t ↦ 0` of the line. -/
local notation "ξℓ" => nonflatEvalPoint (fun _ hc => τ.norm_algebraMap hc) (subst aξ w gF)
  (nonflat_eval_subst_zero_ne_zero E τ.baseEval w)

set_option hygiene false in
/-- The line restricted to `B`: `ι : B → B_F → Q`. -/
local notation "ιℓ" => (IsScalarTower.toAlgHom k (Localization.Away gF) Qℓ).comp
  (nonflatCoordBaseHom F E)

omit [IsAlgClosed k] [IsDomain A] [IsDomain B] [IsUltrametricDist F] in
/-- **Generic fibres of the normalized curve and the weights** (`lem:nf-generic-fibre`, with
`def:nf-weights` over `S_0`). For a line admissible for `h`, there is `0 ≠ c ∈ Q` such that for
every `z ∈ (Spec Q)^an` with `|c|_z ≠ 0`, the point `ι^* z` of `(Spec B)^an` lies in `S_0^an` and
`N_q (u ∘ r ∘ p)(z) = N_π u (ι^* z)`, for every function `u` on `Y^an`. This combines lane NF3b's
`AffineLine.nonflatLine_exists_flatNormFun_eq` with `nonflat_coord_flatNormFun_eq_nonflatNorm`. -/
theorem NonflatRigidEmbedding.exists_flatNormFun_line_eq_nonflatNorm
    (hφ : (φ : B →+* A).Finite) {S : Finset A} {h : B} (hh : IsNonflatGoodLocus φ S h)
    (w : σ → F) (j : σ) (hj : w j ≠ 0)
    (hadm : principalLineHom aξ w gF (nonflatBaseEquiv F E ((1 : F) ⊗ₜ[k] h)) ≠ 0)
    (u : Berk k A → EReal) :
    letI := (φF).toRingHom.toAlgebra
    letI := (principalLineHom aξ w gF).toRingHom.toAlgebra
    letI := (normalizedLineProductHom aξ w j gF hj φF).toRingHom.toAlgebra
    letI : Module.Finite Qℓ R' := normalizedLineProductHom_finite aξ w j gF hj φF
      (nonflatCoordMap_finite F E φ hφ)
    haveI := nonflatLine_isScalarTower_k_base (k := k) gF φF
    haveI := nonflatLine_isScalarTower_k_line (k := k) aξ w gF
    haveI := nonflatLine_isScalarTower_k_curve (k := k) aξ w j gF hj φF
    ∃ c : Qℓ, c ≠ 0 ∧ ∀ z : Berk k Qℓ, z.val c ≠ 0 → (comap (ιℓ) z).val h ≠ 0 ∧
      flatNormFun (B := Qℓ) (fun y : Berk k R' =>
          u (comap (Algebra.TensorProduct.includeRight : A →ₐ[k] F ⊗[k] A) (comap (ρℓ) y))) z =
        nonflatNorm φ hφ h u (comap (ιℓ) z) := by
  let := (φF).toRingHom.toAlgebra
  let := (principalLineHom aξ w gF).toRingHom.toAlgebra
  let := (normalizedLineProductHom aξ w j gF hj φF).toRingHom.toAlgebra
  have hp : (subst aξ w gF).eval 0 ≠ 0 := nonflat_eval_subst_zero_ne_zero E τ.baseEval w
  have hline : subst aξ w gF ≠ 0 := fun h0 => hp (by rw [h0, Polynomial.eval_zero])
  have hφF : (φF).toRingHom.Finite := nonflatCoordMap_finite F E φ hφ
  have key := nonflatLine_exists_flatNormFun_eq (k := k) aξ w j gF hj φF hline hφF
    (nonflatBaseEquiv F E ((1 : F) ⊗ₜ[k] h)) hadm _ (hh.coord_etale (F := F) (E := E))
  obtain ⟨c, hc, -, hgen⟩ := key
  refine ⟨c, hc, fun z hz => ?_⟩
  obtain ⟨hzh, hzU⟩ := hgen z hz
  exact ⟨hzh, (hzU _).trans (nonflat_coord_flatNormFun_eq_nonflatNorm F E φ hφ (h := h) u _ hzh)⟩

omit [IsDomain B] [IsUltrametricDist F] in
/-- **Local approximants on the normalized curve** (`lem:nf-local-approx`, for
`u'' = u ∘ r ∘ p`). Let `u` be regularizable on the charts `A[σs/σ']` of a blowup, `0 ≠ σ₀ ∈ σs`,
`φ(e) = σ₀ a₀` (in the application `e = χ_{σ₀}(0)`, `lem:nf-charpoly` (3)), and let the line be
admissible for `e`. Then every point `x` of `(Spec R')^an` has `g ∈ R'`, `|g|_x ≠ 0`, such that
`u''` is, on `{|g| ≠ 0}`, the limit of a decreasing sequence of functions of FS type in `R'_g`
(lane NF5's `exists_nonflatLocalApprox`, with the factors `D_P` Dedekind by
`AffineLine.nonflatLine_normalizedCurve_structure`). -/
theorem NonflatRigidEmbedding.exists_nonflatLocalApprox_line (hS0 : hS ≠ 0)
    (hφ : (φ : B →+* A).Finite) (hinj : Function.Injective φ) {u : Berk k A → EReal}
    {σs : Finset A} (hureg : ∀ σ' ∈ σs, σ' ≠ 0 → IsRegularizable (u ∘ comap (chartMap k σs σ')))
    {σ₀ a₀ : A} (hσ₀ : σ₀ ∈ σs) {e : B} (he : φ e = σ₀ * a₀) (w : σ → F) (j : σ)
    (hj : w j ≠ 0)
    (hadm : principalLineHom aξ w gF (nonflatBaseEquiv F E ((1 : F) ⊗ₜ[k] e)) ≠ 0) :
    letI := (φF).toRingHom.toAlgebra
    haveI := nonflatLine_isScalarTower_k_base (k := k) gF φF
    ∀ x : Berk k R', ∃ g : R', x.val g ≠ 0 ∧ ∃ G : ℕ → Berk k R' → EReal,
      (∀ j, IsNonflatAwayFS g (G j)) ∧ (∀ z, z.val g ≠ 0 → Antitone fun j => G j z) ∧
      ∀ z, z.val g ≠ 0 → u (comap (Algebra.TensorProduct.includeRight : A →ₐ[k] F ⊗[k] A)
        (comap (ρℓ) z)) = ⨅ j, G j z := by
  let := (φF).toRingHom.toAlgebra
  have hp : (subst aξ w gF).eval 0 ≠ 0 := nonflat_eval_subst_zero_ne_zero E τ.baseEval w
  have hline : subst aξ w gF ≠ 0 := fun h0 => hp (by rw [h0, Polynomial.eval_zero])
  have hφF : (φF).toRingHom.Finite := nonflatCoordMap_finite F E φ hφ
  have hiφF : Function.Injective (φF) := nonflatCoordMap_injective F E φ hinj
  have hg : gF ≠ 0 := nonflat_map_ne_zero F hS0
  have : IsDomain (F ⊗[k] A) := tensorProduct_isDomain_of_algClosed k F A
  have := nonflatLine_isScalarTower_k_base (k := k) gF φF
  have : Finite (Index (linePreimageIdeal aξ w j gF φF)) :=
    linePreimageIndex_finite aξ w j gF φF hφF
  have hstr := nonflatLine_normalizedCurve_structure aξ w j gF hj φF hg hline hφF hiφF
  have : ∀ i : Index (linePreimageIdeal aξ w j gF φF),
      IsDedekindDomain (CurveNormalization.Ring (Component (linePreimageIdeal aξ w j gF φF) i)) :=
    fun i => (hstr.1 i).1
  -- `σ₀` is nonzero on every factor: `ψ(σ₀ a₀) = ψ(φ(e))` is the image of `ι(e) ≠ 0`
  have hψ : ∀ i, (ψℓ) σ₀ i ≠ 0 := by
    refine nonflat_apply_ne_zero_of_mul (ψℓ) (a := a₀) ?_
    refine nonflatLine_comp_apply_ne_zero aξ w j gF hj φF hg hline hφF hiφF _ hadm ?_
    rw [nonflatCoordMap_nonflatBaseEquiv, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.includeRight_apply, he]
  intro x
  obtain ⟨g, hxg, G, hG, hanti, hlim⟩ := exists_nonflatLocalApprox (ψℓ) hureg ⟨σ₀, hσ₀, hψ⟩ x
  refine ⟨g, hxg, G, hG, hanti, fun z hz => ?_⟩
  rw [← Berk.comap_comp]
  exact hlim z hz

omit [IsAlgClosed k] [IsDomain A] [IsDomain B] [IsAlgClosed F] [Fintype σ] in
/-- **The line passes through `s`** (`lem:nf-hull-approach`, `s_0 = s`): the restriction to `B` of
the point `ξ : t ↦ 0` of the line through the rigid point is `s`. -/
theorem NonflatRigidEmbedding.comap_coordLine_nonflatEvalPoint (w : σ → F) :
    letI := (principalLineHom aξ w gF).toRingHom.toAlgebra
    haveI := nonflatLine_isScalarTower_k_line (k := k) aξ w gF
    comap (ιℓ) (ξℓ) = s := by
  let := (principalLineHom aξ w gF).toRingHom.toAlgebra
  have := nonflatLine_isScalarTower_k_line (k := k) aξ w gF
  rw [Berk.comap_comp, τ.comap_line_nonflatEvalPoint E w]
  apply Berk.ext_val
  intro b'
  rw [comap_val_apply, comap_val_apply, nonflatCoordBaseHom_apply, AlgHom.restrictScalars_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply, τ.basePoint_val_tmul, nnnorm_one, one_mul]

/-- **Identification off the étale locus on a line** (`prop:nf-identification`, for a rigid
datum `τ` of `s`, a separating element `b` and the rigid weights `m_y = ∑_{r(z) = y} M_z`). Let `u`
be upper semicontinuous and regularizable on the charts `A[σs/σ']` of a blowup, `0 ≠ σ₀ ∈ σs`,
`φ(e) = σ₀ a₀`, and let the line `t ↦ a + t w` through the rigid point be admissible for `h e`.
If `v` satisfies the hull inequality, is upper semicontinuous and agrees with `N_π u` on
`S_0^an`, then `v(s) = ∑_{π(y) = s} m_y u(y)`.

Proof (`prop:nf-identification`): `N_q u''(ξ) = ∑ m_y u(y)` (`flatNormFun_line_eq_sum_rigidWeight`,
lane NF6); the local approximants (`exists_nonflatLocalApprox_line`), the generic fibres
(`exists_flatNormFun_line_eq_nonflatNorm`) and `ι^* ξ = s` (`comap_coordLine_nonflatEvalPoint`)
give the hypotheses of `nonflat_eq_flatNormFun_of_gaussRay`. -/
theorem NonflatRigidEmbedding.eq_sum_rigidWeight_of_line (hκ : ∃ κ : F, 1 < ‖κ‖)
    (hS0 : hS ≠ 0) (hinj : Function.Injective φ) (hφ : (φ : B →+* A).Finite) {S : Finset A}
    {h : B} (hh : IsNonflatGoodLocus φ S h) {u : Berk k A → EReal}
    (husc : UpperSemicontinuous u) {σs : Finset A}
    (hureg : ∀ σ' ∈ σs, σ' ≠ 0 → IsRegularizable (u ∘ comap (chartMap k σs σ')))
    {σ₀ a₀ : A} (hσ₀ : σ₀ ∈ σs) {e : B} (he : φ e = σ₀ * a₀) (w : σ → F) (j : σ)
    (hj : w j ≠ 0)
    (hadm : principalLineHom aξ w gF (nonflatBaseEquiv F E ((1 : F) ⊗ₜ[k] (h * e))) ≠ 0)
    (b : F ⊗[k] A) (hb : ∀ (z₁ : Berk k (F ⊗[k] A)) (h₁ : z₁ ∈ τ.fibre φ)
      (z₂ : Berk k (F ⊗[k] A)) (h₂ : z₂ ∈ τ.fibre φ),
      τ.fibreEval φ hφ h₁ b = τ.fibreEval φ hφ h₂ b → z₁ = z₂)
    {v : Berk k B → EReal} (hvhull : SatisfiesHullIneq v) (hvusc : UpperSemicontinuous v)
    (hv : ∀ s' : Berk k B, s'.val h ≠ 0 → v s' = nonflatNorm φ hφ h u s') :
    v s = ∑ y ∈ (finite_preimage_comap_singleton φ hφ s).toFinset,
      ((τ.rigidWeight φ hφ b y : ℝ) : EReal) * u y := by
  classical
  obtain ⟨hadmh, hadme⟩ := nonflat_admissible_of_mul E τ.baseEval w hadm
  have hp : (subst aξ w gF).eval 0 ≠ 0 := nonflat_eval_subst_zero_ne_zero E τ.baseEval w
  have hline : subst aξ w gF ≠ 0 := fun h0 => hp (by rw [h0, Polynomial.eval_zero])
  have hφF : (φF).toRingHom.Finite := nonflatCoordMap_finite F E φ hφ
  have hiφF : Function.Injective (φF) := nonflatCoordMap_injective F E φ hinj
  have hg : gF ≠ 0 := nonflat_map_ne_zero F hS0
  have : IsDomain (F ⊗[k] A) := tensorProduct_isDomain_of_algClosed k F A
  let := (φF).toRingHom.toAlgebra
  let := (principalLineHom aξ w gF).toRingHom.toAlgebra
  let := (normalizedLineProductHom aξ w j gF hj φF).toRingHom.toAlgebra
  have : Module.Finite Qℓ R' := normalizedLineProductHom_finite aξ w j gF hj φF hφF
  have : Module.Free Qℓ R' := normalizedLineProductHom_free aξ w j gF hj φF hg hline hφF hiφF
  have := nonflatLine_isScalarTower_k_base (k := k) gF φF
  have := nonflatLine_isScalarTower_k_line (k := k) aξ w gF
  have := nonflatLine_isScalarTower_k_curve (k := k) aξ w j gF hj φF
  -- the first display of `prop:nf-identification`: `N_q u''(ξ) = ∑ m_y u(y)`
  have hN0 := τ.flatNormFun_line_eq_sum_rigidWeight E φ hS0 hφ hinj hh w j hj hadmh b hb u
  -- generic fibres, local approximants and `ι^* ξ = s`
  obtain ⟨c, hc, hgen⟩ := τ.exists_flatNormFun_line_eq_nonflatNorm E φ hφ hh w j hj hadmh u
  have hloc := τ.exists_nonflatLocalApprox_line E φ hS0 hφ hinj hureg hσ₀ he w j hj hadme
  have hξs := τ.comap_coordLine_nonflatEvalPoint E w
  have hmain := nonflat_eq_flatNormFun_of_gaussRay (fun _ hc => τ.norm_algebraMap hc) hp hκ
    (R := R') (ιℓ) (fun x _ => hloc x)
    (fun x _ => (husc.comp ((continuous_comap _).comp (continuous_comap _))) x) hc
    (fun z hz => ((hgen z hz).2).trans (hv _ (hgen z hz).1).symm) hvhull hvusc
  rw [hξs] at hmain
  exact hmain.trans hN0

end LineIdentification

/-! ### Identification off the étale locus (`prop:nf-identification`) -/

section Identification

variable {k : Type u} [Field k] [IsAlgClosed k] {A B : Type u} [CommRing A] [IsDomain A]
  [Algebra k A] [Algebra.FiniteType k A] [CommRing B] [Algebra k B]

/-- **Identification off the étale locus** (`prop:nf-identification`), pointwise form. Let
`B ≅ k[x]_{h_S}` be a principal open of `𝔸ⁿ` (`n ≥ 1`), `φ : B → A` finite and injective, `h` a
good locus element, and `u` regularizable on the charts of a blowup. If `v` satisfies the hull
inequality, is upper semicontinuous and agrees with `N_π u = nonflatNorm φ hφ h u` on `S_0^an`,
then `v(s) = N_π u(s)` for every `s ∈ S^an`.

Proof: for `s ∉ S_0^an` take the canonical rigid datum `nonflatRigidEmbedding s` (nontrivially
valued), `e = χ_{σ₀}(0)` for some `0 ≠ σ₀` in the witness (`lem:nf-charpoly` (3):
`e ≠ 0`, `σ₀ ∣ φ(e)`), a direction admissible for `h e` (`lem:nf-line-exists`), and apply
`NonflatRigidEmbedding.eq_sum_rigidWeight_of_line` with the separating element
`nonflatSeparating`; the result is `N_π u(s)` by `nonflatNorm_of_eq_zero`. -/
theorem IsChartRegularizable.eq_nonflatNorm_of_satisfiesHullIneq {n : ℕ} (hn : 1 ≤ n)
    (hB : IsAffineSpacePrincipalOpen k B n) (φ : B →ₐ[k] A) (hinj : Function.Injective φ)
    (hφ : (φ : B →+* A).Finite) {S : Finset A} {h : B} (hh : IsNonflatGoodLocus φ S h)
    {u : Berk k A → EReal} (hu : IsChartRegularizable u) {v : Berk k B → EReal}
    (hvhull : SatisfiesHullIneq v) (hvusc : UpperSemicontinuous v)
    (hv : ∀ s : Berk k B, s.val h ≠ 0 → v s = nonflatNorm φ hφ h u s) (s : Berk k B) :
    v s = nonflatNorm φ hφ h u s := by
  classical
  by_cases hs : s.val h ≠ 0
  · exact hv s hs
  rw [not_not] at hs
  have := hB.isDomain
  have := hB.isIntegrallyClosed
  have husc := hu.upperSemicontinuous
  obtain ⟨hS, hS0, ⟨E⟩⟩ :=
    (hB.exists_ulift : ∃ hS : MvPolynomial (ULift.{u} (Fin n)) k, hS ≠ 0 ∧
      Nonempty (B ≃ₐ[k] Localization.Away hS))
  have : Nonempty (ULift.{u} (Fin n)) := ⟨⟨⟨0, hn⟩⟩⟩
  obtain ⟨σs, ⟨σ₀, hσ₀s, hσ₀⟩, hureg⟩ := hu
  -- `e = χ_{σ₀}(0)`: `e ≠ 0` and `φ(e) ∈ σ₀ A`
  obtain ⟨e, he, a₀, ha₀⟩ : ∃ e : B, e ≠ 0 ∧ ∃ a₀ : A, φ e = σ₀ * a₀ := by
    let := (φ : B →+* A).toAlgebra
    have : Module.Finite B A := hφ
    have : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).2 hinj
    exact ⟨_, coeff_zero_nonflatCharpoly_ne_zero hσ₀, dvd_algebraMap_coeff_zero_nonflatCharpoly σ₀⟩
  -- a line through the rigid point admissible for `h e`
  obtain ⟨w, hw0, -, hadm⟩ := nonflat_exists_admissible_direction E
    (nonflatRigidEmbedding s).baseEval (mul_ne_zero hh.ne_zero he)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw0
  rw [nonflatNorm_of_eq_zero φ hφ hs u]
  exact (nonflatRigidEmbedding s).eq_sum_rigidWeight_of_line E φ
    (nonflatRigidField_exists_one_lt_norm s) hS0 hinj hφ hh husc hureg hσ₀s ha₀ w j hj hadm
    (nonflatSeparating φ hφ s) (nonflatSeparating_spec φ hφ s) hvhull hvusc hv

/-- **Identification off the étale locus** (`prop:nf-identification`). Let `B ≅ k[x]_{h_S}` be a
principal open of `𝔸ⁿ` (`n ≥ 1`), `φ : B → A` finite and injective, `h` a good locus element
(`S_0 = S_h`), and `u` regularizable on the charts of a blowup. If `v ∈ ℛ(S)` and `v = N_π u` on
`S_0^an`, then `v = N_π u` on `S^an`. (The covering hypothesis of the blueprint statement is not
needed.) -/
theorem IsChartRegularizable.eq_nonflatNorm {n : ℕ} (hn : 1 ≤ n)
    (hB : IsAffineSpacePrincipalOpen k B n) (φ : B →ₐ[k] A) (hinj : Function.Injective φ)
    (hφ : (φ : B →+* A).Finite) {S : Finset A} {h : B} (hh : IsNonflatGoodLocus φ S h)
    {u : Berk k A → EReal} (hu : IsChartRegularizable u) {v : Berk k B → EReal}
    (hvreg : IsRegularizable v)
    (hv : ∀ s : Berk k B, s.val h ≠ 0 → v s = nonflatNorm φ hφ h u s) :
    v = nonflatNorm φ hφ h u :=
  funext (hu.eq_nonflatNorm_of_satisfiesHullIneq hn hB φ hinj hφ hh hvreg.satisfiesHullIneq
    hvreg.upperSemicontinuous hv)

end Identification

end EnvelopeProperty
