/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.Unibranch
import EnvelopeProperty.Global.Comparison

/-!
# Descent through the normalization under the envelope property, and unibranchness

Let `k` be an algebraically closed field with the trivial absolute value, `𝒳 = (K, S, z)` an
integral multiprojective model of rank `r` (`EnvelopeProperty.MultiModel`, `def:gl-model`),
`𝒴 = 𝒳^ν` its normalization (`MultiModel.normalization`, `rmk:gl-model-examples`(2)) and
`ν^an : 𝒴^an → 𝒳^an` the restriction map (`FiniteHom.ofNormalization`, `def:gl-maps`). This file
implements the blueprint node `prop:gl-conductor-descent` and the implication (3) ⇒ (1) of
`cor:gl-characterization` (reused verbatim in `cor:nn-characterization`) of the global chapter
`global.tex` (subsection `subsec:gl-main`) of the formalization of Fang–Han–Xia, *The envelope
property for unibranch projective varieties* (FHX, Corollary 1.1,
`cor:intro-characterization`, (3) ⇒ (1)):
Boucksom–Jonsson's Theorem 5.12 (BJ22, "the envelope property for one ample class
forces unibranchness") is re-proved through the conductor, without BJ22 Theorem 4.32,
Lemma 2.21 for general blowups, the non-negligibility of divisorial points (BJ22 Theorem 5.6)
or GAGA.

## The conductor

`S^ν` is a finite `S`-module (`MultiModel.finite_normalization`) inside `Frac S = K(T)`
(`MultiModel.isFractionRing_S`), so a common denominator `d ∈ S ∖ 0` of a finite generating set
satisfies `d S^ν ⊆ S` (`MultiModel.exists_conductor_poly`). Since `S` is graded, the coefficient
`g` of `d` in any degree `e` of its support is a **homogeneous conductor element**
(`MultiModel.IsConductorElem e g`, `MultiModel.exists_isConductorElem`): `f g ∈ S_{a + e}` for every
homogeneous `f T^a ∈ S^ν`. Consequently (`MultiModel.IsConductorElem.mul_mem_sections`,
`IsConductorElem.secAbs_mul_anMap`)

* `g R_b(𝒴) ⊆ R_{b + e}(𝒳)` with `|F g|_{ν(w)} = |F|_w |g|_{ν(w)}`;
* `ν^an` is injective over the open set `Ω = {|g| ≠ 0} ⊆ 𝒳^an`
  (`IsConductorElem.eq_of_anMap_eq_of_secAbs_ne_zero`), which contains `𝒳^div` and whose preimage
  contains `𝒴^div` (`lem:gl-div-generic`).

## Twisted Fubini–Study functions

For Fubini–Study data `D = (m, (s_t, λ_t))` of class `a` on `𝒴` and `M ≥ 1`, the data with sections
`s_t^M g^m` and weights `M λ_t` (`IsConductorElem.twistData`, built as the sum of `D` with the
one-term data `FSData.conductorTwist` of `M⁻¹ log |g|`, then transported to `𝒳` by
`FSData.descendNormalization`) is a Fubini–Study function `φ_{D,M} ∈ 𝓗(𝒳, a + M⁻¹ e)` with
`φ_{D,M} ∘ ν^an = D + M⁻¹ log |g| ∘ ν^an` (`IsConductorElem.eval_twistData`).

## Main results

* **`prop:gl-conductor-descent`** (`MultiModel.HasEnvelopeProperty.exists_isPSH_comp_anMap_eq`):
  if `ω ∈ ℝ^r` is positive and `EP_𝒳(ω)` holds, every `ψ ∈ PSH(𝒴, ω)` is `φ ∘ ν^an` for some
  `φ ∈ PSH(𝒳, ω)`. Write `ψ = inf_α ψ_α`, `ψ_α ∈ 𝓗(𝒴, a_α)`, `ε_M = (M + 1)⁻¹` and
  `ℓ = log |g| ≤ 0`. The twisted functions `φ_{α,M}` decrease in `α` (`ν^an` is surjective), so
  `φ_M = inf_α φ_{α,M} ∈ PSH(𝒳, ω + ε_M e)`, with `φ_M ∘ ν^an = ψ + ε_M ℓ ∘ ν^an` on
  `(ν^an)⁻¹(Ω)`; the `φ_M` increase with `M` and are bounded by `ψ(⋆)`. For `δ > 0` and `M ≥ M₀(δ)`,
  `ω + ε_M e ≤ (1 + δ) ω`, so `EP_𝒳((1 + δ) ω)` (`lem:gl-ep-basic`(2)) gives
  `φ = (sup_M φ_M)^⋆ = (sup_{M ≥ M₀} φ_M)^⋆ ∈ PSH(𝒳, (1 + δ) ω)` for every `δ`, hence
  `φ ∈ PSH(𝒳, ω)` by PSH2 at `ω ∈ N(𝒳)` (`thm:gl-fs-system-theory`(2)). On `Ω`,
  `sup_M φ_M = ψ ∘ (ν^an|)⁻¹`, which is usc since `ν^an` restricts to a homeomorphism
  `(ν^an)⁻¹(Ω) ≃ₜ Ω` (a continuous closed bijection), so `φ = ψ ∘ (ν^an|)⁻¹` on `Ω`
  (`lem:gl-usc-local`(1)). Finally `φ ∘ ν^an` and `ψ` are `ω`-psh on `𝒴` and agree on
  `(ν^an)⁻¹(Ω) ⊇ 𝒴^div`, hence are equal (`lem:gl-usc-local`(3), `thm:gl-comparison`).
* **`cor:gl-characterization`, (3) ⇒ (1)**
  (`MultiModel.HasEnvelopeProperty.anMap_ofNormalization_injective`,
  `MultiModel.HasEnvelopeProperty.isUnibranch`,
  `MultiModel.isUnibranch_of_exists_hasEnvelopeProperty`): if `EP_𝒳(ω)` holds for one positive
  `ω`, then `ν^an` is injective, hence `𝒳` is unibranch
  (`MultiModel.isUnibranch_of_anMap_injective`). For a homogeneous
  `0 ≠ f T^a ∈ S^ν`, `log |f| ∈ PSH(𝒴, a) ⊆ PSH(𝒴, t ω)` for `t = 1 + ∑_c a_c / ω_c`, and
  `EP_𝒳(t ω)` holds by `lem:gl-ep-basic`(2); so `log |f|` descends and takes equal values at
  points with the same image. Multigraded points agreeing on homogeneous
  elements are equal (`MultiModel.ext_of_ofPiece`). No imported statement is used.

## Deviations from the blueprint proofs

* `prop:gl-conductor-descent`: the independence of `(sup_ε φ_ε)^⋆` from `δ` is obtained from the
  monotonicity of `φ_M` in `M` (the supremum over `M ≥ M₀` is the supremum over all `M`,
  `Monotone.iSup_nat_add`), not from the comparison theorem on `Ω`; the comparison theorem is used
  once, on `𝒴`, at the end. The homeomorphism `(ν^an)⁻¹(Ω) ≃ₜ Ω` is obtained from injectivity
  over `Ω` (conductor) and closedness of `ν^an`, rather than from `S[τ⁻¹] = S^ν[τ⁻¹]`. Only the
  conductor property for homogeneous elements of `S^ν` is needed and proved.
* `cor:gl-characterization`, (3) ⇒ (1): instead of the functions `n⁻¹ max(log |p|, -C)` of classes
  `≤ ω`, the functions `log |f|` of class `a ≤ t ω` are descended with `EP_𝒳(t ω)`; point separation
  is `ext_of_ofPiece` (no PL functions, `lem:gl-pl`, are needed).
-/

open scoped NNReal ENNReal Topology
open Topology Filter MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r}

variable (X) in
/-- **Denominators**: every `q ∈ K[T]` has a nonzero multiple `b q ∈ S` with `b ∈ S`, since
`Frac S = K(T)` (`MultiModel.isFractionRing_S`). -/
theorem exists_ne_zero_mul_mem_S (q : MvPolynomial (Fin r) K) :
    ∃ b ∈ X.S, b ≠ 0 ∧ b * q ∈ X.S := by
  have := X.isFractionRing_S
  set L := FractionRing (MvPolynomial (Fin r) K)
  have hι : Function.Injective (algebraMap (MvPolynomial (Fin r) K) L) :=
    IsFractionRing.injective _ _
  obtain ⟨⟨x, y⟩, h⟩ := IsLocalization.surj (nonZeroDivisors X.S)
    (algebraMap (MvPolynomial (Fin r) K) L q)
  refine ⟨(y : X.S).1, (y : X.S).2, fun h0 => nonZeroDivisors.ne_zero y.2 (Subtype.ext h0), ?_⟩
  have h' : algebraMap _ L ((y : X.S).1 * q) = algebraMap _ L x.1 := by
    rw [map_mul, mul_comm]
    exact h
  rw [hι h']
  exact x.2

section Conductor

variable [Infinite k] [PerfectField k]

variable (X) in
/-- **The conductor is nonzero**: some `0 ≠ d ∈ S` satisfies `d S^ν ⊆ S` (a common denominator of
finitely many generators of the finite `S`-module `S^ν`, `MultiModel.finite_normalization`). -/
theorem exists_conductor_poly :
    ∃ d ∈ X.S, d ≠ 0 ∧ ∀ q ∈ X.normalization.S, d * q ∈ X.S := by
  classical
  let _ : Algebra X.S (X.normalizationInS K) := (X.normalizationInHom K).toAlgebra
  have : Module.Finite X.S (X.normalizationInS K) := X.finite_normalization
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := X.S) (M := X.normalizationInS K)
  choose b hbS hb0 hbq using fun q : X.normalizationInS K => X.exists_ne_zero_mul_mem_S q.1
  set d := ∏ q ∈ s, b q with hd
  refine ⟨d, ?_, Finset.prod_ne_zero_iff.2 fun q _ => hb0 q, ?_⟩
  · exact Subalgebra.prod_mem _ fun q _ => hbS q
  let N : Submodule X.S (X.normalizationInS K) :=
    { carrier := {q' | d * q'.1 ∈ X.S}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq, Subalgebra.coe_add, mul_add] at hx hy ⊢
        exact X.S.add_mem hx hy
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [Algebra.smul_def, Subalgebra.coe_mul, RingHom.algebraMap_toAlgebra]
        have hc : ((X.normalizationInHom K c : X.normalizationInS K) :
            MvPolynomial (Fin r) K) = c.1 := by
          change coeffMap k K c.1 = c.1
          rw [coeffMap_apply, Algebra.algebraMap_self, MvPolynomial.map_id]
        rw [hc, mul_left_comm]
        exact X.S.mul_mem c.2 hx }
  have hsN : (s : Set (X.normalizationInS K)) ⊆ N := fun q hq => by
    change d * q.1 ∈ X.S
    rw [hd, ← Finset.mul_prod_erase s b hq, mul_comm (b q), mul_assoc]
    exact X.S.mul_mem (Subalgebra.prod_mem _ fun q' _ => hbS q') (hbq q)
  intro q hq
  have hle : (⊤ : Submodule X.S (X.normalizationInS K)) ≤ N := by
    rw [← hs]
    exact Submodule.span_le.2 hsN
  exact hle (Submodule.mem_top (x := ⟨q, hq⟩))

variable (X) in
/-- A **homogeneous conductor element** of degree `e` (`prop:gl-conductor-descent`): a nonzero
`g ∈ S_e` with `f g ∈ S_{a + e}` for every homogeneous `f T^a ∈ S^ν`, i.e. `g T^e` lies in the
conductor `{c ∈ S : c S^ν ⊆ S}`. -/
structure IsConductorElem (e : Fin r →₀ ℕ) (g : K) : Prop where
  /-- `g ≠ 0`. -/
  ne_zero : g ≠ 0
  /-- `g T^e ∈ S`. -/
  mem_piece : g ∈ X.piece e
  /-- `(f T^a) (g T^e) ∈ S` for every `f T^a ∈ S^ν`. -/
  mul_mem_piece : ∀ (a : Fin r →₀ ℕ) (f : K), f ∈ X.normalization.piece a → f * g ∈ X.piece (a + e)

variable (X) in
/-- **The conductor contains a nonzero homogeneous element.** -/
theorem exists_isConductorElem : ∃ (e : Fin r →₀ ℕ) (g : K), X.IsConductorElem e g := by
  obtain ⟨d, hdS, hd0, hd⟩ := X.exists_conductor_poly
  obtain ⟨e, he⟩ := MvPolynomial.ne_zero_iff.1 hd0
  refine ⟨e, d.coeff e, he, X.isGraded d hdS e, fun a f hf => ?_⟩
  have h1 := X.isGraded _ (hd _ hf) (e + a)
  rw [coeff_mul_monomial] at h1
  rw [mem_piece, add_comm a e, mul_comm]
  exact h1

namespace IsConductorElem

variable {e : Fin r →₀ ℕ} {g : K} (hc : X.IsConductorElem e g)
include hc

/-- `g ∈ S_e ⊆ R_e(𝒳)`. -/
theorem mem_sections : g ∈ X.sections fun c => (e c : ℤ) :=
  mem_sections_of_mem_piece (fun _ => rfl) hc.mem_piece

/-- `g ∈ R_e(𝒳^ν)`. -/
theorem mem_sections_normalization : g ∈ X.normalization.sections fun c => (e c : ℤ) :=
  (FiniteHom.ofNormalization X).mem_sections hc.mem_sections

/-- **`g R_d(𝒳^ν) ⊆ R_{d + e}(𝒳)`**: an admissible degree `b` of `F` on `𝒳^ν` is admissible for
`F g` on `𝒳`. -/
theorem mul_mem_sections {d : Fin r → ℤ} {F : K} (hF : F ∈ X.normalization.sections d) :
    F * g ∈ X.sections (d + fun c => (e c : ℤ)) := by
  obtain ⟨b, hb⟩ := hF
  refine ⟨b, fun c => ?_, fun β hβ => ?_⟩
  · have := hb.nonneg c
    simp only [Pi.add_apply]
    omega
  · have h1 := hb.mul_zCoeff_mem ((FiniteHom.ofNormalization X).monEquiv_mem_monSet hβ)
    rw [(FiniteHom.ofNormalization X).zCoeff_monEquiv] at h1
    have h2 := hc.mul_mem_piece _ _ h1
    have hdeg : addDeg (d + fun c => (e c : ℤ)) b = addDeg d b + e := by
      ext c
      have := hb.nonneg c
      simp only [addDeg_apply, Finsupp.add_apply, Pi.add_apply]
      omega
    rw [hdeg, show F * g * X.zCoeff β = F * X.zCoeff β * g by ring]
    exact h2

/-- Values: `|F g|_{ν(w)} = |F|_w |g|_{ν(w)}` for `F ∈ R_d(𝒳^ν)`. -/
theorem secAbs_mul_anMap {d : Fin r → ℤ} {F : K} (hF : F ∈ X.normalization.sections d)
    (w : X.normalization.an) :
    X.secAbs ((FiniteHom.ofNormalization X).anMap w).1 (d + fun c => (e c : ℤ)) (F * g) =
      X.normalization.secAbs w.1 d F *
        X.secAbs ((FiniteHom.ofNormalization X).anMap w).1 (fun c => (e c : ℤ)) g := by
  rw [← (FiniteHom.ofNormalization X).secAbs_anMap w (hc.mul_mem_sections hF),
    ← (FiniteHom.ofNormalization X).secAbs_anMap w hc.mem_sections]
  exact secAbs_mul w.2.2 hF hc.mem_sections_normalization

/-- **`ν^an` is injective over `{|g| ≠ 0}`**: if `ν(w) = ν(w')` and `|g|_{ν(w)} ≠ 0`, then
`|f|_w = |g f|_{ν(w)} / |g|_{ν(w)} = |f|_{w'}` for every homogeneous `f T^a ∈ S^ν`, so `w = w'`. -/
theorem eq_of_anMap_eq_of_secAbs_ne_zero {w w' : X.normalization.an}
    (hww' : (FiniteHom.ofNormalization X).anMap w = (FiniteHom.ofNormalization X).anMap w')
    (hw : X.secAbs ((FiniteHom.ofNormalization X).anMap w).1 (fun c => (e c : ℤ)) g ≠ 0) :
    w = w' := by
  refine Subtype.ext (ext_of_ofPiece w.2.1 w'.2.1 fun a f hf => ?_)
  have hfs : f ∈ X.normalization.sections fun c => (a c : ℤ) :=
    mem_sections_of_mem_piece (fun _ => rfl) hf
  rw [← secAbs_of_mem_piece w.2.2 (fun _ => rfl) hf,
    ← secAbs_of_mem_piece w'.2.2 (fun _ => rfl) hf]
  have h1 := hc.secAbs_mul_anMap hfs w
  have h2 := hc.secAbs_mul_anMap hfs w'
  rw [← hww'] at h2
  exact mul_right_cancel₀ hw (h1.symm.trans h2)

/-- `g^n R_d(𝒳^ν) ⊆ R_{d + n e}(𝒳)` for `n ≥ 1`. -/
theorem mul_pow_mem_sections {d : Fin r → ℤ} {F : K} (hF : F ∈ X.normalization.sections d)
    {n : ℕ} (hn : 0 < n) : F * g ^ n ∈ X.sections (d + n • fun c => (e c : ℤ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := hc.mul_mem_sections
    (MultiModel.mul_mem_sections hF (pow_mem_sections hc.mem_sections_normalization m))
  rw [pow_succ, ← mul_assoc, succ_nsmul, ← add_assoc]
  exact h

end IsConductorElem

/-! ### Descending Fubini–Study data through the normalization -/

/-- Fubini–Study data on `𝒳^ν` all of whose sections are sections of `𝒳`, viewed as data on
`𝒳`. -/
def FSData.descendNormalization {a : Fin r → ℚ} (D : X.normalization.FSData a)
    (hD : ∀ t ∈ D.terms, t.1 ∈ X.sections D.deg) : X.FSData a where
  m := D.m
  m_pos := D.m_pos
  deg := D.deg
  deg_eq := D.deg_eq
  terms := D.terms
  mem_sections := hD

/-- The descended data compute the same function: `D'(ν(w)) = D(w)`. -/
theorem FSData.eval_descendNormalization {a : Fin r → ℚ} (D : X.normalization.FSData a)
    (hD : ∀ t ∈ D.terms, t.1 ∈ X.sections D.deg) (w : X.normalization.an) :
    (D.descendNormalization hD).eval ((FiniteHom.ofNormalization X).anMap w) = D.eval w := by
  rw [FSData.eval_def, FSData.eval_def]
  congr 1
  refine Finset.sup_congr rfl fun t ht => ?_
  rw [termVal_def, termVal_def]
  congr 1
  exact ((FiniteHom.ofNormalization X).logSecAbs_anMap w (hD t ht)).symm

end Conductor

/-- The data of `M⁻¹ log |g|` (one term, `m = M`), of class `M⁻¹ d`, for a section `g ∈ R_d`. -/
def FSData.conductorTwist {Z : MultiModel k K r} {d : Fin r → ℤ} {g : K} (hg : g ∈ Z.sections d)
    (M : ℕ) (hM : 0 < M) : Z.FSData ((1 / (M : ℚ)) • fun c => (d c : ℚ)) where
  m := M
  m_pos := hM
  deg := d
  deg_eq c := by
    have : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  terms := {(g, 0)}
  mem_sections t ht := by
    rw [Finset.mem_singleton] at ht
    subst ht
    exact hg

/-- `(M⁻¹ log |g|)(v) = M⁻¹ log |g|_v`. -/
theorem FSData.eval_conductorTwist {Z : MultiModel k K r} {d : Fin r → ℤ} {g : K}
    (hg : g ∈ Z.sections d) (M : ℕ) (hM : 0 < M) (v : Z.an) :
    (FSData.conductorTwist hg M hM).eval v = (((M : ℝ)⁻¹ : ℝ) : EReal) * Z.logSecAbs v.1 d g := by
  rw [FSData.eval_def]
  change (((M : ℝ)⁻¹ : ℝ) : EReal) * (({(g, 0)} : Finset (K × ℝ)).sup fun t => Z.termVal d t v) = _
  rw [Finset.sup_singleton, termVal_def, EReal.coe_zero, add_zero]

section Conductor2

variable [Infinite k] [PerfectField k]

namespace IsConductorElem

variable {e : Fin r →₀ ℕ} {g : K} (hc : X.IsConductorElem e g)

/-- **The twisted descended data** (`prop:gl-conductor-descent`): for data `D` of class `a` on
`𝒳^ν` with sections `s_t` and `M ≥ 1`, the data on `𝒳` with sections `s_t^M g^m`
(`m = D.m`), of class `a + M⁻¹ e`; its value at `ν(w)` is `D(w) + M⁻¹ log |g|_{ν(w)}`
(`IsConductorElem.eval_twistData`). -/
def twistData {a : Fin r → ℚ} (D : X.normalization.FSData a) (M : ℕ) (hM : 0 < M) :
    X.FSData (a + (1 / (M : ℚ)) • fun c => ((e c : ℤ) : ℚ)) :=
  (D.add (FSData.conductorTwist hc.mem_sections_normalization M hM)).descendNormalization (by
    classical
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ht
    rw [Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [show p.2 = (g, 0) from Finset.mem_singleton.1 hp2]
    exact hc.mul_pow_mem_sections (pow_mem_sections (D.mem_sections _ hp1) M) D.m_pos)

/-- **The twisted data descend `D + M⁻¹ log |g|`**: `φ_{D,M}(ν(w)) = D(w) + M⁻¹ log |g|_{ν(w)}`. -/
theorem eval_twistData {a : Fin r → ℚ} (D : X.normalization.FSData a) (M : ℕ) (hM : 0 < M)
    (w : X.normalization.an) :
    (hc.twistData D M hM).eval ((FiniteHom.ofNormalization X).anMap w) =
      D.eval w + (((M : ℝ)⁻¹ : ℝ) : EReal) *
        X.logSecAbs ((FiniteHom.ofNormalization X).anMap w).1 (fun c => (e c : ℤ)) g := by
  rw [twistData, FSData.eval_descendNormalization, FSData.eval_add, FSData.eval_conductorTwist,
    ← (FiniteHom.ofNormalization X).logSecAbs_anMap w hc.mem_sections]
  rfl

end IsConductorElem

end Conductor2

/-! ### Descent of psh functions (`prop:gl-conductor-descent`) -/

section Descent

variable [IsAlgClosed k]

/-- **Descent through the normalization under the envelope property**
(`prop:gl-conductor-descent`; BJ22 Lemma 5.13 for the normalization, re-proved through
the conductor instead of BJ22 Theorem 4.32): if `ω ∈ ℝ^r` is positive and `EP_𝒳(ω)` holds, every
`ψ ∈ PSH(𝒳^ν, ω)` is of the form `φ ∘ ν^an` with `φ ∈ PSH(𝒳, ω)`. -/
theorem HasEnvelopeProperty.exists_isPSH_comp_anMap_eq {ω : Fin r → ℝ} (hω : ∀ c, 0 < ω c)
    (hEP : X.HasEnvelopeProperty ω) {ψ : X.normalization.an → EReal}
    (hψ : X.normalization.IsPSH ω ψ) :
    ∃ φ : X.an → EReal, X.IsPSH ω φ ∧ φ ∘ (FiniteHom.ofNormalization X).anMap = ψ := by
  classical
  set ν := FiniteHom.ofNormalization X
  obtain ⟨e, g, hc⟩ := X.exists_isConductorElem
  set e' : Fin r → ℤ := fun c => (e c : ℤ)
  set eQ : Fin r → ℚ := fun c => ((e c : ℤ) : ℚ) with heQ
  set eR : Fin r → ℝ := fun c => (e c : ℝ) with heR
  set ℓ : X.an → EReal := fun v => X.logSecAbs v.1 e' g
  have hgX : g ∈ X.sections e' := hc.mem_sections
  have hgY : g ∈ X.normalization.sections e' := hc.mem_sections_normalization
  have hℓle : ∀ v, ℓ v ≤ 0 := fun v => logSecAbs_le_zero v.2.2 _ _
  have hℓtriv : ℓ X.triv = 0 := logSecAbs_triv hgX hc.ne_zero
  have hsurj : Function.Surjective ν.anMap := ν.anMap_surjective
  -- the coefficients `c_M = (M + 1)⁻¹`
  set cM : ℕ → ℝ := fun M => ((M + 1 : ℕ) : ℝ)⁻¹ with hcM
  have hcM_pos : ∀ M, 0 < cM M := fun M => by positivity
  have hcM_anti : ∀ M, cM (M + 1) ≤ cM M := fun M => by
    simp only [hcM]
    gcongr
    omega
  have hcM_tendsto : Tendsto cM atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    refine this.congr fun M => ?_
    simp [hcM, one_div]
  have hcMQ : ∀ M, (((1 / ((M + 1 : ℕ) : ℚ)) : ℚ) : ℝ) = cM M := fun M => by
    simp [hcM, one_div]
  -- the decreasing net defining `ψ`
  have hψ' := hψ
  obtain ⟨-, -, ι, _, _, _, a, ψs, hψs, ha, hanti, hinf⟩ := hψ'
  have hψs' : ∀ i, ∃ D : X.normalization.FSData (a i), (∃ t ∈ D.terms, t.1 ≠ 0) ∧
      ∀ v, ψs i v = D.eval v := hψs
  choose D hD0 hDeval using hψs'
  -- the twisted descended functions `φ_{i,M} ∈ 𝓗(𝒳, a_i + c_M e)`
  set φs : ℕ → ι → X.an → EReal := fun M i => (hc.twistData (D i) (M + 1) M.succ_pos).eval
  have hKI : ∀ M i w, φs M i (ν.anMap w) = ψs i w + ((cM M : ℝ) : EReal) * ℓ (ν.anMap w) :=
    fun M i w => by
      rw [hDeval i w]
      exact hc.eval_twistData (D i) (M + 1) M.succ_pos w
  have hφanti : ∀ M v, Antitone fun i => φs M i v := by
    intro M v i j hij
    obtain ⟨w, rfl⟩ := hsurj v
    dsimp only
    rw [hKI, hKI]
    exact add_le_add (hanti w hij) le_rfl
  set Φs : ℕ → X.an → EReal := fun M v => ⨅ i, φs M i v with hΦs
  have hΦtriv : ∀ M, Φs M X.triv = ψ X.normalization.triv := by
    intro M
    have h : ∀ i, φs M i X.triv = ψs i X.normalization.triv := fun i => by
      rw [← ν.anMap_triv, hKI, ν.anMap_triv, hℓtriv, mul_zero, add_zero]
    simp only [hΦs, h]
    exact (hinf _).symm
  have hΦpsh : ∀ M, X.IsPSH (ω + cM M • eR) (Φs M) := by
    intro M
    refine FSSystemC.isPSH_of_iInf ⟨X.triv, ?_⟩
      (fun i => a i + (1 / ((M + 1 : ℕ) : ℚ)) • eQ) (φs M) (fun i => ?_) ?_ (hφanti M)
      (fun v => rfl)
    · rw [hΦtriv]
      exact FSSystemC.IsPSH.apply_triv_ne_bot hψ
    · refine isFS_iff.2 ⟨hc.twistData (D i) (M + 1) M.succ_pos, ?_, fun v => rfl⟩
      rw [← ν.anMap_triv, hc.eval_twistData, ν.anMap_triv]
      change (D i).eval X.normalization.triv + ((cM M : ℝ) : EReal) * ℓ X.triv ≠ ⊥
      rw [hℓtriv, mul_zero, add_zero]
      exact (FSData.eval_triv_ne_bot_iff _).2 (hD0 i)
    · have h := ha.add (tendsto_const_nhds (x := cM M • eR))
      refine h.congr fun i => ?_
      funext c
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_add, Rat.cast_mul, hcMQ,
        heQ, heR, Int.cast_natCast, Rat.cast_natCast]
  -- monotonicity in `M` (`ℓ ≤ 0`) and the uniform bound `ψ(⋆)`
  have hΦmono : ∀ v, Monotone fun M => Φs M v := by
    intro v
    obtain ⟨w, rfl⟩ := hsurj v
    refine monotone_nat_of_le_succ fun M => iInf_mono fun i => ?_
    rw [hKI, hKI]
    exact add_le_add le_rfl
      (ProjBerk.ereal_coe_mul_le_of_nonpos (hcM_pos (M + 1)) (hcM_anti M) (hℓle _))
  have hΦle : ∀ M v, Φs M v ≤ ((ψ X.normalization.triv).toReal : EReal) := by
    intro M v
    obtain ⟨w, rfl⟩ := hsurj v
    calc Φs M (ν.anMap w) ≤ ⨅ i, ψs i w := iInf_mono fun i => by
            rw [hKI]
            refine add_le_of_nonpos_right ?_
            simpa only [mul_zero] using
              ProjBerk.ereal_coe_mul_monotone (hcM_pos M).le (hℓle (ν.anMap w))
      _ = ψ w := (hinf w).symm
      _ ≤ _ := FSSystemC.IsPSH.le_toReal_apply_triv hψ w
  -- the open set `Ω = {|g| ≠ 0}`, over which `ν^an` is a homeomorphism
  set Ω : Set X.an := {v | ℓ v ≠ ⊥}
  have hℓcont : Continuous ℓ := (X.continuous_logSecAbs e' g).comp continuous_subtype_val
  have hΩopen : IsOpen Ω := isOpen_compl_singleton.preimage hℓcont
  have hinjΩ : ∀ w w', ν.anMap w = ν.anMap w' → ν.anMap w ∈ Ω → w = w' := fun w w' h hw =>
    hc.eq_of_anMap_eq_of_secAbs_ne_zero h fun h0 => hw ((logSecAbs_eq_bot_iff _ _ _).2 h0)
  have hbij : Function.Bijective (Ω.restrictPreimage ν.anMap) :=
    ⟨fun w w' h => Subtype.ext (hinjΩ w w' (congrArg Subtype.val h) w.2),
      Set.restrictPreimage_surjective _ hsurj⟩
  let E := (Equiv.ofBijective _ hbij).toHomeomorphOfContinuousClosed
    ν.continuous_anMap.restrictPreimage (ν.isClosedMap_anMap.restrictPreimage Ω)
  set s : Ω → X.normalization.an := fun v => (E.symm v).1
  have hs_cont : Continuous s := continuous_subtype_val.comp E.symm.continuous
  have hνs : ∀ v : Ω, ν.anMap (s v) = v := fun v => congrArg Subtype.val (E.apply_symm_apply v)
  -- on `Ω`, `sup_M φ_M = ψ ∘ (ν^an)⁻¹`
  have hQ : ∀ w, ν.anMap w ∈ Ω → ⨆ M, Φs M (ν.anMap w) = ψ w := by
    intro w hw
    have hne_top : ℓ (ν.anMap w) ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top (hℓle _)
    have hℓl : ℓ (ν.anMap w) = ((ℓ (ν.anMap w)).toReal : EReal) :=
      (EReal.coe_toReal hne_top hw).symm
    set l := (ℓ (ν.anMap w)).toReal
    have hl0 : l ≤ 0 := by
      have := hℓle (ν.anMap w)
      rw [hℓl] at this
      exact_mod_cast this
    have hΦ : ∀ M, Φs M (ν.anMap w) = ψ w + ((cM M * l : ℝ) : EReal) := by
      intro M
      simp only [hΦs, hKI, hℓl, ← EReal.coe_mul]
      rw [← ereal_iInf_add_coe, ← hinf w]
    simp only [hΦ]
    refine le_antisymm (iSup_le fun M => add_le_of_nonpos_right ?_) ?_
    · exact EReal.coe_nonpos.2 (mul_nonpos_of_nonneg_of_nonpos (hcM_pos M).le hl0)
    · have h0 : Tendsto (fun M => ((cM M * l : ℝ) : EReal)) atTop (𝓝 0) := by
        have := hcM_tendsto.mul_const l
        rw [zero_mul] at this
        exact EReal.tendsto_coe.2 this
      have ht : Tendsto (fun M => ψ w + ((cM M * l : ℝ) : EReal)) atTop (𝓝 (ψ w + 0)) :=
        (EReal.continuousAt_add (Or.inr EReal.zero_ne_bot) (Or.inr EReal.zero_ne_top)).tendsto.comp
          (tendsto_const_nhds.prodMk_nhds h0)
      rw [add_zero] at ht
      exact le_of_tendsto' ht fun M => le_iSup (fun M => ψ w + ((cM M * l : ℝ) : EReal)) M
  set G : X.an → EReal := fun v => ⨆ M, Φs M v
  have hGs : Ω.domRestrict G = ψ ∘ s := by
    funext v
    have hv : ν.anMap (s v) ∈ Ω := by rw [hνs]; exact v.2
    have := hQ (s v) hv
    rw [hνs] at this
    exact this
  have hGusc : UpperSemicontinuousOn G Ω := by
    refine upperSemicontinuousOn_iff_restrict.1 ?_
    rw [hGs]
    exact (FSSystemC.IsPSH.upperSemicontinuous hψ).comp hs_cont
  have hΦΩ : ∀ w, ν.anMap w ∈ Ω → uscReg G (ν.anMap w) = ψ w := fun w hw => by
    rw [uscReg_apply_of_upperSemicontinuousOn hΩopen hGusc hw]
    exact hQ w hw
  -- `(sup_M φ_M)^⋆ ∈ PSH(𝒳, (1 + δ) ω)` for every `δ > 0`, by `EP_𝒳((1 + δ) ω)`
  have hωnef : ω ∈ X.nefCone := X.mem_nefCone_of_nonneg fun c => (hω c).le
  have hΦθ : ∀ N : ℕ, X.IsPSH ((1 + cM N) • ω) (uscReg G) := by
    intro N
    have hEPN : X.HasEnvelopeProperty ((1 + cM N) • ω) :=
      (hasEnvelopeProperty_smul_iff hωnef (by linarith [hcM_pos N])).2 hEP
    have hev : ∀ᶠ M in atTop, ∀ c, cM M * eR c < cM N * ω c := by
      refine Filter.eventually_all.2 fun c => ?_
      have h := hcM_tendsto.mul_const (eR c)
      rw [zero_mul] at h
      exact h.eventually (gt_mem_nhds (mul_pos (hcM_pos N) (hω c)))
    obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hev
    have hu : ∀ M, X.IsPSH ((1 + cM N) • ω) (Φs (M + M₀)) := fun M =>
      (hΦpsh (M + M₀)).mono_class fun c => by
        have h1 := hM₀ (M + M₀) (by omega) c
        have h2 : (1 + cM N) * ω c = ω c + cM N * ω c := by ring
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h2]
        linarith
    have h := FSSystemC.HasEnvelopeProperty.isPSH_uscReg_iSup hEPN hu
      ⟨(ψ X.normalization.triv).toReal, fun M v => hΦle _ v⟩
    convert h using 2
    funext v
    exact ((hΦmono v).iSup_nat_add M₀).symm
  -- PSH2 at `ω`
  have hθt : Tendsto (fun N : ℕ => (1 + cM N) • ω) atTop (𝓝 ω) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).add hcM_tendsto).smul_const ω
    rw [add_zero, one_smul] at h
    exact h
  have hΦω : X.IsPSH ω (uscReg G) :=
    isPSH_of_antitone_seq hωnef hθt (u := fun _ => uscReg G) hΦθ (fun _ _ _ _ => le_rfl)
      (fun _ => iInf_const.symm) (FSSystemC.IsPSH.exists_ne_bot (hΦθ 0))
  -- `φ ∘ ν^an = ψ`: both are `ω`-psh on `𝒳^ν` and agree on `(ν^an)⁻¹(Ω) ⊇ (𝒳^ν)^div`
  refine ⟨uscReg G, hΦω, ?_⟩
  refine (ν.isPSH_comp hΦω).eq_of_forall_mem_eq hψ (Ω := ν.anMap ⁻¹' Ω) (fun w hw => ?_)
    (fun w hw => hΦΩ w hw)
  change X.logSecAbs (ν.anMap w).1 e' g ≠ ⊥
  rw [← ν.logSecAbs_anMap w hgX]
  exact hw.logSecAbs_ne_bot hgY hc.ne_zero

/-- **The envelope property at one positive class makes `ν^an` injective**
(`cor:gl-characterization`, (3) ⇒ (1), first step): if `ν(w) = ν(w')`, then for every
homogeneous `0 ≠ f T^a ∈ S^ν` the function `log |f| ∈ PSH(𝒳^ν, a) ⊆ PSH(𝒳^ν, t ω)` (`t ≫ 0`) is
of the form `φ ∘ ν^an` (`HasEnvelopeProperty.exists_isPSH_comp_anMap_eq`, with `EP_𝒳(t ω)` from
`lem:gl-ep-basic`(2)), so `|f|_w = |f|_{w'}`; multigraded points agreeing on homogeneous
elements are equal. -/
theorem HasEnvelopeProperty.anMap_ofNormalization_injective {ω : Fin r → ℝ}
    (hω : ∀ c, 0 < ω c) (hEP : X.HasEnvelopeProperty ω) :
    Function.Injective (FiniteHom.ofNormalization X).anMap := by
  intro w w' hww'
  refine Subtype.ext (ext_of_ofPiece w.2.1 w'.2.1 fun a f hf => ?_)
  rw [← secAbs_of_mem_piece w.2.2 (fun _ => rfl) hf,
    ← secAbs_of_mem_piece w'.2.2 (fun _ => rfl) hf]
  by_cases hf0 : f = 0
  · rw [hf0, secAbs_zero, secAbs_zero]
  have hfs : f ∈ X.normalization.sections fun c => (a c : ℤ) :=
    mem_sections_of_mem_piece (fun _ => rfl) hf
  -- a positive multiple `t ω` dominating the degree `a`
  set S : ℝ := ∑ c, (a c : ℝ) / ω c
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun c _ => div_nonneg (Nat.cast_nonneg _) (hω c).le
  have ht : 0 < 1 + S := by linarith
  have hle : (fun c => (((a c : ℤ) : ℚ) : ℝ)) ≤ (1 + S) • ω := fun c => by
    have h1 : (a c : ℝ) / ω c ≤ S :=
      Finset.single_le_sum (f := fun c' => (a c' : ℝ) / ω c')
        (fun c' _ => div_nonneg (Nat.cast_nonneg _) (hω c').le) (Finset.mem_univ c)
    have h2 : (a c : ℝ) / ω c * ω c = a c := div_mul_cancel₀ _ (hω c).ne'
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_natCast]
    calc (a c : ℝ) = (a c : ℝ) / ω c * ω c := h2.symm
      _ ≤ S * ω c := mul_le_mul_of_nonneg_right h1 (hω c).le
      _ ≤ (1 + S) * ω c := mul_le_mul_of_nonneg_right (by linarith) (hω c).le
  have hEPt : X.HasEnvelopeProperty ((1 + S) • ω) :=
    (hasEnvelopeProperty_smul_iff (X.mem_nefCone_of_nonneg fun c => (hω c).le) ht).2 hEP
  have hψ : X.normalization.IsPSH ((1 + S) • ω) fun v =>
      X.normalization.logSecAbs v.1 (fun c => (a c : ℤ)) f :=
    (isPSH_logSecAbs hfs hf0).mono_class hle
  obtain ⟨φ, -, hφ⟩ :=
    hEPt.exists_isPSH_comp_anMap_eq (fun c => by simpa using mul_pos ht (hω c)) hψ
  have h1 := congrFun hφ w
  have h2 := congrFun hφ w'
  simp only [Function.comp_apply] at h1 h2
  rw [hww'] at h1
  have h3 := h1.symm.trans h2
  simp only [logSecAbs] at h3
  exact_mod_cast ENNReal.log_injective h3

/-- **FHX Corollary 1.1, (3) ⇒ (1)** (`cor:gl-characterization`, `cor:nn-characterization`;
BJ22 Theorem 5.12, re-proved without BJ22 Theorem 5.6 and GAGA): if `EP_𝒳(ω)` holds for one
positive class `ω`, then `𝒳` is unibranch. -/
theorem HasEnvelopeProperty.isUnibranch {ω : Fin r → ℝ} (hω : ∀ c, 0 < ω c)
    (hEP : X.HasEnvelopeProperty ω) : X.IsUnibranch :=
  isUnibranch_of_anMap_injective (hEP.anMap_ofNormalization_injective hω)

/-- **FHX Corollary 1.1, (3) ⇒ (1)**: a model with the envelope property for some positive class
is unibranch. -/
theorem isUnibranch_of_exists_hasEnvelopeProperty
    (h : ∃ ω : Fin r → ℝ, (∀ c, 0 < ω c) ∧ X.HasEnvelopeProperty ω) : X.IsUnibranch := by
  obtain ⟨ω, hω, hEP⟩ := h
  exact hEP.isUnibranch hω

end Descent

end MultiModel
end EnvelopeProperty
