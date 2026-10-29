/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.BlowupModel
import EnvelopeProperty.Berkovich.Blowup
import EnvelopeProperty.Local.WeaklyPSH

/-!
# Blowup charts of the blowup model and surjectivity of `μ`

Let `X = V(I) ⊆ ℙ^M`, `B : X.BlowupCenter M'` the forms `G₀, …, G_{M'}` of degree `d`, and
`μ : X'^an → X^an` the blowup model of `EnvelopeProperty.Projective.BlowupModel`. This file
implements the blueprint nodes `lem:pg-blowup-chart` and `lem:pg-blowup-surjective` of
`projective-general.tex`: over the chart `U_{x_i} ∩ X^an ≅ (Spec A_i)^an` of `X`
(`A_i = QuotChartAlg I (X i) 1`, the degree-zero part of `S[x̄_i⁻¹]`, `S = R_M / I`), the blowup
`X'` is covered by the affine blowup charts `Spec A_i[𝔞_i/g]` of `EnvelopeProperty.blowupChart`,
`𝔞_i = {g₀, …, g_{M'}}`, `g_m = Ḡ_m / x̄_i^d`; these are the witnesses of weak
plurisubharmonicity (`EnvelopeProperty.IsWeaklyPSHOn`, FHX Definition 5.6) used for the descent
of Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Corollary 5.26
(`cor:normal-weak-global`, through `lem:pg-descent-weakly-psh`).

## Main definitions

Throughout `i : Fin (M + 1)` and `A_i = QuotChartAlg V.ideal (X i) 1`, assumed to be a domain
(`[IsDomain A_i]`, equivalent to `x_i ∉ I`: `X_notMem_ideal_of_isDomain`,
`ProjBerk.isDomain_quotChartAlg`).

* `B.centerGen i m = g_m = Ḡ_m / x̄_i^d ∈ A_i` and `B.centerSet i = 𝔞_i ⊆ A_i`, the finite set used
  as the witness `s` of `IsWeaklyPSHOn`; it contains a nonzero element
  (`exists_mem_centerSet_ne_zero`).
* `B.chartHom i g = δ : R_{M,M'} → A_i[𝔞_i/g]`, `xⱼ ↦ x̄ⱼ / x̄_i`, `y_m ↦ g_m / g`, an instance of
  the generic dehomogenization `dehomHom`.
* `B.chartPoint i hg hg0 w = κ(w) ∈ X'^an` for `g ∈ 𝔞_i`, `g ≠ 0` and
  `w ∈ (Spec A_i[𝔞_i/g])^an`; it is continuous in `w` (`continuous_chartPoint`).

## Main results (`lem:pg-blowup-chart`)

* (1) `chartHom_eq_zero_of_mem`: `δ(F) = 0` for `F ∈ I'`. This rests on the dehomogenization
  formula `F(z, h/g) = g^{-b} · F(x, G)(z)` in `Frac A` for `F` of bidegree `(a, b)` and
  `h_m = G_m(z)` (`coe_dehomHom_of_isWeightedHomogeneous`); for `z = (x̄ⱼ/x̄_i)ⱼ`,
  `F(x, G)(z) = (F(x, G)/x_i^{a + b d})‾` (`aeval_quotChartMk_X`). No embedding of `Frac A_i`
  into `Frac S` is needed.
* (2) `chartPoint_val_of_isWeightedHomogeneous`: `|F|_{κ(w)} = |δ(F)|_w μ_x(w)^{-a} μ_y(w)^{-b}`
  for `F` of bidegree `(a, b)`, with `μ_x(w) = max_j |x̄ⱼ/x̄_i|_w ≥ 1` and
  `μ_y(w) = max_m |g_m/g|_w ≥ 1` (`BiProjBerk.scaleX`, `BiProjBerk.scaleY` of `δ`;
  `scaleX_chartHom`, `one_le_scaleX_chartHom`, `one_le_scaleY_chartHom`);
  `logAbs_chartPoint_of_isWeightedHomogeneous` is the logarithmic form.
* (3) `proj_chartPoint`: `μ(κ(w)) = ι_{x_i}⁻¹(w|_{A_i})`, with `w|_{A_i}` the restriction along
  `EnvelopeProperty.chartMap : A_i → A_i[𝔞_i/g]`; `chartPoint_val_X_inl_self`,
  `chartPoint_val_X_inr_of_centerGen_eq`, `chartInv_comap_val_X_self`:
  `|x_i|_{κ(w)} = |x_i|_{ι_{x_i}⁻¹(w|_{A_i})} = μ_x(w)⁻¹` and `|y_l|_{κ(w)} = μ_y(w)⁻¹` for
  `g = g_l`; `proj_chartPoint_val_of_isHomogeneous`.
* `isWeaklyPSHOn_of_forall_chart`: the blowup of `Spec A_i` along `𝔞_i` as a witness of
  `IsWeaklyPSHOn` (the form used by `lem:pg-descent-weakly-psh`).

## Surjectivity (`lem:pg-blowup-surjective`)

`exists_chartPoint_proj_eq`: every `x ∈ U_{x_i} ∩ X^an` is `μ(κ(w))` for a point `w` of some chart
`A_i[𝔞_i/g]`, `g ∈ 𝔞_i \ {0}`, with `w|_{A_i} = ι_{x_i}(x)` (`exists_comap_chartMap_eq`, the
formalized surjectivity of blowup charts); hence `proj_surjective`.

## Implementation notes

Synthesizing the `k`-algebra and ring structures of `A[s/g]` directly for
`A = QuotChartAlg I σ d` is slow and produces instance terms that differ from the generic ones
of `EnvelopeProperty.Berkovich.Blowup` and `IsWeaklyPSHOn` (instantiated at `A_i`), and unifying the
two is very expensive. We therefore (a) state the algebra of the charts for a general domain `A`
(`dehomHom` and its lemmas), and (b) declare the shortcut instances
`ProjBerk.instAlgebraBlowupChartQuotChartAlg` and `ProjBerk.instCommRingBlowupChartQuotChartAlg`,
which unfold to the generic instances (`blowupChartAlgebra`, `blowupChartCommRing`). Hypotheses
passed to the generic lemmas are elaborated separately (`have`) before being applied.
-/

open scoped NNReal ENNReal Topology

open Topology MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Generic blowup charts

For a domain `A` over `k`, `s ⊆ A` finite and `g ∈ A`, the dehomogenization
`R_{M,M'} → A[s/g]`, `xⱼ ↦ zⱼ`, `y_m ↦ h_m / g` (`dehomHom`), for elements `zⱼ ∈ A` and
`h_m ∈ s`. Stating it for a general `A` keeps the instances on `A[s/g]` those of
`EnvelopeProperty.Berkovich.Blowup` (and of `IsWeaklyPSHOn`). -/

section Generic

variable (k : Type*) [Field k] {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]

/-- The `k`-algebra structure of a blowup chart `A[s/g]`, as synthesized for a general domain
`A`. It is used to declare the shortcut instance
`ProjBerk.instAlgebraBlowupChartQuotChartAlg` on the charts of `A = QuotChartAlg I σ d`, where the
direct synthesis is slow. -/
abbrev blowupChartAlgebra (s : Finset A) (g : A) : Algebra k (blowupChart s g) := inferInstance

omit [Algebra k A] in
/-- The ring structure of a blowup chart `A[s/g]`, as synthesized for a general domain `A`; used
for the shortcut instance `ProjBerk.instCommRingBlowupChartQuotChartAlg`. -/
abbrev blowupChartCommRing (s : Finset A) (g : A) : CommRing (blowupChart s g) := inferInstance

variable {k} {M M' : ℕ} (s : Finset A) (g : A) (z : Fin (M + 1) → A) (h : Fin (M' + 1) → A)
  (hs : ∀ m, h m ∈ s)

variable (k) in
/-- The **dehomogenization** `R_{M,M'} → A[s/g]`, `xⱼ ↦ zⱼ`, `y_m ↦ h_m / g`. -/
def dehomHom : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k →ₐ[k] blowupChart s g :=
  aeval (Sum.elim (fun j => chartMap k s g (z j)) (fun m => chartFrac s g (hs m)))

@[simp]
theorem dehomHom_X_inl (j : Fin (M + 1)) :
    dehomHom k s g z h hs (X (Sum.inl j)) = chartMap k s g (z j) := by
  simp [dehomHom]

@[simp]
theorem dehomHom_X_inr (m : Fin (M' + 1)) :
    dehomHom k s g z h hs (X (Sum.inr m)) = chartFrac s g (hs m) := by
  simp [dehomHom]

/-- **Dehomogenization formula**: if `h_m = G_m(z)` for polynomials `G_m ∈ R_M`, then for `F`
bihomogeneous of bidegree `(a, b)`, `F(z, h/g) = g^{-b} · F(x, G)(z)` in `Frac A`. -/
theorem coe_dehomHom_of_isWeightedHomogeneous {G : Fin (M' + 1) → MvPolynomial (Fin (M + 1)) k}
    (hG : ∀ m, aeval z (G m) = h m) {a b : ℕ} {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    ((dehomHom k s g z h hs F : blowupChart s g) : FractionRing A) =
      (algebraMap A (FractionRing A) g)⁻¹ ^ b *
        algebraMap A (FractionRing A) (aeval z (aeval (Sum.elim X G) F)) := by
  set K := FractionRing A
  let ψ : A →ₐ[k] K := IsScalarTower.toAlgHom k A K
  let Φ : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k →ₐ[k] K :=
    aeval fun v => (1 : K) ^ (biWeight M M' v).1 * (ψ g)⁻¹ ^ (biWeight M M' v).2 *
      ψ (aeval z (Sum.elim X G v))
  have key : ((blowupChart s g).val.toRingHom.comp (dehomHom k s g z h hs).toRingHom) =
      Φ.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change ((dehomHom k s g z h hs (algebraMap k _ c) : blowupChart s g) : K) =
        Φ (algebraMap k _ c)
      rw [AlgHom.commutes, AlgHom.commutes]
      rfl
    · rintro (j | m)
      · change ((dehomHom k s g z h hs (X (Sum.inl j)) : blowupChart s g) : K) =
          Φ (X (Sum.inl j))
        simp only [dehomHom_X_inl, coe_chartMap, Φ, aeval_X, Sum.elim_inl, biWeight_inl,
          pow_one, pow_zero, one_mul, mul_one]
        rfl
      · change ((dehomHom k s g z h hs (X (Sum.inr m)) : blowupChart s g) : K) =
          Φ (X (Sum.inr m))
        simp only [dehomHom_X_inr, coe_chartFrac, Φ, aeval_X, Sum.elim_inr, biWeight_inr,
          pow_one, pow_zero, one_mul, hG]
        exact div_eq_inv_mul _ _
  have h1 : ((dehomHom k s g z h hs F : blowupChart s g) : K) = Φ F :=
    RingHom.congr_fun key F
  rw [h1, hF.aeval_pow_mul_pow_mul, one_pow, one_mul]
  congr 1
  have h2 := comp_aeval_apply (Sum.elim X G) (ψ.comp (aeval z)) F
  simp only [AlgHom.comp_apply] at h2
  exact h2.symm

/-- `F(z, h/g) = 0` if `F_{(a,b)}(x, G)(z) = 0` for all bidegrees, where `h_m = G_m(z)`. -/
theorem dehomHom_eq_zero {G : Fin (M' + 1) → MvPolynomial (Fin (M + 1)) k}
    (hG : ∀ m, aeval z (G m) = h m) {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : ∀ p, aeval z (aeval (Sum.elim X G) (weightedHomogeneousComponent (biWeight M M') p F)) =
      0) :
    dehomHom k s g z h hs F = 0 := by
  rw [← sum_weightSupport (w := biWeight M M') F, map_sum]
  refine Finset.sum_eq_zero fun p _ => Subtype.ext ?_
  rw [coe_dehomHom_of_isWeightedHomogeneous s g z h hs hG (a := p.1) (b := p.2)
    (weightedHomogeneousComponent_isWeightedHomogeneous p F), hF p, map_zero, mul_zero]
  rfl

/-- `f(z, h/g) = f(z) ∈ A` for `f ∈ R_M`. -/
theorem dehomHom_rename_inl (f : MvPolynomial (Fin (M + 1)) k) :
    dehomHom k s g z h hs (rename Sum.inl f) = chartMap k s g (aeval z f) := by
  rw [dehomHom, aeval_rename, Sum.elim_comp_inl]
  exact (comp_aeval_apply z (chartMap k s g) f).symm

end Generic

/-- `log(v / (x^a y^b)) = log v - (a log x + b log y)` for `x, y ≠ 0` in `ℝ≥0`, computed in
`EReal`. -/
theorem log_coe_div_pow_mul_pow (v : ℝ≥0) {x y : ℝ≥0} (hx : x ≠ 0) (hy : y ≠ 0) (a b : ℕ) :
    ENNReal.log ((v / (x ^ a * y ^ b) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.log (v : ℝ≥0∞) - ((a : EReal) * ENNReal.log (x : ℝ≥0∞) +
        (b : EReal) * ENNReal.log (y : ℝ≥0∞)) := by
  rw [ENNReal.coe_div (mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hy)), div_eq_mul_inv,
    ENNReal.log_mul_add, ENNReal.log_inv, ENNReal.coe_mul, ENNReal.log_mul_add, ENNReal.coe_pow,
    ENNReal.coe_pow, ENNReal.log_pow, ENNReal.log_pow, sub_eq_add_neg]

namespace ProjBerk

variable {k : Type*} [Field k] {M : ℕ}

/-- Shortcut instance: the `k`-algebra structure of the blowup charts `A[s/g]` of
`A = QuotChartAlg I σ d`, equal to the generic one (`blowupChartAlgebra`). Without it, the
synthesis of `SMul k (FractionRing (QuotChartAlg I σ d))` times out. -/
instance instAlgebraBlowupChartQuotChartAlg (I : Ideal (MvPolynomial (Fin (M + 1)) k))
    (σ : MvPolynomial (Fin (M + 1)) k) (d : ℕ) [IsDomain (QuotChartAlg I σ d)]
    (s : Finset (QuotChartAlg I σ d)) (g : QuotChartAlg I σ d) : Algebra k (blowupChart s g) :=
  blowupChartAlgebra k s g

/-- Shortcut instance: the ring structure of the blowup charts `A[s/g]` of
`A = QuotChartAlg I σ d`, equal to the generic one (`blowupChartCommRing`), so that statements
about `Berk k A[s/g]` agree with the generic ones of `EnvelopeProperty.Berkovich.Blowup` and
`IsWeaklyPSHOn` up to unfolding of instances. -/
instance instCommRingBlowupChartQuotChartAlg (I : Ideal (MvPolynomial (Fin (M + 1)) k))
    (σ : MvPolynomial (Fin (M + 1)) k) (d : ℕ) [IsDomain (QuotChartAlg I σ d)]
    (s : Finset (QuotChartAlg I σ d)) (g : QuotChartAlg I σ d) : CommRing (blowupChart s g) :=
  blowupChartCommRing s g

end ProjBerk

namespace ProjSubvariety.BlowupCenter

open ProjBerk

variable {k : Type u} [Field k] {M : ℕ} {V : ProjSubvariety k M} {M' : ℕ} (B : V.BlowupCenter M')

/-! ### The centre in the chart `x_i ≠ 0` -/

section Center

variable (i : Fin (M + 1))

/-- The generator `g_m = Ḡ_m / x̄_i^d ∈ A_i` of the ideal `𝔞_i` of the centre in the chart
`x_i ≠ 0` (`lem:pg-blowup-chart`). -/
def centerGen (m : Fin (M' + 1)) : QuotChartAlg V.ideal (X i) 1 :=
  quotChartMk V.ideal (X i) 1 B.d (B.G m)

open Classical in
/-- The finite set `𝔞_i = {g₀, …, g_{M'}} ⊆ A_i` (`lem:pg-blowup-chart`); the blowup of
`Spec A_i` along the ideal it generates is the part of `X'` over the chart `x_i ≠ 0`, with charts
`EnvelopeProperty.blowupChart (B.centerSet i) g`. -/
def centerSet : Finset (QuotChartAlg V.ideal (X i) 1) :=
  Finset.univ.image (B.centerGen i)

theorem centerGen_mem_centerSet (m : Fin (M' + 1)) : B.centerGen i m ∈ B.centerSet i := by
  classical
  exact Finset.mem_image_of_mem _ (Finset.mem_univ m)

theorem mem_centerSet_iff {g : QuotChartAlg V.ideal (X i) 1} :
    g ∈ B.centerSet i ↔ ∃ m, B.centerGen i m = g := by
  classical
  simp [centerSet]

/-- `g_m = 0` iff `G_m ∈ I`, for `x_i ∉ I`. -/
theorem centerGen_eq_zero_iff (hi : (X i : MvPolynomial (Fin (M + 1)) k) ∉ V.ideal)
    (m : Fin (M' + 1)) : B.centerGen i m = 0 ↔ B.G m ∈ V.ideal :=
  quotChartMk_eq_zero_iff hi (by rw [mul_one]; exact B.isHomogeneous m)

omit B in
/-- `x̄_i / x̄_i = 1` in `A_i`. -/
theorem quotChartMk_X_self : quotChartMk V.ideal (X i) 1 1 (X i) = 1 := by
  have h := chartMk_pow_self (σ := (X i : MvPolynomial (Fin (M + 1)) k)) (isHomogeneous_X k i) 1
  rw [pow_one] at h
  rw [quotChartMk, h, map_one]

/-- `A_i` is the zero ring if `x_i ∈ I`; so `A_i` is a domain iff `x_i ∉ I`
(`ProjBerk.isDomain_quotChartAlg`). -/
theorem X_notMem_ideal_of_isDomain [IsDomain (QuotChartAlg V.ideal (X i) 1)] :
    (X i : MvPolynomial (Fin (M + 1)) k) ∉ V.ideal := by
  intro h
  have hX : (X i : MvPolynomial (Fin (M + 1)) k).IsHomogeneous (1 * 1) := by
    rw [one_mul]
    exact isHomogeneous_X k i
  have h1 : quotChartMk V.ideal (X i) 1 1 (X i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (chartMk_mem_chartIdeal hX h)
  exact @one_ne_zero _ _ _ (@NeZero.one _ _ IsDomain.toNontrivial)
    ((quotChartMk_X_self (V := V) i).symm.trans h1)

/-- `𝔞_i` contains a nonzero element (`G_m ∉ I` for some `m`), as required of the witnesses of
`IsWeaklyPSHOn`. -/
theorem exists_mem_centerSet_ne_zero [IsDomain (QuotChartAlg V.ideal (X i) 1)] :
    ∃ g ∈ B.centerSet i, g ≠ 0 := by
  obtain ⟨m, hm⟩ := B.exists_notMem
  exact ⟨B.centerGen i m, B.centerGen_mem_centerSet i m,
    fun h => hm ((B.centerGen_eq_zero_iff i (X_notMem_ideal_of_isDomain i) m).1 h)⟩

/-- Dehomogenization in the chart `x_i ≠ 0`: `τ(x̄₀/x̄_i, …, x̄_M/x̄_i) = τ̄ / x̄_i^N` for a form
`τ` of degree `N`. -/
theorem aeval_quotChartMk_X {N : ℕ} {τ : MvPolynomial (Fin (M + 1)) k}
    (hτ : τ.IsHomogeneous N) :
    aeval (fun j => quotChartMk V.ideal (X i) 1 1 (X j)) τ = quotChartMk V.ideal (X i) 1 N τ := by
  have h := comp_aeval_apply (B := QuotChartAlg V.ideal (X i) 1)
    (fun j => chartMk (X i) 1 1 (X j)) (Ideal.Quotient.mkₐ k (chartIdeal V.ideal (X i) 1)) τ
  rw [aeval_chartMk_X hτ] at h
  exact h.symm

theorem aeval_quotChartMk_X_G (m : Fin (M' + 1)) :
    aeval (fun j => quotChartMk V.ideal (X i) 1 1 (X j)) (B.G m) = B.centerGen i m :=
  aeval_quotChartMk_X i (B.isHomogeneous m)

/-- `|g_m|_{ι_{x_i}(x)} = |G_m|_x / |x_i|_x^d` (`lem:wu-proj-chart`(3)). -/
theorem chartMap_val_centerGen (x : V.an) (hx : (x : ProjBerk k M).1.val (X i) ≠ 0)
    (m : Fin (M' + 1)) :
    (V.chartMap (X i) 1 x hx).val (B.centerGen i m) =
      (x : ProjBerk k M).1.val (B.G m) / (x : ProjBerk k M).1.val (X i) ^ B.d :=
  chartMap_val_quotChartMk x hx (by rw [mul_one]; exact B.isHomogeneous m)

end Center

/-! ### The dehomogenization `δ` (`lem:pg-blowup-chart`(1)) -/

section ChartHom

variable (i : Fin (M + 1)) [IsDomain (QuotChartAlg V.ideal (X i) 1)]

/-- The **dehomogenization** `δ : R_{M,M'} → A_i[𝔞_i/g]`, `xⱼ ↦ x̄ⱼ / x̄_i`, `y_m ↦ g_m / g`
(`lem:pg-blowup-chart`). -/
def chartHom (g : QuotChartAlg V.ideal (X i) 1) :=
  dehomHom k (B.centerSet i) g (fun j => quotChartMk V.ideal (X i) 1 1 (X j)) (B.centerGen i)
    (B.centerGen_mem_centerSet i)

variable {i}

@[simp]
theorem chartHom_X_inl (g : QuotChartAlg V.ideal (X i) 1) (j : Fin (M + 1)) :
    B.chartHom i g (X (Sum.inl j)) =
      EnvelopeProperty.chartMap k (B.centerSet i) g (quotChartMk V.ideal (X i) 1 1 (X j)) :=
  dehomHom_X_inl _ _ _ _ _ j

@[simp]
theorem chartHom_X_inr (g : QuotChartAlg V.ideal (X i) 1) (m : Fin (M' + 1)) :
    B.chartHom i g (X (Sum.inr m)) =
      chartFrac (B.centerSet i) g (B.centerGen_mem_centerSet i m) :=
  dehomHom_X_inr _ _ _ _ _ m

/-- `δ(f(x)) = f̄ / x̄_i^c ∈ A_i` for a form `f` of degree `c` in `x`. -/
theorem chartHom_rename_inl (g : QuotChartAlg V.ideal (X i) 1) {c : ℕ}
    {f : MvPolynomial (Fin (M + 1)) k} (hf : f.IsHomogeneous c) :
    B.chartHom i g (rename Sum.inl f) =
      EnvelopeProperty.chartMap k (B.centerSet i) g (quotChartMk V.ideal (X i) 1 c f) := by
  rw [chartHom, dehomHom_rename_inl, aeval_quotChartMk_X i hf]

/-- **`lem:pg-blowup-chart`(1)**: `δ(F) = 0` for `F ∈ I'`. By the dehomogenization formula
`δ(F) = g^{-b} · (F(x, G) / x_i^{a + b d})‾` in `Frac A_i` for `F` of bidegree `(a, b)`
(`coe_dehomHom_of_isWeightedHomogeneous`), and `F_{(a,b)}(x, G) ∈ I` for `F ∈ I'`. -/
theorem chartHom_eq_zero_of_mem (g : QuotChartAlg V.ideal (X i) 1)
    {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k} (hF : F ∈ B.ideal) :
    B.chartHom i g F = 0 := by
  rw [chartHom]
  have key := @dehomHom_eq_zero k _ _ _ _ _ M M' (B.centerSet i) g
    (fun j => quotChartMk V.ideal (X i) 1 1 (X j)) (B.centerGen i) (B.centerGen_mem_centerSet i) B.G
  have hG := B.aeval_quotChartMk_X_G i
  have hF' : ∀ p, aeval (fun j => quotChartMk V.ideal (X i) 1 1 (X j))
      (aeval (Sum.elim X B.G) (weightedHomogeneousComponent (biWeight M M') p F)) = 0 := by
    intro p
    have hdeg : (B.subst (weightedHomogeneousComponent (biWeight M M') p F)).IsHomogeneous
        ((p.1 + p.2 * B.d) * 1) := by
      rw [mul_one]
      exact B.isHomogeneous_subst (weightedHomogeneousComponent_isWeightedHomogeneous p F)
    have h := aeval_quotChartMk_X (V := V) i (B.isHomogeneous_subst (a := p.1) (b := p.2)
      (weightedHomogeneousComponent_isWeightedHomogeneous p F))
    rw [subst] at h
    rw [h]
    exact Ideal.Quotient.eq_zero_iff_mem.2
      (chartMk_mem_chartIdeal hdeg (B.subst_weightedHomogeneousComponent_mem hF p))
  have key2 := @key hG F hF'
  exact key2

/-! ### The scales `μ_x`, `μ_y` -/

theorem chartHom_X_inl_self (g : QuotChartAlg V.ideal (X i) 1) :
    B.chartHom i g (X (Sum.inl i)) = 1 := by
  rw [chartHom_X_inl, quotChartMk_X_self, map_one]

theorem chartHom_X_inr_of_centerGen_eq {g : QuotChartAlg V.ideal (X i) 1} (hg0 : g ≠ 0)
    {l : Fin (M' + 1)} (hl : B.centerGen i l = g) : B.chartHom i g (X (Sum.inr l)) = 1 := by
  rw [chartHom_X_inr]
  subst hl
  exact chartFrac_self _ hg0

/-- `μ_x(w) = max_j |x̄ⱼ/x̄_i|_{w|_{A_i}}`. -/
theorem scaleX_chartHom (g : QuotChartAlg V.ideal (X i) 1)
    (w : Berk k (blowupChart (B.centerSet i) g)) :
    BiProjBerk.scaleX (B.chartHom i g) w =
      Finset.univ.sup fun j => (Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) g) w).val
        (quotChartMk V.ideal (X i) 1 1 (X j)) := by
  simp only [BiProjBerk.scaleX, chartHom_X_inl, Berk.comap_val_apply]

/-- `μ_x(w) ≥ |δ(x_i)|_w = 1`. -/
theorem one_le_scaleX_chartHom (g : QuotChartAlg V.ideal (X i) 1)
    (w : Berk k (blowupChart (B.centerSet i) g)) : 1 ≤ BiProjBerk.scaleX (B.chartHom i g) w := by
  have h := BiProjBerk.le_scaleX (φ := B.chartHom i g) (w := w) i
  rwa [chartHom_X_inl_self, map_one] at h

/-- `μ_y(w) ≥ |δ(y_l)|_w = |g/g|_w = 1` for `g = g_l ≠ 0`. -/
theorem one_le_scaleY_chartHom {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i)
    (hg0 : g ≠ 0) (w : Berk k (blowupChart (B.centerSet i) g)) :
    1 ≤ BiProjBerk.scaleY (B.chartHom i g) w := by
  obtain ⟨l, hl⟩ := (B.mem_centerSet_iff i).1 hg
  have h := BiProjBerk.le_scaleY (φ := B.chartHom i g) (w := w) l
  rwa [B.chartHom_X_inr_of_centerGen_eq hg0 hl, map_one] at h

theorem scaleX_chartHom_ne_zero (g : QuotChartAlg V.ideal (X i) 1)
    (w : Berk k (blowupChart (B.centerSet i) g)) : BiProjBerk.scaleX (B.chartHom i g) w ≠ 0 :=
  (zero_lt_one.trans_le (B.one_le_scaleX_chartHom g w)).ne'

theorem scaleY_chartHom_ne_zero {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i)
    (hg0 : g ≠ 0) (w : Berk k (blowupChart (B.centerSet i) g)) :
    BiProjBerk.scaleY (B.chartHom i g) w ≠ 0 :=
  (zero_lt_one.trans_le (B.one_le_scaleY_chartHom hg hg0 w)).ne'

/-! ### The points `κ(w)` (`lem:pg-blowup-chart`(2)) -/

variable (i) in
/-- The **blowup-chart point** `κ(w) ∈ X'^an` of `w ∈ (Spec A_i[𝔞_i/g])^an`, `g ∈ 𝔞_i`, `g ≠ 0`
(`lem:pg-blowup-chart`(2)): the rescaled pullback `BiProjBerk.ofComap` of `w` along `δ`,
`|F|_{κ(w)} = |δ(F)|_w μ_x(w)^{-a} μ_y(w)^{-b}` for `F` of bidegree `(a, b)`. -/
def chartPoint {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
    (w : Berk k (blowupChart (B.centerSet i) g)) : B.an :=
  ⟨BiProjBerk.ofComap (B.chartHom i g) w (B.scaleX_chartHom_ne_zero g w)
      (B.scaleY_chartHom_ne_zero hg hg0 w),
    fun _ hF => BiProjBerk.ofComap_val_eq_zero _ _ fun p => by
      rw [B.chartHom_eq_zero_of_mem g (B.weightedHomogeneousComponent_mem_ideal hF p), map_zero]⟩

theorem coe_chartPoint {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
    (w : Berk k (blowupChart (B.centerSet i) g)) :
    (B.chartPoint i hg hg0 w : BiProjBerk k M M') =
      BiProjBerk.ofComap (B.chartHom i g) w (B.scaleX_chartHom_ne_zero g w)
        (B.scaleY_chartHom_ne_zero hg hg0 w) :=
  rfl

/-- **`lem:pg-blowup-chart`(2)**: `|F|_{κ(w)} = |δ(F)|_w / (μ_x(w)^a μ_y(w)^b)` for `F`
bihomogeneous of bidegree `(a, b)`. -/
theorem chartPoint_val_of_isWeightedHomogeneous {g : QuotChartAlg V.ideal (X i) 1}
    (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0) (w : Berk k (blowupChart (B.centerSet i) g))
    {a b : ℕ} {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    (B.chartPoint i hg hg0 w : BiProjBerk k M M').1.val F =
      w.val (B.chartHom i g F) /
        (BiProjBerk.scaleX (B.chartHom i g) w ^ a * BiProjBerk.scaleY (B.chartHom i g) w ^ b) := by
  rw [coe_chartPoint, BiProjBerk.ofComap_val_of_isWeightedHomogeneous _ _ hF]

/-- **`lem:pg-blowup-chart`(2)**, logarithmic form:
`log|F|_{κ(w)} = log|δ(F)|_w - a log μ_x(w) - b log μ_y(w)` for `F` of bidegree `(a, b)`. -/
theorem logAbs_chartPoint_of_isWeightedHomogeneous {g : QuotChartAlg V.ideal (X i) 1}
    (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0) (w : Berk k (blowupChart (B.centerSet i) g))
    {a b : ℕ} {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    BiProjBerk.logAbs F (B.chartPoint i hg hg0 w) =
      Berk.logAbs (B.chartHom i g F) w -
        ((a : EReal) * ENNReal.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ≥0∞) +
          (b : EReal) * ENNReal.log (BiProjBerk.scaleY (B.chartHom i g) w : ℝ≥0∞)) := by
  rw [BiProjBerk.logAbs_def, B.chartPoint_val_of_isWeightedHomogeneous hg hg0 w hF,
    Berk.logAbs_def]
  exact log_coe_div_pow_mul_pow _ (B.scaleX_chartHom_ne_zero g w)
    (B.scaleY_chartHom_ne_zero hg hg0 w) a b

/-! ### `μ ∘ κ` (`lem:pg-blowup-chart`(3)) -/

/-- `|x_i|_{κ(w)} = μ_x(w)⁻¹` (`lem:pg-blowup-chart`(3)). -/
theorem chartPoint_val_X_inl_self {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i)
    (hg0 : g ≠ 0) (w : Berk k (blowupChart (B.centerSet i) g)) :
    (B.chartPoint i hg hg0 w : BiProjBerk k M M').1.val (X (Sum.inl i)) =
      (BiProjBerk.scaleX (B.chartHom i g) w)⁻¹ := by
  rw [B.chartPoint_val_of_isWeightedHomogeneous hg hg0 w
    (isWeightedHomogeneous_X k (biWeight M M') (Sum.inl i)), chartHom_X_inl_self, map_one,
    pow_one, pow_zero, mul_one, one_div]

/-- `|y_l|_{κ(w)} = μ_y(w)⁻¹` for `g = g_l` (`lem:pg-blowup-chart`(3)). -/
theorem chartPoint_val_X_inr_of_centerGen_eq {g : QuotChartAlg V.ideal (X i) 1}
    (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0) (w : Berk k (blowupChart (B.centerSet i) g))
    {l : Fin (M' + 1)} (hl : B.centerGen i l = g) :
    (B.chartPoint i hg hg0 w : BiProjBerk k M M').1.val (X (Sum.inr l)) =
      (BiProjBerk.scaleY (B.chartHom i g) w)⁻¹ := by
  rw [B.chartPoint_val_of_isWeightedHomogeneous hg hg0 w
    (isWeightedHomogeneous_X k (biWeight M M') (Sum.inr l)),
    B.chartHom_X_inr_of_centerGen_eq hg0 hl, map_one, pow_one, pow_zero, one_mul, one_div]

/-- `κ` is continuous: `|F|_{κ(w)} = max_p |δ(F_p)|_w / (μ_x(w)^{p₁} μ_y(w)^{p₂})`, and `μ_x`,
`μ_y` are continuous and nonzero. -/
theorem continuous_chartPoint {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i)
    (hg0 : g ≠ 0) : Continuous (B.chartPoint i hg hg0) := by
  refine Continuous.subtype_mk (BiProjBerk.continuous_iff.2 fun F => ?_) _
  have hX : Continuous fun w : Berk k (blowupChart (B.centerSet i) g) =>
      BiProjBerk.scaleX (B.chartHom i g) w :=
    Continuous.finset_sup_apply fun _ _ => Berk.continuous_val_apply _
  have hY : Continuous fun w : Berk k (blowupChart (B.centerSet i) g) =>
      BiProjBerk.scaleY (B.chartHom i g) w :=
    Continuous.finset_sup_apply fun _ _ => Berk.continuous_val_apply _
  change Continuous fun w => BiProjBerk.bigradedFun (BiProjBerk.comapNorm (B.chartHom i g) w) F
  refine Continuous.finset_sup_apply fun p _ => ?_
  exact (Berk.continuous_val_apply _).div₀ ((hX.pow _).mul (hY.pow _)) fun w =>
    mul_ne_zero (pow_ne_zero _ (B.scaleX_chartHom_ne_zero g w))
      (pow_ne_zero _ (B.scaleY_chartHom_ne_zero hg hg0 w))

/-- `|f|_{μ(κ(w))} = |f̄/x̄_i^c|_{w|_{A_i}} / μ_x(w)^c` for a form `f` of degree `c`. -/
theorem proj_chartPoint_val_of_isHomogeneous {g : QuotChartAlg V.ideal (X i) 1}
    (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0) (w : Berk k (blowupChart (B.centerSet i) g)) {c : ℕ}
    {f : MvPolynomial (Fin (M + 1)) k} (hf : f.IsHomogeneous c) :
    (B.proj (B.chartPoint i hg hg0 w) : ProjBerk k M).1.val f =
      (Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) g) w).val
          (quotChartMk V.ideal (X i) 1 c f) / BiProjBerk.scaleX (B.chartHom i g) w ^ c := by
  rw [proj_val_apply, B.chartPoint_val_of_isWeightedHomogeneous hg hg0 w
    (isWeightedHomogeneous_rename_inl hf), B.chartHom_rename_inl g hf, pow_zero, mul_one]
  rfl

/-- **`lem:pg-blowup-chart`(3)**: `μ(κ(w)) = ι_{x_i}⁻¹(w|_{A_i})`, `w|_{A_i}` the restriction along
`A_i → A_i[𝔞_i/g]`. Both points lie in the chart `x_i ≠ 0` (`|x_i|_{κ(w)} = μ_x(w)⁻¹`), and the
chart image of `μ(κ(w))` is `w|_{A_i}`: `|τ̄/x̄_i^N|_{ι(μ(κ(w)))} = |τ|_{κ(w)} / |x_i|_{κ(w)}^N
= |τ̄/x̄_i^N|_w` for forms `τ` of degree `N`. -/
theorem proj_chartPoint {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
    (w : Berk k (blowupChart (B.centerSet i) g)) :
    B.proj (B.chartPoint i hg hg0 w) = V.chartInv (X i) 1 (isHomogeneous_X k i) one_pos
      (Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) g) w) := by
  have hμ := B.scaleX_chartHom_ne_zero g w
  have hv : (B.proj (B.chartPoint i hg hg0 w) : ProjBerk k M).1.val (X i) ≠ 0 := by
    rw [proj_val_apply, rename_X, B.chartPoint_val_X_inl_self hg hg0 w]
    exact inv_ne_zero hμ
  refine (chartInv_chartMap (isHomogeneous_X k i) one_pos _ hv).symm.trans (congrArg _ ?_)
  refine Berk.ext_val fun a => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨N, τ, hτ, rfl⟩ := exists_eq_chartMk (isHomogeneous_X k i) a
  have hτ' : τ.IsHomogeneous N := by rwa [mul_one] at hτ
  have h1 := chartMap_val_quotChartMk (B.proj (B.chartPoint i hg hg0 w)) hv hτ
  have h2 := B.proj_chartPoint_val_of_isHomogeneous hg hg0 w hτ'
  have h3 : (B.proj (B.chartPoint i hg hg0 w) : ProjBerk k M).1.val (X i) =
      (BiProjBerk.scaleX (B.chartHom i g) w)⁻¹ := by
    rw [proj_val_apply, rename_X, B.chartPoint_val_X_inl_self hg hg0 w]
  change (V.chartMap (X i) 1 _ hv).val (quotChartMk V.ideal (X i) 1 N τ) = _ at h1 ⊢
  rw [h1, h2, h3, inv_pow, div_inv_eq_mul, div_mul_cancel₀ _ (pow_ne_zero _ hμ)]
  rfl

/-- `|x_i|_{ι_{x_i}⁻¹(w|_{A_i})} = μ_x(w)⁻¹`, i.e. `-log|x_i| ∘ ι_{x_i}⁻¹ = log μ_x` along the
chart. -/
theorem chartInv_comap_val_X_self {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i)
    (hg0 : g ≠ 0) (w : Berk k (blowupChart (B.centerSet i) g)) :
    (V.chartInv (X i) 1 (isHomogeneous_X k i) one_pos
        (Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) g) w) : ProjBerk k M).1.val (X i) =
      (BiProjBerk.scaleX (B.chartHom i g) w)⁻¹ := by
  rw [← B.proj_chartPoint hg hg0 w, proj_val_apply, rename_X, B.chartPoint_val_X_inl_self hg hg0 w]

/-- `log|x_i| ∘ ι_{x_i}⁻¹(w|_{A_i}) = -log μ_x(w)`. -/
theorem logAbs_chartInv_comap_X_self {g : QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i)
    (hg0 : g ≠ 0) (w : Berk k (blowupChart (B.centerSet i) g)) :
    ProjBerk.logAbs (X i) (V.chartInv (X i) 1 (isHomogeneous_X k i) one_pos
        (Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) g) w) : ProjBerk k M) =
      -ENNReal.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ≥0∞) := by
  rw [ProjBerk.logAbs_def, B.chartInv_comap_val_X_self hg hg0 w,
    ENNReal.coe_inv (B.scaleX_chartHom_ne_zero g w), ENNReal.log_inv]

/-! ### Weak plurisubharmonicity witnesses -/

/-- **The blowup charts as witnesses of weak plurisubharmonicity** (FHX Definition 5.6,
`IsWeaklyPSHOn`): a function `u` on `U ⊆ (Spec A_i)^an` is weakly psh, with the blowup of
`Spec A_i` along `𝔞_i` as witness, as soon as `u ∘ (w ↦ w|_{A_i})` is locally psh on the preimage
of `U` in every chart `A_i[𝔞_i/g]`, `g ∈ 𝔞_i \ {0}`. This is the form in which
`lem:pg-descent-weakly-psh` uses `lem:pg-blowup-chart`. -/
theorem isWeaklyPSHOn_of_forall_chart {U : Set (Berk k (QuotChartAlg V.ideal (X i) 1))}
    {u : Berk k (QuotChartAlg V.ideal (X i) 1) → EReal}
    (h : ∀ g ∈ B.centerSet i, g ≠ 0 →
      IsLocallyPSHOn (Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) g) ⁻¹' U)
        fun y => u (Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) g) y)) :
    IsWeaklyPSHOn U u :=
  ⟨B.centerSet i, B.exists_mem_centerSet_ne_zero i, h⟩

/-! ### Surjectivity (`lem:pg-blowup-surjective`) -/

variable (i) in
/-- **Surjectivity over the chart `x_i ≠ 0`** (proof of `lem:pg-blowup-surjective`): for
`x ∈ X^an` with `|x_i|_x ≠ 0` there are `g ∈ 𝔞_i \ {0}` and a point `w` of the chart
`A_i[𝔞_i/g]` with `w|_{A_i} = ι_{x_i}(x)` (the blowup charts cover `(Spec A_i)^an`,
`exists_comap_chartMap_eq`), and then `μ(κ(w)) = x`. -/
theorem exists_chartPoint_proj_eq (x : V.an) (hx : (x : ProjBerk k M).1.val (X i) ≠ 0) :
    ∃ (g : QuotChartAlg V.ideal (X i) 1) (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
      (w : Berk k (blowupChart (B.centerSet i) g)),
      Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) g) w = V.chartMap (X i) 1 x hx ∧
        B.proj (B.chartPoint i hg hg0 w) = x := by
  have h := exists_comap_chartMap_eq (k := k) (B.exists_mem_centerSet_ne_zero i)
    (V.chartMap (X i) 1 x hx)
  obtain ⟨g, hg, hg0, w, hw⟩ := h
  refine ⟨g, hg, hg0, w, hw, ?_⟩
  rw [B.proj_chartPoint hg hg0 w, hw, chartInv_chartMap]

end ChartHom

/-- **`lem:pg-blowup-surjective`**: `μ : X'^an → X^an` is surjective. For `x ∈ X^an` choose `i`
with `|x_i|_x = 1`; then `x_i ∉ I`, `A_i` is a domain, and `x = μ(κ(w))` for a point `w` of a
blowup chart over the chart `x_i ≠ 0` (`exists_chartPoint_proj_eq`). -/
theorem proj_surjective : Function.Surjective B.proj := by
  intro x
  obtain ⟨i, hi⟩ := (x : ProjBerk k M).exists_val_X_eq_one
  have hx : (x : ProjBerk k M).1.val (X i) ≠ 0 := by
    rw [hi]
    exact one_ne_zero
  have := isDomain_quotChartAlg (d := 1) (notMem_ideal_of_val_ne_zero hx)
  obtain ⟨g, hg, hg0, w, -, h⟩ := B.exists_chartPoint_proj_eq i x hx
  exact ⟨_, h⟩



end ProjSubvariety.BlowupCenter

end EnvelopeProperty
