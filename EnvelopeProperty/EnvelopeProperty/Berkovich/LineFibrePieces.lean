/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.LineGaussPaths
import EnvelopeProperty.Berkovich.OpenAffineLine
import EnvelopeProperty.Berkovich.FlatNormBaseChange
import EnvelopeProperty.Berkovich.SpectrumFiniteNorm

/-!
# Gauss rays, fibres over small discs and the weighted maximum principle on pieces

This file proves the analytic lemmas of the identification step of Fang–Han–Xia, *The envelope
property for unibranch projective varieties*, Proposition 5.22 (`prop:nonflat-norm`), along the
route of the blueprint chapter `nonflat-route.tex` (`lem:nf-gauss-ray`, `lem:nf-fibre-shrink`,
`lem:nf-pieces`, `lem:nf-pieces-fs`, and the two bounds of `prop:nf-identification`). This route
replaces the subharmonic functions of FHX Lemma 5.21 (`lem:curves`) by a maximum principle at
the Gauss points of small discs.

**Setting.** `F` is a non-Archimedean normed field and a `k`-algebra with `‖c‖ = 1` for
`0 ≠ c ∈ k`, so that a point of `(Spec Q)^an` over `F` is a point of `Berk k Q` restricting to
`‖·‖` on `F` (`EnvelopeProperty.nonflatFieldPoint` converts the author's relative spectra
`Berkovich.RelativeSpectrum (NormedField.valuation (K := F)) Q`). Further `p ∈ F[t]` with
`p(0) ≠ 0`, `Q = F[t]_p` (`AffineLine.OpenLineRing p`), and `R` is a finite free `Q`-algebra
(in the application, the normalized line product `∏ D_i`; no product structure is used). The
fibre of `q : (Spec R)^an → (Spec Q)^an` over `y` is the finset `nonflatFibre R y`, and the
multiplicities are `Berk.flatFibreMult`, as in `EnvelopeProperty.flatNormFun`.

* **Gauss rays** (`lem:nf-gauss-ray`). `nonflatEvalPoint` is `ξ : t ↦ 0` and
  `nonflatGaussPoint r` is the Gauss point `ζ_r` (`|∑ aᵢ tⁱ| = maxᵢ ‖aᵢ‖ rⁱ`), the image of
  `Berkovich.RelativeSpectrum.centeredGaussAway`. Then `ζ_0 = ξ`, `r ↦ ζ_r` is continuous, `ζ_r`
  has zero kernel for `r > 0`, and `|f(0)| ≤ |f|_{ζ_r}` for `f ∈ Q` and small `r`: for
  `f = P / pⁿ` use the constant term of `P` and `|p|_{ζ_r} = |p(0)|`.
* **Fibres over small discs** (`lem:nf-fibre-shrink`,
  `Berk.eventually_preimage_subset_of_continuous`).
* **The norm identity** `|N_{R/Q}(b)|_y = ∏_{z ↦ y} |b|_z^{m_z}`
  (`Berk.val_algebraNorm_eq_prod_flatFibreMult`, from `Spectrum.val_algebraNorm_of_finiteFree`).
* **Pieces** (`lem:nf-pieces`, `EnvelopeProperty.exists_nonflatPieces`). For `F` algebraically
  closed, the points `x` over `ξ` are `F`-rational
  (`exists_val_sub_eq_zero_of_mem_fibre_nonflatEvalPoint`), so there are `e_x ∈ R` with
  `e_x(x) = 1`, `e_x(x') = 0` for `x' ≠ x`. The open sets
  `U_x = {|1 - e_x| < 1} ∩ ⋂_{x' ≠ x} {|e_{x'}| < 1}` are disjoint and, for `r` near `0`, cut the
  fibre over `ζ_r` into pieces `G_x(r)`. If `F` is nontrivially valued, `∑_{G_x(r)} m = m_x` and
  `∏_{G_x(r)} |b|^m ≥ |b|_x^{m_x}`. The key estimate (`nonflat_piece_norm_estimate`) applies the
  maximum modulus principle to `N_{R/Q}(b E + κ (1 - e)^N)`, `E = 1 - (1 - e)^N`, and lets
  `N → ∞`.
* **Weighted maximum principle** (`lem:nf-pieces-fs`) for functions of Fubini–Study type in
  `R_g` (`IsNonflatAwayFS`) with `|g|_x ≠ 0` and for their decreasing limits
  (`eventually_nonflat_weighted_maxPrinciple`, `eventually_nonflat_weighted_maxPrinciple_iInf`).
* **Norm bounds** (`prop:nf-identification`): `N_q u(ξ) ≤ N_q u(ζ_r)` for `r` near `0` if `u` is
  near each point over `ξ` a decreasing limit of functions of FS type
  (`eventually_flatNormFun_nonflatEvalPoint_le`), and `limsup_{r → 0} N_q u(ζ_r) ≤ N_q u(ξ)` for
  `u` upper semicontinuous (`eventually_flatNormFun_nonflatGaussPoint_lt`).

## Comparison with the blueprint

* `lem:nf-pieces` is proved for an arbitrary finite free `Q`-algebra `R`: the factors `D_i`, their
  idempotents and the positivity of `min_{G_l} |b|` are not needed, because the estimate `(∗)` is
  obtained in the limit `N → ∞` (upper bounds `max(|b|_z, |κ| |1 - e|_z^N)` on the piece). The
  constant `κ` only needs `κ ≠ 0` and `|b| ≤ |κ|` on both fibres.
* Completeness of `F` is not used; algebraic closedness is used only for the rationality of the
  points over `ξ`, nontriviality of the absolute value only for the multiplicities of the pieces.
* "For all sufficiently small `ε > 0`" is stated as `∀ᶠ r in 𝓝 0` (which is stronger).
-/

open scoped NNReal ENNReal Topology Polynomial
open Polynomial Topology Filter

noncomputable section

namespace EnvelopeProperty

open Berk AffineLine

/-! ### Points over a valued field -/

section FieldPoints

variable {k : Type*} [Field k] {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra k F]
variable {Q : Type*} [CommRing Q] [Algebra k Q] [Algebra F Q] [IsScalarTower k F Q]

/-- A seminorm on an `F`-algebra `Q` restricting to the norm of `F`, viewed as a point of the
analytification `Berk k Q` over the trivially valued field `k` (the norm of `F` is trivial on
`k`). This is the convention of `Berkovich/FlatNormBaseChange`: points of `(Spec Q)^an` over `F`
are the points of `Berk k Q` restricting to `‖·‖` on `F`. -/
def nonflatFieldPoint (hF : ∀ c : k, c ≠ 0 → ‖algebraMap k F c‖ = 1)
    (x : Berkovich.RelativeSpectrum (NormedField.valuation (K := F)) Q) : Berk k Q where
  val := x.1.val
  val_algebraMap c hc := by
    rw [IsScalarTower.algebraMap_apply k F Q, x.2 (algebraMap k F c),
      NormedField.valuation_apply]
    exact NNReal.eq (by simpa using hF c hc)

variable (hF : ∀ c : k, c ≠ 0 → ‖algebraMap k F c‖ = 1)

@[simp]
theorem nonflatFieldPoint_val_apply
    (x : Berkovich.RelativeSpectrum (NormedField.valuation (K := F)) Q) (a : Q) :
    (nonflatFieldPoint hF x).val a = x.1.val a := rfl

/-- The points `nonflatFieldPoint hF x` restrict to the norm of `F`. -/
theorem nonflatFieldPoint_val_algebraMap
    (x : Berkovich.RelativeSpectrum (NormedField.valuation (K := F)) Q) (c : F) :
    (nonflatFieldPoint hF x).val (algebraMap F Q c) = ‖c‖₊ := by
  rw [nonflatFieldPoint_val_apply, x.2 c, NormedField.valuation_apply]

@[fun_prop]
theorem continuous_nonflatFieldPoint :
    Continuous (nonflatFieldPoint (Q := Q) hF) := by
  rw [Berk.continuous_iff]
  intro a
  exact Berkovich.RelativeSpectrum.continuous_val_apply a

end FieldPoints

/-! ### Gauss rays on an open line -/

section GaussRay

variable {k : Type*} [Field k] {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra k F]
variable (hF : ∀ c : k, c ≠ 0 → ‖algebraMap k F c‖ = 1) (p : F[X]) (hp : p.eval 0 ≠ 0)

/-- The `F`-rational point `ξ : t ↦ 0` of the open line `Spec F[t]_p` (`p(0) ≠ 0`), as a point of
`Berk k (OpenLineRing p)`: `|f|_ξ = ‖f(0)‖`. -/
def nonflatEvalPoint : Berk k (OpenLineRing p) where
  val := (NormedField.valuation (K := F)).comap (openLineEval p 0 hp : OpenLineRing p →+* F)
  val_algebraMap c hc := by
    rw [Valuation.comap_apply, IsScalarTower.algebraMap_apply k F (OpenLineRing p)]
    simp only [RingHom.coe_coe, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      NormedField.valuation_apply]
    exact NNReal.eq (by simpa using hF c hc)

/-- `|f|_ξ = ‖f(0)‖`. -/
theorem nonflatEvalPoint_val_apply (f : OpenLineRing p) :
    (nonflatEvalPoint hF p hp).val f = ‖openLineEval p 0 hp f‖₊ := by
  rw [nonflatEvalPoint, Valuation.comap_apply, NormedField.valuation_apply]
  rfl

theorem nonflatEvalPoint_val_algebraMap_polynomial (P : F[X]) :
    (nonflatEvalPoint hF p hp).val (algebraMap F[X] (OpenLineRing p) P) = ‖P.eval 0‖₊ := by
  rw [nonflatEvalPoint_val_apply, openLineEval_algebraMap]

/-- `ξ` restricts to the norm of `F`. -/
theorem nonflatEvalPoint_val_algebraMap (c : F) :
    (nonflatEvalPoint hF p hp).val (algebraMap F (OpenLineRing p) c) = ‖c‖₊ := by
  rw [nonflatEvalPoint_val_apply, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

include hp in
theorem nonflat_self_val_eval_ne_zero :
    Berkovich.RelativeSpectrum.val
      (Berkovich.RelativeSpectrum.self (NormedField.valuation (K := F))) (p.eval 0) ≠ 0 := by
  rw [Berkovich.RelativeSpectrum.val_apply, Berkovich.RelativeSpectrum.self_val,
    NormedField.valuation_apply]
  exact nnnorm_ne_zero_iff.mpr hp

/-- The **Gauss point** `ζ_r` of the disc `|t| ≤ r` in the open line `Spec F[t]_p`, `p(0) ≠ 0`:
`|∑ aᵢ tⁱ|_{ζ_r} = maxᵢ ‖aᵢ‖ rⁱ` on `F[t]`, extended to `F[t]_p`. It is the image in
`Berk k (OpenLineRing p)` of the author's localized centred Gauss point
`Berkovich.RelativeSpectrum.centeredGaussAway` (centre `0`, base point the norm of `F`). -/
def nonflatGaussPoint (r : ℝ≥0) : Berk k (OpenLineRing p) :=
  nonflatFieldPoint hF (Berkovich.RelativeSpectrum.centeredGaussAway (OpenLineRing p) p
    (Berkovich.RelativeSpectrum.self (NormedField.valuation (K := F))) 0
    (nonflat_self_val_eval_ne_zero p hp) r)

theorem nonflatGaussPoint_val_algebraMap_polynomial (r : ℝ≥0) (P : F[X]) :
    (nonflatGaussPoint hF p hp r).val (algebraMap F[X] (OpenLineRing p) P) =
      Berkovich.RelativeSpectrum.val (Berkovich.RelativeSpectrum.centeredGauss
        (Berkovich.RelativeSpectrum.self (NormedField.valuation (K := F))) 0 r) P :=
  Berkovich.RelativeSpectrum.centeredGaussAway_val_algebraMap (OpenLineRing p) p _ 0
    (nonflat_self_val_eval_ne_zero p hp) r P

/-- The centred Gauss value at centre `0` is the plain Gauss value
`maxᵢ ‖aᵢ‖ rⁱ`. -/
theorem nonflat_centeredGauss_zero_val (r : ℝ≥0) (P : F[X]) :
    Berkovich.RelativeSpectrum.val (Berkovich.RelativeSpectrum.centeredGauss
        (Berkovich.RelativeSpectrum.self (NormedField.valuation (K := F))) 0 r) P =
      (Berkovich.Spectrum.gauss
        (Berkovich.RelativeSpectrum.self (NormedField.valuation (K := F))).1 r).val P := by
  rw [Berkovich.RelativeSpectrum.centeredGauss_val_apply]
  have h : Polynomial.algEquivAevalXAddC (0 : F) P = P := by
    rw [Polynomial.algEquivAevalXAddC_apply, map_zero, add_zero]
    simp
  rw [h]
  rfl

/-- `|P|_{ζ_r} ≤ M` iff `‖aᵢ‖ rⁱ ≤ M` for all coefficients `aᵢ` of `P`. -/
theorem nonflatGaussPoint_val_algebraMap_polynomial_le_iff (r : ℝ≥0) (P : F[X]) (M : ℝ≥0) :
    (nonflatGaussPoint hF p hp r).val (algebraMap F[X] (OpenLineRing p) P) ≤ M ↔
      ∀ i, ‖P.coeff i‖₊ * r ^ i ≤ M := by
  rw [nonflatGaussPoint_val_algebraMap_polynomial, nonflat_centeredGauss_zero_val,
    Berkovich.Spectrum.gauss_val_le_iff]
  simp [NormedField.valuation_apply]

/-- `|P(0)| ≤ |P|_{ζ_r}` on polynomials. -/
theorem nonflatEvalPoint_val_le_nonflatGaussPoint_polynomial (r : ℝ≥0) (P : F[X]) :
    (nonflatEvalPoint hF p hp).val (algebraMap F[X] (OpenLineRing p) P) ≤
      (nonflatGaussPoint hF p hp r).val (algebraMap F[X] (OpenLineRing p) P) := by
  rw [nonflatEvalPoint_val_algebraMap_polynomial, nonflatGaussPoint_val_algebraMap_polynomial]
  have h := Berkovich.RelativeSpectrum.eval_val_le_centeredGauss
    (Berkovich.RelativeSpectrum.self (NormedField.valuation (K := F))) 0 r P
  simpa [NormedField.valuation_apply] using h

/-- `ζ_r` restricts to the norm of `F`. -/
theorem nonflatGaussPoint_val_algebraMap (r : ℝ≥0) (c : F) :
    (nonflatGaussPoint hF p hp r).val (algebraMap F (OpenLineRing p) c) = ‖c‖₊ :=
  nonflatFieldPoint_val_algebraMap hF _ c

/-- Radius zero is the evaluation at `0`. -/
theorem nonflatGaussPoint_zero : nonflatGaussPoint hF p hp 0 = nonflatEvalPoint hF p hp := by
  apply Berk.awayComap_injective (k := k) p
  apply Berk.ext
  apply Valuation.ext
  intro P
  change (nonflatGaussPoint hF p hp 0).val (algebraMap F[X] (OpenLineRing p) P) =
    (nonflatEvalPoint hF p hp).val (algebraMap F[X] (OpenLineRing p) P)
  rw [nonflatGaussPoint_val_algebraMap_polynomial, nonflatEvalPoint_val_algebraMap_polynomial,
    Berkovich.RelativeSpectrum.centeredGauss_zero, Berkovich.RelativeSpectrum.comap_val_apply]
  simp [NormedField.valuation_apply]

/-- The Gauss ray `r ↦ ζ_r` is continuous. -/
@[fun_prop]
theorem continuous_nonflatGaussPoint : Continuous (nonflatGaussPoint hF p hp) :=
  (continuous_nonflatFieldPoint hF).comp
    (Berkovich.RelativeSpectrum.continuous_centeredGaussAway (OpenLineRing p) p _ 0
      (nonflat_self_val_eval_ne_zero p hp))

/-- For `r > 0` the Gauss point `ζ_r` has zero kernel. -/
theorem nonflatGaussPoint_val_ne_zero {r : ℝ≥0} (hr : 0 < r) {f : OpenLineRing p} (hf : f ≠ 0) :
    (nonflatGaussPoint hF p hp r).val f ≠ 0 :=
  Berkovich.RelativeSpectrum.centeredGaussAway_val_ne_zero (OpenLineRing p) p _ 0
    (nonflat_self_val_eval_ne_zero p hp) r hr f hf

/-- The Gauss points `ζ_r` converge to `ξ` as `r → 0`. -/
theorem tendsto_nonflatGaussPoint_zero :
    Tendsto (nonflatGaussPoint hF p hp) (𝓝 0) (𝓝 (nonflatEvalPoint hF p hp)) := by
  rw [← nonflatGaussPoint_zero hF p hp]
  exact (continuous_nonflatGaussPoint hF p hp).tendsto 0

/-- **Maximum modulus on small discs** (`lem:nf-gauss-ray`): there is `ε₀ > 0` with
`|f(0)| ≤ |f|_{ζ_r}` for all `f ∈ F[t]_p` and `r ≤ ε₀`. -/
theorem exists_nonflatGaussPoint_maxModulus :
    ∃ ε₀ : ℝ≥0, 0 < ε₀ ∧ ∀ r : ℝ≥0, r ≤ ε₀ → ∀ f : OpenLineRing p,
      (nonflatEvalPoint hF p hp).val f ≤ (nonflatGaussPoint hF p hp r).val f := by
  set S : ℝ≥0 := ∑ i ∈ p.support, ‖p.coeff i‖₊
  have hp0 : 0 < ‖p.eval 0‖₊ := nnnorm_pos.mpr hp
  refine ⟨min 1 (‖p.eval 0‖₊ / (S + 1)), lt_min one_pos (div_pos hp0 (by positivity)), ?_⟩
  intro r hr f
  have hr1 : r ≤ 1 := hr.trans (min_le_left _ _)
  have hr2 : r ≤ ‖p.eval 0‖₊ / (S + 1) := hr.trans (min_le_right _ _)
  -- the value of `p` is constant on the small discs
  have hpval : (nonflatGaussPoint hF p hp r).val (algebraMap F[X] (OpenLineRing p) p) =
      ‖p.eval 0‖₊ := by
    apply le_antisymm
    · rw [nonflatGaussPoint_val_algebraMap_polynomial_le_iff]
      intro i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [Polynomial.coeff_zero_eq_eval_zero]
      · have hci : ‖p.coeff i‖₊ ≤ S := by
          by_cases hmem : i ∈ p.support
          · exact Finset.single_le_sum (f := fun i => ‖p.coeff i‖₊) (fun _ _ => zero_le) hmem
          · rw [Polynomial.notMem_support_iff.mp hmem, nnnorm_zero]
            exact zero_le
        calc ‖p.coeff i‖₊ * r ^ i ≤ S * r := by
              gcongr
              exact pow_le_of_le_one zero_le hr1 hi.ne'
          _ ≤ S * (‖p.eval 0‖₊ / (S + 1)) := by gcongr
          _ ≤ ‖p.eval 0‖₊ := by
              rw [mul_div_assoc']
              rw [div_le_iff₀ (by positivity)]
              nlinarith [(zero_le : 0 ≤ S), (zero_le : 0 ≤ ‖p.eval 0‖₊)]
    · have h := nonflatEvalPoint_val_le_nonflatGaussPoint_polynomial hF p hp r p
      rwa [nonflatEvalPoint_val_algebraMap_polynomial] at h
  obtain ⟨P, n, rfl⟩ := Berk.Away.exists_eq_mk' (OpenLineRing p) p f
  rw [Berk.awayComap_val_mk', Berk.awayComap_val_mk', Berk.awayComap_val_apply,
    Berk.awayComap_val_apply, Berk.awayComap_val_apply, Berk.awayComap_val_apply, hpval,
    nonflatEvalPoint_val_algebraMap_polynomial hF p hp P,
    nonflatEvalPoint_val_algebraMap_polynomial hF p hp p]
  gcongr
  have h := nonflatEvalPoint_val_le_nonflatGaussPoint_polynomial hF p hp r P
  rwa [nonflatEvalPoint_val_algebraMap_polynomial] at h

/-- The maximum modulus principle `|f(0)| ≤ |f|_{ζ_r}` holds for all `r` near `0`. -/
theorem eventually_nonflatGaussPoint_maxModulus :
    ∀ᶠ r in 𝓝 (0 : ℝ≥0), ∀ f : OpenLineRing p,
      (nonflatEvalPoint hF p hp).val f ≤ (nonflatGaussPoint hF p hp r).val f := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_nonflatGaussPoint_maxModulus hF p hp
  filter_upwards [Iic_mem_nhds hε₀] with r hr using h r hr

end GaussRay

/-! ### Fibres of finite free covers -/

section FiniteCover

variable {k : Type*} [Field k] {Q R : Type*} [CommRing Q] [CommRing R] [Algebra k Q]
  [Algebra k R] [Algebra Q R] [IsScalarTower k Q R]

/-- Points of the fibre over `y` restrict to `y` on `Q`. -/
theorem Berk.val_algebraMap_of_mem_fibre [Module.Finite Q R] {y : Berk k Q} {z : Berk k R}
    (hz : z ∈ (finite_preimage_singleton (A := R) y).toFinset) (q : Q) :
    z.val (algebraMap Q R q) = y.val q := by
  have hz' : z ∈ comap (IsScalarTower.toAlgHom k Q R) ⁻¹' {y} := (Set.Finite.mem_toFinset _).1 hz
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hz'
  rw [← hz', comap_val_apply, IsScalarTower.toAlgHom_apply]

/-- **The norm identity at a point** (`spectrum:finite-free-scalar-norm`, in the `Berk`
convention): for `R` finite free over `Q`, `b ∈ R` and `y ∈ (Spec Q)^an`,
`|N_{R/Q}(b)|_y = ∏_{z ↦ y} |b|_z^{m_z}` with the multiplicities `Berk.flatFibreMult`. This is
`Berkovich.Spectrum.val_algebraNorm_of_finiteFree` transported along
`Berk.absoluteFibreEquiv`. -/
theorem Berk.val_algebraNorm_eq_prod_flatFibreMult [Module.Free Q R] [Module.Finite Q R]
    (b : R) (y : Berk k Q) :
    y.val (Algebra.norm Q b) =
      ∏ z ∈ (finite_preimage_singleton (A := R) y).toFinset, z.val b ^ flatFibreMult Q z := by
  classical
  have h := Berkovich.Spectrum.val_algebraNorm_of_finiteFree (B := Q) b y.toSpectrum
  rw [toSpectrum_val] at h
  rw [h]
  symm
  let e := absoluteFibreEquiv (A := Q) (B := R) y
  refine Finset.prod_bij (fun z hz => (e ⟨z, (Set.Finite.mem_toFinset _).1 hz⟩).1) ?_ ?_ ?_ ?_
  · intro z hz
    exact (Set.Finite.mem_toFinset _).2 (e ⟨z, (Set.Finite.mem_toFinset _).1 hz⟩).2
  · intro z₁ h₁ z₂ h₂ he
    exact congrArg Subtype.val (e.injective (Subtype.ext he))
  · intro w hw
    obtain ⟨⟨z, hz⟩, he⟩ := e.surjective ⟨w, (Set.Finite.mem_toFinset _).1 hw⟩
    exact ⟨z, (Set.Finite.mem_toFinset _).2 hz, congrArg Subtype.val he⟩
  · intro z hz
    dsimp only [e]
    rw [absoluteFibreEquiv_apply_val, flatFibreMult_eq_spectrumFibreNormMult]
    rfl

/-- **Fibres over a path shrink** (`lem:nf-fibre-shrink`). Let `R` be finite over `Q` and
`γ : ℝ≥0 → (Spec Q)^an` continuous. If an open set `V` contains the fibre over `γ 0`, it contains
the fibres over `γ r` for all `r` close to `0`. The preimage of the compact arc `γ [0, 1]` is
compact (`Berk.isCompact_preimage_comap`), so the image of its part outside `V` is a closed set
avoiding `γ 0`. -/
theorem Berk.eventually_preimage_subset_of_continuous [Module.Finite Q R] {γ : ℝ≥0 → Berk k Q}
    (hγ : Continuous γ) {V : Set (Berk k R)} (hV : IsOpen V)
    (h0 : comap (IsScalarTower.toAlgHom k Q R) ⁻¹' {γ 0} ⊆ V) :
    ∀ᶠ r in 𝓝 (0 : ℝ≥0), comap (IsScalarTower.toAlgHom k Q R) ⁻¹' {γ r} ⊆ V := by
  set π := comap (k := k) (IsScalarTower.toAlgHom k Q R)
  have hint : ((IsScalarTower.toAlgHom k Q R : Q →ₐ[k] R) : Q →+* R).IsIntegral :=
    fun x => Algebra.IsIntegral.isIntegral (R := Q) x
  set K := γ '' Set.Icc 0 1
  have hK : IsCompact K := isCompact_Icc.image hγ
  set L := π ⁻¹' K ∩ Vᶜ
  have hL : IsCompact L := (isCompact_preimage_comap _ hint hK).inter_right hV.isClosed_compl
  set M := π '' L
  have hM : IsClosed M := (hL.image (continuous_comap _)).isClosed
  have h0M : γ 0 ∉ M := by
    rintro ⟨z, ⟨-, hzV⟩, hz⟩
    exact hzV (h0 hz)
  have h1 : ∀ᶠ r in 𝓝 (0 : ℝ≥0), γ r ∈ Mᶜ :=
    hγ.continuousAt.eventually (hM.isOpen_compl.mem_nhds h0M)
  have h2 : ∀ᶠ r in 𝓝 (0 : ℝ≥0), r < 1 := Iio_mem_nhds one_pos
  filter_upwards [h1, h2] with r hr hr1 z hz
  by_contra hzV
  have hzr : π z = γ r := hz
  exact hr ⟨z, ⟨⟨r, ⟨zero_le, hr1.le⟩, hzr.symm⟩, hzV⟩, hzr⟩

end FiniteCover

/-! ### Rational points over `ξ` -/

section Rational

variable {k : Type*} [Field k] {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra k F]
variable (hF : ∀ c : k, c ≠ 0 → ‖algebraMap k F c‖ = 1) {p : F[X]} (hp : p.eval 0 ≠ 0)
variable {R : Type*} [CommRing R] [Algebra k R] [Algebra (OpenLineRing p) R]
  [IsScalarTower k (OpenLineRing p) R]

/-- **Points over `ξ` are rational** (`lem:nf-line-weights`, first assertion, abstractly): if `F`
is algebraically closed and `R` is integral over `F[t]_p`, every point `x` of `(Spec R)^an` over
`ξ : t ↦ 0` is an `F`-point: each `b ∈ R` is congruent to a constant `c ∈ F` modulo the kernel of
`x`. A monic equation of `b` over `F[t]_p`, evaluated at `t = 0`, splits over `F`. -/
theorem exists_val_sub_eq_zero_of_mem_fibre_nonflatEvalPoint [IsAlgClosed F]
    [Algebra.IsIntegral (OpenLineRing p) R] [Module.Finite (OpenLineRing p) R] {x : Berk k R}
    (hx : x ∈ (finite_preimage_singleton (A := R) (nonflatEvalPoint hF p hp)).toFinset)
    (b : R) :
    ∃ c : F, x.val (b - algebraMap (OpenLineRing p) R (algebraMap F (OpenLineRing p) c)) = 0 := by
  classical
  set Q := OpenLineRing p
  set ev : Q →+* F := (openLineEval p 0 hp : Q →+* F)
  set φ : F →+* R := (algebraMap Q R).comp (algebraMap F Q)
  have hx' : ∀ q : Q, x.val (algebraMap Q R q) = ‖ev q‖₊ := fun q => by
    rw [Berk.val_algebraMap_of_mem_fibre hx, nonflatEvalPoint_val_apply]
    rfl
  have hev : ∀ q : Q, x.val (φ (ev q) - algebraMap Q R q) = 0 := by
    intro q
    have : φ (ev q) - algebraMap Q R q = algebraMap Q R (algebraMap F Q (ev q) - q) := by
      simp [φ, map_sub]
    rw [this, hx', map_sub]
    simp [ev]
  obtain ⟨P, hPm, hPb⟩ := Algebra.IsIntegral.isIntegral (R := Q) b
  have hdiff : x.val ((P.map ev).eval₂ φ b) = 0 := by
    rw [Polynomial.eval₂_map]
    have h : P.eval₂ (φ.comp ev) b = P.eval₂ (φ.comp ev) b - P.eval₂ (algebraMap Q R) b := by
      rw [hPb, sub_zero]
    rw [h, Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range,
      ← Finset.sum_sub_distrib]
    apply le_antisymm _ zero_le
    apply Valuation.map_sum_le
    intro i _
    rw [← sub_mul, map_mul, RingHom.comp_apply, hev, zero_mul]
  have hsplit := (IsAlgClosed.splits (P.map ev)).eq_prod_roots_of_monic (hPm.map ev)
  rw [hsplit, Polynomial.eval₂_multiset_prod, Multiset.map_map, map_multiset_prod,
    Multiset.prod_eq_zero_iff] at hdiff
  obtain ⟨a, ha, h0⟩ := Multiset.mem_map.1 hdiff
  obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 ha
  refine ⟨c, ?_⟩
  simpa [φ] using h0

end Rational

/-! ### The norm estimate behind the piece lemma -/

section PieceCore

open Classical

variable {k : Type*} [Field k] {Q R : Type*} [CommRing Q] [CommRing R] [Algebra k Q]
  [Algebra k R] [Algebra Q R] [IsScalarTower k Q R]

/-- **The norm estimate of the piece lemma** (`lem:nf-pieces`, claim `(∗)`), in abstract form.
Let `R` be finite free over `Q`, and `y₀, y₁ ∈ (Spec Q)^an` with `|f|_{y₀} ≤ |f|_{y₁}` for all
`f ∈ Q` (the maximum modulus principle `|f(0)| ≤ |f|_{ζ_ε}`). Let `x` be a point over `y₀` and
`e ∈ R` with `|1 - e|_x < 1` and `|e|_z < 1` at the other points `z` over `y₀`; let `G` be a set
of points over `y₁` with `|1 - e| < 1` on `G` and `|e| ≤ 1` at the other points over `y₁`. If
`κ ∈ Q` has the same nonzero value `K` at `y₀` and `y₁` and `|b| ≤ K` on both fibres, then
`|b|_x^{m_x} K^{∑_{z ≠ x} m_z} ≤ ∏_{z ∈ G} |b|_z^{m_z} · K^{∑_{z ∉ G} m_z}`.

Proof: apply the maximum modulus principle to the norm of `b E + κ (1 - e)^N`,
`E = 1 - (1 - e)^N` (Lemma `spectrum:finite-free-scalar-norm`), and let `N → ∞`. -/
theorem nonflat_piece_norm_estimate [Module.Free Q R] [Module.Finite Q R] {y₀ y₁ : Berk k Q}
    (hmax : ∀ f : Q, y₀.val f ≤ y₁.val f) {x : Berk k R}
    (hx : x ∈ (finite_preimage_singleton (A := R) y₀).toFinset)
    {e : R} (hex : x.val (1 - e) < 1)
    (hez : ∀ z ∈ (finite_preimage_singleton (A := R) y₀).toFinset, z ≠ x → z.val e < 1)
    {G : Finset (Berk k R)} (hG : G ⊆ (finite_preimage_singleton (A := R) y₁).toFinset)
    (hGe : ∀ z ∈ G, z.val (1 - e) < 1)
    (hGc : ∀ z ∈ (finite_preimage_singleton (A := R) y₁).toFinset, z ∉ G → z.val e ≤ 1)
    {κ : Q} (hκ : y₁.val κ = y₀.val κ) (hκ0 : y₀.val κ ≠ 0) {b : R}
    (hb₀ : ∀ z ∈ (finite_preimage_singleton (A := R) y₀).toFinset, z.val b ≤ y₀.val κ)
    (hb₁ : ∀ z ∈ (finite_preimage_singleton (A := R) y₁).toFinset, z.val b ≤ y₀.val κ) :
    x.val b ^ flatFibreMult Q x * y₀.val κ ^
        ∑ z ∈ (finite_preimage_singleton (A := R) y₀).toFinset.erase x, flatFibreMult Q z ≤
      (∏ z ∈ G, z.val b ^ flatFibreMult Q z) * y₀.val κ ^
        ∑ z ∈ (finite_preimage_singleton (A := R) y₁).toFinset \ G, flatFibreMult Q z := by
  classical
  set S₀ := (finite_preimage_singleton (A := R) y₀).toFinset
  set S₁ := (finite_preimage_singleton (A := R) y₁).toFinset
  set K := y₀.val κ
  by_cases hb0 : x.val b = 0
  · have hm : flatFibreMult Q x ≠ 0 := by
      have := one_le_flatFibreMult (B := Q) x
      omega
    rw [hb0, zero_pow hm, zero_mul]
    exact zero_le
  have hK : 0 < K := pos_iff_ne_zero.mpr hκ0
  set κ' := algebraMap Q R κ
  have hκz₀ : ∀ z ∈ S₀, z.val κ' = K := fun z hz => Berk.val_algebraMap_of_mem_fibre hz κ
  have hκz₁ : ∀ z ∈ S₁, z.val κ' = K := fun z hz =>
    (Berk.val_algebraMap_of_mem_fibre hz κ).trans hκ
  set E : ℕ → R := fun N => 1 - (1 - e) ^ N
  set b₂ : ℕ → R := fun N => b * E N + κ' * (1 - e) ^ N
  have hE_le : ∀ z : Berk k R, z.val (1 - e) ≤ 1 → ∀ N, z.val (E N) ≤ 1 := by
    intro z hz N
    refine (Valuation.map_sub _ _ _).trans (max_le (by rw [map_one]) ?_)
    rw [map_pow]
    exact pow_le_one₀ zero_le hz
  have hb₂_le : ∀ z : Berk k R, z.val κ' = K → z.val (1 - e) ≤ 1 → ∀ N,
      z.val (b₂ N) ≤ max (z.val b) (K * z.val (1 - e) ^ N) := by
    intro z hzκ hz N
    refine (Valuation.map_add _ _ _).trans (max_le_max ?_ ?_)
    · rw [map_mul]
      exact mul_le_of_le_one_right zero_le (hE_le z hz N)
    · rw [map_mul, map_pow, hzκ]
  have h1e_le : ∀ z : Berk k R, z.val e ≤ 1 → z.val (1 - e) ≤ 1 := fun z hz =>
    (Valuation.map_sub _ _ _).trans (max_le (by rw [map_one]) hz)
  -- the upper bound at `y₁`
  have hup : ∀ N, y₁.val (Algebra.norm Q (b₂ N)) ≤
      (∏ z ∈ G, max (z.val b) (K * z.val (1 - e) ^ N) ^ flatFibreMult Q z) *
        K ^ ∑ z ∈ S₁ \ G, flatFibreMult Q z := by
    intro N
    rw [Berk.val_algebraNorm_eq_prod_flatFibreMult, ← Finset.prod_sdiff hG,
      ← Finset.prod_pow_eq_pow_sum, mul_comm]
    apply mul_le_mul' (Finset.prod_le_prod (fun _ _ => zero_le) fun z hz => ?_)
      (Finset.prod_le_prod (fun _ _ => zero_le) fun z hz => ?_)
    · exact pow_le_pow_left₀ zero_le (hb₂_le z (hκz₁ z (hG hz)) (hGe z hz).le N) _
    · obtain ⟨hz1, hzG⟩ := Finset.mem_sdiff.1 hz
      have hz1e := h1e_le z (hGc z hz1 hzG)
      refine pow_le_pow_left₀ zero_le ((hb₂_le z (hκz₁ z hz1) hz1e N).trans
        (max_le (hb₁ z hz1) ?_)) _
      exact mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hz1e)
  -- the exact value at `y₀` for large `N`
  set θ := x.val (1 - e)
  have hxb : 0 < x.val b := pos_iff_ne_zero.mpr hb0
  have hev : ∀ᶠ N in atTop, 1 ≤ N ∧ K * θ ^ N < x.val b := by
    have ht : Tendsto (fun N : ℕ => K * θ ^ N) atTop (𝓝 0) := by
      simpa using (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hex).const_mul K
    exact (eventually_ge_atTop 1).and (ht.eventually (gt_mem_nhds hxb))
  have hlow : ∀ N, 1 ≤ N → K * θ ^ N < x.val b →
      y₀.val (Algebra.norm Q (b₂ N)) =
        x.val b ^ flatFibreMult Q x * K ^ ∑ z ∈ S₀.erase x, flatFibreMult Q z := by
    intro N hN hNb
    rw [Berk.val_algebraNorm_eq_prod_flatFibreMult, ← Finset.mul_prod_erase _ _ hx,
      ← Finset.prod_pow_eq_pow_sum]
    congr 1
    · have hθN : x.val ((1 - e) ^ N) < x.val 1 := by
        rw [map_pow, map_one]
        exact pow_lt_one₀ zero_le hex (by omega)
      have hE1 : x.val (E N) = 1 := by
        change x.val (1 - (1 - e) ^ N) = 1
        rw [Valuation.map_sub_eq_of_lt_left _ hθN, map_one]
      have hlt : x.val (κ' * (1 - e) ^ N) < x.val (b * E N) := by
        rw [map_mul, map_mul, hE1, mul_one, map_pow, hκz₀ x hx]
        exact hNb
      have : x.val (b₂ N) = x.val b := by
        change x.val (b * E N + κ' * (1 - e) ^ N) = x.val b
        rw [Valuation.map_add_eq_of_lt_left _ hlt, map_mul, hE1, mul_one]
      rw [this]
    · apply Finset.prod_congr rfl
      intro z hz
      obtain ⟨hzx, hz0⟩ := Finset.mem_erase.1 hz
      have hze := hez z hz0 hzx
      have h1e : z.val (1 - e) = 1 := by
        rw [Valuation.map_sub_eq_of_lt_left _ (by rwa [map_one]), map_one]
      have hgeom : E N = (∑ i ∈ Finset.range N, (1 - e) ^ i) * e := by
        have := geom_sum_mul (1 - e) N
        change 1 - (1 - e) ^ N = _
        linear_combination this
      have hEz : z.val (E N) < 1 := by
        rw [hgeom, map_mul]
        calc z.val (∑ i ∈ Finset.range N, (1 - e) ^ i) * z.val e ≤ 1 * z.val e := by
              gcongr
              apply Valuation.map_sum_le
              intro i _
              rw [map_pow, h1e, one_pow]
          _ < 1 := by rw [one_mul]; exact hze
      have hlt : z.val (b * E N) < z.val (κ' * (1 - e) ^ N) := by
        rw [map_mul, map_mul, map_pow, h1e, one_pow, mul_one, hκz₀ z hz0]
        calc z.val b * z.val (E N) ≤ K * z.val (E N) := by
              gcongr
              exact hb₀ z hz0
          _ < K := mul_lt_of_lt_one_right hK hEz
      have : z.val (b₂ N) = K := by
        change z.val (b * E N + κ' * (1 - e) ^ N) = K
        rw [Valuation.map_add_eq_of_lt_right _ hlt, map_mul, map_pow, h1e, one_pow, mul_one,
          hκz₀ z hz0]
      rw [this]
  -- let `N → ∞`
  have hlim : Tendsto (fun N : ℕ =>
      (∏ z ∈ G, max (z.val b) (K * z.val (1 - e) ^ N) ^ flatFibreMult Q z) *
        K ^ ∑ z ∈ S₁ \ G, flatFibreMult Q z) atTop
      (𝓝 ((∏ z ∈ G, z.val b ^ flatFibreMult Q z) * K ^ ∑ z ∈ S₁ \ G, flatFibreMult Q z)) := by
    apply Tendsto.mul_const
    apply tendsto_finsetProd
    intro z hz
    apply Tendsto.pow
    have h0 : Tendsto (fun N : ℕ => K * z.val (1 - e) ^ N) atTop (𝓝 0) := by
      simpa using (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (hGe z hz)).const_mul K
    have h := (tendsto_const_nhds (x := z.val b)).max h0
    rwa [max_eq_left zero_le] at h
  refine ge_of_tendsto hlim ?_
  filter_upwards [hev] with N hN
  rw [← hlow N hN.1 hN.2]
  exact (hmax _).trans (hup N)

end PieceCore

/-! ### Elementary weighted estimates -/

section Weighted

open Classical

/-- A weighted sum over a set covered by pairwise disjoint pieces is the sum over the pieces. -/
theorem nonflat_sum_eq_sum_pieces {α β M : Type*} [AddCommMonoid M] {S₀ : Finset β}
    {S₁ : Finset α} {U : β → Set α}
    (hdisj : ∀ x ∈ S₀, ∀ x' ∈ S₀, x ≠ x' → Disjoint (U x) (U x'))
    (hcov : ∀ z ∈ S₁, ∃ x ∈ S₀, z ∈ U x) (f : α → M) :
    ∑ z ∈ S₁, f z = ∑ x ∈ S₀, ∑ z ∈ S₁ with z ∈ U x, f z := by
  rw [← Finset.sum_biUnion]
  · congr 1
    ext z
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hz
      obtain ⟨x, hx, hzx⟩ := hcov z hz
      exact ⟨x, hx, hz, hzx⟩
    · rintro ⟨x, -, hz, -⟩
      exact hz
  · intro x hx x' hx' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_filter]
    intro z _ hz hz'
    exact Set.disjoint_left.1 (hdisj x hx x' hx' hne) hz hz'

/-- The logarithmic form of a weighted product inequality: if `v₀^M ≤ ∏ vᵢ^{mᵢ}` with
`∑ mᵢ = M`, then `M (a log v₀ + c) ≤ ∑ mᵢ (a log vᵢ + c)` for `a > 0` (in `[-∞, ∞)`). -/
theorem nonflat_logTerm_le_sum {ι : Type*} (s : Finset ι) (m : ι → ℕ) (hm : ∀ i ∈ s, 1 ≤ m i)
    {M : ℕ} (hM : 1 ≤ M) (hsum : ∑ i ∈ s, m i = M) {a : ℝ} (ha : 0 < a) (c : ℝ)
    (v : ι → ℝ≥0) (v₀ : ℝ≥0) (hv : v₀ ^ M ≤ ∏ i ∈ s, v i ^ m i) :
    ((M : ℝ) : EReal) * ((a : EReal) * ENNReal.log (v₀ : ℝ≥0∞) + (c : EReal)) ≤
      ∑ i ∈ s, ((m i : ℝ) : EReal) * ((a : EReal) * ENNReal.log (v i : ℝ≥0∞) + (c : EReal)) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  by_cases hv₀ : v₀ = 0
  · rw [hv₀, ENNReal.coe_zero, ENNReal.log_zero, EReal.coe_mul_bot_of_pos ha, EReal.bot_add,
      EReal.coe_mul_bot_of_pos hM0]
    exact bot_le
  have hprod : ∏ i ∈ s, v i ^ m i ≠ 0 :=
    (lt_of_lt_of_le (pow_pos (pos_iff_ne_zero.2 hv₀) M) hv).ne'
  have hvi : ∀ i ∈ s, v i ≠ 0 := by
    intro i hi h
    apply hprod
    exact Finset.prod_eq_zero hi (by rw [h]; exact zero_pow (by have := hm i hi; omega))
  rw [ENNReal.log_of_nnreal hv₀]
  rw [Finset.sum_congr rfl fun i hi => by rw [ENNReal.log_of_nnreal (hvi i hi)]]
  have hreal : ∀ i ∈ s, ((m i : ℝ) : EReal) * ((a : EReal) * ((Real.log (v i) : ℝ) : EReal) +
      (c : EReal)) = (((m i : ℝ) * (a * Real.log (v i) + c) : ℝ) : EReal) := by
    intro i _
    simp only [EReal.coe_mul, EReal.coe_add]
  rw [Finset.sum_congr rfl hreal, ← ereal_coe_finsetSum]
  simp only [← EReal.coe_mul, ← EReal.coe_add]
  apply EReal.coe_le_coe_iff.2
  have hlog : Real.log ((v₀ : ℝ) ^ M) ≤ Real.log (∏ i ∈ s, (v i : ℝ) ^ m i) := by
    apply Real.log_le_log (pow_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv₀)) M)
    exact_mod_cast hv
  rw [Real.log_pow, Real.log_prod (fun i hi => pow_ne_zero _ (NNReal.coe_ne_zero.2 (hvi i hi)))]
    at hlog
  simp only [Real.log_pow] at hlog
  have hsumR : ∑ i ∈ s, (m i : ℝ) = M := by exact_mod_cast hsum
  calc (M : ℝ) * (a * Real.log v₀ + c) = a * ((M : ℝ) * Real.log v₀) + (M : ℝ) * c := by ring
    _ ≤ a * ∑ i ∈ s, (m i : ℝ) * Real.log (v i) + (∑ i ∈ s, (m i : ℝ)) * c := by
        rw [hsumR]
        gcongr
    _ = ∑ i ∈ s, (m i : ℝ) * (a * Real.log (v i) + c) := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- The weighted maximum principle for finite maxima of logarithmic terms: if every term satisfies
the product inequality `v₀(t)^M ≤ ∏ vᵢ(t)^{mᵢ}` with `∑ mᵢ = M`, then the function
`max {c₀, max_t (a_t log v(t) + c_t)}` (with `a_t > 0`) satisfies `M Φ₀ ≤ ∑ mᵢ Φᵢ`. -/
theorem nonflat_maxLogTerms_le_sum {ι τ : Type*} (s : Finset ι) (m : ι → ℕ)
    (hm : ∀ i ∈ s, 1 ≤ m i) {M : ℕ} (hM : 1 ≤ M) (hsum : ∑ i ∈ s, m i = M) (T : Finset τ)
    (c₀ : ℝ) (a c : τ → ℝ) (ha : ∀ t ∈ T, 0 < a t) (v : τ → ι → ℝ≥0) (v₀ : τ → ℝ≥0)
    (hv : ∀ t ∈ T, v₀ t ^ M ≤ ∏ i ∈ s, v t i ^ m i) :
    ((M : ℝ) : EReal) * max (c₀ : EReal)
        (T.sup fun t => (a t : EReal) * ENNReal.log (v₀ t : ℝ≥0∞) + (c t : EReal)) ≤
      ∑ i ∈ s, ((m i : ℝ) : EReal) * max (c₀ : EReal)
        (T.sup fun t => (a t : EReal) * ENNReal.log (v t i : ℝ≥0∞) + (c t : EReal)) := by
  have hmono : ∀ L : ι → EReal, (∀ i ∈ s, L i ≤ max (c₀ : EReal)
      (T.sup fun t => (a t : EReal) * ENNReal.log (v t i : ℝ≥0∞) + (c t : EReal))) →
      ∑ i ∈ s, ((m i : ℝ) : EReal) * L i ≤ ∑ i ∈ s, ((m i : ℝ) : EReal) * max (c₀ : EReal)
        (T.sup fun t => (a t : EReal) * ENNReal.log (v t i : ℝ≥0∞) + (c t : EReal)) :=
    fun L hL => Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (hL i hi) (by exact_mod_cast (Nat.cast_nonneg (m i)))
  rcases le_total (T.sup fun t => (a t : EReal) * ENNReal.log (v₀ t : ℝ≥0∞) + (c t : EReal))
    (c₀ : EReal) with h | h
  · rw [max_eq_left h]
    have hc : ((M : ℝ) : EReal) * (c₀ : EReal) = ∑ i ∈ s, ((m i : ℝ) : EReal) * (c₀ : EReal) := by
      rw [← EReal.coe_mul, ← hsum, Nat.cast_sum, Finset.sum_mul, ereal_coe_finsetSum]
      simp only [EReal.coe_mul]
    rw [hc]
    exact hmono _ fun i _ => le_max_left _ _
  · rw [max_eq_right h]
    have hT : T.Nonempty := by
      by_contra hT
      rw [Finset.not_nonempty_iff_eq_empty.1 hT, Finset.sup_empty] at h
      exact absurd h (not_le.2 (EReal.bot_lt_coe c₀))
    obtain ⟨t, ht, hteq⟩ := Finset.exists_mem_eq_sup T hT
      (fun t => (a t : EReal) * ENNReal.log (v₀ t : ℝ≥0∞) + (c t : EReal))
    rw [hteq]
    refine (nonflat_logTerm_le_sum s m hm hM hsum (ha t ht) (c t) (v t) (v₀ t) (hv t ht)).trans ?_
    refine hmono _ fun i _ => le_trans ?_ (le_max_right _ _)
    exact Finset.le_sup (f := fun t => (a t : EReal) * ENNReal.log (v t i : ℝ≥0∞) + (c t : EReal))
      ht

/-- If a positive combination `∑ wᵢ aᵢ` of values `aᵢ < ∞` is `< C`, there are reals `cᵢ > aᵢ`
with `∑ wᵢ cᵢ < C`. -/
theorem nonflat_exists_real_gt_of_sum_lt {ι : Type*} (s : Finset ι) (w : ι → ℕ)
    (hw : ∀ i ∈ s, 1 ≤ w i) (a : ι → EReal) (ha : ∀ i ∈ s, a i ≠ ⊤) {C : EReal}
    (hC : ∑ i ∈ s, ((w i : ℝ) : EReal) * a i < C) :
    ∃ c : ι → ℝ, (∀ i ∈ s, a i < c i) ∧ ∑ i ∈ s, ((w i : ℝ) : EReal) * (c i : EReal) < C := by
  have hCbot : C ≠ ⊥ := ne_bot_of_gt hC
  by_cases hbot : ∃ i₀ ∈ s, a i₀ = ⊥
  · obtain ⟨i₀, hi₀, hai₀⟩ := hbot
    set c' : ι → ℝ := fun i => if a i = ⊥ then 0 else (a i).toReal + 1
    have hc' : ∀ i ∈ s, a i < c' i := by
      intro i hi
      by_cases h : a i = ⊥
      · simp only [c', if_pos h, h]
        exact EReal.bot_lt_coe 0
      · simp only [c', if_neg h]
        conv_lhs => rw [← EReal.coe_toReal (ha i hi) h]
        exact EReal.coe_lt_coe_iff.2 (by linarith)
    set T : ℝ := ∑ i ∈ s.erase i₀, (w i : ℝ) * c' i
    set t : ℝ := if C = ⊤ then 0 else (C.toReal - T - 1) / w i₀
    refine ⟨Function.update c' i₀ t, ?_, ?_⟩
    · intro i hi
      by_cases h : i = i₀
      · subst h
        rw [hai₀]
        exact EReal.bot_lt_coe _
      · rw [Function.update_of_ne h]
        exact hc' i hi
    · rw [← Finset.add_sum_erase _ _ hi₀, Function.update_self]
      have hsumT : ∑ i ∈ s.erase i₀, ((w i : ℝ) : EReal) * (Function.update c' i₀ t i : EReal) =
          (T : EReal) := by
        rw [ereal_coe_finsetSum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi), EReal.coe_mul]
      rw [hsumT, ← EReal.coe_mul, ← EReal.coe_add]
      by_cases hCtop : C = ⊤
      · rw [hCtop]
        exact EReal.coe_lt_top _
      · rw [← EReal.coe_toReal hCtop hCbot]
        apply EReal.coe_lt_coe_iff.2
        simp only [t, if_neg hCtop]
        have hw0 : (0 : ℝ) < w i₀ := by exact_mod_cast hw i₀ hi₀
        rw [mul_div_cancel₀ _ hw0.ne']
        linarith
  · push Not at hbot
    set A : ℝ := ∑ i ∈ s, (w i : ℝ) * (a i).toReal
    have hA : ∑ i ∈ s, ((w i : ℝ) : EReal) * a i = (A : EReal) := by
      rw [ereal_coe_finsetSum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [EReal.coe_mul, EReal.coe_toReal (ha i hi) (hbot i hi)]
    set W : ℝ := ∑ i ∈ s, (w i : ℝ)
    have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    rw [hA] at hC
    set δ : ℝ := if C = ⊤ then 1 else (C.toReal - A) / (W + 1)
    have hAC : C ≠ ⊤ → A < C.toReal := fun hCtop => by
      rw [← EReal.coe_toReal hCtop hCbot] at hC
      exact EReal.coe_lt_coe_iff.1 hC
    have hδ : 0 < δ := by
      by_cases hCtop : C = ⊤
      · simp [δ, hCtop]
      · simp only [δ, if_neg hCtop]
        exact div_pos (by linarith [hAC hCtop]) (by linarith)
    refine ⟨fun i => (a i).toReal + δ, fun i hi => ?_, ?_⟩
    · conv_lhs => rw [← EReal.coe_toReal (ha i hi) (hbot i hi)]
      exact EReal.coe_lt_coe_iff.2 (by linarith)
    · have hsum : ∑ i ∈ s, ((w i : ℝ) : EReal) * (((a i).toReal + δ : ℝ) : EReal) =
          ((A + δ * W : ℝ) : EReal) := by
        have hreal : A + δ * W = ∑ i ∈ s, (w i : ℝ) * ((a i).toReal + δ) := by
          simp only [A, W, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hreal, ereal_coe_finsetSum]
        simp only [EReal.coe_mul]
      rw [hsum]
      by_cases hCtop : C = ⊤
      · rw [hCtop]
        exact EReal.coe_lt_top _
      · rw [← EReal.coe_toReal hCtop hCbot]
        apply EReal.coe_lt_coe_iff.2
        have h1 := hAC hCtop
        simp only [δ, if_neg hCtop]
        have h2 : (C.toReal - A) / (W + 1) * W < C.toReal - A := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
          nlinarith
        linarith

end Weighted

/-! ### Pieces of fibres over Gauss points -/

section Pieces

open Classical

variable {k : Type*} [Field k] {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra k F]
variable (hF : ∀ c : k, c ≠ 0 → ‖algebraMap k F c‖ = 1) {p : F[X]} (hp : p.eval 0 ≠ 0)
variable {R : Type*} [CommRing R] [Algebra k R] [Algebra (OpenLineRing p) R]
  [IsScalarTower k (OpenLineRing p) R]

variable (R) in
/-- The fibre of `(Spec R)^an → (Spec Q)^an` over `y`, as a finset (`R` finite over `Q`): the
index set of the weighted sums `EnvelopeProperty.flatNormFun`. -/
abbrev nonflatFibre {Q : Type*} [CommRing Q] [Algebra k Q] [Algebra Q R] [IsScalarTower k Q R]
    [Module.Finite Q R] (y : Berk k Q) : Finset (Berk k R) :=
  (finite_preimage_singleton (A := R) y).toFinset

/-- **Separating elements** at the rational points over `ξ`: for `x` over `ξ` there is `e ∈ R`
with `e(x) = 1` and `e(z) = 0` at the other points `z` over `ξ` (`lem:nf-pieces`, the Chinese
remainder step). -/
theorem exists_nonflat_separating [IsAlgClosed F] [Module.Finite (OpenLineRing p) R]
    {x : Berk k R} (hx : x ∈ nonflatFibre R (nonflatEvalPoint hF p hp)) :
    ∃ e : R, x.val (1 - e) = 0 ∧
      ∀ z ∈ nonflatFibre R (nonflatEvalPoint hF p hp), z ≠ x → z.val e = 0 := by
  set S₀ := nonflatFibre R (nonflatEvalPoint hF p hp)
  set ι : F → R := fun c => algebraMap (OpenLineRing p) R (algebraMap F (OpenLineRing p) c)
  have hnorm : ∀ z ∈ S₀, ∀ c : F, z.val (ι c) = ‖c‖₊ := fun z hz c => by
    rw [Berk.val_algebraMap_of_mem_fibre hz, nonflatEvalPoint_val_algebraMap]
  have hsep : ∀ z ∈ S₀, z ≠ x → ∃ a : R, z.val a = 0 ∧ x.val a ≠ 0 := by
    intro z hz hzx
    obtain ⟨b, hb⟩ : ∃ b, z.val b ≠ x.val b := by
      by_contra! h
      exact hzx (Berk.ext (Valuation.ext h))
    obtain ⟨c, hc⟩ := exists_val_sub_eq_zero_of_mem_fibre_nonflatEvalPoint hF hp hz b
    refine ⟨b - ι c, hc, fun hxc => hb ?_⟩
    have h1 : b = ι c + (b - ι c) := by ring
    rw [h1, Valuation.map_add_supp _ _ ((Valuation.mem_supp_iff _ _).2 hc),
      Valuation.map_add_supp _ _ ((Valuation.mem_supp_iff _ _).2 hxc), hnorm z hz, hnorm x hx]
  choose! a ha using hsep
  set e₀ := ∏ z ∈ S₀.erase x, a z
  have hxe₀ : x.val e₀ ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun z hz =>
      (ha z (Finset.mem_of_mem_erase hz) (Finset.ne_of_mem_erase hz)).2
  have hze₀ : ∀ z ∈ S₀, z ≠ x → z.val e₀ = 0 := by
    intro z hz hzx
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hzx, hz⟩) (ha z hz hzx).1
  obtain ⟨c₀, hc₀⟩ := exists_val_sub_eq_zero_of_mem_fibre_nonflatEvalPoint hF hp hx e₀
  have hc₀ne : c₀ ≠ 0 := by
    intro h
    apply hxe₀
    have : e₀ = ι c₀ + (e₀ - ι c₀) := by ring
    rw [this, Valuation.map_add_supp _ _ ((Valuation.mem_supp_iff _ _).2 hc₀), hnorm x hx, h,
      nnnorm_zero]
  have hι : ι c₀⁻¹ * ι c₀ = 1 := by
    simp only [ι, ← map_mul, inv_mul_cancel₀ hc₀ne, map_one]
  refine ⟨ι c₀⁻¹ * e₀, ?_, fun z hz hzx => by rw [map_mul, hze₀ z hz hzx, mul_zero]⟩
  have : 1 - ι c₀⁻¹ * e₀ = ι c₀⁻¹ * (ι c₀ - e₀) := by
    rw [mul_sub, hι]
  rw [this, map_mul, Valuation.map_sub_swap, hc₀, mul_zero]

/-- The fibres over `ζ_r` stay inside a neighbourhood of the fibre over `ξ` for `r` near `0`
(`lem:nf-fibre-shrink` for the Gauss ray). -/
theorem eventually_nonflatFibre_nonflatGaussPoint_subset [Module.Finite (OpenLineRing p) R]
    {V : Set (Berk k R)} (hV : IsOpen V)
    (hS : ∀ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp), x ∈ V) :
    ∀ᶠ r in 𝓝 (0 : ℝ≥0), ∀ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r), z ∈ V := by
  have h0 : Berk.comap (IsScalarTower.toAlgHom k (OpenLineRing p) R) ⁻¹'
      {nonflatGaussPoint hF p hp 0} ⊆ V := by
    intro z hz
    rw [nonflatGaussPoint_zero] at hz
    exact hS z ((Set.Finite.mem_toFinset _).2 hz)
  filter_upwards [Berk.eventually_preimage_subset_of_continuous
    (continuous_nonflatGaussPoint hF p hp) hV h0] with r hr z hz
  exact hr ((Set.Finite.mem_toFinset _).1 hz)

/-- **Pieces of fibres over Gauss points** (`lem:nf-pieces`). Let `F` be algebraically closed and
nontrivially valued, `p(0) ≠ 0`, and `R` finite free over `Q = F[t]_p`; let `ξ` be the point
`t = 0` and `ζ_r` the Gauss points. There are open neighbourhoods `U x` of the points `x` over
`ξ`, pairwise disjoint, such that for all `r` close to `0`, with `G_x(r)` the points over `ζ_r`
in `U x`:
1. the fibre over `ζ_r` is covered by the `U x` (so it is the disjoint union of the `G_x(r)`);
2. `∑_{z ∈ G_x(r)} m_z = m_x`;
3. `∏_{z ∈ G_x(r)} |b|_z^{m_z} ≥ |b|_x^{m_x}` for every `b ∈ R`;
4. for every neighbourhood `V` of `x`, `G_x(r) ⊆ V` for `r` close to `0`. -/
theorem exists_nonflatPieces [IsAlgClosed F] (hκ : ∃ κ : F, 1 < ‖κ‖)
    [Module.Free (OpenLineRing p) R] [Module.Finite (OpenLineRing p) R] :
    ∃ U : Berk k R → Set (Berk k R),
      (∀ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp), IsOpen (U x) ∧ x ∈ U x) ∧
      (∀ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp),
        ∀ x' ∈ nonflatFibre R (nonflatEvalPoint hF p hp), x ≠ x' → Disjoint (U x) (U x')) ∧
      (∀ᶠ r in 𝓝 (0 : ℝ≥0),
        (∀ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r),
          ∃ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp), z ∈ U x) ∧
        (∀ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp),
          ∑ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r) with z ∈ U x,
            flatFibreMult (OpenLineRing p) z = flatFibreMult (OpenLineRing p) x) ∧
        (∀ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp), ∀ b : R,
          x.val b ^ flatFibreMult (OpenLineRing p) x ≤
            ∏ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r) with z ∈ U x,
              z.val b ^ flatFibreMult (OpenLineRing p) z)) ∧
      (∀ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp), ∀ V ∈ 𝓝 x,
        ∀ᶠ r in 𝓝 (0 : ℝ≥0), ∀ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r),
          z ∈ U x → z ∈ V) := by
  set ξ := nonflatEvalPoint hF p hp
  set S₀ := nonflatFibre R ξ
  obtain ⟨κ₀, hκ₀⟩ := hκ
  have hsep := fun x (hx : x ∈ S₀) => exists_nonflat_separating hF hp hx
  choose! e he using hsep
  set U : Berk k R → Set (Berk k R) := fun x =>
    {w | w.val (1 - e x) < 1} ∩ {w | ∀ x' ∈ S₀.erase x, w.val (e x') < 1}
  have hUopen : ∀ x, IsOpen (U x) := by
    intro x
    refine (isOpen_lt (Berk.continuous_abs _) continuous_const).inter ?_
    have : {w : Berk k R | ∀ x' ∈ S₀.erase x, w.val (e x') < 1} =
        ⋂ x' ∈ S₀.erase x, {w | w.val (e x') < 1} := by
      ext
      simp
    rw [this]
    exact isOpen_biInter_finset fun x' _ => isOpen_lt (Berk.continuous_abs _) continuous_const
  have hxU : ∀ x ∈ S₀, x ∈ U x := by
    intro x hx
    refine ⟨by
      change x.val (1 - e x) < 1
      rw [(he x hx).1]
      exact zero_lt_one, fun x' hx' => ?_⟩
    obtain ⟨hne, hx'S⟩ := Finset.mem_erase.1 hx'
    rw [(he x' hx'S).2 x hx (Ne.symm hne)]
    exact zero_lt_one
  have hdisj : ∀ x ∈ S₀, ∀ x' ∈ S₀, x ≠ x' → Disjoint (U x) (U x') := by
    intro x hx x' hx' hne
    rw [Set.disjoint_left]
    rintro w ⟨hw1, -⟩ ⟨-, hw2⟩
    have h2 : w.val (e x) < 1 := hw2 x (Finset.mem_erase.2 ⟨hne, hx⟩)
    have h3 : w.val (1 - e x + e x) ≤ max (w.val (1 - e x)) (w.val (e x)) :=
      Valuation.map_add _ _ _
    rw [sub_add_cancel, map_one] at h3
    exact absurd h3 (not_le.2 (max_lt hw1 h2))
  have hU1 : ∀ x z, z ∈ U x → z.val (1 - e x) < 1 := fun x z hz => hz.1
  have hU2 : ∀ x x' z, z ∈ U x' → x ∈ S₀ → x ≠ x' → z.val (e x) < 1 :=
    fun x x' z hz hx hne => hz.2 x (Finset.mem_erase.2 ⟨hne, hx⟩)
  clear_value U
  have hcover : ∀ᶠ r in 𝓝 (0 : ℝ≥0), ∀ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r),
      ∃ x ∈ S₀, z ∈ U x := by
    have hV : IsOpen (⋃ x ∈ S₀, U x) := isOpen_biUnion fun x _ => hUopen x
    filter_upwards [eventually_nonflatFibre_nonflatGaussPoint_subset hF hp hV
      fun x hx => Set.mem_biUnion hx (hxU x hx)] with r hr z hz
    simpa using hr z hz
  obtain ⟨ε₀, hε₀, hmax⟩ := exists_nonflatGaussPoint_maxModulus hF p hp
  refine ⟨U, fun x hx => ⟨hUopen x, hxU x hx⟩, hdisj, ?_, ?_⟩
  · filter_upwards [hcover, Iic_mem_nhds hε₀] with r hcov hrε
    set S₁ := nonflatFibre R (nonflatGaussPoint hF p hp r)
    have hmax' : ∀ f : OpenLineRing p, ξ.val f ≤ (nonflatGaussPoint hF p hp r).val f :=
      hmax r hrε
    have hcomp : ∀ x ∈ S₀, ∀ z ∈ S₁, z ∉ S₁.filter (· ∈ U x) → z.val (e x) ≤ 1 := by
      intro x hx z hz hzG
      obtain ⟨x', hx', hzx'⟩ := hcov z hz
      have hne : x ≠ x' := by
        rintro rfl
        exact hzG (Finset.mem_filter.2 ⟨hz, hzx'⟩)
      exact (hU2 x x' z hzx' hx hne).le
    have hGe : ∀ x, ∀ z ∈ S₁.filter (· ∈ U x), z.val (1 - e x) < 1 := fun x z hz =>
      hU1 x z (Finset.mem_filter.1 hz).2
    have hd₀ : ∑ z ∈ S₀, flatFibreMult (OpenLineRing p) z =
        Module.finrank (OpenLineRing p) R :=
      sum_flatFibreMult_of_free ξ
    have hd₁ : ∑ z ∈ S₁, flatFibreMult (OpenLineRing p) z = Module.finrank (OpenLineRing p) R :=
      sum_flatFibreMult_of_free _
    have hpart : ∑ x ∈ S₀, ∑ z ∈ S₁ with z ∈ U x, flatFibreMult (OpenLineRing p) z =
        Module.finrank (OpenLineRing p) R := by
      rw [← nonflat_sum_eq_sum_pieces hdisj hcov, hd₁]
    -- the estimate `(∗)` in the two forms used below
    have hstar : ∀ x ∈ S₀, ∀ (κ : F), ‖κ‖₊ ≠ 0 → ∀ b : R, (∀ z ∈ S₀, z.val b ≤ ‖κ‖₊) →
        (∀ z ∈ S₁, z.val b ≤ ‖κ‖₊) →
        x.val b ^ flatFibreMult (OpenLineRing p) x *
            ‖κ‖₊ ^ ∑ z ∈ S₀.erase x, flatFibreMult (OpenLineRing p) z ≤
          (∏ z ∈ S₁ with z ∈ U x, z.val b ^ flatFibreMult (OpenLineRing p) z) *
            ‖κ‖₊ ^ ∑ z ∈ S₁ \ S₁.filter (· ∈ U x), flatFibreMult (OpenLineRing p) z := by
      intro x hx κ hκ b hb₀ hb₁
      have hκξ : ξ.val (algebraMap F (OpenLineRing p) κ) = ‖κ‖₊ :=
        nonflatEvalPoint_val_algebraMap hF p hp κ
      have h := nonflat_piece_norm_estimate hmax' hx (e := e x)
        (by rw [(he x hx).1]; exact zero_lt_one)
        (fun z hz hzx => by rw [(he x hx).2 z hz hzx]; exact zero_lt_one)
        (Finset.filter_subset _ _) (hGe x) (hcomp x hx)
        (κ := algebraMap F (OpenLineRing p) κ)
        (by rw [nonflatGaussPoint_val_algebraMap, hκξ]) (by rw [hκξ]; exact hκ)
        (b := b) (by rw [hκξ]; exact hb₀) (by rw [hκξ]; exact hb₁)
      rwa [hκξ] at h
    have hK1 : 1 < ‖κ₀‖₊ := by exact_mod_cast hκ₀
    -- multiplicities of the pieces
    have hle : ∀ x ∈ S₀, ∑ z ∈ S₁ with z ∈ U x, flatFibreMult (OpenLineRing p) z ≤
        flatFibreMult (OpenLineRing p) x := by
      intro x hx
      have h := hstar x hx κ₀ (by positivity) 1 (fun z _ => by rw [map_one]; exact hK1.le)
        (fun z _ => by rw [map_one]; exact hK1.le)
      simp only [map_one, one_pow, Finset.prod_const_one, one_mul] at h
      rw [pow_le_pow_iff_right₀ hK1] at h
      have h1 := Finset.add_sum_erase S₀ (fun z => flatFibreMult (OpenLineRing p) z) hx
      have h2 := Finset.sum_sdiff (f := fun z => flatFibreMult (OpenLineRing p) z)
        (Finset.filter_subset (· ∈ U x) S₁)
      omega
    have hmass : ∀ x ∈ S₀, ∑ z ∈ S₁ with z ∈ U x, flatFibreMult (OpenLineRing p) z =
        flatFibreMult (OpenLineRing p) x :=
      (Finset.sum_eq_sum_iff_of_le hle).1 (hpart.trans hd₀.symm)
    refine ⟨hcov, hmass, fun x hx b => ?_⟩
    by_cases hb0 : x.val b = 0
    · have hm : flatFibreMult (OpenLineRing p) x ≠ 0 := by
        have := one_le_flatFibreMult (B := OpenLineRing p) x
        omega
      rw [hb0, zero_pow hm]
      exact zero_le
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((S₀ ∪ S₁).sup fun z => z.val b) hK1
    have hbM : ∀ z ∈ S₀ ∪ S₁, z.val b ≤ ‖κ₀ ^ n‖₊ := fun z hz => by
      rw [nnnorm_pow]
      exact (Finset.le_sup (f := fun z => z.val b) hz).trans hn.le
    have hKpos : 0 < ‖κ₀ ^ n‖₊ := by
      rw [nnnorm_pow]
      exact pow_pos (zero_lt_one.trans hK1) n
    have h := hstar x hx (κ₀ ^ n) hKpos.ne' b (fun z hz => hbM z (Finset.mem_union_left _ hz))
      (fun z hz => hbM z (Finset.mem_union_right _ hz))
    have hAB : ∑ z ∈ S₁ \ S₁.filter (· ∈ U x), flatFibreMult (OpenLineRing p) z =
        ∑ z ∈ S₀.erase x, flatFibreMult (OpenLineRing p) z := by
      have h1 := Finset.add_sum_erase S₀ (fun z => flatFibreMult (OpenLineRing p) z) hx
      have h2 := Finset.sum_sdiff (f := fun z => flatFibreMult (OpenLineRing p) z)
        (Finset.filter_subset (· ∈ U x) S₁)
      have h3 := hmass x hx
      omega
    rw [hAB] at h
    exact le_of_mul_le_mul_right h (pow_pos hKpos _)
  · intro x hx V hV
    obtain ⟨V', hV'V, hV'open, hxV'⟩ := mem_nhds_iff.1 hV
    have hW : IsOpen ((V' ∩ U x) ∪ ⋃ x' ∈ S₀.erase x, U x') :=
      (hV'open.inter (hUopen x)).union (isOpen_biUnion fun x' _ => hUopen x')
    have hSW : ∀ y ∈ S₀, y ∈ (V' ∩ U x) ∪ ⋃ x' ∈ S₀.erase x, U x' := by
      intro y hy
      by_cases hyx : y = x
      · subst hyx
        exact Or.inl ⟨hxV', hxU y hy⟩
      · exact Or.inr (Set.mem_biUnion (Finset.mem_erase.2 ⟨hyx, hy⟩) (hxU y hy))
    filter_upwards [eventually_nonflatFibre_nonflatGaussPoint_subset hF hp hW hSW] with r hr z hz
      hzU
    rcases hr z hz with h | h
    · exact hV'V h.1
    · obtain ⟨x', hx', hzx'⟩ := Set.mem_iUnion₂.1 h
      obtain ⟨hne, hx'S⟩ := Finset.mem_erase.1 hx'
      exact absurd hzx' (Set.disjoint_left.1 (hdisj x hx x' hx'S (Ne.symm hne)) hzU)

end Pieces

/-! ### Functions of Fubini–Study type in a localization -/

section AwayFS

variable {k : Type*} [Field k] {R : Type*} [CommRing R] [Algebra k R]

/-- **Functions of Fubini–Study type in `R_g`** (`lem:nf-pieces-fs`): on `{|g| ≠ 0}`, `G` equals
`max {c₀, maxᵢ (aᵢ log|βᵢ| + cᵢ)}` for finitely many terms `(βᵢ, aᵢ, cᵢ)` with `βᵢ ∈ R_g`,
`aᵢ ∈ ℚ_{>0}`, `cᵢ ∈ ℝ`, and a constant `c₀ ∈ ℝ`; `|β|` at a point `z` with `|g|_z ≠ 0` is the
value at the lift of `z` to `(Spec R_g)^an` (`Berk.awayLift`). Values of `G` off `{|g| ≠ 0}` are
not constrained. -/
def IsNonflatAwayFS (g : R) (G : Berk k R → EReal) : Prop :=
  ∃ (T : Finset (Localization.Away g × ℚ × ℝ)) (c₀ : ℝ), (∀ t ∈ T, 0 < t.2.1) ∧
    ∀ (z : Berk k R) (hz : z.val g ≠ 0), G z = max (c₀ : EReal)
      (T.sup fun t => ((t.2.1 : ℝ) : EReal) * logAbs t.1 (awayLift g z hz) + (t.2.2 : EReal))

/-- Functions of FS type in `R_g` are finite from above on `{|g| ≠ 0}`. -/
theorem IsNonflatAwayFS.ne_top {g : R} {G : Berk k R → EReal} (hG : IsNonflatAwayFS g G)
    {z : Berk k R} (hz : z.val g ≠ 0) : G z ≠ ⊤ := by
  obtain ⟨T, c₀, hpos, hGeq⟩ := hG
  rw [hGeq z hz]
  refine (max_lt (EReal.coe_lt_top c₀) ((Finset.sup_lt_iff (bot_lt_top)).2 fun t ht => ?_)).ne
  exact EReal.add_lt_top (ereal_coe_mul_ne_top (by exact_mod_cast (hpos t ht).le)
    (logAbs_ne_top _ _)) (EReal.coe_ne_top _)

end AwayFS

/-! ### The weighted maximum principle -/

section MaxPrinciple

open Classical

variable {k : Type*} [Field k] {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra k F]
variable (hF : ∀ c : k, c ≠ 0 → ‖algebraMap k F c‖ = 1) {p : F[X]} (hp : p.eval 0 ≠ 0)
variable {R : Type*} [CommRing R] [Algebra k R] [Algebra (OpenLineRing p) R]
  [IsScalarTower k (OpenLineRing p) R]

/-- **Weighted maximum principle for Fubini–Study pullbacks** (`lem:nf-pieces-fs`(1)). Let `x` be
a point over `ξ` and `U` a set whose traces `G_x(r)` on the fibres over `ζ_r` satisfy, for `r`
close to `0`, the conclusions (2)–(4) of `EnvelopeProperty.exists_nonflatPieces`. Let `g ∈ R`
with `|g|_x ≠ 0`. Then for `r` close to `0`, `|g| ≠ 0` on `G_x(r)` and
`m_x G(x) ≤ ∑_{z ∈ G_x(r)} m_z G(z)` for every function `G` of FS type in `R_g`. -/
theorem eventually_nonflat_weighted_maxPrinciple [IsAlgClosed F]
    [Module.Finite (OpenLineRing p) R] {x : Berk k R}
    (hx : x ∈ nonflatFibre R (nonflatEvalPoint hF p hp)) {U : Set (Berk k R)}
    (hmass : ∀ᶠ r in 𝓝 (0 : ℝ≥0),
      ∑ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r) with z ∈ U,
        flatFibreMult (OpenLineRing p) z = flatFibreMult (OpenLineRing p) x)
    (hprod : ∀ᶠ r in 𝓝 (0 : ℝ≥0), ∀ b : R, x.val b ^ flatFibreMult (OpenLineRing p) x ≤
      ∏ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r) with z ∈ U,
        z.val b ^ flatFibreMult (OpenLineRing p) z)
    (hloc : ∀ V ∈ 𝓝 x, ∀ᶠ r in 𝓝 (0 : ℝ≥0),
      ∀ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r), z ∈ U → z ∈ V)
    {g : R} (hg : x.val g ≠ 0) :
    ∀ᶠ r in 𝓝 (0 : ℝ≥0),
      (∀ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r), z ∈ U → z.val g ≠ 0) ∧
      ∀ G : Berk k R → EReal, IsNonflatAwayFS g G →
        ((flatFibreMult (OpenLineRing p) x : ℝ) : EReal) * G x ≤
          ∑ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r) with z ∈ U,
            ((flatFibreMult (OpenLineRing p) z : ℝ) : EReal) * G z := by
  obtain ⟨c, hc⟩ := exists_val_sub_eq_zero_of_mem_fibre_nonflatEvalPoint hF hp hx g
  set ι : F → R := fun c => algebraMap (OpenLineRing p) R (algebraMap F (OpenLineRing p) c)
  have hxc : x.val g = ‖c‖₊ := by
    have : g = ι c + (g - ι c) := by ring
    rw [this, Valuation.map_add_supp _ _ ((Valuation.mem_supp_iff _ _).2 hc),
      Berk.val_algebraMap_of_mem_fibre hx, nonflatEvalPoint_val_algebraMap]
  have hc0 : 0 < ‖c‖₊ := by
    rw [← hxc]
    exact pos_iff_ne_zero.2 hg
  have hV : {z : Berk k R | z.val (g - ι c) < ‖c‖₊} ∈ 𝓝 x :=
    (isOpen_lt (Berk.continuous_abs _) continuous_const).mem_nhds (by
      change x.val (g - ι c) < ‖c‖₊
      rw [hc]
      exact hc0)
  filter_upwards [hmass, hprod, hloc _ hV] with r hmr hpr hlr
  have hgz : ∀ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r), z ∈ U → z.val g = ‖c‖₊ := by
    intro z hz1 hzU
    have hzV : z.val (g - ι c) < ‖c‖₊ := hlr z hz1 hzU
    have hzc : z.val (ι c) = ‖c‖₊ := by
      rw [Berk.val_algebraMap_of_mem_fibre hz1, nonflatGaussPoint_val_algebraMap]
    have : g = ι c + (g - ι c) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ (hzc.symm ▸ hzV), hzc]
  refine ⟨fun z hz hzU => by rw [hgz z hz hzU]; exact hc0.ne', ?_⟩
  intro G hG
  obtain ⟨T, c₀, hpos, hGeq⟩ := hG
  have hrep : ∀ β : Localization.Away g, ∃ (b : R) (n : ℕ), ∀ (z : Berk k R)
      (hz : z.val g ≠ 0), (awayLift g z hz).val β = z.val b / z.val g ^ n := by
    intro β
    obtain ⟨b, n, rfl⟩ := Berk.Away.exists_eq_mk' (Localization.Away g) g β
    exact ⟨b, n, fun z hz => Berk.awayLift_val_mk' g z hz b n⟩
  choose bf nf hbf using hrep
  set v : (Localization.Away g × ℚ × ℝ) → Berk k R → ℝ≥0 :=
    fun t z => z.val (bf t.1) / ‖c‖₊ ^ nf t.1
  have hGv : ∀ z, z.val g = ‖c‖₊ → G z = max (c₀ : EReal) (T.sup fun t =>
      ((t.2.1 : ℝ) : EReal) * ENNReal.log (v t z : ℝ≥0∞) + (t.2.2 : EReal)) := by
    intro z hz
    have hz0 : z.val g ≠ 0 := by
      rw [hz]
      exact hc0.ne'
    rw [hGeq z hz0]
    congr 1
    apply Finset.sup_congr rfl
    intro t _
    rw [logAbs_def, hbf t.1 z hz0, hz]
  rw [hGv x hxc, Finset.sum_congr rfl fun z hz => by
    rw [hGv z (hgz z (Finset.mem_filter.1 hz).1 (Finset.mem_filter.1 hz).2)]]
  refine nonflat_maxLogTerms_le_sum _ (fun z => flatFibreMult (OpenLineRing p) z)
    (fun z _ => one_le_flatFibreMult z) (one_le_flatFibreMult x) hmr T c₀
    (fun t => (t.2.1 : ℝ)) (fun t => t.2.2) (fun t ht => by exact_mod_cast hpos t ht) v
    (fun t => v t x) fun t _ => ?_
  simp only [v]
  rw [div_pow, Finset.prod_congr rfl (fun z _ => div_pow _ _ _), Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum, hmr]
  exact div_le_div_of_nonneg_right (hpr (bf t.1)) zero_le

/-- **Weighted maximum principle for decreasing limits** (`lem:nf-pieces-fs`(2)). In the setting
of `EnvelopeProperty.eventually_nonflat_weighted_maxPrinciple`, if `W` is, on `{|g| ≠ 0}`, the
pointwise limit of a decreasing sequence `G_j` of functions of FS type in `R_g`, then
`m_x W(x) ≤ ∑_{z ∈ G_x(r)} m_z W(z)` for `r` close to `0`. -/
theorem eventually_nonflat_weighted_maxPrinciple_iInf [IsAlgClosed F]
    [Module.Finite (OpenLineRing p) R] {x : Berk k R}
    (hx : x ∈ nonflatFibre R (nonflatEvalPoint hF p hp)) {U : Set (Berk k R)}
    (hmass : ∀ᶠ r in 𝓝 (0 : ℝ≥0),
      ∑ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r) with z ∈ U,
        flatFibreMult (OpenLineRing p) z = flatFibreMult (OpenLineRing p) x)
    (hprod : ∀ᶠ r in 𝓝 (0 : ℝ≥0), ∀ b : R, x.val b ^ flatFibreMult (OpenLineRing p) x ≤
      ∏ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r) with z ∈ U,
        z.val b ^ flatFibreMult (OpenLineRing p) z)
    (hloc : ∀ V ∈ 𝓝 x, ∀ᶠ r in 𝓝 (0 : ℝ≥0),
      ∀ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r), z ∈ U → z ∈ V)
    {g : R} (hg : x.val g ≠ 0) {W : Berk k R → EReal} {G : ℕ → Berk k R → EReal}
    (hG : ∀ j, IsNonflatAwayFS g (G j)) (hanti : ∀ z, z.val g ≠ 0 → Antitone fun j => G j z)
    (hW : ∀ z, z.val g ≠ 0 → W z = ⨅ j, G j z) :
    ∀ᶠ r in 𝓝 (0 : ℝ≥0), ((flatFibreMult (OpenLineRing p) x : ℝ) : EReal) * W x ≤
      ∑ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r) with z ∈ U,
        ((flatFibreMult (OpenLineRing p) z : ℝ) : EReal) * W z := by
  filter_upwards [eventually_nonflat_weighted_maxPrinciple hF hp hx hmass hprod hloc hg]
    with r hr
  obtain ⟨hg', hmp⟩ := hr
  have hgP : ∀ z ∈ (nonflatFibre R (nonflatGaussPoint hF p hp r)).filter (· ∈ U),
      z.val g ≠ 0 :=
    fun z hz => hg' z (Finset.mem_filter.1 hz).1 (Finset.mem_filter.1 hz).2
  have hsum : ∑ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r) with z ∈ U,
      ((flatFibreMult (OpenLineRing p) z : ℝ) : EReal) * W z =
        ⨅ j, ∑ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r) with z ∈ U,
          ((flatFibreMult (OpenLineRing p) z : ℝ) : EReal) * G j z := by
    rw [iInf_finsetSum_coe_mul_of_antitone _ (fun z => (flatFibreMult (OpenLineRing p) z : ℝ))
      (fun z _ => by exact_mod_cast one_le_flatFibreMult z) (fun z j => G j z)
      (fun z hz => hanti z (hgP z hz)) (fun z hz => (hG 0).ne_top (hgP z hz))]
    exact Finset.sum_congr rfl fun z hz => by rw [hW z (hgP z hz)]
  rw [hsum]
  refine le_iInf fun j => le_trans ?_ (hmp (G j) (hG j))
  apply mul_le_mul_of_nonneg_left _ (EReal.coe_nonneg.2 (Nat.cast_nonneg _))
  rw [hW x hg]
  exact iInf_le _ j

end MaxPrinciple

/-! ### Norms over Gauss points: the two bounds used in the identification -/

section NormBounds

open Classical

variable {k : Type*} [Field k] {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra k F]
variable (hF : ∀ c : k, c ≠ 0 → ‖algebraMap k F c‖ = 1) {p : F[X]} (hp : p.eval 0 ≠ 0)
variable {R : Type*} [CommRing R] [Algebra k R] [Algebra (OpenLineRing p) R]
  [IsScalarTower k (OpenLineRing p) R]

/-- **Lower bound for the norm over Gauss points** (`prop:nf-identification`, lower bound). Let
`F` be algebraically closed and nontrivially valued, `R` finite free over `F[t]_p`, and `u` a
function on `(Spec R)^an` such that near every point `x` over `ξ` it is a decreasing limit of
functions of FS type in some `R_g`, `|g|_x ≠ 0` (on `{|g| ≠ 0}`). Then
`N_q u(ξ) ≤ N_q u(ζ_r)` for all `r` close to `0`. -/
theorem eventually_flatNormFun_nonflatEvalPoint_le [IsAlgClosed F] (hκ : ∃ κ : F, 1 < ‖κ‖)
    [Module.Free (OpenLineRing p) R] [Module.Finite (OpenLineRing p) R] {u : Berk k R → EReal}
    (hu : ∀ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp), ∃ g : R, x.val g ≠ 0 ∧
      ∃ G : ℕ → Berk k R → EReal, (∀ j, IsNonflatAwayFS g (G j)) ∧
        (∀ z, z.val g ≠ 0 → Antitone fun j => G j z) ∧ ∀ z, z.val g ≠ 0 → u z = ⨅ j, G j z) :
    ∀ᶠ r in 𝓝 (0 : ℝ≥0), flatNormFun (B := OpenLineRing p) u (nonflatEvalPoint hF p hp) ≤
      flatNormFun (B := OpenLineRing p) u (nonflatGaussPoint hF p hp r) := by
  obtain ⟨U, -, hdisj, hev, hloc⟩ := exists_nonflatPieces hF hp hκ (R := R)
  choose! g hg G hG hanti hW using hu
  have hx : ∀ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp), ∀ᶠ r in 𝓝 (0 : ℝ≥0),
      ((flatFibreMult (OpenLineRing p) x : ℝ) : EReal) * u x ≤
        ∑ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r) with z ∈ U x,
          ((flatFibreMult (OpenLineRing p) z : ℝ) : EReal) * u z := fun x hx =>
    eventually_nonflat_weighted_maxPrinciple_iInf hF hp hx (hev.mono fun _ h => h.2.1 x hx)
      (hev.mono fun _ h => h.2.2 x hx) (hloc x hx) (hg x hx) (hG x hx) (hanti x hx) (hW x hx)
  filter_upwards [hev, (Filter.eventually_all_finset _).2 hx] with r hr hxr
  unfold flatNormFun
  rw [nonflat_sum_eq_sum_pieces hdisj hr.1]
  exact Finset.sum_le_sum hxr

/-- **Upper bound for the norm over Gauss points** (`prop:nf-identification`, upper bound). If
`u` is upper semicontinuous and `< ∞` at the points over `ξ`, then for every `C > N_q u(ξ)`,
`N_q u(ζ_r) < C` for all `r` close to `0`; that is, `limsup_{r → 0} N_q u(ζ_r) ≤ N_q u(ξ)`. -/
theorem eventually_flatNormFun_nonflatGaussPoint_lt [IsAlgClosed F] (hκ : ∃ κ : F, 1 < ‖κ‖)
    [Module.Free (OpenLineRing p) R] [Module.Finite (OpenLineRing p) R] {u : Berk k R → EReal}
    (husc : ∀ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp), UpperSemicontinuousAt u x)
    (htop : ∀ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp), u x ≠ ⊤) {C : EReal}
    (hC : flatNormFun (B := OpenLineRing p) u (nonflatEvalPoint hF p hp) < C) :
    ∀ᶠ r in 𝓝 (0 : ℝ≥0), flatNormFun (B := OpenLineRing p) u (nonflatGaussPoint hF p hp r) < C := by
  obtain ⟨U, -, hdisj, hev, hloc⟩ := exists_nonflatPieces hF hp hκ (R := R)
  obtain ⟨c, hc, hcC⟩ := nonflat_exists_real_gt_of_sum_lt _
    (fun z => flatFibreMult (OpenLineRing p) z) (fun z _ => one_le_flatFibreMult z) u htop hC
  have hx : ∀ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp), ∀ᶠ r in 𝓝 (0 : ℝ≥0),
      ∀ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r), z ∈ U x → u z < c x := fun x hx =>
    hloc x hx _ (husc x hx (c x) (hc x hx))
  filter_upwards [hev, (Filter.eventually_all_finset _).2 hx] with r hr hxr
  unfold flatNormFun
  rw [nonflat_sum_eq_sum_pieces hdisj hr.1]
  refine lt_of_le_of_lt (Finset.sum_le_sum fun x hx => ?_) hcC
  calc ∑ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r) with z ∈ U x,
        ((flatFibreMult (OpenLineRing p) z : ℝ) : EReal) * u z
      ≤ ∑ z ∈ nonflatFibre R (nonflatGaussPoint hF p hp r) with z ∈ U x,
        ((flatFibreMult (OpenLineRing p) z : ℝ) : EReal) * (c x : EReal) :=
        Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left
          (hxr x hx z (Finset.mem_filter.1 hz).1 (Finset.mem_filter.1 hz).2).le
          (EReal.coe_nonneg.2 (Nat.cast_nonneg _))
    _ = ((flatFibreMult (OpenLineRing p) x : ℝ) : EReal) * (c x : EReal) := by
        rw [← hr.2.1 x hx, Nat.cast_sum, ← EReal.coe_mul, Finset.sum_mul, ereal_coe_finsetSum]
        simp only [EReal.coe_mul]

end NormBounds

end EnvelopeProperty
