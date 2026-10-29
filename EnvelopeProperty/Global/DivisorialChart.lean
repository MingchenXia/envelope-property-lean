/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.Divisorial

/-!
# The points `v_V` of the charts are divisorial

Let `𝒳 = (K, S, z)` be an integral multiprojective model (`EnvelopeProperty.MultiModel`,
`def:gl-model`), `j` a chart with all `f^{(c)}_{j_c} ≠ 0`, `A_j` its chart algebra
(`lem:gl-charts`) and `B_j = A_j[t]` (`MultiModel.ChartRing`). This file proves the divisorial part
of the blueprint node `lem:gl-rees-points` of the global chapter `global.tex` (subsection
`subsec:gl-comparison`) of the formalization of Fang–Han–Xia, *The envelope property for unibranch
projective varieties* (FHX), following Boucksom–Jonsson, *Global
pluripotential theory over a trivially valued field* (BJ22, Lemma 2.13, §1.3): for a
discrete valuation ring `V` birational to `B_j`, monomial in `t` with `ord_V(t) = b > 0`, the point
`v_V = MultiModel.chartDivPoint X j hj V b` is divisorial (`def:gl-div`), with `c = 1/b` and `R'`
the Gauss extension of `V` in the `r` variables `z^{(c)}_{j_c}`.

## The chart expansion

* `MultiModel.chartRescale X j : K[T] → K[T]`, `T_c ↦ T_c / f^{(c)}_{j_c}`, so that
  `p T^a ↦ (p / z̃_j^a) T^a` (`MultiModel.chartRescale_monomial`);
* `MultiModel.chartExpandS X j : S → A_j[Y_1, …, Y_r]`, `p T^a ↦ (p / z̃_j^a) Y^a`, the
  corestriction of `chartRescale` (`MultiModel.coeff_chartExpandS`);
* `MultiModel.chartExpand X j : S[t] → B_j[Y_1, …, Y_r]`, `p T^a t^λ ↦ (p / z̃_j^a) t^λ Y^a`
  (`MultiModel.coeff_coeff_chartExpand`), injective (`MultiModel.chartExpand_injective`); here
  `Y_c` is the image of `z^{(c)}_{j_c}` (`MultiModel.chartExpandW_C_coordElem`);
* `MultiModel.chartExpandW X j ψ : S[t] → W[Y_1, …, Y_r]`, its composite with a map
  `ψ : B_j → W` (for `W = V`, `ψ = (B_j ⊆ V)`).

If every element of `W` is a quotient of elements of `ψ(B_j)` (e.g. `B_j ⊆ W ⊆ Frac B_j`), the
image of `chartExpandW` generates the fraction field of `W[Y]`
(`MultiModel.mem_closure_chartExpandW`: `A_j` consists of the quotients `(p T^a) / z_j^a`, and `t`
and `Y_c = z^{(c)}_{j_c}` are in the image).

## Gauss extensions inside a fraction field

`BirationalDVR.ofMvGauss θ hθ hcl`: for a domain `R`, a discrete valuation ring `W` essentially of
finite type over `k`, and an injective `θ : R → W[Y]` whose image generates `Frac(W[Y])`, the
Gauss extension `W[Y]_{m_W W[Y]}` (`EnvelopeProperty.mvGaussIdeal`) realized inside `Frac R`
through the isomorphism `Frac R ≅ Frac(W[Y])` induced by `θ` (`BirationalDVR.mvGaussFracEquiv`),
as a `BirationalDVR k R`, with `ord(g) = min_a ord_W(θ(g)_a)` (`BirationalDVR.ord_ofMvGauss`,
Gauss's lemma).

## The discrete valuation ring `R'`

`MultiModel.chartGaussDVR X hj V = BirationalDVR.ofMvGauss (chartExpandW (B_j ⊆ V))`: the Gauss
extension of `V` in the variables `z^{(c)}_{j_c}`, inside `Frac(S[t])`. Its valuation on `S[t]` is
`ord_{R'}(g) = min_{a, λ} (ord_V(g_{a,λ} / z̃_j^a) + λ b)` for `g = ∑ g_{a,λ} T^a t^λ`
(`MultiModel.chartGaussDVR_ord_eq_iInf`, using the monomiality of `V` in `t`), and
`ord_{R'}(g) = ord_V(g^{(j)})` for `g` homogeneous in `T` with dehomogenization `g^{(j)} ∈ B_j`
(`MultiModel.chartGaussDVR_ord_of_eq_monomial`).

## Main results

* `MultiModel.gaussPt_chartDivPoint_val`: `|g|_{σ(v_V)} = e^{-ord_{R'}(g)/b}`;
* **`lem:gl-rees-points`**: `MultiModel.isDivisorial_chartDivPoint`.
-/

open scoped NNReal ENNReal Topology Polynomial

open IsDiscreteValuationRing

noncomputable section

namespace EnvelopeProperty

universe u

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r} {j : X.ChartIndex}

/-! ### The rescaling `T_c ↦ T_c / f^{(c)}_{j_c}` -/

variable (X j) in
/-- The rescaling `ρ_j : K[T] → K[T]`, `T_c ↦ T_c / f^{(c)}_{j_c}`. -/
def chartRescale : MvPolynomial (Fin r) K →ₐ[k] MvPolynomial (Fin r) K :=
  (MvPolynomial.aeval fun c =>
    MvPolynomial.C (X.coord c (j c))⁻¹ * MvPolynomial.X c).restrictScalars k

theorem chartRescale_monomial (a : Fin r →₀ ℕ) (f : K) :
    X.chartRescale j (MvPolynomial.monomial a f) =
      MvPolynomial.monomial a (f / X.chartDen j a) := by
  rw [chartRescale, AlgHom.restrictScalars_apply, MvPolynomial.aeval_monomial,
    MvPolynomial.algebraMap_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  rw [← mul_assoc, ← map_mul, chartDen, div_eq_mul_inv, ← Finset.prod_inv_distrib]
  simp only [inv_pow]

theorem coeff_chartRescale (p : MvPolynomial (Fin r) K) (a : Fin r →₀ ℕ) :
    (X.chartRescale j p).coeff a = p.coeff a / X.chartDen j a := by
  conv_lhs => rw [p.as_sum, map_sum]
  simp only [chartRescale_monomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, zero_div]

/-! ### The expansion `S → A_j[Y]` -/

theorem chartRescale_mem_range (p : X.S) :
    X.chartRescale j p.1 ∈ (MvPolynomial.mapAlgHom (X.chartAlg j).val).range := by
  have : X.chartRescale j p.1 ∈
      Set.range (MvPolynomial.map ((X.chartAlg j).val : X.chartAlg j →+* K)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro x hx
    obtain ⟨a, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hx
    rw [coeff_chartRescale]
    exact ⟨⟨_, div_chartDen_mem_chartAlg (X.coeff_mem_piece p.2 a)⟩, rfl⟩
  obtain ⟨q, hq⟩ := this
  exact ⟨q, hq⟩

theorem mapAlgHom_chartAlg_val_injective :
    Function.Injective (MvPolynomial.mapAlgHom (σ := Fin r) (X.chartAlg j).val) :=
  fun _ _ h => MvPolynomial.map_injective _ Subtype.val_injective h

variable (X j) in
/-- The expansion `S → A_j[Y_1, …, Y_r]`, `p T^a ↦ (p / z̃_j^a) Y^a` (the corestriction of the
rescaling `chartRescale` to `S`). -/
def chartExpandS : X.S →ₐ[k] MvPolynomial (Fin r) (X.chartAlg j) :=
  (AlgEquiv.ofInjective _ mapAlgHom_chartAlg_val_injective).symm.toAlgHom.comp
    (((X.chartRescale j).comp X.S.val).codRestrict _ fun p => chartRescale_mem_range p)

theorem map_chartExpandS (p : X.S) :
    MvPolynomial.map ((X.chartAlg j).val : X.chartAlg j →+* K) (X.chartExpandS j p) =
      X.chartRescale j p.1 := by
  set e := AlgEquiv.ofInjective _ (mapAlgHom_chartAlg_val_injective (X := X) (j := j))
  have h := AlgEquiv.ofInjective_apply _ (mapAlgHom_chartAlg_val_injective (X := X) (j := j))
    (e.symm ⟨X.chartRescale j p.1, chartRescale_mem_range p⟩)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

/-- `(chartExpandS p)_a = p_a / z̃_j^a`. -/
theorem coeff_chartExpandS (p : X.S) (a : Fin r →₀ ℕ) :
    (((X.chartExpandS j p).coeff a : X.chartAlg j) : K) = p.1.coeff a / X.chartDen j a := by
  have := congrArg (MvPolynomial.coeff a) (map_chartExpandS (j := j) p)
  rwa [MvPolynomial.coeff_map, coeff_chartRescale] at this

theorem chartExpandS_ofPiece {a : Fin r →₀ ℕ} {f : K} (hf : f ∈ X.piece a) :
    X.chartExpandS j (X.ofPiece hf) =
      MvPolynomial.monomial a ⟨f / X.chartDen j a, div_chartDen_mem_chartAlg hf⟩ := by
  apply MvPolynomial.map_injective ((X.chartAlg j).val : X.chartAlg j →+* K)
    Subtype.val_injective
  rw [map_chartExpandS, MvPolynomial.map_monomial, coe_ofPiece, chartRescale_monomial]
  rfl

/-! ### The expansion `S[t] → B_j[Y]` -/

theorem mvPolynomial_coeff_mul_C {R σ : Type*} [CommSemiring R] (P : MvPolynomial σ R) (c : R)
    (a : σ →₀ ℕ) : (P * MvPolynomial.C c).coeff a = P.coeff a * c := by
  rw [mul_comm, MvPolynomial.coeff_C_mul, mul_comm]

variable (X j) in
/-- The **chart expansion** `S[t] → B_j[Y_1, …, Y_r]`, `p T^a t^λ ↦ (p / z̃_j^a) t^λ Y^a`. -/
def chartExpand : Polynomial X.S →ₐ[k] MvPolynomial (Fin r) (X.ChartRing j) :=
  Polynomial.aevalTower
    ((MvPolynomial.mapAlgHom (Polynomial.CAlgHom : X.chartAlg j →ₐ[k] X.ChartRing j)).comp
      (X.chartExpandS j))
    (MvPolynomial.C Polynomial.X)

theorem chartExpand_C (p : X.S) :
    X.chartExpand j (Polynomial.C p) = MvPolynomial.map Polynomial.C (X.chartExpandS j p) := by
  rw [chartExpand, Polynomial.aevalTower_C]
  rfl

theorem chartExpand_X :
    X.chartExpand j Polynomial.X = MvPolynomial.C (Polynomial.X : X.ChartRing j) := by
  rw [chartExpand, Polynomial.aevalTower_X]

/-- `((chartExpand g)_a)_λ = (chartExpandS g_λ)_a`, i.e. `g_{a,λ} / z̃_j^a`. -/
theorem coeff_coeff_chartExpand (g : Polynomial X.S) (a : Fin r →₀ ℕ) (ℓ : ℕ) :
    ((X.chartExpand j g).coeff a).coeff ℓ = (X.chartExpandS j (g.coeff ℓ)).coeff a := by
  conv_lhs => rw [g.as_sum_support_C_mul_X_pow]
  rw [map_sum, MvPolynomial.coeff_sum, Polynomial.finsetSum_coeff]
  simp only [map_mul, map_pow, chartExpand_C, chartExpand_X]
  simp only [← MvPolynomial.C_pow]
  simp only [mvPolynomial_coeff_mul_C, MvPolynomial.coeff_map, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Polynomial.notMem_support_iff.1 h, map_zero, MvPolynomial.coeff_zero]

variable (hj : ∀ c, X.coord c (j c) ≠ 0)

include hj in
/-- The chart expansion is injective. -/
theorem chartExpand_injective : Function.Injective (X.chartExpand j) := by
  intro g g' h
  ext ℓ a
  have h1 := congrArg (fun P => (P.coeff a).coeff ℓ) h
  simp only [coeff_coeff_chartExpand] at h1
  have h2 := congrArg Subtype.val h1
  rw [coeff_chartExpandS, coeff_chartExpandS] at h2
  exact (div_left_inj' (chartDen_ne_zero hj a)).1 h2

/-! ### The expansion `S[t] → W[Y]` for a ring `W ⊇ B_j` -/

section Expand

variable {W : Type*} [CommRing W] [Algebra k W] (ψ : X.ChartRing j →ₐ[k] W)

variable (X j) in
/-- The composite `S[t] → B_j[Y] → W[Y]` of the chart expansion with a map `ψ : B_j → W`. -/
def chartExpandW (ψ : X.ChartRing j →ₐ[k] W) : Polynomial X.S →ₐ[k] MvPolynomial (Fin r) W :=
  (MvPolynomial.mapAlgHom ψ).comp (X.chartExpand j)

theorem coeff_chartExpandW (g : Polynomial X.S) (a : Fin r →₀ ℕ) :
    (X.chartExpandW j ψ g).coeff a = ψ ((X.chartExpand j g).coeff a) := by
  rw [chartExpandW, AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply, MvPolynomial.coeff_map]
  rfl

include hj in
theorem chartExpandW_injective (hψ : Function.Injective ψ) :
    Function.Injective (X.chartExpandW j ψ) :=
  (MvPolynomial.map_injective (ψ : X.ChartRing j →+* W) hψ).comp (chartExpand_injective hj)

theorem chartExpandW_C_ofPiece {a : Fin r →₀ ℕ} {f : K} (hf : f ∈ X.piece a) :
    X.chartExpandW j ψ (Polynomial.C (X.ofPiece hf)) =
      MvPolynomial.monomial a
        (ψ (Polynomial.C ⟨f / X.chartDen j a, div_chartDen_mem_chartAlg hf⟩)) := by
  rw [chartExpandW, AlgHom.comp_apply, chartExpand_C, chartExpandS_ofPiece,
    MvPolynomial.map_monomial, MvPolynomial.mapAlgHom_apply, MvPolynomial.map_monomial]
  rfl

include hj in
theorem chartExpandW_C_chartMono (a : Fin r →₀ ℕ) :
    X.chartExpandW j ψ (Polynomial.C (X.chartMono j a)) = MvPolynomial.monomial a 1 := by
  rw [chartMono, chartExpandW_C_ofPiece]
  have : (⟨X.chartDen j a / X.chartDen j a, div_chartDen_mem_chartAlg
      (X.chartDen_mem_piece j a)⟩ : X.chartAlg j) = 1 :=
    Subtype.ext (div_self (chartDen_ne_zero hj a))
  rw [this, map_one, map_one]

include hj in
/-- The image of `z^{(c)}_{j_c}` is the variable `Y_c`. -/
theorem chartExpandW_C_coordElem (c : Fin r) :
    X.chartExpandW j ψ (Polynomial.C (X.coordElem ⟨c, j c⟩)) = MvPolynomial.X c := by
  rw [← X.chartMono_single, chartExpandW_C_chartMono hj]
  rfl

theorem chartExpandW_X :
    X.chartExpandW j ψ Polynomial.X = MvPolynomial.C (ψ Polynomial.X) := by
  rw [chartExpandW, AlgHom.comp_apply, chartExpand_X, MvPolynomial.mapAlgHom_apply,
    MvPolynomial.map_C]
  rfl

variable [IsDomain W]

include hj in
/-- **The image of `S[t]` generates `Frac(W[Y])`** if every element of `W` is a quotient of
elements of `ψ(B_j)` (e.g. `W ⊆ Frac B_j`). -/
theorem mem_closure_chartExpandW
    (hψ : ∀ w : W, ∃ β γ : X.ChartRing j, ψ γ ≠ 0 ∧ w * ψ γ = ψ β)
    (z : FractionRing (MvPolynomial (Fin r) W)) :
    z ∈ Subfield.closure (Set.range fun g => algebraMap (MvPolynomial (Fin r) W)
      (FractionRing (MvPolynomial (Fin r) W)) (X.chartExpandW j ψ g)) := by
  have hι : Function.Injective (algebraMap (MvPolynomial (Fin r) W)
      (FractionRing (MvPolynomial (Fin r) W))) :=
    IsFractionRing.injective (MvPolynomial (Fin r) W) (FractionRing (MvPolynomial (Fin r) W))
  have hmem : ∀ g, algebraMap (MvPolynomial (Fin r) W) (FractionRing (MvPolynomial (Fin r) W))
      (X.chartExpandW j ψ g) ∈ Subfield.closure (Set.range fun g => algebraMap
        (MvPolynomial (Fin r) W) (FractionRing (MvPolynomial (Fin r) W)) (X.chartExpandW j ψ g)) :=
    fun g => Subfield.subset_closure ⟨g, rfl⟩
  generalize hF : Subfield.closure (Set.range fun g => algebraMap (MvPolynomial (Fin r) W)
    (FractionRing (MvPolynomial (Fin r) W)) (X.chartExpandW j ψ g)) = F at hmem ⊢
  -- the constants `ψ β`, `β ∈ B_j`
  have hB : ∀ β : X.ChartRing j, algebraMap (MvPolynomial (Fin r) W)
      (FractionRing (MvPolynomial (Fin r) W)) (MvPolynomial.C (ψ β)) ∈ F := by
    intro β
    induction β using Polynomial.induction_on with
    | C a =>
      obtain ⟨d, f, hf, ha⟩ := (mem_chartAlg_iff hj).1 a.2
      have ha' : a = ⟨f / X.chartDen j d, div_chartDen_mem_chartAlg hf⟩ := Subtype.ext ha
      have h0 : algebraMap (MvPolynomial (Fin r) W) (FractionRing (MvPolynomial (Fin r) W))
          (MvPolynomial.monomial d 1) ≠ 0 :=
        (map_ne_zero_iff _ hι).2 (by simp)
      have e : algebraMap (MvPolynomial (Fin r) W) (FractionRing (MvPolynomial (Fin r) W))
            (MvPolynomial.C (ψ (Polynomial.C a))) =
          algebraMap (MvPolynomial (Fin r) W) (FractionRing (MvPolynomial (Fin r) W))
              (X.chartExpandW j ψ (Polynomial.C (X.ofPiece hf))) /
            algebraMap (MvPolynomial (Fin r) W) (FractionRing (MvPolynomial (Fin r) W))
              (X.chartExpandW j ψ (Polynomial.C (X.chartMono j d))) := by
        rw [chartExpandW_C_ofPiece, chartExpandW_C_chartMono hj, eq_div_iff h0, ← map_mul,
          MvPolynomial.C_mul_monomial, mul_one, ha']
      rw [e]
      exact div_mem (hmem _) (hmem _)
    | add p q hp hq =>
      rw [map_add, map_add, map_add]
      exact add_mem hp hq
    | monomial n a ih =>
      have e : algebraMap (MvPolynomial (Fin r) W) (FractionRing (MvPolynomial (Fin r) W))
            (MvPolynomial.C (ψ (Polynomial.C a * Polynomial.X ^ (n + 1)))) =
          algebraMap (MvPolynomial (Fin r) W) (FractionRing (MvPolynomial (Fin r) W))
              (MvPolynomial.C (ψ (Polynomial.C a * Polynomial.X ^ n))) *
            algebraMap (MvPolynomial (Fin r) W) (FractionRing (MvPolynomial (Fin r) W))
              (X.chartExpandW j ψ Polynomial.X) := by
        rw [chartExpandW_X, ← map_mul, ← map_mul, ← map_mul, pow_succ, mul_assoc]
      rw [e]
      exact mul_mem ih (hmem _)
  have hP : ∀ p : MvPolynomial (Fin r) W,
      algebraMap (MvPolynomial (Fin r) W) (FractionRing (MvPolynomial (Fin r) W)) p ∈ F := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C w =>
      obtain ⟨β, γ, hγ, hw⟩ := hψ w
      have e : algebraMap (MvPolynomial (Fin r) W) (FractionRing (MvPolynomial (Fin r) W))
            (MvPolynomial.C w) =
          algebraMap (MvPolynomial (Fin r) W) (FractionRing (MvPolynomial (Fin r) W))
              (MvPolynomial.C (ψ β)) /
            algebraMap (MvPolynomial (Fin r) W) (FractionRing (MvPolynomial (Fin r) W))
              (MvPolynomial.C (ψ γ)) := by
        rw [eq_div_iff ((map_ne_zero_iff _ hι).2 (MvPolynomial.C_ne_zero.2 hγ)), ← map_mul,
          ← map_mul, hw]
      rw [e]
      exact div_mem (hB β) (hB γ)
    | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
    | mul_X p c ih =>
      rw [map_mul, ← chartExpandW_C_coordElem hj ψ c]
      exact mul_mem ih (hmem _)
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin r) W) z
  exact div_mem (hP p) (hP q)

end Expand

end MultiModel

/-! ### Gauss extensions inside the fraction field of a domain -/

namespace BirationalDVR

section OfMvGauss

variable {k : Type*} [Field k] {R : Type*} [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type*} {W : Type*} [CommRing W] [IsDomain W] [Algebra k W]
  (θ : R →ₐ[k] MvPolynomial σ W) (hθ : Function.Injective θ)
  (hcl : ∀ z : FractionRing (MvPolynomial σ W), z ∈ Subfield.closure
    (Set.range fun g => algebraMap (MvPolynomial σ W) (FractionRing (MvPolynomial σ W)) (θ g)))

omit [IsDomain R] [IsDomain W] in
include hθ in
theorem algebraMap_comp_injective_of_mvGauss :
    Function.Injective ((IsScalarTower.toAlgHom k (MvPolynomial σ W)
      (FractionRing (MvPolynomial σ W))).comp θ) :=
  fun _ _ h => hθ (IsFractionRing.injective (MvPolynomial σ W)
    (FractionRing (MvPolynomial σ W)) h)

/-- The field embedding `Frac R → Frac(W[Y])` induced by an injective `θ : R → W[Y]`. -/
def mvGaussFracHom : FractionRing R →ₐ[k] FractionRing (MvPolynomial σ W) :=
  IsFractionRing.liftAlgHom (algebraMap_comp_injective_of_mvGauss θ hθ)

theorem mvGaussFracHom_algebraMap (g : R) :
    mvGaussFracHom θ hθ (algebraMap R _ g) = algebraMap _ _ (θ g) := by
  rw [mvGaussFracHom, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

include hcl in
theorem mvGaussFracHom_bijective : Function.Bijective (mvGaussFracHom θ hθ) := by
  refine ⟨(mvGaussFracHom θ hθ).toRingHom.injective, fun z => ?_⟩
  have hle : Subfield.closure (Set.range fun g => algebraMap (MvPolynomial σ W)
      (FractionRing (MvPolynomial σ W)) (θ g)) ≤ (mvGaussFracHom θ hθ).toRingHom.fieldRange := by
    rw [Subfield.closure_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨algebraMap _ _ g, mvGaussFracHom_algebraMap θ hθ g⟩
  exact hle (hcl z)

/-- The isomorphism `Frac R ≅ Frac(W[Y])` induced by `θ` when its image generates `Frac(W[Y])`. -/
def mvGaussFracEquiv : FractionRing R ≃ₐ[k] FractionRing (MvPolynomial σ W) :=
  AlgEquiv.ofBijective _ (mvGaussFracHom_bijective θ hθ hcl)

/-- The embedding `W[Y] → Frac R`. -/
def mvGaussEmb : MvPolynomial σ W →ₐ[k] FractionRing R :=
  (mvGaussFracEquiv θ hθ hcl).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom k _ (FractionRing (MvPolynomial σ W)))

theorem mvGaussEmb_injective : Function.Injective (mvGaussEmb θ hθ hcl) :=
  (mvGaussFracEquiv θ hθ hcl).symm.injective.comp (IsFractionRing.injective _ _)

theorem mvGaussEmb_apply (g : R) : mvGaussEmb θ hθ hcl (θ g) = algebraMap _ _ g := by
  change (mvGaussFracEquiv θ hθ hcl).symm (algebraMap _ _ (θ g)) = _
  rw [AlgEquiv.symm_apply_eq, mvGaussFracEquiv, AlgEquiv.ofBijective_apply,
    mvGaussFracHom_algebraMap]

variable [Finite σ] [IsDiscreteValuationRing W] [Algebra.EssFiniteType k W]

instance essFiniteType_mvPolynomial_of_essFiniteType :
    Algebra.EssFiniteType k (MvPolynomial σ W) :=
  Algebra.EssFiniteType.comp k W _

/-- **The Gauss extension of `W` inside `Frac R`**: for an injective `θ : R → W[Y]` whose image
generates `Frac(W[Y])`, the discrete valuation ring `W[Y]_{m_W W[Y]}` realized inside `Frac R`,
as a discrete valuation ring birational to `R`. -/
def ofMvGauss : BirationalDVR k R where
  ring := atPrimeRange (P := mvGaussIdeal σ W) (mvGaussEmb θ hθ hcl) (mvGaussEmb_injective θ hθ hcl)
  isDVR := by
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible W
    exact isDiscreteValuationRing_atPrimeRange _ _ (mvGaussIdeal_eq_span hϖ)
      (MvPolynomial.C_ne_zero.2 hϖ.ne_zero)
  essFiniteType := essFiniteType_atPrimeRange _ _
  algebraMap_mem g := by
    rw [← mvGaussEmb_apply θ hθ hcl g]
    exact mem_atPrimeRange _ _ _

/-- `ord_{R'}(g) = min_a ord_W(θ(g)_a)` (Gauss's lemma). -/
theorem ord_ofMvGauss (g : R) :
    (ofMvGauss θ hθ hcl).ord g = (θ g).support.inf fun a => addVal W ((θ g).coeff a) := by
  have : IsDiscreteValuationRing (atPrimeRange (P := mvGaussIdeal σ W) (mvGaussEmb θ hθ hcl)
      (mvGaussEmb_injective θ hθ hcl)) := (ofMvGauss θ hθ hcl).isDVR
  have h1 : (ofMvGauss θ hθ hcl).toRing g =
      ⟨mvGaussEmb θ hθ hcl (θ g), mem_atPrimeRange _ _ _⟩ :=
    Subtype.ext (mvGaussEmb_apply θ hθ hcl g).symm
  rw [BirationalDVR.ord, h1]
  erw [addVal_atPrimeRange_eq]
  exact addVal_mvGaussIdeal _

end OfMvGauss

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]

/-- Every element of a discrete valuation ring `V` birational to `B` is a quotient of elements
of `B`. -/
theorem exists_mul_toRing_eq (V : BirationalDVR k B) (w : V.ring) :
    ∃ β γ : B, V.toRing γ ≠ 0 ∧ w * V.toRing γ = V.toRing β := by
  obtain ⟨β, γ, hγ, hw⟩ := IsFractionRing.div_surjective (A := B) (w : FractionRing B)
  have hγ0 : γ ≠ 0 := nonZeroDivisors.ne_zero hγ
  refine ⟨β, γ, (map_ne_zero_iff _ V.toRing_injective).2 hγ0, Subtype.ext ?_⟩
  rw [Subalgebra.coe_mul, coe_toRing, coe_toRing, ← hw,
    div_mul_cancel₀ _ ((map_ne_zero_iff _ (IsFractionRing.injective B (FractionRing B))).2 hγ0)]

end BirationalDVR

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r} {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0)
  (V : BirationalDVR k (X.ChartRing j))

/-! ### The Gauss extension of `V` inside `Frac(S[t])` -/

variable (X) in
/-- **The discrete valuation ring `R'` of `lem:gl-rees-points`**: the Gauss extension
`V[Y]_{m_V V[Y]}` of `V` in the variables `Y_c = z^{(c)}_{j_c}`, inside `Frac(S[t])` through the
isomorphism `Frac(S[t]) ≅ Frac(V[Y])` induced by the chart expansion. -/
def chartGaussDVR (hj : ∀ c, X.coord c (j c) ≠ 0) (V : BirationalDVR k (X.ChartRing j)) :
    BirationalDVR k (Polynomial X.S) :=
  BirationalDVR.ofMvGauss (X.chartExpandW j V.toRing)
    (chartExpandW_injective hj _ V.toRing_injective)
    (mem_closure_chartExpandW hj _ V.exists_mul_toRing_eq)

/-- `ord_{R'}(g) = min_{a, λ} (ord_V(g_{a,λ} / z̃_j^a) + λ b)` if `V` is monomial in `t`. -/
theorem chartGaussDVR_ord_eq_iInf {b : ℕ}
    (htorus : ∀ F : X.ChartRing j, V.ord F = F.support.inf fun ℓ =>
      V.ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞))
    (g : Polynomial X.S) :
    (X.chartGaussDVR hj V).ord g = ⨅ a, ⨅ ℓ,
      (V.ord (Polynomial.C ((X.chartExpandS j (g.coeff ℓ)).coeff a)) + ((ℓ * b : ℕ) : ℕ∞)) := by
  rw [chartGaussDVR, BirationalDVR.ord_ofMvGauss, ProjBerk.finset_inf_eq_iInf_of_top]
  · refine iInf_congr fun a => ?_
    rw [coeff_chartExpandW]
    change V.ord _ = _
    rw [htorus, ProjBerk.finset_inf_eq_iInf_of_top]
    · simp only [coeff_coeff_chartExpand]
    · intro ℓ hℓ
      rw [Polynomial.notMem_support_iff.1 hℓ, map_zero, BirationalDVR.ord_zero, top_add]
  · intro a ha
    rw [MvPolynomial.notMem_support_iff.1 ha, AddValuation.map_zero]

/-- For `g ∈ S[t]` homogeneous in `T` of degree `a`, with dehomogenization
`chartExpand g = g^{(j)} Y^a`, `ord_{R'}(g) = ord_V(g^{(j)})`. -/
theorem chartGaussDVR_ord_of_eq_monomial {g : Polynomial X.S} {a : Fin r →₀ ℕ}
    {F : X.ChartRing j} (h : X.chartExpand j g = MvPolynomial.monomial a F) :
    (X.chartGaussDVR hj V).ord g = V.ord F := by
  classical
  have h' : X.chartExpandW j V.toRing g = MvPolynomial.monomial a (V.toRing F) := by
    rw [chartExpandW, AlgHom.comp_apply, h, MvPolynomial.mapAlgHom_apply,
      MvPolynomial.map_monomial]
    rfl
  rw [chartGaussDVR, BirationalDVR.ord_ofMvGauss, h']
  by_cases hF : V.toRing F = 0
  · rw [hF, map_zero, MvPolynomial.support_zero, Finset.inf_empty,
      (map_eq_zero_iff _ V.toRing_injective).1 hF, BirationalDVR.ord_zero]
  · rw [MvPolynomial.support_monomial, if_neg hF, Finset.inf_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]
    rfl

/-! ### Divisoriality of `v_V` (`lem:gl-rees-points`) -/

variable (b : ℕ)

/-- `|p|_{v_V} = e^{-min_a ord_V(p_a / z̃_j^a)/b}` for `p ∈ S`. -/
theorem chartDivPoint_val (p : X.S) :
    (X.chartDivPoint j hj V b).1.val p = expOrd (expNeg (b : ℝ)⁻¹)
      (⨅ a, V.ord (Polynomial.C ((X.chartExpandS j p).coeff a))) := by
  rw [(X.chartDivPoint j hj V b).2.1.val_eq_sup,
    expOrd_iInf_eq_finset_sup (expNeg_inv_le_one b) p.1.support]
  · refine Finset.sup_congr rfl fun a _ => ?_
    rw [homComp, chartDivPoint_val_ofPiece]
    congr 3
    exact Subtype.ext (coeff_chartExpandS p a).symm
  · intro a ha
    have h0 : (X.chartExpandS j p).coeff a = 0 := by
      apply Subtype.ext
      rw [coeff_chartExpandS, MvPolynomial.notMem_support_iff.1 ha, zero_div,
        ZeroMemClass.coe_zero]
    rw [h0, map_zero, BirationalDVR.ord_zero]

/-- `|g|_{σ(v_V)} = e^{-ord_{R'}(g)/b}` (`lem:gl-rees-points`). -/
theorem gaussPt_chartDivPoint_val (hb : 0 < b)
    (htorus : ∀ F : X.ChartRing j, V.ord F = F.support.inf fun ℓ =>
      V.ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞))
    (g : Polynomial X.S) :
    (X.gaussPt (X.chartDivPoint j hj V b).1).val g =
      expOrd (expNeg (b : ℝ)⁻¹) ((X.chartGaussDVR hj V).ord g) := by
  rw [chartGaussDVR_ord_eq_iInf hj V htorus, iInf_comm, gaussPt_val,
    expOrd_iInf_eq_finset_sup (expNeg_inv_le_one b) g.support]
  · refine Finset.sup_congr rfl fun ℓ _ => ?_
    rw [chartDivPoint_val, ProjBerk.gaussRadius_eq_pow hb, ← pow_mul, ← expOrd_coe,
      ← expOrd_add, ENat.iInf_add, mul_comm b ℓ]
  · intro ℓ hℓ
    rw [Polynomial.notMem_support_iff.1 hℓ]
    refine iInf_eq_top.2 fun a => ?_
    have h0 : (X.chartExpandS j 0).coeff a = 0 := by rw [map_zero, MvPolynomial.coeff_zero]
    rw [h0, map_zero, BirationalDVR.ord_zero, top_add]

/-- **`lem:gl-rees-points`** (divisoriality): if `V` is a discrete valuation ring birational to
`B_j = A_j[t]`, monomial in `t` with `ord_V(t) = b > 0`, then the point `v_V` is divisorial, with
`R'` the Gauss extension of `V` in the variables `z^{(c)}_{j_c}` and `c = 1/b`. -/
theorem isDivisorial_chartDivPoint (hb : 0 < b)
    (htorus : ∀ F : X.ChartRing j, V.ord F = F.support.inf fun ℓ =>
      V.ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞)) :
    X.IsDivisorial (X.chartDivPoint j hj V b) :=
  isDivisorial_of_val_eq (X.chartGaussDVR hj V) (c := (b : ℚ)⁻¹) (by positivity) fun g => by
    rw [gaussPt_chartDivPoint_val hj V b hb htorus]
    push_cast
    rfl

end MultiModel

end EnvelopeProperty
