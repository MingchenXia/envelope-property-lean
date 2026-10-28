/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SmoothConeCharts

/-!
# The chart cover of the punctured cone, the twisted forms `M₀`, `𝔍₀`, and `ConeTraceData`

Let `k` be an algebraically closed field of characteristic `p` and `X = V(I) ⊆ ℙᴹ` projectively
normal with smooth charts and `n = dim X ≥ 1`. This file completes the subsection `subsec:sg-cone`
of the blueprint chapter `smooth-general.tex` up to `lem:sg-sat` (the test ideals on the punctured
cone of Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Theorem 3.1,
`thm:smooth-EP`, on smooth `X`), and packages the data used for the global Frobenius trace
`Θ^e_N(𝔞) = Φ^e_z(𝔞^N M₀) 𝔍₀` (`lem:sg-theta-local`) into `ProjSubvariety.ConeTraceData`.

## Main definitions

* `ProjSubvariety.ConeTraceData X p`: the homogeneous `p`-basis `z = (x̄_{i₀}, …, x̄_{iₙ}, t)` of
  `K = Frac T` (`lem:sg-homog-pbasis`), a finite cover of the punctured cone by charts
  `D_c = T_{s_c}` with `p`-bases `v_c` (`def:sg-charts`), and the exponent `N₁` of `def:sg-forms`.
* For `D : X.ConeTraceData p`: the Jacobians `D.jac c = J(z/v_c)`, the twisted forms
  `D.mu c = s_c^{N₁} / J_c ∈ K` and `D.iota c ∈ T` (`ι_c = s_c^{N₁} J_c`), the `T`-module
  `D.M0 = ∑_c T μ_c ⊆ K` and the ideal `D.J0 = ∑_c T ι_c ⊆ T` (`def:sg-forms`).

## Main results

* `ProjSubvariety.ConeTraceData.nonempty` (`def:sg-charts`, `def:sg-forms`): the data exist for
  `X` projectively normal with smooth charts and `dim X ≥ 1`.
* `lem:sg-jacobians`: (1) `ConeTraceData.isBihom_jac`, `jac_mem`, `jac_ne_zero`; (2)
  `ProjSubvariety.ChartDatum.div_jac_mem`; (3) `ConeTraceData.irrelevant_le_radical`,
  `ConeTraceData.exists_eq_algebraMap_of_forall_mem` (`⋂_c D_c = T`); (4)
  `ConeTraceData.traceIter_inv_jac_mul` (`Φ^e_z(J_c^{-1} a) = J_c^{-1} Φ^e_{v_c}(a)`).
* `def:sg-forms`: `ConeTraceData.mu_mul_iota`, `isBihom_mu`, `isBihom_iota`,
  `mu_mul_jac_mem`, `iota_div_jac_mem`, `inv_jac_eq`, `jac_eq_iota`, and
  `ConeTraceData.span_M0_eq` (`M₀ D_c = J_c^{-1} D_c`), `ConeTraceData.map_J0_eq`
  (`𝔍₀ D_c = J_c D_c`).
* `ProjSubvariety.exists_chartDatum_cover_all` (`def:sg-charts`, from `cor:sg-pbasis-cover`):
  finitely many chart data cover the punctured cone, `𝔪₊ ⊆ √((s_c)_c)`.

## Deviations from the blueprint

* The charts are `T_{s_c} ⊆ K` with `s_c = x̄ᵢ h̃` (as in `def:sg-charts`), indexed by `Fin N`;
  the p-bases `v_c = (u_c, x̄ᵢ, t)` are shown to be `p`-bases of `T_{s_c}` directly (images of
  `T`, and `T_{s_c}` a localization), without the isomorphism `T_{s_c} ≅ (A_i)_h[x̄ᵢ^{±1}][t]`.
* `lem:sg-jacobians`(2) is used in the form `J_c/J_{c'} ∈ T_{s_c s_{c'}}` (both quotients), which
  is what `def:sg-forms` needs; `N₁` is part of the data.
* `lem:sg-jacobians`(3) is stated as `𝔪₊ ⊆ √((s_c)_c)` (equivalently `𝔪₊^{N₀} ⊆ (s_c)_c` for some
  `N₀`, `T` being Noetherian) and `⋂_c D_c = T`.
* **`lem:sg-sat`**: `ConeTraceData.mem_saturation_iff`: `𝔟^sat = {f ∈ T : f ∈ 𝔟 D_c for all c}`.
-/

open scoped NNReal ENNReal Topology Polynomial

noncomputable section

namespace EnvelopeProperty

open ProjBerk (quotChartMk QuotChartAlg)

universe u

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}

open Cartier

/-! ### Covering the punctured cone by charts -/

section Cover

/-- If the elements of `S ⊆ A_j` generate the unit ideal and each `a ∈ S` satisfies
`a x̄ⱼ^L ∈ 𝔞` for some `L`, then `x̄ⱼ^L ∈ 𝔞` for some `L` (proof of `lem:sg-jacobians`(3)). -/
theorem exists_pow_mem_of_span_eq_top {j : Fin (M + 1)} [Fact (MvPolynomial.X j ∉ X.ideal)]
    (𝔞 : Ideal X.ConeRing) {S : Set (X.ChartAlg j)} (hS : Ideal.span S = ⊤)
    (hmem : ∀ a ∈ S, ∃ (L : ℕ), ∃ t ∈ 𝔞, X.chartAlgToFrac j a * X.fracMk (MvPolynomial.X j) ^ L =
      algebraMap X.ConeRing (FractionRing X.ConeRing) t) :
    ∃ L : ℕ, X.coneS (MvPolynomial.X j) ^ L ∈ 𝔞 := by
  set x := X.fracMk (MvPolynomial.X j)
  have hx : algebraMap X.ConeRing (FractionRing X.ConeRing) (X.coneS (MvPolynomial.X j)) = x :=
    algebraMap_coneS _
  let Q : Ideal (X.ChartAlg j) :=
    { carrier := {a | ∃ (L : ℕ), ∃ t ∈ 𝔞, X.chartAlgToFrac j a * x ^ L =
        algebraMap X.ConeRing (FractionRing X.ConeRing) t}
      add_mem' := by
        rintro a b ⟨L₁, t₁, ht₁, h₁⟩ ⟨L₂, t₂, ht₂, h₂⟩
        refine ⟨L₁ + L₂,
          t₁ * X.coneS (MvPolynomial.X j) ^ L₂ + t₂ * X.coneS (MvPolynomial.X j) ^ L₁,
          𝔞.add_mem (𝔞.mul_mem_right _ ht₁) (𝔞.mul_mem_right _ ht₂), ?_⟩
        rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, hx, ← h₁, ← h₂, pow_add]
        ring
      zero_mem' := ⟨0, 0, 𝔞.zero_mem, by simp⟩
      smul_mem' := by
        rintro b a ⟨L, t, ht, h⟩
        obtain ⟨N, β, hβ, rfl⟩ := exists_quotDehom_eq b
        refine ⟨N + L, X.coneS β * t, 𝔞.mul_mem_left _ ht, ?_⟩
        rw [smul_eq_mul, map_mul, map_mul, ← h, algebraMap_coneS,
          ← chartAlgToFrac_quotDehom_mul (X := X) (j := j) hβ, pow_add]
        ring }
  have hQ : Ideal.span S ≤ Q := Ideal.span_le.2 hmem
  rw [hS, top_le_iff] at hQ
  obtain ⟨L, t, ht, h⟩ : (1 : X.ChartAlg j) ∈ Q := hQ ▸ Submodule.mem_top
  refine ⟨L, ?_⟩
  have : X.coneS (MvPolynomial.X j) ^ L = t := by
    apply IsFractionRing.injective X.ConeRing (FractionRing X.ConeRing)
    rw [map_pow, hx, ← h, map_one, one_mul]
  rw [this]
  exact ht

variable (p : ℕ) [hp : Fact p.Prime] [CharP k p]

/-- **The chart cover over one chart** (`def:sg-charts`, from `cor:sg-pbasis-cover`): for
`xⱼ ∉ I` with `A_j` smooth there are finitely many chart data with forms `s_r` and `L` with
`x̄ⱼ^L ∈ (s_r)_r T`. -/
theorem exists_chartDatum_cover [IsAlgClosed k] (hs : X.HasSmoothCharts) (j : Fin (M + 1))
    (hj : MvPolynomial.X j ∉ X.ideal) :
    ∃ (m : ℕ) (C : Fin m → X.ChartDatum p), ∃ L : ℕ,
      X.coneS (MvPolynomial.X j) ^ L ∈ Ideal.span (Set.range fun r => (C r).s) := by
  have : Fact (MvPolynomial.X j ∉ X.ideal) := ⟨hj⟩
  have : Algebra.Smooth k (X.ChartAlg j) := hs j hj
  obtain ⟨sA, hspan, hsA⟩ := exists_isPBasis_cover_of_smooth_of_trdeg (p := p) k (X.ChartAlg j)
    (X.ChartField j) (trdeg_chartField_eq_dim (X := X) (j := j))
  have hdat : ∀ a : sA, ∃ C : X.ChartDatum p, ∃ L : ℕ,
      X.chartAlgToFrac j a * X.fracMk (MvPolynomial.X j) ^ L =
        algebraMap X.ConeRing (FractionRing X.ConeRing) C.s := by
    rintro ⟨a, ha⟩
    obtain ⟨N, τ, hτ, rfl⟩ := exists_quotDehom_eq a
    obtain ⟨hne, u, hu, hB⟩ := hsA _ ha
    have hτI : τ ∉ X.ideal := fun h => hne (quotDehom_eq_zero_of_mem h)
    have : CharP (Localization.Away (X.quotDehom j τ)) p :=
      charP_of_isLocalization_away (p := p) hne _
    refine ⟨⟨j, τ, N, hτ, hτI, u, hu, hB _⟩, N + 1, ?_⟩
    change _ = algebraMap X.ConeRing (FractionRing X.ConeRing) (X.coneS (MvPolynomial.X j * τ))
    rw [algebraMap_coneS, map_mul, ← chartAlgToFrac_quotDehom_mul (X := X) (j := j) hτ, pow_succ]
    ring
  choose C hC using hdat
  refine ⟨sA.card, fun r => C (sA.equivFin.symm r), ?_⟩
  refine exists_pow_mem_of_span_eq_top _ hspan fun a ha => ?_
  obtain ⟨L, hL⟩ := hC ⟨a, ha⟩
  refine ⟨L, (C ⟨a, ha⟩).s, Ideal.subset_span ⟨sA.equivFin ⟨a, ha⟩, by simp⟩, hL⟩

/-- **The chart cover** (`def:sg-charts`, `lem:sg-jacobians`(3)): finitely many chart data whose
forms `s_c` satisfy `𝔪₊ ⊆ √((s_c)_c)`. -/
theorem exists_chartDatum_cover_all [IsAlgClosed k] (hs : X.HasSmoothCharts) :
    ∃ (m : ℕ) (C : Fin m → X.ChartDatum p),
      X.coneIrrelevant ≤ (Ideal.span (Set.range fun c => (C c).s)).radical := by
  have H : ∀ j : Fin (M + 1), ∃ (m : ℕ) (C : Fin m → X.ChartDatum p),
      MvPolynomial.X j ∉ X.ideal → ∃ L : ℕ,
        X.coneS (MvPolynomial.X j) ^ L ∈ Ideal.span (Set.range fun r => (C r).s) := by
    intro j
    by_cases hj : MvPolynomial.X j ∈ X.ideal
    · exact ⟨0, Fin.elim0, fun h => (h hj).elim⟩
    · obtain ⟨m, C, hC⟩ := exists_chartDatum_cover p hs j hj
      exact ⟨m, C, fun _ => hC⟩
  choose m C hC using H
  let e := (finSigmaFinEquiv (m := M + 1) (n := m)).symm
  refine ⟨_, fun c => C (e c).1 (e c).2, ?_⟩
  rw [coneIrrelevant, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  by_cases hj : MvPolynomial.X j ∈ X.ideal
  · change Polynomial.C (X.coordMk (MvPolynomial.X j)) ∈ _
    rw [coordMk_eq_zero_iff.2 hj, Polynomial.C_0]
    exact Ideal.zero_mem _
  · obtain ⟨L, hL⟩ := hC j hj
    refine ⟨L, Ideal.span_mono ?_ hL⟩
    rintro _ ⟨r, rfl⟩
    refine ⟨e.symm ⟨j, r⟩, ?_⟩
    show (C (e (e.symm ⟨j, r⟩)).1 (e (e.symm ⟨j, r⟩)).2).s = (C j r).s
    generalize hy : e (e.symm ⟨j, r⟩) = y
    rw [Equiv.apply_symm_apply] at hy
    subst hy
    rfl

end Cover

/-! ### Saturation through a cover -/

section Saturation

/-- If `𝔪₊ ⊆ √((s_c)_c)` and `s_c^{m_c} f ∈ 𝔟` for all `c`, then `𝔪₊^r f ⊆ 𝔟` for some `r`. -/
theorem exists_pow_irrelevant_mul_le {ι : Type*} [Finite ι] (s : ι → X.ConeRing)
    (hs : X.coneIrrelevant ≤ (Ideal.span (Set.range s)).radical) (𝔟 : Ideal X.ConeRing)
    {f : X.ConeRing} (hf : ∀ c, ∃ m : ℕ, s c ^ m * f ∈ 𝔟) :
    ∃ r : ℕ, ∀ a ∈ X.coneIrrelevant ^ r, a * f ∈ 𝔟 := by
  have : Fintype ι := Fintype.ofFinite ι
  choose m hm using hf
  set N := Finset.univ.sup m
  have hmN : ∀ c, s c ^ N * f ∈ 𝔟 := fun c => by
    rw [← Nat.sub_add_cancel (show m c ≤ N from Finset.le_sup (f := m) (Finset.mem_univ c)),
      pow_add, mul_assoc]
    exact 𝔟.mul_mem_left _ (hm c)
  have hrad : X.coneIrrelevant ≤ (Ideal.span (Set.range fun c => s c ^ N)).radical := by
    refine hs.trans ((Ideal.radical_le_radical_iff).2 ?_)
    rw [Ideal.span_le]
    rintro _ ⟨c, rfl⟩
    exact ⟨N, Ideal.subset_span ⟨c, rfl⟩⟩
  obtain ⟨r, hr⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (IsNoetherian.noetherian X.coneIrrelevant)
  refine ⟨r, fun a ha => ?_⟩
  have ha' := hr ha
  have hle : Ideal.span (Set.range fun c => s c ^ N) ≤ 𝔟.colon {f} := by
    rw [Ideal.span_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul]
    exact hmN c
  have := hle ha'
  rwa [Submodule.mem_colon_singleton, smul_eq_mul] at this

end Saturation

/-! ### Cone trace data -/

section ConeTraceData

variable (X) (p : ℕ) [hp : Fact p.Prime] [CharP k p]

/-- **Cone trace data** (`lem:sg-homog-pbasis`, `def:sg-charts`, `lem:sg-jacobians`,
`def:sg-forms`) for `X = V(I)`, `T = S[t]`, `K = Frac T`:
* the homogeneous `p`-basis `z = X.coneZ ι = (x̄_{i₀}, x̄_{i₁}, …, x̄_{iₙ}, t)` of `K`, `n = dim X`;
* finitely many chart data `C_c` (`ProjSubvariety.ChartDatum`), with charts `D_c = T_{s_c} ⊆ K`
  carrying the `p`-bases `v_c = (u_c, x̄_{i_c}, t)`, covering the punctured cone
  (`𝔪₊ ⊆ √((s_c)_c)`) and with `⋂_c D_c = T` (projective normality);
* the exponent `N₁` of `def:sg-forms`: `ι_c = s_c^{N₁} J_c ∈ T` and
  `s_c^{N₁} J_{c'}/J_c, s_c^{N₁} J_c/J_{c'} ∈ D_{c'}` for the Jacobians `J_c = J(z/v_c)`. -/
structure ConeTraceData where
  /-- The indices `i₀ = ι(none), i₁ = ι(some 0), …` of the homogeneous `p`-basis `z = X.coneZ ι`. -/
  idx : Option (Fin X.dim) → Fin (M + 1)
  idx_none_notMem : MvPolynomial.X (idx none) ∉ X.ideal
  isPBasis_z : IsPBasis p (algebraMap X.ConeRing (FractionRing X.ConeRing) ∘ X.coneZ idx)
  /-- The number of charts. -/
  nCharts : ℕ
  /-- The chart data `C_c`: charts `D_c = T_{s_c}` with `p`-bases `v_c`. -/
  chart : Fin nCharts → X.ChartDatum p
  irrelevant_le_radical :
    X.coneIrrelevant ≤ (Ideal.span (Set.range fun c => (chart c).s)).radical
  exists_eq_algebraMap_of_forall_mem : ∀ f : FractionRing X.ConeRing,
    (∀ c, f ∈ (chart c).D) → ∃ a : X.ConeRing, f = algebraMap X.ConeRing (FractionRing X.ConeRing) a
  /-- The exponent `N₁` of `def:sg-forms`. -/
  N1 : ℕ
  pow_mul_jac_mem : ∀ c, algebraMap X.ConeRing (FractionRing X.ConeRing) (chart c).s ^ N1 *
    (chart c).jac idx ∈ (⊥ : Subalgebra X.ConeRing (FractionRing X.ConeRing))
  pow_mul_jac_div_mem : ∀ c c', algebraMap X.ConeRing (FractionRing X.ConeRing) (chart c).s ^ N1 *
    ((chart c').jac idx / (chart c).jac idx) ∈ (chart c').D
  pow_mul_jac_div_mem' : ∀ c c', algebraMap X.ConeRing (FractionRing X.ConeRing) (chart c).s ^ N1 *
    ((chart c).jac idx / (chart c').jac idx) ∈ (chart c').D

namespace ConeTraceData

variable {X p} (D : X.ConeTraceData p)

/-- The Jacobian `J_c = J(z/v_c)` of the chart `c` (`def:sg-charts`). -/
abbrev jac (c : Fin D.nCharts) : FractionRing X.ConeRing := (D.chart c).jac D.idx

/-- `s_c ∈ T` as an element of `K`. -/
abbrev sK (c : Fin D.nCharts) : FractionRing X.ConeRing :=
  algebraMap X.ConeRing (FractionRing X.ConeRing) (D.chart c).s

theorem sK_ne_zero (c : Fin D.nCharts) : D.sK c ≠ 0 := (D.chart c).algebraMap_s_ne_zero

theorem jac_ne_zero (c : Fin D.nCharts) : D.jac c ≠ 0 := (D.chart c).jac_ne_zero D.isPBasis_z

/-- **`lem:sg-jacobians`(1)**: `J_c` is bihomogeneous of bidegree `(n, 0)`, `n = dim X`. -/
theorem isBihom_jac (c : Fin D.nCharts) : X.IsBihom (D.jac c) X.dim 0 :=
  (D.chart c).isBihom_jac D.idx

theorem isBihom_sK_pow (c : Fin D.nCharts) (N : ℕ) :
    X.IsBihom (D.sK c ^ N) (N * ((D.chart c).e + 1) : ℕ) 0 := by
  have h := isBihom_fracMk_mul (X := X) ((D.chart c).form_isHomogeneous.pow N) 0
  rw [pow_zero, mul_one, map_pow] at h
  rw [sK, ChartDatum.algebraMap_s]
  simpa [mul_comm] using h

/-- The twisted form `ι_c = s_c^{N₁} J_c ∈ T` (`def:sg-forms`). -/
def iota (c : Fin D.nCharts) : X.ConeRing := (Algebra.mem_bot.1 (D.pow_mul_jac_mem c)).choose

theorem algebraMap_iota (c : Fin D.nCharts) :
    algebraMap X.ConeRing (FractionRing X.ConeRing) (D.iota c) = D.sK c ^ D.N1 * D.jac c :=
  (Algebra.mem_bot.1 (D.pow_mul_jac_mem c)).choose_spec

/-- The twisted form `μ_c = s_c^{N₁} / J_c ∈ K` (`def:sg-forms`). -/
def mu (c : Fin D.nCharts) : FractionRing X.ConeRing := D.sK c ^ D.N1 / D.jac c

/-- `M₀ = ∑_c T μ_c ⊆ K` (`def:sg-forms`): the regular top forms divided by `dz`. -/
def M0 : Submodule X.ConeRing (FractionRing X.ConeRing) :=
  Submodule.span X.ConeRing (Set.range D.mu)

/-- `𝔍₀ = ∑_c T ι_c ⊆ T` (`def:sg-forms`). -/
def J0 : Ideal X.ConeRing := Ideal.span (Set.range D.iota)

theorem mu_mul_iota (c : Fin D.nCharts) :
    D.mu c * algebraMap X.ConeRing (FractionRing X.ConeRing) (D.iota c) = D.sK c ^ (2 * D.N1) := by
  rw [mu, algebraMap_iota, two_mul, pow_add]
  field_simp [D.jac_ne_zero c]

/-- `μ_c` is bihomogeneous of bidegree `(N₁ deg s_c - n, 0)`. -/
theorem isBihom_mu (c : Fin D.nCharts) :
    X.IsBihom (D.mu c) ((D.N1 * ((D.chart c).e + 1) : ℕ) - X.dim) 0 := by
  rw [mu, div_eq_mul_inv]
  simpa [sub_eq_add_neg] using (D.isBihom_sK_pow c D.N1).mul (D.isBihom_jac c).inv

/-- `ι_c` is bihomogeneous of bidegree `(N₁ deg s_c + n, 0)`; it is the class of a form of that
degree (`exists_eq_coneMk_of_isBihom`). -/
theorem isBihom_iota (c : Fin D.nCharts) :
    X.IsBihom (algebraMap X.ConeRing (FractionRing X.ConeRing) (D.iota c))
      ((D.N1 * ((D.chart c).e + 1) : ℕ) + X.dim) 0 := by
  rw [algebraMap_iota]
  simpa using (D.isBihom_sK_pow c D.N1).mul (D.isBihom_jac c)

/-- `μ_{c'} J_c ∈ D_c`: `M₀ D_c ⊆ J_c^{-1} D_c` (`def:sg-forms`). -/
theorem mu_mul_jac_mem (c c' : Fin D.nCharts) : D.mu c' * D.jac c ∈ (D.chart c).D := by
  have h := D.pow_mul_jac_div_mem c' c
  rw [mu]
  convert h using 1
  ring

/-- `ι_{c'} / J_c ∈ D_c`: `𝔍₀ D_c ⊆ J_c D_c` (`def:sg-forms`). -/
theorem iota_div_jac_mem (c c' : Fin D.nCharts) :
    algebraMap X.ConeRing (FractionRing X.ConeRing) (D.iota c') / D.jac c ∈ (D.chart c).D := by
  have h := D.pow_mul_jac_div_mem' c' c
  rw [algebraMap_iota]
  convert h using 1
  ring

theorem inv_sK_mem (c : Fin D.nCharts) : (D.sK c)⁻¹ ∈ (D.chart c).D :=
  inv_mem_awaySubalgebra _

/-- `J_c^{-1} = μ_c s_c^{-N₁}`: `J_c^{-1} D_c ⊆ M₀ D_c` (`def:sg-forms`). -/
theorem inv_jac_eq (c : Fin D.nCharts) : (D.jac c)⁻¹ = D.mu c * (D.sK c)⁻¹ ^ D.N1 := by
  rw [mu, div_mul_eq_mul_div, ← mul_pow, mul_inv_cancel₀ (D.sK_ne_zero c), one_pow, one_div]

/-- `J_c = ι_c s_c^{-N₁}`: `J_c D_c ⊆ 𝔍₀ D_c` (`def:sg-forms`). -/
theorem jac_eq_iota (c : Fin D.nCharts) :
    D.jac c = algebraMap X.ConeRing (FractionRing X.ConeRing) (D.iota c) * (D.sK c)⁻¹ ^ D.N1 := by
  rw [algebraMap_iota, mul_comm (D.sK c ^ D.N1), mul_assoc, ← mul_pow,
    mul_inv_cancel₀ (D.sK_ne_zero c), one_pow, mul_one]

theorem mu_mem_M0 (c : Fin D.nCharts) : D.mu c ∈ D.M0 := Submodule.subset_span ⟨c, rfl⟩

theorem iota_mem_J0 (c : Fin D.nCharts) : D.iota c ∈ D.J0 := Ideal.subset_span ⟨c, rfl⟩

/-- `J_c ∈ D_c` (`lem:sg-jacobians`(1)). -/
theorem jac_mem (c : Fin D.nCharts) : D.jac c ∈ (D.chart c).D :=
  ⟨D.iota c, D.N1, by rw [D.algebraMap_iota, mul_comm]⟩

/-- **`def:sg-forms`: `M₀ D_c = J_c^{-1} D_c`** (as `D_c`-submodules of `K`). -/
theorem span_M0_eq (c : Fin D.nCharts) :
    Submodule.span (D.chart c).D (D.M0 : Set (FractionRing X.ConeRing)) =
      Submodule.span (D.chart c).D {(D.jac c)⁻¹} := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    change x ∈ Submodule.span X.ConeRing (Set.range D.mu) at hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨c', rfl⟩ := h
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      refine ⟨⟨D.mu c' * D.jac c, D.mu_mul_jac_mem c c'⟩, ?_⟩
      change (D.mu c' * D.jac c) * (D.jac c)⁻¹ = D.mu c'
      rw [mul_assoc, mul_inv_cancel₀ (D.jac_ne_zero c), mul_one]
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul (D.chart c).D a x]
      exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le, Set.singleton_subset_iff, D.inv_jac_eq c]
    have h1 : D.mu c ∈ Submodule.span (D.chart c).D (D.M0 : Set (FractionRing X.ConeRing)) :=
      Submodule.subset_span (D.mu_mem_M0 c)
    have := Submodule.smul_mem _
      (⟨_, ((D.chart c).D.pow_mem (D.inv_sK_mem c) D.N1)⟩ : (D.chart c).D) h1
    rw [SetLike.mem_coe, mul_comm]
    exact this

/-- **`def:sg-forms`: `𝔍₀ D_c = J_c D_c`** (as ideals of `D_c`). -/
theorem map_J0_eq (c : Fin D.nCharts) :
    D.J0.map (algebraMap X.ConeRing (D.chart c).D) =
      Ideal.span {(⟨D.jac c, D.jac_mem c⟩ : (D.chart c).D)} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, ConeTraceData.J0, Ideal.span_le]
    rintro _ ⟨c', rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨⟨_, D.iota_div_jac_mem c c'⟩, Subtype.ext ?_⟩
    change algebraMap X.ConeRing (FractionRing X.ConeRing) (D.iota c') / D.jac c * D.jac c = _
    rw [div_mul_cancel₀ _ (D.jac_ne_zero c)]
    rfl
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have h : (⟨D.jac c, D.jac_mem c⟩ : (D.chart c).D) =
        algebraMap X.ConeRing (D.chart c).D (D.iota c) *
          ⟨_, (D.chart c).D.pow_mem (D.inv_sK_mem c) D.N1⟩ :=
      Subtype.ext (D.jac_eq_iota c)
    rw [h]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (D.iota_mem_J0 c))

/-- **`lem:sg-jacobians`(4)**: `Φ^e_z(J_c^{-1} a) = J_c^{-1} Φ^e_{v_c}(a)` in `K`. -/
theorem traceIter_inv_jac_mul (c : Fin D.nCharts) (e : ℕ) (a : FractionRing X.ConeRing) :
    D.isPBasis_z.traceIter e ((D.jac c)⁻¹ * a) =
      (D.jac c)⁻¹ * (D.chart c).isPBasis_vK.traceIter e a := by
  have hv := (D.chart c).isPBasis_vK
  have h1 := IsPBasis.jac_mul_jac hv D.isPBasis_z
  have h2 : D.isPBasis_z.jac (D.chart c).vK = (D.jac c)⁻¹ :=
    eq_inv_of_mul_eq_one_right h1
  rw [IsPBasis.traceIter_eq_traceIter_jac_pow_mul hv D.isPBasis_z, h2, ← mul_assoc, ← pow_succ,
    Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.out.pos), IsPBasis.traceIter_pow_mul]

/-- **`lem:sg-jacobians`(3)**: `⋂_c D_c = T`. -/
theorem exists_eq_algebraMap_of_forall_mem' {f : FractionRing X.ConeRing}
    (hf : ∀ c, f ∈ (D.chart c).D) : ∃ a : X.ConeRing,
      f = algebraMap X.ConeRing (FractionRing X.ConeRing) a :=
  D.exists_eq_algebraMap_of_forall_mem f hf

/-- **`lem:sg-sat`**: `𝔟^sat = {f ∈ T : f ∈ 𝔟 D_c for all c}`. -/
theorem mem_saturation_iff (𝔟 : Ideal X.ConeRing) (f : X.ConeRing) :
    f ∈ X.saturation 𝔟 ↔ ∀ c, algebraMap X.ConeRing (D.chart c).D f ∈
      𝔟.map (algebraMap X.ConeRing (D.chart c).D) := by
  constructor
  · intro hf c
    obtain ⟨r, hr⟩ := ProjSubvariety.mem_saturation_iff.1 hf
    have hsr : (D.chart c).s ^ r ∈ X.coneIrrelevant ^ r := by
      refine Ideal.pow_mem_pow ?_ r
      rw [ChartDatum.s, coneS, ChartDatum.form, map_mul, Polynomial.C_mul]
      exact X.coneIrrelevant.mul_mem_right _ (Ideal.subset_span ⟨(D.chart c).i, rfl⟩)
    rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers (D.chart c).s)]
    exact ⟨(⟨(D.chart c).s ^ r * f, hr _ hsr⟩, ⟨(D.chart c).s ^ r, r, rfl⟩), by
      rw [map_mul, mul_comm]⟩
  · intro hf
    refine ProjSubvariety.mem_saturation_iff.2
      (exists_pow_irrelevant_mul_le (fun c => (D.chart c).s) D.irrelevant_le_radical 𝔟 fun c => ?_)
    obtain ⟨⟨⟨b, hb⟩, ⟨_, m, rfl⟩⟩, h⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers (D.chart c).s) (D.chart c).D).1
        (hf c)
    refine ⟨m, ?_⟩
    have : (D.chart c).s ^ m * f = b := by
      apply IsLocalization.injective (D.chart c).D
        (powers_le_nonZeroDivisors_of_noZeroDivisors (D.chart c).s_ne_zero)
      rw [map_mul, mul_comm]
      exact h
    rw [this]
    exact hb

/-- **Existence of cone trace data** (`lem:sg-homog-pbasis`, `def:sg-charts`, `lem:sg-jacobians`,
`def:sg-forms`): for `k` algebraically closed of characteristic `p` and `X` projectively normal with
smooth charts and `dim X ≥ 1`. -/
theorem nonempty [IsAlgClosed k] (hX : X.IsProjNormal) (hs : X.HasSmoothCharts)
    (hn : 1 ≤ X.dim) : Nonempty (X.ConeTraceData p) := by
  obtain ⟨i₀, hi₀⟩ := X.exists_X_notMem
  obtain ⟨idx, hidx, hz⟩ := exists_isPBasis_coneZ (X := X) p i₀ hi₀
  obtain ⟨m, C, hC⟩ := exists_chartDatum_cover_all (X := X) p hs
  -- `⋂_c D_c = T`
  have hinter : ∀ f : FractionRing X.ConeRing, (∀ c, f ∈ (C c).D) →
      ∃ a : X.ConeRing, f = algebraMap X.ConeRing (FractionRing X.ConeRing) a := by
    intro f hf
    refine exists_eq_algebraMap_of_forall_mul_pow X hX hn fun j _ => ?_
    let Q : Ideal X.ConeRing :=
      { carrier := {y | ∃ a : X.ConeRing, f * algebraMap X.ConeRing (FractionRing X.ConeRing) y =
          algebraMap X.ConeRing (FractionRing X.ConeRing) a}
        add_mem' := by
          rintro y y' ⟨a, ha⟩ ⟨a', ha'⟩
          exact ⟨a + a', by rw [map_add, mul_add, ha, ha', map_add]⟩
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro b y ⟨a, ha⟩
          exact ⟨b * a, by rw [smul_eq_mul, map_mul, mul_left_comm, ha, map_mul]⟩ }
    obtain ⟨r, hr⟩ := exists_pow_irrelevant_mul_le (fun c => (C c).s) hC Q (f := 1) fun c => by
      obtain ⟨a, N, h⟩ := hf c
      refine ⟨N, ?_⟩
      show ∃ a' : X.ConeRing, f * algebraMap X.ConeRing (FractionRing X.ConeRing)
        ((C c).s ^ N * 1) = algebraMap X.ConeRing (FractionRing X.ConeRing) a'
      exact ⟨a, by rw [mul_one, map_pow]; exact h⟩
    have hx : X.coneS (MvPolynomial.X j) ^ r ∈ X.coneIrrelevant ^ r :=
      Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self (f := fun i =>
        Polynomial.C (X.coordMk (MvPolynomial.X i))) j)) r
    obtain ⟨a, ha⟩ : ∃ a : X.ConeRing, f * algebraMap X.ConeRing (FractionRing X.ConeRing)
        (X.coneS (MvPolynomial.X j) ^ r * 1) = algebraMap X.ConeRing (FractionRing X.ConeRing) a :=
      hr _ hx
    exact ⟨a, r, by rw [← ha, mul_one, map_pow, algebraMap_coneS]⟩
  -- the exponent `N₁`
  have h1 : ∀ c, ∃ N : ℕ, algebraMap X.ConeRing (FractionRing X.ConeRing) (C c).s ^ N *
      (C c).jac idx ∈ (⊥ : Subalgebra X.ConeRing (FractionRing X.ConeRing)) := by
    intro c
    obtain ⟨a, N, h⟩ := (C c).jac_mem idx
    exact ⟨N, Algebra.mem_bot.2 ⟨a, by rw [← h, mul_comm]⟩⟩
  have h2 : ∀ c c', ∃ N : ℕ, algebraMap X.ConeRing (FractionRing X.ConeRing) (C c).s ^ N *
      ((C c').jac idx / (C c).jac idx) ∈ (C c').D := by
    intro c c'
    obtain ⟨a, N, h⟩ := (C c').div_jac_mem (C c) hz
    refine ⟨N, a, N, ?_⟩
    rw [← h, map_mul, mul_pow]
    ring
  have h3 : ∀ c c', ∃ N : ℕ, algebraMap X.ConeRing (FractionRing X.ConeRing) (C c).s ^ N *
      ((C c).jac idx / (C c').jac idx) ∈ (C c').D := by
    intro c c'
    obtain ⟨a, N, h⟩ := (C c).div_jac_mem (C c') hz
    refine ⟨N, a, N, ?_⟩
    rw [← h, map_mul, mul_pow]
    ring
  choose N₁ hN₁ using h1
  choose N₂ hN₂ using h2
  choose N₃ hN₃ using h3
  set N := Finset.univ.sup N₁ +
    Finset.univ.sup fun cc : Fin m × Fin m => N₂ cc.1 cc.2 + N₃ cc.1 cc.2
  have mono : ∀ {S : Subalgebra X.ConeRing (FractionRing X.ConeRing)} {x : FractionRing X.ConeRing}
      {c : Fin m} {n n' : ℕ}, n ≤ n' →
      algebraMap X.ConeRing (FractionRing X.ConeRing) (C c).s ^ n * x ∈ S →
      algebraMap X.ConeRing (FractionRing X.ConeRing) (C c).s ^ n' * x ∈ S := by
    intro S x c n n' hle h
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
    exact S.mul_mem (S.pow_mem (S.algebraMap_mem _) _) h
  have hle1 : ∀ c, N₁ c ≤ N := fun c =>
    (Finset.le_sup (f := N₁) (Finset.mem_univ c)).trans (Nat.le_add_right _ _)
  have hle23 : ∀ c c', N₂ c c' + N₃ c c' ≤ N := fun c c' =>
    (Finset.le_sup (f := fun cc : Fin m × Fin m => N₂ cc.1 cc.2 + N₃ cc.1 cc.2)
      (Finset.mem_univ (c, c'))).trans (Nat.le_add_left _ _)
  exact ⟨{ idx := idx
           idx_none_notMem := hidx ▸ hi₀
           isPBasis_z := hz
           nCharts := m
           chart := C
           irrelevant_le_radical := hC
           exists_eq_algebraMap_of_forall_mem := hinter
           N1 := N
           pow_mul_jac_mem := fun c => mono (hle1 c) (hN₁ c)
           pow_mul_jac_div_mem := fun c c' =>
             mono ((Nat.le_add_right _ _).trans (hle23 c c')) (hN₂ c c')
           pow_mul_jac_div_mem' := fun c c' =>
             mono ((Nat.le_add_left _ _).trans (hle23 c c')) (hN₃ c c') }⟩

end ConeTraceData

end ConeTraceData

end ProjSubvariety

end EnvelopeProperty
