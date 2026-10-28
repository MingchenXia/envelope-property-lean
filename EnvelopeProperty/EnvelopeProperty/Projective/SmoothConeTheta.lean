/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SmoothConeForms
import EnvelopeProperty.TestIdeal.PBasisTest

/-!
# The global Frobenius trace `Θ^e_N(𝔞) = Φ^e_z(𝔞^N M₀) 𝔍₀` on the punctured cone

Let `k` be a perfect field of characteristic `p`, `X = V(I) ⊆ ℙᴹ` with cone ring `T = S[t]`
(`ProjSubvariety.ConeRing`), `K = Frac T`, and let `D : X.ConeTraceData p` be the data of
`lem:sg-homog-pbasis`, `def:sg-charts` and `def:sg-forms` of the blueprint chapter
`smooth-general.tex` (`subsec:sg-cone`): the homogeneous `p`-basis `z` of `K`, the charts
`D_c = T_{s_c} ⊆ K` with `p`-bases `v_c`, and the twisted forms `M₀ = ∑_c T μ_c ⊆ K`,
`𝔍₀ = ∑_c T ι_c ⊆ T`. This file proves **`lem:sg-theta-local`**, the step which replaces the
canonical sheaf and the Grothendieck trace in the proof of Fang–Han–Xia, *The envelope property
for unibranch projective varieties*, Theorem 3.1 (`thm:smooth-EP`, §3, eq. `eq:test-def`) on a
smooth projectively normal `X`:

for an ideal `𝔞 ⊆ T` and `e, N ≥ 0`, `Θ^e_N(𝔞) = Φ^e_z(𝔞^N M₀) 𝔍₀` is an ideal of `T`, and its
localization on every chart is the local Frobenius root: `Θ^e_N(𝔞) D_c = (𝔞^N D_c)^{[1/p^e]}`
with respect to `v_c`.

## Main definitions

* `ConeTraceData.traceSubmodule D e 𝔫 = Φ^e_z(𝔫)`: the image of a `T`-submodule `𝔫 ⊆ K` under
  the Frobenius trace `Φ^e_z`; a `T`-submodule by `Φ^e_z(g^{p^e} f) = g Φ^e_z(f)`.
* `ConeTraceData.thetaK D e N 𝔞 = Φ^e_z(𝔞^N M₀) · 𝔍₀`, a `T`-submodule of `K`, and
  `ConeTraceData.theta D e N 𝔞 = Θ^e_N(𝔞)`, its preimage in `T`.

## Main results

* `ConeTraceData.exists_mem_frobRoot_eq_of_mem_thetaK`: every element of `Φ^e_z(𝔞^N M₀) 𝔍₀` lies
  in `(𝔞^N D_c)^{[1/p^e]} ⊆ D_c` for every chart `c`.
* `ConeTraceData.exists_eq_algebraMap_of_mem_thetaK`, `ConeTraceData.map_theta`:
  `Φ^e_z(𝔞^N M₀) 𝔍₀ ⊆ ⋂_c D_c = T`, so `Θ^e_N(𝔞)` "is" `Φ^e_z(𝔞^N M₀) 𝔍₀`.
* **`ConeTraceData.map_theta_chart`** (`lem:sg-theta-local`):
  `Θ^e_N(𝔞) D_c = (𝔞^N D_c)^{[1/p^e]}`.

## Deviations from the blueprint

* The proof is elementwise and uses only `μ_{c'} J_c ∈ D_c`, `ι_{c'}/J_c ∈ D_c`,
  `J_c^{-1} = μ_c s_c^{-N₁}`, `J_c = ι_c s_c^{-N₁}` and `Φ^e_z(J_c^{-1} a) = J_c^{-1} Φ^e_{v_c}(a)`
  (`def:sg-forms`, `lem:sg-jacobians`(4)); the identities `M₀ D_c = J_c^{-1} D_c`,
  `𝔍₀ D_c = J_c D_c` are not needed in this form. `Φ^e_z(L) ⊆ L` is not needed either: the trace
  is taken in `K`.
-/

open scoped NNReal ENNReal Topology Polynomial

noncomputable section

namespace EnvelopeProperty

universe u

/-- `(s⁻¹^N)^Q s^{N(Q-1)} = s⁻¹^N` in a field, for `s ≠ 0` and `Q ≥ 1`. -/
theorem inv_pow_pow_mul_pow_mul_sub_one {F : Type*} [Field F] {s : F} (hs : s ≠ 0) (N : ℕ)
    {Q : ℕ} (hQ : 1 ≤ Q) : (s⁻¹ ^ N) ^ Q * s ^ (N * (Q - 1)) = s⁻¹ ^ N := by
  obtain ⟨Q', rfl⟩ := Nat.exists_eq_add_of_le' hQ
  rw [Nat.add_sub_cancel, pow_succ, pow_mul, mul_right_comm, ← mul_pow, ← mul_pow,
    inv_mul_cancel₀ hs, one_pow, one_pow, one_mul]

namespace ProjSubvariety

namespace ConeTraceData

open Cartier

variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M} {p : ℕ} [hp : Fact p.Prime]
  [CharP k p] (D : X.ConeTraceData p)

/-! ### The trace of a submodule -/

/-- The **Frobenius trace** `Φ^e_z(𝔫)` of a `T`-submodule `𝔫 ⊆ K`, for the homogeneous `p`-basis
`z` of `K` (`lem:sg-theta-local`): a `T`-submodule of `K`, since
`g Φ^e_z(f) = Φ^e_z(g^{p^e} f)`. -/
def traceSubmodule (e : ℕ) (𝔫 : Submodule X.ConeRing (FractionRing X.ConeRing)) :
    Submodule X.ConeRing (FractionRing X.ConeRing) where
  carrier := D.isPBasis_z.traceIter e '' 𝔫
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, 𝔫.add_mem hf hg, D.isPBasis_z.traceIter_add e f g⟩
  zero_mem' := ⟨0, 𝔫.zero_mem, D.isPBasis_z.traceIter_map_zero e⟩
  smul_mem' := by
    rintro c _ ⟨f, hf, rfl⟩
    refine ⟨c ^ p ^ e • f, 𝔫.smul_mem _ hf, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, map_pow, D.isPBasis_z.traceIter_pow_mul]

theorem mem_traceSubmodule {e : ℕ} {𝔫 : Submodule X.ConeRing (FractionRing X.ConeRing)}
    {y : FractionRing X.ConeRing} :
    y ∈ D.traceSubmodule e 𝔫 ↔ ∃ x ∈ 𝔫, D.isPBasis_z.traceIter e x = y :=
  Iff.rfl

theorem traceIter_mem_traceSubmodule {e : ℕ} {𝔫 : Submodule X.ConeRing (FractionRing X.ConeRing)}
    {x : FractionRing X.ConeRing} (hx : x ∈ 𝔫) :
    D.isPBasis_z.traceIter e x ∈ D.traceSubmodule e 𝔫 :=
  ⟨x, hx, rfl⟩

/-! ### `Θ^e_N(𝔞)` -/

/-- `Φ^e_z(𝔞^N M₀) · 𝔍₀ ⊆ K` (`lem:sg-theta-local`), a `T`-submodule of `K`; it lies in `T`
(`exists_eq_algebraMap_of_mem_thetaK`). -/
def thetaK (e N : ℕ) (𝔞 : Ideal X.ConeRing) : Submodule X.ConeRing (FractionRing X.ConeRing) :=
  D.traceSubmodule e (𝔞 ^ N • D.M0) *
    Submodule.map (Algebra.linearMap X.ConeRing (FractionRing X.ConeRing)) D.J0

/-- **The global trace** `Θ^e_N(𝔞) = Φ^e_z(𝔞^N M₀) 𝔍₀`, as an ideal of `T`
(`lem:sg-theta-local`): the preimage of `thetaK` in `T`; by `map_theta` its image in `K` is all
of `thetaK`. -/
def theta (e N : ℕ) (𝔞 : Ideal X.ConeRing) : Ideal X.ConeRing :=
  Submodule.comap (Algebra.linearMap X.ConeRing (FractionRing X.ConeRing)) (D.thetaK e N 𝔞)

theorem mem_theta {e N : ℕ} {𝔞 : Ideal X.ConeRing} {f : X.ConeRing} :
    f ∈ D.theta e N 𝔞 ↔ algebraMap X.ConeRing (FractionRing X.ConeRing) f ∈ D.thetaK e N 𝔞 :=
  Iff.rfl

theorem traceIter_mul_iota_mem_thetaK {e N : ℕ} {𝔞 : Ideal X.ConeRing}
    {x : FractionRing X.ConeRing} (hx : x ∈ 𝔞 ^ N • D.M0) {j : X.ConeRing} (hj : j ∈ D.J0) :
    D.isPBasis_z.traceIter e x * algebraMap X.ConeRing (FractionRing X.ConeRing) j ∈
      D.thetaK e N 𝔞 :=
  Submodule.mul_mem_mul (D.traceIter_mem_traceSubmodule hx) (Submodule.mem_map_of_mem hj)

/-! ### The charts -/

/-- `J_c x ∈ D_c` for `x ∈ M₀` (`def:sg-forms`: `M₀ D_c ⊆ J_c^{-1} D_c`). -/
theorem jac_mul_mem_of_mem_M0 (c : Fin D.nCharts) {x : FractionRing X.ConeRing}
    (hx : x ∈ D.M0) : D.jac c * x ∈ (D.chart c).D := by
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨c', rfl⟩ := h
    rw [mul_comm]
    exact D.mu_mul_jac_mem c c'
  | zero => rw [mul_zero]; exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Subalgebra.add_mem _ hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def, mul_left_comm]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) hx

/-- `j / J_c ∈ D_c` for `j ∈ 𝔍₀` (`def:sg-forms`: `𝔍₀ D_c ⊆ J_c D_c`). -/
theorem div_jac_mem_of_mem_J0 (c : Fin D.nCharts) {j : X.ConeRing} (hj : j ∈ D.J0) :
    algebraMap X.ConeRing (FractionRing X.ConeRing) j / D.jac c ∈ (D.chart c).D := by
  induction hj using Submodule.span_induction with
  | mem x h =>
    obtain ⟨c', rfl⟩ := h
    exact D.iota_div_jac_mem c c'
  | zero => rw [map_zero, zero_div]; exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => rw [map_add, add_div]; exact Subalgebra.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_mul, map_mul, mul_div_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) hx

/-- For `x ∈ 𝔞^N M₀`, `J_c x` is (the image of) an element of `(𝔞 D_c)^N`. -/
theorem exists_mem_pow_map_eq_jac_mul (c : Fin D.nCharts) {N : ℕ} {𝔞 : Ideal X.ConeRing}
    {x : FractionRing X.ConeRing} (hx : x ∈ 𝔞 ^ N • D.M0) :
    ∃ g ∈ (𝔞.map (algebraMap X.ConeRing (D.chart c).D)) ^ N,
      (g : FractionRing X.ConeRing) = D.jac c * x := by
  refine Submodule.smul_induction_on hx (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · refine ⟨algebraMap X.ConeRing (D.chart c).D r * ⟨D.jac c * n, D.jac_mul_mem_of_mem_M0 c hn⟩,
      Ideal.mul_mem_right _ _ (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hr), ?_⟩
    rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Algebra.smul_def]
    ring
  · obtain ⟨g, hg, hgx⟩ := hx
    obtain ⟨g', hg', hgy⟩ := hy
    exact ⟨g + g', Ideal.add_mem _ hg hg', by
      rw [Subalgebra.coe_add, hgx, hgy, mul_add]⟩

variable [PerfectRing k p]

/-- The trace of `v_c` on `D_c` is the restriction of the trace of `v_c` on `K`. -/
theorem coe_traceIter_v (c : Fin D.nCharts) (e : ℕ) (g : (D.chart c).D) :
    (((D.chart c).isPBasis_v.traceIter e g : (D.chart c).D) : FractionRing X.ConeRing) =
      (D.chart c).isPBasis_vK.traceIter e (g : FractionRing X.ConeRing) :=
  (IsPBasis.traceIter_map ((D.chart c).D.val : (D.chart c).D →+* FractionRing X.ConeRing)
    (D.chart c).isPBasis_v (D.chart c).isPBasis_vK e g).symm

/-- **`Φ^e_z(𝔞^N M₀) 𝔍₀ ⊆ (𝔞^N D_c)^{[1/p^e]}`** (`lem:sg-theta-local`, one inclusion): for
`x ∈ 𝔞^N M₀` and `j ∈ 𝔍₀`, `Φ^e_z(x) j = (j / J_c) Φ^e_{v_c}(J_c x)` with `J_c x ∈ 𝔞^N D_c`
and `j / J_c ∈ D_c`. -/
theorem exists_mem_frobRoot_eq_of_mem_thetaK (c : Fin D.nCharts) {e N : ℕ}
    {𝔞 : Ideal X.ConeRing} {y : FractionRing X.ConeRing} (hy : y ∈ D.thetaK e N 𝔞) :
    ∃ w ∈ (D.chart c).isPBasis_v.frobRoot e ((𝔞.map (algebraMap X.ConeRing (D.chart c).D)) ^ N),
      (w : FractionRing X.ConeRing) = y := by
  refine Submodule.mul_induction_on hy (fun m hm n hn => ?_) (fun y y' hy hy' => ?_)
  · obtain ⟨x, hx, rfl⟩ := hm
    obtain ⟨j, hj, rfl⟩ := Submodule.mem_map.1 hn
    obtain ⟨g, hg, hgx⟩ := D.exists_mem_pow_map_eq_jac_mul c hx
    refine ⟨⟨_, D.div_jac_mem_of_mem_J0 c hj⟩ * (D.chart c).isPBasis_v.traceIter e g,
      Ideal.mul_mem_left _ _ ((D.chart c).isPBasis_v.traceIter_mem_frobRoot hg), ?_⟩
    have hJ := D.jac_ne_zero c
    have h1 : D.isPBasis_z.traceIter e x =
        (D.jac c)⁻¹ * (D.chart c).isPBasis_vK.traceIter e (D.jac c * x) := by
      rw [← D.traceIter_inv_jac_mul, inv_mul_cancel_left₀ hJ]
    rw [Subalgebra.coe_mul, D.coe_traceIter_v, hgx, h1, Algebra.linearMap_apply]
    change algebraMap X.ConeRing (FractionRing X.ConeRing) j / D.jac c * _ = _
    field_simp
  · obtain ⟨w, hw, rfl⟩ := hy
    obtain ⟨w', hw', rfl⟩ := hy'
    exact ⟨w + w', Ideal.add_mem _ hw hw', Subalgebra.coe_add _ _ _⟩

/-- `Φ^e_z(𝔞^N M₀) 𝔍₀ ⊆ D_c` for every chart `c`. -/
theorem mem_chart_of_mem_thetaK (c : Fin D.nCharts) {e N : ℕ} {𝔞 : Ideal X.ConeRing}
    {y : FractionRing X.ConeRing} (hy : y ∈ D.thetaK e N 𝔞) : y ∈ (D.chart c).D := by
  obtain ⟨w, -, rfl⟩ := D.exists_mem_frobRoot_eq_of_mem_thetaK c hy
  exact w.2

/-- **`Φ^e_z(𝔞^N M₀) 𝔍₀ ⊆ ⋂_c D_c = T`** (`lem:sg-theta-local`, `lem:sg-jacobians`(3)). -/
theorem exists_eq_algebraMap_of_mem_thetaK {e N : ℕ} {𝔞 : Ideal X.ConeRing}
    {y : FractionRing X.ConeRing} (hy : y ∈ D.thetaK e N 𝔞) :
    ∃ a : X.ConeRing, y = algebraMap X.ConeRing (FractionRing X.ConeRing) a :=
  D.exists_eq_algebraMap_of_forall_mem y fun c => D.mem_chart_of_mem_thetaK c hy

/-- The image of `Θ^e_N(𝔞)` in `K` is `Φ^e_z(𝔞^N M₀) 𝔍₀`. -/
theorem map_theta (e N : ℕ) (𝔞 : Ideal X.ConeRing) :
    Submodule.map (Algebra.linearMap X.ConeRing (FractionRing X.ConeRing)) (D.theta e N 𝔞) =
      D.thetaK e N 𝔞 := by
  refine le_antisymm (Submodule.map_comap_le _ _) fun y hy => ?_
  obtain ⟨a, rfl⟩ := D.exists_eq_algebraMap_of_mem_thetaK hy
  exact Submodule.mem_map_of_mem (D.mem_theta.2 hy)

/-- `Φ^e_{v_c}(h) ∈ Θ^e_N(𝔞) D_c` for `h ∈ 𝔞^N`: in `K`,
`Φ^e_{v_c}(h) = J_c Φ^e_z(J_c^{-1} h) = s_c^{-2N₁} Φ^e_z(s_c^{N₁(p^e-1)} h μ_c) ι_c`. -/
theorem traceIter_algebraMap_mem_map_theta (c : Fin D.nCharts) {e N : ℕ} {𝔞 : Ideal X.ConeRing}
    {h : X.ConeRing} (hh : h ∈ 𝔞 ^ N) :
    (D.chart c).isPBasis_v.traceIter e (algebraMap X.ConeRing (D.chart c).D h) ∈
      (D.theta e N 𝔞).map (algebraMap X.ConeRing (D.chart c).D) := by
  set Q := p ^ e
  have hQ : 1 ≤ Q := Nat.one_le_pow _ _ hp.out.pos
  set x : FractionRing X.ConeRing := ((D.chart c).s ^ (D.N1 * (Q - 1)) * h) • D.mu c
  have hx : x ∈ 𝔞 ^ N • D.M0 := Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ hh) (D.mu_mem_M0 c)
  obtain ⟨θ, hθ⟩ := D.exists_eq_algebraMap_of_mem_thetaK
    (D.traceIter_mul_iota_mem_thetaK (e := e) hx (D.iota_mem_J0 c))
  have hθmem : θ ∈ D.theta e N 𝔞 := by
    rw [mem_theta, ← hθ]
    exact D.traceIter_mul_iota_mem_thetaK hx (D.iota_mem_J0 c)
  set τ : (D.chart c).D := ⟨(D.sK c)⁻¹, D.inv_sK_mem c⟩
  have key : (D.chart c).isPBasis_v.traceIter e (algebraMap X.ConeRing (D.chart c).D h) =
      τ ^ (2 * D.N1) * algebraMap X.ConeRing (D.chart c).D θ := by
    apply Subtype.ext
    have hs := D.sK_ne_zero c
    have hJ := D.jac_ne_zero c
    have h1 : (D.chart c).isPBasis_vK.traceIter e (algebraMap X.ConeRing _ h) =
        D.jac c * D.isPBasis_z.traceIter e ((D.jac c)⁻¹ * algebraMap X.ConeRing _ h) := by
      rw [D.traceIter_inv_jac_mul, mul_inv_cancel_left₀ hJ]
    have h2 : (D.jac c)⁻¹ * algebraMap X.ConeRing (FractionRing X.ConeRing) h =
        ((D.sK c)⁻¹ ^ D.N1) ^ Q * x := by
      have hxdef : x = algebraMap X.ConeRing (FractionRing X.ConeRing)
          ((D.chart c).s ^ (D.N1 * (Q - 1)) * h) * D.mu c := Algebra.smul_def _ _
      rw [D.inv_jac_eq c, hxdef, map_mul, map_pow, ← mul_assoc, ← mul_assoc,
        inv_pow_pow_mul_pow_mul_sub_one hs D.N1 hQ]
      ring
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap, D.coe_traceIter_v,
      Subalgebra.coe_algebraMap, ← hθ, h1, h2, D.isPBasis_z.traceIter_pow_mul, D.jac_eq_iota c]
    change _ = (D.sK c)⁻¹ ^ (2 * D.N1) * _
    ring
  rw [key]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hθmem)

/-- **`lem:sg-theta-local`**: `Θ^e_N(𝔞) D_c = (𝔞^N D_c)^{[1/p^e]}`, the Frobenius root in the
chart `D_c` with respect to its `p`-basis `v_c`. -/
theorem map_theta_chart (c : Fin D.nCharts) (e N : ℕ) (𝔞 : Ideal X.ConeRing) :
    (D.theta e N 𝔞).map (algebraMap X.ConeRing (D.chart c).D) =
      (D.chart c).isPBasis_v.frobRoot e ((𝔞.map (algebraMap X.ConeRing (D.chart c).D)) ^ N) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    obtain ⟨w, hw, hwf⟩ := D.exists_mem_frobRoot_eq_of_mem_thetaK c (D.mem_theta.1 hf)
    rw [Ideal.mem_comap, show algebraMap X.ConeRing (D.chart c).D f = w from Subtype.ext hwf.symm]
    exact hw
  · rintro _ ⟨g, hg, rfl⟩
    rw [← Ideal.map_pow] at hg
    obtain ⟨⟨⟨h, hh⟩, ⟨_, l, rfl⟩⟩, hgh⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers (D.chart c).s) (D.chart c).D).1 hg
    set Q := p ^ e
    have hQ : 1 ≤ Q := Nat.one_le_pow _ _ hp.out.pos
    set τ : (D.chart c).D := ⟨(D.sK c)⁻¹, D.inv_sK_mem c⟩
    have hgeq : g = (τ ^ l) ^ Q *
        algebraMap X.ConeRing (D.chart c).D ((D.chart c).s ^ (l * (Q - 1)) * h) := by
      apply Subtype.ext
      have hs := D.sK_ne_zero c
      have h1 : (g : FractionRing X.ConeRing) * D.sK c ^ l =
          algebraMap X.ConeRing (FractionRing X.ConeRing) h := by
        have := congrArg Subtype.val hgh
        rwa [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap,
          map_pow] at this
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_pow, Subalgebra.coe_algebraMap,
        map_mul, map_pow]
      change (g : FractionRing X.ConeRing) = ((D.sK c)⁻¹ ^ l) ^ Q *
        (D.sK c ^ (l * (Q - 1)) * algebraMap X.ConeRing (FractionRing X.ConeRing) h)
      rw [← mul_assoc, inv_pow_pow_mul_pow_mul_sub_one hs l hQ, ← h1, mul_left_comm, ← mul_pow,
        inv_mul_cancel₀ hs, one_pow, mul_one]
    rw [hgeq, (D.chart c).isPBasis_v.traceIter_pow_mul]
    exact Ideal.mul_mem_left _ _
      (D.traceIter_algebraMap_mem_map_theta c (Ideal.mul_mem_left _ _ hh))

end ConeTraceData

end ProjSubvariety

end EnvelopeProperty
