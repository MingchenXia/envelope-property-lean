/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.Comparison
import EnvelopeProperty.Projective.PSHBasic
import EnvelopeProperty.Char0.AssemblyInputs
import EnvelopeProperty.Char0.Bridge
import EnvelopeProperty.Char0.Embedding

/-!
# The envelope property of `ℙⁿ` in characteristic `0`

This file assembles Fang–Han–Xia, *The envelope property for unibranch projective varieties*
(FHX), Theorem 3.1 (`thm:smooth-EP`) for `X = ℙⁿ` over a countable algebraically closed field `k`
of characteristic `0` (the standing assumption of FHX §5), following the blueprint chapter
`char0.tex` (`thm:c0-pn-ep`). The analytic inputs over `ℂ`, the valuative bound
(`prop:c0-valuative-bound`, `cor:c0-valuative-upper`) and the Bergman lower bound
(`cor:c0-bergman-lower`), are taken as explicit hypotheses `Char0.ValuativeUpperBound` and
`Char0.BergmanLowerBound` (`EnvelopeProperty.Char0.AssemblyInputs`); nothing else is assumed.

## The route

Fix `d ∈ ℤ_{>0}`, a rational PL function `φ` and `J_m = J_m(φ)` (`obstacleIdeal`).

* `lem:c0-shilov-description` (`ProjBerk.IsRatPL.exists_shilov_description`): finitely many
  divisorial points `w ∈ Σ`, with rings `V_w`, constants `c_w` and `γ_w = -φ(w)/c_w`, satisfy
  `V_m(φ) = {g ∈ R_{md}[t] : ord_{V_w}(g) ≥ m γ_w ∀ w}`. `Σ` is the Shilov set (`lem:bj-shilov`)
  of `ψ₁` for `φ = ψ₁ - ψ₂`.
* `prop:c0-key-inequality` (`ProjBerk.IsRatPL.exists_key_inequality`): for a field embedding
  `ι : k → ℂ` there is `N₀` with `(m/q) φ_{J_q} ≤ φ_{J_{m+2}} + N₀` for all `m, q ≥ 1`. The
  divisorial valuation rings are extended to `ℂ` (`BirationalDVR.coneBaseChange`,
  `BirationalDVR.coneMvBaseChange`, `lem:c0-base-change-dvr`); the Bergman lower bound for
  generators of `J_q` gives `x`-homogeneous `P_k` with `|P|^q ≥ c_K^q |J_q|^m`; the valuative bound
  at the `V_{w,ℂ}` puts `t^{N₀} x^α P_k` into `J_{m+2} ℂ[x][t]`
  (`ProjBerk.mem_map_coneMap_obstacleIdeal`, `cor:c0-base-change-orders`(1)); at a divisorial
  point `cor:c0-valuative-upper` and `cor:c0-base-change-orders`(2) give the inequality, which
  extends to `(ℙⁿ)^an` by divisorial comparison (`thm:bj-divisorial-comparison`).
* `thm:c0-envelope-pl` (`ProjBerk.IsRatPL.isPSH_envelope_nat_of_nonpos_of_inputs`): for `φ ≤ 0`,
  `P_d(φ) = sup_q q⁻¹ φ_{J_q}` (`envelope_eq_iSup_obstacleIdeal`) satisfies
  `m⁻¹ φ_{J_m} ≤ P_d(φ) ≤ m⁻¹ φ_{J_m} + N₀/m` for `m ≥ 3`, so it is a uniform limit of functions in
  `H_ℚ(d)` and hence `d`-psh (`isPSH_of_uniform_limit`).
* `thm:c0-pn-ep` (`ProjBerk.hasEnvelopeProperty_of_charZero_of_inputs`): the reductions of
  `rmk:bj-pn-ep-assembly`, step (a)
  (`ProjBerk.hasEnvelopeProperty_of_forall_isPSH_envelope_nat_of_nonpos`),
  and the embedding `k → ℂ` (`lem:c0-embedding`, `nonempty_ringHom_complex`).

## Main results

* `ProjBerk.IsRatPL.exists_shilov_description` (`lem:c0-shilov-description`).
* `ProjBerk.IsRatPL.exists_key_inequality` (`prop:c0-key-inequality`).
* `ProjBerk.IsRatPL.isPSH_envelope_nat_of_nonpos_of_inputs` (`thm:c0-envelope-pl`).
* `ProjBerk.hasEnvelopeProperty_of_ringHom_complex_of_inputs`,
  `ProjBerk.hasEnvelopeProperty_of_charZero_of_inputs` (`thm:c0-pn-ep`).

## Deviations from the blueprint

* `lem:c0-shilov-description` is stated with `γ_w = -φ(w)/c_w` and the index set `Σ` itself; the
  proof uses the comparison form of `lem:bj-shilov` (`IsFiniteRatFS.exists_finset_le_of_le`)
  instead of its `sup`-form.
* In Step 1 of `prop:c0-key-inequality` only the monomials `x^α = xₗ^{(m+2)d - deg P_k}` are used
  (Step 2 needs nothing else), and `W` is the full space `R_{(m+2)d}[t]` instead of its subspace of
  bounded `t`-degree (`cor:c0-base-change-orders`(1) is formalized for arbitrary subspaces). The
  constant is `N₀ = ⌈∑_w |c_w (A_w + 2 γ_w)|⌉₊`, so that `N₀ τ_w ≥ A_w + 2 γ_w` with
  `τ_w = ord_{V_w}(t) = 1/c_w`; the blueprint's `max_w ⌈(A_w + 2|γ_w|)/τ_w⌉` also works.
* The key inequality does not need `φ ≤ 0`; it is used for `φ ≤ 0` only in `thm:c0-envelope-pl`,
  through `P_d(φ) ≤ 0` (`(m+2) Q ≤ m Q`).
* Uniform convergence is applied to the sequence `(j + 3)⁻¹ φ_{J_{j+3}}`.
-/

open scoped NNReal ENNReal Topology Polynomial

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

namespace ProjBerk

/-! ### Auxiliary facts on `ℕ∞ ⊆ EReal` -/

/-- The coercion `ℕ∞ → EReal` on natural numbers. -/
theorem enat_toEReal_natCast (N : ℕ) : ((N : ℕ∞) : EReal) = ((N : ℝ) : EReal) := by
  norm_cast

/-- The coercion `ℕ∞ → EReal` maps `⊤` to `⊤`. -/
theorem enat_toEReal_top : ((⊤ : ℕ∞) : EReal) = ⊤ := by
  simp

/-- The coercion `ℕ∞ → EReal` is an order embedding. -/
theorem enat_toEReal_le_toEReal {x y : ℕ∞} : (x : EReal) ≤ (y : EReal) ↔ x ≤ y := by
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- `x ↦ -c x` is antitone on `ℕ∞ ⊆ EReal` for `c ≥ 0`. -/
theorem neg_mul_enat_antitone {c : ℝ} (hc : 0 ≤ c) {x y : ℕ∞} (h : x ≤ y) :
    -(c : EReal) * (y : EReal) ≤ -(c : EReal) * (x : EReal) := by
  rw [EReal.neg_mul, EReal.neg_mul, EReal.neg_le_neg_iff]
  exact ereal_coe_mul_monotone hc (enat_toEReal_le_toEReal.2 h)

/-- If `-c x = r` with `c > 0`, `x ∈ ℕ∞` and `r ∈ ℝ`, then `x` is finite. -/
theorem exists_eq_natCast_of_neg_mul_eq {c : ℝ} (hc : 0 < c) {x : ℕ∞} {r : ℝ}
    (h : -(c : EReal) * (x : EReal) = (r : EReal)) : ∃ N : ℕ, x = N ∧ -c * N = r := by
  induction x using ENat.recTopCoe with
  | top =>
    rw [enat_toEReal_top, ← EReal.coe_neg, EReal.coe_mul_top_of_neg (neg_neg_of_pos hc)] at h
    exact absurd h.symm (EReal.coe_ne_bot r)
  | coe N =>
    refine ⟨N, rfl, ?_⟩
    rw [enat_toEReal_natCast, ← EReal.coe_neg, ← EReal.coe_mul] at h
    exact_mod_cast h

/-- `m⁻¹ x + y ≤ z ↔ x ≤ m (z - y)` in `EReal`, for real `m > 0`, `y`, `z`. -/
theorem ereal_inv_mul_add_le_iff {m : ℝ} (hm : 0 < m) (x : EReal) (y z : ℝ) :
    ((m⁻¹ : ℝ) : EReal) * x + (y : EReal) ≤ (z : EReal) ↔ x ≤ ((m * (z - y) : ℝ) : EReal) := by
  induction x using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos (inv_pos.2 hm)]
  | top =>
    rw [EReal.coe_mul_top_of_pos (inv_pos.2 hm), EReal.top_add_coe, top_le_iff, top_le_iff]
    exact ⟨fun h => absurd h (EReal.coe_ne_top _), fun h => absurd h (EReal.coe_ne_top _)⟩
  | coe x =>
    rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor
    · intro h
      have := mul_le_mul_of_nonneg_left (show m⁻¹ * x ≤ z - y by linarith) hm.le
      rwa [mul_inv_cancel_left₀ hm.ne'] at this
    · intro h
      have := mul_le_mul_of_nonneg_left h (inv_pos.2 hm).le
      rw [inv_mul_cancel_left₀ hm.ne'] at this
      linarith

variable {k : Type u} [Field k] {n : ℕ}

/-! ### Divisorial points -/

section Divisorial

variable {v : ProjBerk k n} {R' : BirationalDVR k (MvPolynomial (Fin (n + 1)) k)[X]} {c : ℝ}

/-- At a divisorial point `v` with ring `V` and constant `c`, `φ_I(v) = -c ord_V(I)` with
`ord_V(I) = inf_{f ∈ I} ord_V(f)` (`def:c0-dvr`). The infimum is attained since `ℕ∞` is well
ordered. -/
theorem phiIdeal_eq_neg_mul_iInf_ord (hc : 0 < c)
    (hv : ∀ g, Berk.logAbs g (gaussExt v) = -(c : EReal) * (R'.ord g : EReal))
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)[X]) :
    phiIdeal I v = -(c : EReal) * ((⨅ f ∈ I, R'.ord f : ℕ∞) : EReal) := by
  have hinf : (⨅ f ∈ I, R'.ord f) = ⨅ f : I, R'.ord f := by rw [iInf_subtype']
  obtain ⟨f₀, hf₀⟩ := ciInf_mem (fun f : I => R'.ord f)
  refine le_antisymm (iSup₂_le fun g hg => ?_) ?_
  · rw [hv]
    exact neg_mul_enat_antitone hc.le (iInf₂_le g hg)
  · rw [hinf, ← hf₀, ← hv]
    exact le_phiIdeal I v f₀.2

/-- At a divisorial point, `ord_V(t) = τ ∈ ℕ` with `c τ = 1`, since `log|t|_{σ(v)} = -1`. -/
theorem exists_ord_X_eq (hc : 0 < c)
    (hv : ∀ g, Berk.logAbs g (gaussExt v) = -(c : EReal) * (R'.ord g : EReal)) :
    ∃ τ : ℕ, R'.ord (Polynomial.X : (MvPolynomial (Fin (n + 1)) k)[X]) = τ ∧ c * τ = 1 := by
  have h := hv Polynomial.X
  rw [logAbs_X_gaussExt] at h
  obtain ⟨τ, hτ, h'⟩ := exists_eq_natCast_of_neg_mul_eq hc (r := -1) (by rw [← h]; rfl)
  exact ⟨τ, hτ, by linarith⟩

/-- At a divisorial point, `ord_V(xⱼ) = 0` for a coordinate with `|xⱼ|_v = 1`. -/
theorem ord_C_X_eq_zero (hc : 0 < c)
    (hv : ∀ g, Berk.logAbs g (gaussExt v) = -(c : EReal) * (R'.ord g : EReal)) {j : Fin (n + 1)}
    (hj : v.1.val (MvPolynomial.X j) = 1) :
    R'.ord (Polynomial.C (MvPolynomial.X j) : (MvPolynomial (Fin (n + 1)) k)[X]) = 0 := by
  have h := hv (Polynomial.C (MvPolynomial.X j))
  rw [logAbs_C_gaussExt, logAbs_def, hj, ENNReal.coe_one, ENNReal.log_one] at h
  obtain ⟨N, hN, h'⟩ := exists_eq_natCast_of_neg_mul_eq hc (r := 0) (by rw [← h]; rfl)
  have : (N : ℝ) = 0 := by
    have := mul_eq_zero.1 h'
    rcases this with h1 | h1
    · exact absurd (neg_eq_zero.1 h1) hc.ne'
    · exact h1
  rw [hN]
  exact_mod_cast this

end Divisorial

/-! ### Orders and real thresholds -/

/-- `-c x ≤ r ↔ -r/c ≤ x` for `x ∈ ℕ∞ ⊆ EReal`, `c > 0`, `r ∈ ℝ`. -/
theorem neg_mul_enat_le_iff {c : ℝ} (hc : 0 < c) (x : ℕ∞) (r : ℝ) :
    -(c : EReal) * (x : EReal) ≤ (r : EReal) ↔ ((-r / c : ℝ) : EReal) ≤ (x : EReal) := by
  induction x using ENat.recTopCoe with
  | top =>
    rw [enat_toEReal_top, ← EReal.coe_neg, EReal.coe_mul_top_of_neg (neg_neg_of_pos hc)]
    simp
  | coe N =>
    rw [enat_toEReal_natCast, ← EReal.coe_neg, ← EReal.coe_mul, EReal.coe_le_coe_iff,
      EReal.coe_le_coe_iff, div_le_iff₀ hc]
    constructor <;> intro h <;> linarith

/-- A real lower bound `r ≤ x` for `x ∈ ℕ∞` is the lower bound `⌈r⌉₊ ≤ x`. -/
theorem natCeil_le_enat_iff (x : ℕ∞) (r : ℝ) :
    ((⌈r⌉₊ : ℕ) : ℕ∞) ≤ x ↔ (r : EReal) ≤ (x : EReal) := by
  induction x using ENat.recTopCoe with
  | top => simp
  | coe N =>
    rw [enat_toEReal_natCast, EReal.coe_le_coe_iff, Nat.cast_le, Nat.ceil_le]

/-! ### Finitely many valuations define `J_m` (`lem:c0-shilov-description`) -/

section Shilov

variable [IsAlgClosed k] {d : ℕ} {φ : ProjBerk k n → ℝ}

omit [IsAlgClosed k] in
/-- `φ_{(g)} = log|g|_{σ(·)}` for a principal ideal. -/
theorem phiIdeal_span_singleton (g : (MvPolynomial (Fin (n + 1)) k)[X]) (v : ProjBerk k n) :
    phiIdeal (Ideal.span {g}) v = Berk.logAbs g (gaussExt v) := by
  have h := phiIdeal_span_finset v ({g} : Finset (MvPolynomial (Fin (n + 1)) k)[X])
  rwa [Finset.coe_singleton, Finset.sup_singleton] at h

/-- The Shilov step of `lem:c0-shilov-description`: for a rational PL function `φ = ψ₁ - ψ₂` there
is a finite set `Σ ⊆ (ℙⁿ)^div` (the Shilov set of `ψ₁`, `lem:bj-shilov`) such that an element `g` of
`x`-degree `m d` lies in `V_m(φ)` as soon as `log|g|_{σ(w)} ≤ m φ(w)` for `w ∈ Σ`: the function
`m⁻¹ log|g|_{σ(·)} + ψ₂` is a rational FS function, which is `≤ ψ₁` on `Σ`, hence everywhere. -/
theorem IsRatPL.exists_finset_mem_obstacleSpace (hφ : IsRatPL φ) :
    ∃ S : Finset (ProjBerk k n), (∀ w ∈ S, w.IsDivisorial) ∧ ∀ m : ℕ, 0 < m →
      ∀ g : (MvPolynomial (Fin (n + 1)) k)[X], IsXHomogeneous g (m * d) →
        (∀ w ∈ S, Berk.logAbs g (gaussExt w) ≤ (((m : ℝ) * φ w : ℝ) : EReal)) →
          g ∈ obstacleSpace k n d φ m := by
  obtain ⟨a, b, ψ₁, ψ₂, h₁, h₂, hf⟩ := hφ
  obtain ⟨S, -, hSdiv, hle⟩ := h₁.exists_finset_le_of_le
  refine ⟨S, hSdiv, fun m hm g hg hS => ⟨hg, fun v => ?_⟩⟩
  by_cases hg0 : g = 0
  · rw [hg0, Berk.logAbs_zero]
    exact bot_le
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set F : ProjBerk k n → EReal := fun v =>
    (((m : ℝ)⁻¹ : ℝ) : EReal) * Berk.logAbs g (gaussExt v) + ψ₂ v with hF
  have hFS : IsRatFS ((d : ℚ) + b) F := by
    have h := isRatFS_inv_mul_phiIdeal (d := d) hm (I := Ideal.span {g}) (S := {g}) rfl
      (fun g' hg' ℓ => ⟨m * d, le_rfl, by rw [Set.mem_singleton_iff.1 hg']; exact hg ℓ⟩)
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
    simp only [phiIdeal_span_singleton] at h
    exact h.add h₂.1
  have hψ : ∀ {c : ℚ} {ψ : ProjBerk k n → EReal}, IsFiniteRatFS c ψ →
      ∀ v, ψ v = ((ψ v).toReal : EReal) := fun hψ v =>
    (EReal.coe_toReal (hψ.isFS.ne_top v) (hψ.2 v)).symm
  have key : ∀ v, F v ≤ ψ₁ v ↔ Berk.logAbs g (gaussExt v) ≤ (((m : ℝ) * φ v : ℝ) : EReal) := by
    intro v
    simp only [hF]
    rw [hψ h₂ v, hψ h₁ v, ereal_inv_mul_add_le_iff hm', hf v]
  exact (key v).1 (hle _ F hFS (fun w hw => (key w).2 (hS w hw)) v)

/-- **Finitely many valuations define `J_m`** (`lem:c0-shilov-description`, after BJ22
`lem:Shilov`): for a rational PL function `φ` there are finitely many divisorial points `w ∈ Σ`,
with rings `V_w` and constants `c_w > 0` as in `ProjBerk.IsDivisorial`
(`log|g|_{σ(w)} = -c_w ord_{V_w}(g)`), and reals `γ_w = -φ(w)/c_w`, such that for every `m ≥ 1`
`V_m(φ) = {g ∈ R_{md}[t] : ord_{V_w}(g) ≥ m γ_w for all w ∈ Σ}`. -/
theorem IsRatPL.exists_shilov_description (hφ : IsRatPL φ) :
    ∃ (S : Finset (ProjBerk k n)) (V : S → BirationalDVR k (MvPolynomial (Fin (n + 1)) k)[X])
      (c : S → ℚ) (γ : S → ℝ), (∀ w, 0 < c w) ∧
      (∀ w g, Berk.logAbs g (gaussExt w.1) = -((c w : ℝ) : EReal) * ((V w).ord g : EReal)) ∧
      ∀ m : ℕ, 0 < m → ∀ g : (MvPolynomial (Fin (n + 1)) k)[X],
        g ∈ obstacleSpace k n d φ m ↔
          IsXHomogeneous g (m * d) ∧
            ∀ w, (((m : ℝ) * γ w : ℝ) : EReal) ≤ ((V w).ord g : EReal) := by
  obtain ⟨S, hSdiv, hS⟩ := hφ.exists_finset_mem_obstacleSpace (d := d)
  choose V c hc hV using fun w : S => hSdiv w.1 w.2
  have hc' : ∀ w, (0 : ℝ) < c w := fun w => by exact_mod_cast hc w
  refine ⟨S, V, c, fun w => -φ w / c w, hc, hV, fun m hm g => ?_⟩
  have key : ∀ w : S, Berk.logAbs g (gaussExt w.1) ≤ (((m : ℝ) * φ w : ℝ) : EReal) ↔
      (((m : ℝ) * (-φ w / c w) : ℝ) : EReal) ≤ ((V w).ord g : EReal) := fun w => by
    rw [hV, neg_mul_enat_le_iff (hc' w)]
    congr! 2
    ring
  constructor
  · rintro ⟨hg, hgv⟩
    exact ⟨hg, fun w => (key w).1 (hgv w)⟩
  · rintro ⟨hg, hgw⟩
    exact hS m hm g hg fun w hw => (key ⟨w, hw⟩).2 (hgw ⟨w, hw⟩)

end Shilov

/-! ### Extension of scalars of the ideals `J_m` -/

section BaseChange

open Char0

variable [IsAlgClosed k] {d : ℕ} {φ : ProjBerk k n → ℝ} (K' : Type*) [Field K'] [Algebra k K']

/-- **Membership in `J_m K'[x][t]`** (`prop:c0-key-inequality`, end of Step 1): if `V_m(φ)` is cut
out in `R_{md}[t]` by the conditions `ord_{V_w} ≥ m γ_w` (`lem:c0-shilov-description`), then every
`G ∈ K'[x][t]` of `x`-degree `m d` with `ord_{V_{w,K'}}(G) ≥ m γ_w` for all `w` lies in the
extension `J_m K'[x][t]` of `J_m(φ)`. By `cor:c0-base-change-orders`(1), such `G` lie in
`V_m(φ) ⊗_k K'`. -/
theorem mem_map_coneMap_obstacleIdeal {ι : Type*}
    (V : ι → BirationalDVR k (MvPolynomial (Fin (n + 1)) k)[X]) (γ : ι → ℝ) {m : ℕ}
    (hdesc : ∀ g, IsXHomogeneous g (m * d) →
      (∀ w, (((m : ℝ) * γ w : ℝ) : EReal) ≤ ((V w).ord g : EReal)) →
        g ∈ obstacleSpace k n d φ m)
    {G : (MvPolynomial (Fin (n + 1)) K')[X]} (hG : IsXHomogeneous G (m * d))
    (hord : ∀ w, (((m : ℝ) * γ w : ℝ) : EReal) ≤ (((V w).coneBaseChange K').ord G : EReal)) :
    G ∈ (obstacleIdeal k n d φ m).map (coneMap K') := by
  set μ : ι → ℕ∞ := fun w => ((⌈(m : ℝ) * γ w⌉₊ : ℕ) : ℕ∞) with hμ
  have h1 := (BirationalDVR.mem_span_coneMap_ordIdeal_iff K' V μ
    (xHomogeneousSubmodule k n (m * d)) G).1
      ⟨mem_span_coneMap_xHomogeneousSubmodule K' hG,
        fun w => (natCeil_le_enat_iff _ _).2 (hord w)⟩
  have h2 : ((xHomogeneousSubmodule k n (m * d) ⊓ ⨅ w, ((V w).ordIdeal (μ w)).restrictScalars k :
      Submodule k (MvPolynomial (Fin (n + 1)) k)[X]) : Set (MvPolynomial (Fin (n + 1)) k)[X]) ⊆
        obstacleSpace k n d φ m := by
    intro f hf
    rw [SetLike.mem_coe, Submodule.mem_inf, Submodule.mem_iInf] at hf
    refine hdesc f hf.1 fun w => ?_
    have := hf.2 w
    rw [Submodule.restrictScalars_mem, BirationalDVR.mem_ordIdeal] at this
    exact (natCeil_le_enat_iff _ _).1 this
  have h3 : Submodule.span K' (coneMap K' '' (obstacleSpace k n d φ m :
      Set (MvPolynomial (Fin (n + 1)) k)[X])) ≤
        ((obstacleIdeal k n d φ m).map (coneMap K')).restrictScalars K' := by
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact Ideal.mem_map_of_mem _ (mem_obstacleIdeal_of_mem hf)
  exact h3 (Submodule.span_mono (Set.image_mono h2) h1)

end BaseChange

/-! ### The key inequality (`prop:c0-key-inequality`) -/

section KeyInequalityAux

/-- `J_q` is generated by finitely many bihomogeneous elements `s t^ℓ` of `V_q(φ)`
(`lem:bj-Jm-basic`; `R[t]` is Noetherian). -/
theorem exists_finset_obstacleIdeal_eq_span (d : ℕ) (φ : ProjBerk k n → ℝ) (q : ℕ) :
    ∃ T : Finset (MvPolynomial (Fin (n + 1)) k)[X],
      (∀ f ∈ T, f ∈ obstacleSpace k n d φ q ∧ ∃ ℓ s, f = Polynomial.monomial ℓ s) ∧
        obstacleIdeal k n d φ q = Ideal.span (T : Set (MvPolynomial (Fin (n + 1)) k)[X]) := by
  have hfg : (Ideal.span {g | g ∈ obstacleSpace k n d φ q ∧
      ∃ ℓ s, g = Polynomial.monomial ℓ s}).FG := by
    rw [← obstacleIdeal_eq_span_monomial]
    exact IsNoetherian.noetherian _
  obtain ⟨T, hTS, hT⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  exact ⟨T, fun f hf => hTS hf, obstacleIdeal_eq_span_monomial.trans hT⟩

/-- `ord_V((T)) = min_{f ∈ T} ord_V(f)` for the ideal generated by a finite set `T`. -/
theorem iInf_ord_span_finset (R' : BirationalDVR k (MvPolynomial (Fin (n + 1)) k)[X])
    (T : Finset (MvPolynomial (Fin (n + 1)) k)[X]) :
    ⨅ f ∈ Ideal.span (T : Set (MvPolynomial (Fin (n + 1)) k)[X]), R'.ord f =
      ⨅ f : T, R'.ord f := by
  refine le_antisymm (le_iInf fun f => iInf₂_le f.1 (Ideal.subset_span f.2))
    (le_iInf₂ fun f hf => ?_)
  have hle : Ideal.span (T : Set (MvPolynomial (Fin (n + 1)) k)[X]) ≤
      R'.ordIdeal (⨅ f : T, R'.ord f) :=
    Ideal.span_le.2 fun g hg => R'.mem_ordIdeal.2 (iInf_le (fun f : T => R'.ord f)
      ⟨g, hg⟩)
  exact R'.mem_ordIdeal.1 (hle hf)

/-- A real lower bound for every member of a family is a lower bound for its infimum in `ℕ∞`. -/
theorem le_iInf_enat_toEReal {ι : Type*} {x : ι → ℕ∞} {r : ℝ}
    (h : ∀ i, (r : EReal) ≤ (x i : EReal)) : (r : EReal) ≤ ((⨅ i, x i : ℕ∞) : EReal) :=
  (natCeil_le_enat_iff _ _).1 (le_iInf fun i => (natCeil_le_enat_iff _ _).2 (h i))

/-- Step 1 of `prop:c0-key-inequality`, the valuative bound with constants: from
`ord(g) ≥ q γ` and `ord(P) > (m/q) ord(g) - A` we get `ord(P) > m γ - A`. -/
theorem keyIneq_valuative_arith {m q : ℕ} (hq : 0 < q) {γ A : ℝ} {oG : ℕ∞}
    (hoG : (((q : ℝ) * γ : ℝ) : EReal) ≤ (oG : EReal)) {y : EReal}
    (hy : ((((m : ℝ) / q : ℝ)) : EReal) * (oG : EReal) - (A : EReal) < y) :
    ((((m : ℝ) * γ - A : ℝ)) : EReal) < y := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  refine lt_of_le_of_lt ?_ hy
  rw [EReal.coe_sub]
  refine EReal.sub_le_sub ?_ le_rfl
  have h := ereal_coe_mul_monotone (c := (m : ℝ) / q) (by positivity) hoG
  dsimp only at h
  refine le_trans (le_of_eq ?_) h
  rw [← EReal.coe_mul]
  congr 1
  field_simp

/-- Step 1 of `prop:c0-key-inequality`, the order of `t^{N₀} x^α P`: if `c τ = 1`,
`N₀ ≥ c (A + 2γ)` and `ord(P) > m γ - A`, then `N₀ τ + x + ord(P) ≥ (m + 2) γ`. -/
theorem keyIneq_step_one_arith {c A γ : ℝ} {m N₀ τ : ℕ} (hcτ : c * τ = 1)
    (hN₀ : c * (A + 2 * γ) ≤ N₀)
    {p : ℕ∞} (hp : ((((m : ℝ) * γ - A : ℝ)) : EReal) < (p : EReal)) (x : ℕ∞) :
    ((((m + 2 : ℕ) : ℝ) * γ : ℝ) : EReal) ≤ ((N₀ • (τ : ℕ∞) + x + p : ℕ∞) : EReal) := by
  induction p using ENat.recTopCoe with
  | top => simp
  | coe P =>
    induction x using ENat.recTopCoe with
    | top => simp
    | coe X =>
      rw [enat_toEReal_natCast] at hp
      have hp' : (m : ℝ) * γ - A < P := EReal.coe_lt_coe_iff.1 hp
      have hτ : A + 2 * γ ≤ N₀ * τ := by
        have h := mul_le_mul_of_nonneg_right hN₀ (Nat.cast_nonneg τ)
        calc A + 2 * γ = c * (A + 2 * γ) * τ := by
              rw [mul_comm c, mul_assoc, hcτ, mul_one]
          _ ≤ N₀ * τ := h
      have : N₀ • (τ : ℕ∞) + (X : ℕ∞) + (P : ℕ∞) = ((N₀ * τ + X + P : ℕ) : ℕ∞) := by
        push_cast
        rw [nsmul_eq_mul]
      rw [this, enat_toEReal_natCast, EReal.coe_le_coe_iff]
      push_cast
      have hX : (0 : ℝ) ≤ X := Nat.cast_nonneg X
      linarith

/-- Step 2 of `prop:c0-key-inequality`, in terms of `φ_I(v) = -c ord_V(I)`: if `c τ = 1` and
`q ord(J_{m+2}) ≤ q N₀ τ + m ord(J_q)` then `(m/q) φ_{J_q}(v) ≤ φ_{J_{m+2}}(v) + N₀`. -/
theorem keyIneq_step_two_arith {c : ℝ} (hc : 0 < c) {m q N₀ τ : ℕ} (hm : 0 < m) (hq : 0 < q)
    (hcτ : c * τ = 1) {oJ oq : ℕ∞} (h : q • oJ ≤ q • (N₀ • (τ : ℕ∞)) + m • oq) :
    ((((m : ℝ) / q : ℝ)) : EReal) * (-(c : EReal) * (oq : EReal)) ≤
      -(c : EReal) * (oJ : EReal) + ((N₀ : ℝ) : EReal) := by
  have hmq : (0 : ℝ) < (m : ℝ) / q := by positivity
  induction oq using ENat.recTopCoe with
  | top =>
    rw [enat_toEReal_top, ← EReal.coe_neg, EReal.coe_mul_top_of_neg (neg_neg_of_pos hc),
      EReal.coe_mul_bot_of_pos hmq]
    exact bot_le
  | coe Q =>
    induction oJ using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : q • (⊤ : ℕ∞) ≤ ((q * (N₀ * τ) + m * Q : ℕ) : ℕ∞) := by
        refine h.trans (le_of_eq ?_)
        push_cast
        simp only [nsmul_eq_mul]
      rw [nsmul_eq_mul, ENat.mul_top (by exact_mod_cast hq.ne')] at h'
      exact absurd h' (not_le.2 (ENat.natCast_lt_top _))
    | coe J =>
      have h' : q * J ≤ q * (N₀ * τ) + m * Q := by
        have : ((q * J : ℕ) : ℕ∞) ≤ ((q * (N₀ * τ) + m * Q : ℕ) : ℕ∞) := by
          refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
          · push_cast
            simp only [nsmul_eq_mul]
          · push_cast
            simp only [nsmul_eq_mul]
        exact_mod_cast this
      have h'' : (q : ℝ) * J ≤ q * (N₀ * τ) + m * Q := by exact_mod_cast h'
      rw [enat_toEReal_natCast, enat_toEReal_natCast, ← EReal.coe_neg, ← EReal.coe_mul,
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have hq' : (0 : ℝ) < q := Nat.cast_pos.2 hq
      have key : c * J ≤ N₀ + (m : ℝ) / q * (c * Q) := by
        have h3 := mul_le_mul_of_nonneg_left h'' (show (0 : ℝ) ≤ c / q by positivity)
        have e1 : c / q * (q * J) = c * J := by field_simp
        have e2 : c / q * (q * (N₀ * τ) + m * Q) = N₀ * (c * τ) + (m : ℝ) / q * (c * Q) := by
          field_simp
        rw [e1, e2, hcτ, mul_one] at h3
        exact h3
      nlinarith

/-- `cK |g|^{m/q} ≤ |P|` gives `cK^q |g|^m ≤ |P|^q`, with `|g| = √N`. -/
theorem keyIneq_pow_bound {N R cK : ℝ} (hN : 0 ≤ N) (hcK : 0 < cK) {m q : ℕ} (hq : 0 < q)
    (h : cK * N ^ ((m : ℝ) / q / 2) ≤ R) : cK ^ q * Real.sqrt N ^ m ≤ R ^ q := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have e : cK ^ q * Real.sqrt N ^ m = (cK * N ^ ((m : ℝ) / q / 2)) ^ q := by
    rw [mul_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast (N ^ ((m : ℝ) / q / 2)),
      ← Real.rpow_mul hN, ← Real.rpow_natCast (N ^ (1 / 2 : ℝ)), ← Real.rpow_mul hN]
    congr 2
    field_simp
  rw [e]
  exact pow_le_pow_left₀ (by positivity) h q

end KeyInequalityAux

section KeyInequality

open Char0

variable [IsAlgClosed k]

/-- **The key inequality** (`prop:c0-key-inequality`). Let `ι : k → ℂ` be a field embedding, `d > 0`
and `φ` a rational PL function on `(ℙⁿ)^an`. Given the valuative bound and the Bergman lower bound
over `ℂ` (`Char0.ValuativeUpperBound`, `Char0.BergmanLowerBound`), there is `N₀ ∈ ℕ` such that
`(m/q) φ_{J_q} ≤ φ_{J_{m+2}} + N₀` on `(ℙⁿ)^an` for all `m, q ≥ 1`, where `J_m = J_m(φ)`.

Proof (blueprint): let `Σ`, `V_w`, `c_w`, `γ_w` be as in `lem:c0-shilov-description`, `A_w` the
constants of the valuative bound at `V_{w,ℂ}`, `τ_w = ord_{V_w}(t) = 1/c_w`, and
`N₀ ≥ c_w (A_w + 2 γ_w)`. The Bergman lower bound for generators `g_j` of `J_q` gives `P_k`.
Step 1: `t^{N₀} xₗ^{(m+2)d - deg P_k} P_k ∈ J_{m+2} ℂ[x][t]` (valuative bound at the `V_{w,ℂ}` and
`cor:c0-base-change-orders`(1)). Step 2: at a divisorial point `v` with ring `V`, choose `xₗ` with
`ord_V(xₗ) = 0`; Step 1 and `cor:c0-base-change-orders`(2) give
`ord_V(J_{m+2}) ≤ N₀ ord_V(t) + ord_{V_ℂ}(P)`, and `cor:c0-valuative-upper` gives
`q ord_{V_ℂ}(P) ≤ m ord_V(J_q)`. Step 3: `(m/q) φ_{J_q}` is psh and `φ_{J_{m+2}} + N₀` is
continuous, so the inequality on `(ℙⁿ)^div` extends to `(ℙⁿ)^an` by divisorial comparison
(`thm:bj-divisorial-comparison`). -/
theorem IsRatPL.exists_key_inequality (ι : k →+* ℂ) (hval : ValuativeUpperBound)
    (hberg : BergmanLowerBound) {d : ℕ} (hd : 0 < d) {φ : ProjBerk k n → ℝ} (hφ : IsRatPL φ) :
    ∃ N₀ : ℕ, ∀ m q : ℕ, 0 < m → 0 < q → ∀ v : ProjBerk k n,
      ((((m : ℝ) / q : ℝ)) : EReal) * phiIdeal (obstacleIdeal k n d φ q) v ≤
        phiIdeal (obstacleIdeal k n d φ (m + 2)) v + ((N₀ : ℝ) : EReal) := by
  let _ : Algebra k ℂ := ι.toAlgebra
  obtain ⟨S, V, c, γ, hc, hV, hdesc⟩ := hφ.exists_shilov_description (d := d)
  have hc' : ∀ w, (0 : ℝ) < c w := fun w => by exact_mod_cast hc w
  choose A hA using fun w : S => hval.valuative_bound n ((V w).coneMvBaseChange ℂ)
  choose τ hτ hcτ using fun w : S => exists_ord_X_eq (hc' w) (hV w)
  set N₀ : ℕ := ⌈∑ w : S, |(c w : ℝ) * (A w + 2 * γ w)|⌉₊
  have hN₀ : ∀ w, (c w : ℝ) * (A w + 2 * γ w) ≤ N₀ := fun w =>
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun w => |(c w : ℝ) * (A w + 2 * γ w)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ w)).trans (Nat.le_ceil _))
  refine ⟨N₀, fun m q hm hq v => ?_⟩
  obtain ⟨C₀, hC₀⟩ := hφ.exists_abs_le
  have hφC : ∀ v, -C₀ ≤ φ v := fun v => neg_le_of_abs_le (hC₀ v)
  -- generators of `J_q` and their images over `ℂ`
  obtain ⟨T, hT, hTspan⟩ := exists_finset_obstacleIdeal_eq_span d φ q
  have hcone_inj : Function.Injective (coneMap (n := n) ℂ : (MvPolynomial (Fin (n + 1)) k)[X] →
      (MvPolynomial (Fin (n + 1)) ℂ)[X]) :=
    Polynomial.map_injective _ (MvPolynomial.map_injective _ (algebraMap k ℂ).injective)
  obtain ⟨g, hg⟩ : ∃ g : Fin T.card → MvPolynomial (Fin (n + 2)) ℂ, ∀ i,
      g i = coneMvEquiv ℂ n (coneMap ℂ ((T.equivFin.symm i : T) :
        (MvPolynomial (Fin (n + 1)) k)[X])) := ⟨_, fun i => rfl⟩
  have hgbi : ∀ i, ∃ l, IsXTBihomogeneous (q * d) l (g i) := by
    intro i
    obtain ⟨hfV, ℓ, s₀, hfs⟩ := hT _ (T.equivFin.symm i).2
    have hs₀ : s₀.IsHomogeneous (q * d) := by
      have := hfV.1 ℓ
      rwa [hfs, Polynomial.coeff_monomial, if_pos rfl] at this
    refine ⟨ℓ, ?_⟩
    rw [hg, hfs, coneMap_apply, Polynomial.map_monomial]
    exact isXTBihomogeneous_coneMvEquiv_monomial (hs₀.map _) ℓ
  have hgne : ∃ i, g i ≠ 0 := by
    by_contra h
    push Not at h
    apply obstacleIdeal_ne_bot (d := d) hφC q
    rw [hTspan, Ideal.span_eq_bot]
    intro f hf
    have := h (T.equivFin ⟨f, hf⟩)
    rw [hg, Equiv.symm_apply_apply] at this
    exact hcone_inj ((coneMvEquiv ℂ n).injective (this.trans (map_zero _).symm) |>.trans
      (map_zero _).symm)
  -- the Bergman lower bound
  obtain ⟨s, hs, hlow⟩ := hberg.exists_lower_bound n (Fin T.card) g (q * d) hgbi hgne
    ((m : ℝ) / q) (by positivity)
  -- Step 1: `t^{N₀} xₗ^{(m+2)d - e} P ∈ J_{m+2} ℂ[x][t]` for `P` of `x`-degree `e`
  have step1 : ∀ P ∈ s, ∃ e : ℕ, ∀ l : Fin (n + 1),
      (Polynomial.X : (MvPolynomial (Fin (n + 1)) ℂ)[X]) ^ N₀ *
        Polynomial.C (MvPolynomial.X l) ^ ((m + 2) * d - e) *
          MvPolynomial.finSuccEquiv ℂ (n + 1) P ∈
        (obstacleIdeal k n d φ (m + 2)).map (coneMap ℂ) := by
    intro P hP
    obtain ⟨hdeg, hsq, e, he⟩ := hs P hP
    refine ⟨e, fun l => ?_⟩
    by_cases hP0 : P = 0
    · rw [hP0, map_zero, mul_zero]
      exact Ideal.zero_mem _
    have heP : e ≤ (m + 2) * d := by
      obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.1 hP0
      have h1 := he hμ
      rw [weight_xWeightFin] at h1
      have h2 := hdeg μ (MvPolynomial.mem_support_iff.2 hμ)
      rw [h1] at h2
      have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
      have h3 : (m : ℝ) / q * ((q * d : ℕ) : ℝ) = m * d := by push_cast; field_simp
      rw [h3] at h2
      have h4 : (e : ℝ) ≤ ((m * d + 2 : ℕ) : ℝ) := by push_cast; linarith
      have h5 := Nat.cast_le.1 h4
      nlinarith
    have hhom : IsXHomogeneous ((Polynomial.X : (MvPolynomial (Fin (n + 1)) ℂ)[X]) ^ N₀ *
        Polynomial.C (MvPolynomial.X l) ^ ((m + 2) * d - e) *
          MvPolynomial.finSuccEquiv ℂ (n + 1) P) ((m + 2) * d) := by
      have h1 : IsXHomogeneous (Polynomial.X : (MvPolynomial (Fin (n + 1)) ℂ)[X]) 0 := by
        simpa using IsXHomogeneous.C_mul_X_pow
          (MvPolynomial.isHomogeneous_one (Fin (n + 1)) ℂ) 1
      have h2 : IsXHomogeneous (Polynomial.C (MvPolynomial.X l) :
          (MvPolynomial (Fin (n + 1)) ℂ)[X]) 1 := by
        simpa using IsXHomogeneous.C_mul_X_pow
          (MvPolynomial.isHomogeneous_X ℂ l) 0
      have h3 := ((h1.pow N₀).mul (h2.pow ((m + 2) * d - e))).mul
        (isXHomogeneous_finSuccEquiv_iff.2 he)
      convert h3 using 1
      omega
    refine mem_map_coneMap_obstacleIdeal ℂ V γ
      (fun f hf hfw => (hdesc (m + 2) (by omega) f).2 ⟨hf, hfw⟩) hhom fun w => ?_
    -- the orders at `V_{w,ℂ}`
    have hvb := hA w (Fin T.card) g hgne ((m : ℝ) / q) (by positivity) P hsq
    have hoG : (((q : ℝ) * γ w : ℝ) : EReal) ≤
        ((⨅ i, ((V w).coneMvBaseChange ℂ).ord (g i) : ℕ∞) : EReal) := by
      refine le_iInf_enat_toEReal fun i => ?_
      rw [hg, BirationalDVR.ord_coneMvBaseChange_coneMap]
      exact ((hdesc q hq _).1 (hT _ (T.equivFin.symm i).2).1).2 w
    have hP := keyIneq_valuative_arith hq hoG hvb
    rw [BirationalDVR.ord_coneMvBaseChange] at hP
    rw [BirationalDVR.ord_mul, BirationalDVR.ord_mul, BirationalDVR.ord_pow,
      BirationalDVR.ord_pow]
    have hX : ((V w).coneBaseChange ℂ).ord (Polynomial.X : (MvPolynomial (Fin (n + 1)) ℂ)[X]) =
        τ w := by
      rw [← hτ w, ← BirationalDVR.ord_coneBaseChange_map (V w) ℂ, coneMap_apply,
        Polynomial.map_X]
    rw [hX]
    exact keyIneq_step_one_arith (hcτ w) (hN₀ w) hP _
  -- Step 3: divisorial comparison
  have hu : IsPSH (((m : ℚ) * d : ℚ) : ℝ) fun v =>
      ((((m : ℝ) / q : ℝ)) : EReal) * phiIdeal (obstacleIdeal k n d φ q) v := by
    have h := ((isFiniteRatFS_obstacleIdeal (d := d) hφC hq).smul
      (c := (m : ℚ)) (by exact_mod_cast hm)).isRatFS.isPSH
    convert h using 2 with v
    rw [ereal_coe_mul_coe_mul]
    congr 2
  have husc : UpperSemicontinuous fun v =>
      phiIdeal (obstacleIdeal k n d φ (m + 2)) v + ((N₀ : ℝ) : EReal) :=
    ((continuous_ereal_add_coe _).comp (continuous_phiIdeal _)).upperSemicontinuous
  have htop : ∀ v, phiIdeal (obstacleIdeal k n d φ (m + 2)) v + ((N₀ : ℝ) : EReal) ≠ ⊤ :=
    fun v => (EReal.add_lt_top (ne_top_of_le_ne_top EReal.zero_ne_top (phiIdeal_le_zero _ v))
      (EReal.coe_ne_top _)).ne
  refine hu.le_of_forall_isDivisorial_le husc htop (fun v hv => ?_) v
  -- Step 2: at a divisorial point `v`
  obtain ⟨R', c₁, hc₁, hR'⟩ := hv
  have hc₁' : (0 : ℝ) < c₁ := by exact_mod_cast hc₁
  obtain ⟨τ', hτ', hcτ'⟩ := exists_ord_X_eq hc₁' hR'
  obtain ⟨l, hl⟩ := exists_val_X_eq_one v
  have hl0 := ord_C_X_eq_zero hc₁' hR' hl
  rw [phiIdeal_eq_neg_mul_iInf_ord hc₁' hR', phiIdeal_eq_neg_mul_iInf_ord hc₁' hR']
  refine keyIneq_step_two_arith hc₁' hm hq hcτ' ?_
  have hJ : ∀ P ∈ s, ⨅ f ∈ obstacleIdeal k n d φ (m + 2), R'.ord f ≤
      N₀ • (τ' : ℕ∞) + (R'.coneMvBaseChange ℂ).ord P := by
    intro P hP
    obtain ⟨e, he⟩ := step1 P hP
    rw [← BirationalDVR.iInf_ord_coneBaseChange_map R' ℂ]
    refine (iInf₂_le _ (he l)).trans (le_of_eq ?_)
    have hX : (R'.coneBaseChange ℂ).ord (Polynomial.X : (MvPolynomial (Fin (n + 1)) ℂ)[X]) =
        τ' := by
      rw [← hτ', ← BirationalDVR.ord_coneBaseChange_map R' ℂ, coneMap_apply, Polynomial.map_X]
    have hCX : (R'.coneBaseChange ℂ).ord (Polynomial.C (MvPolynomial.X l) :
        (MvPolynomial (Fin (n + 1)) ℂ)[X]) = 0 := by
      rw [← hl0, ← BirationalDVR.ord_coneBaseChange_map R' ℂ, coneMap_apply, Polynomial.map_C,
        MvPolynomial.map_X]
    rw [BirationalDVR.ord_mul, BirationalDVR.ord_mul, BirationalDVR.ord_pow,
      BirationalDVR.ord_pow, hX, hCX, smul_zero, add_zero, BirationalDVR.ord_coneMvBaseChange]
  have hJ' : ⨅ f ∈ obstacleIdeal k n d φ (m + 2), R'.ord f ≤
      N₀ • (τ' : ℕ∞) + ⨅ P : s, (R'.coneMvBaseChange ℂ).ord P := by
    rw [ENat.add_iInf]
    exact le_iInf fun P => hJ P.1 P.2
  have hK : ∀ K : Set (Fin (n + 2) → ℂ), IsCompact K → ∃ cK : ℝ, 0 < cK ∧ ∀ y ∈ K,
      cK * Real.sqrt (normSqFam g y) ^ m ≤
        Real.sqrt (normSqFam (fun P : s => (P : MvPolynomial (Fin (n + 2)) ℂ)) y) ^ q := by
    intro K hK
    obtain ⟨cK, hcK, hy⟩ := hlow K hK
    refine ⟨cK ^ q, pow_pos hcK q, fun y hyK => ?_⟩
    have e : normSqFam (fun P : s => (P : MvPolynomial (Fin (n + 2)) ℂ)) y =
        ∑ P ∈ s, ‖MvPolynomial.eval y P‖ ^ 2 :=
      Finset.sum_coe_sort s (fun P => ‖MvPolynomial.eval y P‖ ^ 2)
    rw [e]
    exact keyIneq_pow_bound (normSqFam_nonneg g y) hcK hq (hy y hyK)
  have hup := hval.valuative_upper n s (Fin T.card) (fun P : s => P.1) g hgne m q hm hq hK
    (R'.coneMvBaseChange ℂ)
  have hgo : ⨅ i, (R'.coneMvBaseChange ℂ).ord (g i) =
      ⨅ f ∈ obstacleIdeal k n d φ q, R'.ord f := by
    simp_rw [hg, BirationalDVR.ord_coneMvBaseChange_coneMap]
    rw [hTspan, iInf_ord_span_finset]
    exact T.equivFin.symm.iInf_comp (g := fun f : T => R'.ord f)
  rw [hgo] at hup
  calc q • ⨅ f ∈ obstacleIdeal k n d φ (m + 2), R'.ord f
      ≤ q • (N₀ • (τ' : ℕ∞) + ⨅ P : s, (R'.coneMvBaseChange ℂ).ord P) :=
        nsmul_le_nsmul_right hJ' q
    _ = q • (N₀ • (τ' : ℕ∞)) + q • ⨅ P : s, (R'.coneMvBaseChange ℂ).ord P := smul_add _ _ _
    _ ≤ q • (N₀ • (τ' : ℕ∞)) + m • ⨅ f ∈ obstacleIdeal k n d φ q, R'.ord f :=
        add_le_add_right hup _

end KeyInequality

/-! ### Envelopes of PL obstacles (`thm:c0-envelope-pl`) -/

section EnvelopePL

open Char0

variable [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- `Q = P_d(φ) ≤ m'⁻¹ (φ_{J_{m'}} + N₀)` for `m' ≥ 3`, from the key inequality with `m = m' - 2`
and `φ_{J_q} ≤ 0` (`thm:c0-envelope-pl`). -/
theorem envelope_le_inv_mul_phiIdeal_add {d : ℕ} (hd : 0 < d) {φ : ProjBerk k n → ℝ}
    (hφ : LowerSemicontinuous φ) (hφ0 : φ triv ≤ 0) {N₀ : ℕ}
    (hN₀ : ∀ m q : ℕ, 0 < m → 0 < q → ∀ v : ProjBerk k n,
      ((((m : ℝ) / q : ℝ)) : EReal) * phiIdeal (obstacleIdeal k n d φ q) v ≤
        phiIdeal (obstacleIdeal k n d φ (m + 2)) v + ((N₀ : ℝ) : EReal))
    (j : ℕ) (v : ProjBerk k n) :
    envelope (d : ℝ) (fun w => (φ w : EReal)) v ≤
      (((((j + 3 : ℕ) : ℝ))⁻¹ : ℝ) : EReal) * phiIdeal (obstacleIdeal k n d φ (j + 3)) v +
        ((((N₀ : ℝ) / ((j + 3 : ℕ) : ℝ)) : ℝ) : EReal) := by
  rw [envelope_eq_iSup_obstacleIdeal hd hφ hφ0 v]
  refine iSup₂_le fun q hq => ?_
  have hj : (0 : ℝ) < ((j + 3 : ℕ) : ℝ) := by positivity
  have hq' : (0 : ℝ) < q := Nat.cast_pos.2 hq
  have h1 := hN₀ (j + 1) q (Nat.succ_pos j) hq v
  have h2 : (((((j + 3 : ℕ) : ℝ) / q : ℝ)) : EReal) * phiIdeal (obstacleIdeal k n d φ q) v ≤
      ((((((j + 1 : ℕ) : ℝ)) / q : ℝ)) : EReal) * phiIdeal (obstacleIdeal k n d φ q) v :=
    ereal_coe_mul_le_of_nonpos (by positivity)
      (div_le_div_of_nonneg_right (by norm_cast; omega) hq'.le) (phiIdeal_le_zero _ v)
  have h3 := ereal_coe_mul_monotone (inv_pos.2 hj).le (h2.trans h1)
  dsimp only at h3
  rw [ereal_coe_mul_coe_mul, ereal_coe_mul_add (inv_pos.2 hj).le, ← EReal.coe_mul] at h3
  convert h3 using 3
  · field_simp
  · field_simp

/-- **Envelopes of PL obstacles in characteristic `0`** (`thm:c0-envelope-pl`), given the analytic
inputs: for a field embedding `k → ℂ`, `d > 0` and a rational PL function `φ ≤ 0`, the functions
`m⁻¹ φ_{J_m}` converge uniformly to `P_d(φ)` (`|P_d(φ) - m⁻¹ φ_{J_m}| ≤ N₀/m` for `m ≥ 3`), hence
`P_d(φ)` is `d`-psh (closedness of `PSH(d)` under uniform limits, BJ22 `thm:PSH`(ii)). -/
theorem IsRatPL.isPSH_envelope_nat_of_nonpos_of_inputs (ι : k →+* ℂ)
    (hval : ValuativeUpperBound) (hberg : BergmanLowerBound) {d : ℕ} (hd : 0 < d)
    {φ : ProjBerk k n → ℝ} (hφ : IsRatPL φ) (hφ0 : ∀ v, φ v ≤ 0) :
    IsPSH (d : ℝ) (envelope (d : ℝ) fun v => (φ v : EReal)) := by
  obtain ⟨N₀, hN₀⟩ := hφ.exists_key_inequality ι hval hberg hd
  obtain ⟨C₀, hC₀⟩ := hφ.exists_abs_le
  have hC : ∀ v, -C₀ ≤ φ v := fun v => neg_le_of_abs_le (hC₀ v)
  have hlsc := hφ.continuous.lowerSemicontinuous
  have hw : ∀ j : ℕ, IsPSH (d : ℝ) fun v =>
      (((((j + 3 : ℕ) : ℝ))⁻¹ : ℝ) : EReal) * phiIdeal (obstacleIdeal k n d φ (j + 3)) v :=
    fun j => by
      have h := (isFiniteRatFS_obstacleIdeal (d := d) hC (Nat.succ_pos (j + 2))).isRatFS.isPSH
      rwa [Rat.cast_natCast] at h
  refine isPSH_of_uniform_limit (l := atTop) hw fun ε hε => ?_
  filter_upwards [eventually_ge_atTop ⌈(N₀ : ℝ) / ε⌉₊] with j hj v
  refine ⟨(inv_mul_phiIdeal_obstacleIdeal_le_envelope (Nat.succ_pos _) v).trans
    (ereal_le_add_coe hε.le _), (envelope_le_inv_mul_phiIdeal_add hd hlsc (hφ0 triv) hN₀ j v).trans
      (add_le_add_right (EReal.coe_le_coe_iff.2 ?_) _)⟩
  have hj3 : (0 : ℝ) < ((j + 3 : ℕ) : ℝ) := by positivity
  rw [div_le_iff₀ hj3]
  have h1 : (N₀ : ℝ) / ε ≤ j := (Nat.le_ceil _).trans (by exact_mod_cast hj)
  rw [div_le_iff₀ hε] at h1
  push_cast
  nlinarith

end EnvelopePL

/-! ### The envelope property (`thm:c0-pn-ep`) -/

section Reduction

/-- **Reduction to integral classes and nonpositive obstacles** (`rmk:bj-pn-ep-assembly`, step (a),
as in `thm:c0-pn-ep`): if `P_d(φ)` is `d`-psh for all `d ∈ ℤ_{>0}` and all rational PL `φ ≤ 0`, then
every `θ ≥ 0` has the envelope property. By `lem:bj-envppty` it suffices to treat rational
`a > 0`; by the envelope criterion `prop:bj-envelope-criterion` it suffices that `P_a(φ)` is
`a`-psh for rational PL `φ`; with `a = d/m`, `P_a(φ) = m⁻¹ P_d(m φ)` (`envelope_mul`) and
`P_d(ψ) = P_d(ψ - N) + N` (`envelope_add_const`). -/
theorem hasEnvelopeProperty_of_forall_isPSH_envelope_nat_of_nonpos
    (H : ∀ d : ℕ, 0 < d → ∀ φ : ProjBerk k n → ℝ, IsRatPL φ → (∀ v, φ v ≤ 0) →
      IsPSH (d : ℝ) (envelope (d : ℝ) fun v => (φ v : EReal)))
    {θ : ℝ} (hθ : 0 ≤ θ) : HasEnvelopeProperty k n θ := by
  -- integral classes, arbitrary obstacles: subtract a constant
  have Hnat : ∀ d : ℕ, 0 < d → ∀ φ : ProjBerk k n → ℝ, IsRatPL φ →
      IsPSH (d : ℝ) (envelope (d : ℝ) fun v => (φ v : EReal)) := by
    intro d hd φ hφ
    obtain ⟨C₀, hC₀⟩ := hφ.exists_abs_le
    obtain ⟨N, hN⟩ := exists_nat_ge C₀
    set ψ : ProjBerk k n → ℝ := fun v => φ v - N with hψ_def
    have hψ : IsRatPL ψ := by simpa using hφ.sub (isRatPL_const (N : ℚ))
    have hψ0 : ∀ v, ψ v ≤ 0 := fun v => by
      simp only [hψ_def]
      linarith [le_abs_self (φ v), hC₀ v]
    have h := (H d hd ψ hψ hψ0).add_const (N : ℝ)
    have e := envelope_add_const (θ := (d : ℝ)) (fun v => (ψ v : EReal)) (N : ℝ)
    have e2 : (fun v => (ψ v : EReal) + ((N : ℝ) : EReal)) = fun v => (φ v : EReal) := by
      funext v
      rw [← EReal.coe_add, hψ_def, sub_add_cancel]
    rw [e2] at e
    rw [e]
    exact h
  -- rational classes: rescale
  have Hrat : ∀ a : ℚ, 0 < a → ∀ φ : ProjBerk k n → ℝ, IsRatPL φ →
      IsPSH (a : ℝ) (envelope (a : ℝ) fun v => (φ v : EReal)) := by
    intro a ha φ hφ
    have hm : (0 : ℝ) < a.den := by exact_mod_cast a.den_pos
    have hd : 0 < a.num.toNat := by have := Rat.num_pos.2 ha; omega
    have hmd : (a.den : ℝ) * a = (a.num.toNat : ℝ) := by
      have h1 : ((a.num.toNat : ℕ) : ℤ) = a.num := Int.toNat_of_nonneg (Rat.num_nonneg.2 ha.le)
      have h3 : ((a.den : ℚ) * a : ℚ) = ((a.num.toNat : ℕ) : ℚ) := by
        rw [Rat.den_mul_eq_num]
        exact_mod_cast h1.symm
      exact_mod_cast h3
    have hψ : IsRatPL fun v => (a.den : ℝ) * φ v := by simpa using hφ.smul (a.den : ℚ)
    have h := Hnat _ hd _ hψ
    have e := envelope_mul (θ := (a : ℝ)) (fun v => (φ v : EReal)) hm
    have e2 : (fun v => ((a.den : ℝ) : EReal) * (φ v : EReal)) =
        fun v => (((a.den : ℝ) * φ v : ℝ) : EReal) := by
      funext v
      rw [EReal.coe_mul]
    rw [e2, hmd] at e
    rw [e, ← hmd] at h
    exact (isPSH_smul_iff hm).1 h
  exact hasEnvelopeProperty_of_forall_rat_gt fun a ha =>
    hasEnvelopeProperty_of_forall_isRatPL fun φ hφ =>
      Hrat a (by exact_mod_cast hθ.trans_lt ha) φ hφ

end Reduction

section Main

open Char0

/-- **Theorem 3.1 on `ℙⁿ` from an embedding into `ℂ`** (`thm:c0-pn-ep`), given the analytic inputs
`Char0.ValuativeUpperBound` and `Char0.BergmanLowerBound`: if the algebraically closed field `k`
admits a field embedding `k → ℂ`, every class `θ ≥ 0` on `ℙⁿ` has the envelope property. -/
theorem hasEnvelopeProperty_of_ringHom_complex_of_inputs [IsAlgClosed k] (ι : k →+* ℂ)
    (hval : ValuativeUpperBound) (hberg : BergmanLowerBound) {θ : ℝ} (hθ : 0 ≤ θ) :
    HasEnvelopeProperty k n θ :=
  hasEnvelopeProperty_of_forall_isPSH_envelope_nat_of_nonpos
    (fun _ hd _ hφ hφ0 => hφ.isPSH_envelope_nat_of_nonpos_of_inputs ι hval hberg hd hφ0) hθ

end Main

end ProjBerk

/-- **FHX Theorem 3.1 for `ℙⁿ` in characteristic `0`** (`thm:c0-pn-ep`, FHX `thm:smooth-EP` in the
setting of FHX §5), conditional on the analytic inputs `Char0.ValuativeUpperBound`
(`prop:c0-valuative-bound`, `cor:c0-valuative-upper`) and `Char0.BergmanLowerBound`
(`cor:c0-bergman-lower`): over a countable algebraically closed field `k` of characteristic `0`,
every class `θ ≥ 0` on `ℙⁿ` has the envelope property. The field `k` embeds into `ℂ`
(`lem:c0-embedding`, `nonempty_ringHom_complex`). -/
theorem ProjBerk.hasEnvelopeProperty_of_charZero_of_inputs {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] [Countable k] (hval : Char0.ValuativeUpperBound)
    (hberg : Char0.BergmanLowerBound) (n : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ProjBerk.HasEnvelopeProperty k n θ := by
  obtain ⟨ι⟩ := nonempty_ringHom_complex k
  exact ProjBerk.hasEnvelopeProperty_of_ringHom_complex_of_inputs ι hval hberg hθ

end EnvelopeProperty
