/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.Jm
import EnvelopeProperty.TestIdeal.Asymptotic
import EnvelopeProperty.Cartier.Polynomial

/-!
# Bridges between `R[t]`, the test-ideal API and the Cartier API

The functions `φ_I` of `EnvelopeProperty.Projective.Basic` (`ProjBerk.phiIdeal`) are attached to
ideals of `R[t] = (MvPolynomial (Fin (n + 1)) k)[X]`, the coordinate ring of `S = ℙⁿ × 𝔸¹` used by
the Gauss extension. The test ideals of `EnvelopeProperty.TestIdeal` (FHX §3, eq. `eq:test-def`,
`lem:test-ideals`) live in a polynomial ring `MvPolynomial σ K`, and the Frobenius trace estimate
of `EnvelopeProperty.Cartier` (`lem:pn-divisorial-trace`) is stated for
`EnvelopeProperty.Cartier.polyTrace`. This file connects the three, as needed for the assembly of
Theorem 3.1 on `ℙⁿ` (blueprint `rmk:bj-pn-ep-assembly`, steps (b) and (d)).

## Main definitions and results

* `EnvelopeProperty.frobTrace_eq_polyTrace`: the Frobenius trace `Φ_e` of the test-ideal API is
  the polynomial trace of the Cartier API (same coefficient formula; the two definitions agree by
  `rfl`); `EnvelopeProperty.frobTrace_eq_traceIter` identifies it with the iterated trace of the
  `p`-basis given by the variables, and `EnvelopeProperty.mem_frobRoot_iff_polyTrace` describes
  Frobenius roots `I^[1/p^e] = Φ_e(I)` through `polyTrace`.
* `ProjBerk.coneEquiv k n : R[t] ≃ₐ[k] k[x₀, …, xₙ, t]`, the inverse of
  `MvPolynomial.optionEquivLeft` (`t = X none`, `xᵢ = X (some i)`), and the weight
  `ProjBerk.xWeight n` (`1` on `xᵢ`, `0` on `t`), whose weighted degree is the `x`-degree:
  `ProjBerk.isWeightedHomogeneous_coneEquiv_iff`.
* Transport of the graded sequence `J_m(φ)` (`ProjBerk.obstacleIdeal`) to `k[x, t]`
  (`ProjBerk.coneObstacleIdeal`): `ProjBerk.coneObstacleIdeal_mul_le` (graded),
  `ProjBerk.coneObstacleIdeal_ne_bot` (nonzero for `φ` bounded below),
  `ProjBerk.hasWeightedGeneratorsLE_coneObstacleIdeal` (`J_q` is generated in `x`-degree `≤ q d`),
  i.e. exactly the hypotheses of `EnvelopeProperty.HasWeightedGeneratorsLE.asymptoticTestIdeal`
  and `EnvelopeProperty.asymptoticTestIdeal_mul_le`.
* Transport of `φ_I` back to `R[t]`: for `B ⊆ k[x, t]`, `φ_B` means `φ_{B.comap coneEquiv}`;
  `ProjBerk.phiIdeal_comap_coneEquiv` (formula), `ProjBerk.phiIdeal_comap_coneEquiv_mul`,
  `ProjBerk.phiIdeal_comap_coneEquiv_pow`, `ProjBerk.comap_map_coneEquiv`, and
  `ProjBerk.isRatFS_inv_mul_phiIdeal_comap`: if `B ≠ 0` is generated in `x`-degree `≤ m d`, then
  `m⁻¹ φ_B ∈ H^gf_ℚ(d)` (step (b) of `rmk:bj-pn-ep-assembly`, padding generators with monomials).
* For the asymptotic test ideals `B_m = τ(J_•^m)` of `coneObstacleIdeal` (`k` perfect of
  characteristic `p`): `ProjBerk.obstacleIdeal_le_comap_asymptoticTestIdeal` (`J_m ⊆ B_m`),
  `ProjBerk.hasWeightedGeneratorsLE_asymptoticTestIdeal_coneObstacleIdeal` (generation in
  `x`-degree `≤ m d`), `ProjBerk.isRatFS_asymptoticTestIdeal_coneObstacleIdeal`
  (`m⁻¹ φ_{B_m} ∈ H^gf_ℚ(d)`) and `ProjBerk.phiIdeal_comap_asymptoticTestIdeal_mul_le`
  (`φ_{B_{ml}} ≤ l φ_{B_m}`).
-/

open scoped Polynomial

noncomputable section

namespace EnvelopeProperty

/-! ### The Frobenius trace of the test-ideal API is the Cartier polynomial trace -/

section Trace

variable {σ K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]
  [Fintype σ]

/-- The Frobenius trace `Φ_e` of `EnvelopeProperty.TestIdeal.FrobeniusRoot` coincides with the
polynomial trace `Φ_e` of `EnvelopeProperty.Cartier.Polynomial`: both are
`coeff c (Φ_e f) = (coeff (p^e • c + (p^e - 1, …, p^e - 1)) f)^{1/p^e}`. -/
theorem frobTrace_eq_polyTrace (e : ℕ) :
    (frobTrace p e : MvPolynomial σ K →+ MvPolynomial σ K) = Cartier.polyTrace p e :=
  rfl

theorem frobTrace_apply_eq_polyTrace (e : ℕ) (f : MvPolynomial σ K) :
    frobTrace p e f = Cartier.polyTrace p e f :=
  rfl

/-- `Φ_e` is the `e`-th iterate of the trace of the `p`-basis of `K[σ]` given by the variables. -/
theorem frobTrace_eq_traceIter [DecidableEq σ] (e : ℕ) (f : MvPolynomial σ K) :
    frobTrace p e f = (Cartier.isPBasis_X (σ := σ) (k := K) p).traceIter e f := by
  rw [Cartier.traceIter_X, frobTrace_apply_eq_polyTrace]

/-- Frobenius roots through the Cartier trace: `I^[1/p^e] = Φ_e(I)`. -/
theorem mem_frobRoot_iff_polyTrace {e : ℕ} {I : Ideal (MvPolynomial σ K)}
    {f : MvPolynomial σ K} : f ∈ frobRoot p e I ↔ ∃ g ∈ I, Cartier.polyTrace p e g = f :=
  Iff.rfl

end Trace

namespace ProjBerk

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-! ### The cone coordinate ring `k[x₀, …, xₙ, t]` -/

/-- The isomorphism `R[t] ≃ k[x₀, …, xₙ, t]` of the coordinate rings of `S = ℙⁿ × 𝔸¹`, with
`t = X none` and `xᵢ = X (some i)`: the inverse of `MvPolynomial.optionEquivLeft`. -/
def coneEquiv : (MvPolynomial (Fin (n + 1)) k)[X] ≃ₐ[k] MvPolynomial (Option (Fin (n + 1))) k :=
  (MvPolynomial.optionEquivLeft k (Fin (n + 1))).symm

/-- The weight `1` on the `xᵢ` and `0` on `t`: the weighted degree is the `x`-degree. -/
def xWeight : Option (Fin (n + 1)) → ℕ := fun o => o.elim 0 fun _ => 1

variable {k n}

@[simp]
theorem xWeight_none : xWeight n none = 0 := rfl

@[simp]
theorem xWeight_some (i : Fin (n + 1)) : xWeight n (some i) = 1 := rfl

@[simp]
theorem coneEquiv_symm_apply (F : MvPolynomial (Option (Fin (n + 1))) k) :
    (coneEquiv k n).symm F = MvPolynomial.optionEquivLeft k (Fin (n + 1)) F :=
  rfl

@[simp]
theorem coneEquiv_X : coneEquiv k n Polynomial.X = MvPolynomial.X none := by
  simp [coneEquiv]

@[simp]
theorem coneEquiv_C_X (i : Fin (n + 1)) :
    coneEquiv k n (Polynomial.C (MvPolynomial.X i)) = MvPolynomial.X (some i) := by
  simp [coneEquiv]

/-- The coefficient of `x^m t^ℓ` in `coneEquiv g` is the coefficient of `x^m` in `g_ℓ`. -/
theorem coeff_coneEquiv (g : (MvPolynomial (Fin (n + 1)) k)[X]) (ℓ : ℕ)
    (m : Fin (n + 1) →₀ ℕ) :
    MvPolynomial.coeff (m.optionElim ℓ) (coneEquiv k n g) = MvPolynomial.coeff m (g.coeff ℓ) := by
  rw [← MvPolynomial.optionEquivLeft_coeff_some_coeff_none, coneEquiv, AlgEquiv.apply_symm_apply,
    Finsupp.some_optionElim, Finsupp.optionElim_apply_none]

/-- The weighted degree of `x^m t^ℓ` is `|m|`. -/
theorem weight_xWeight_optionElim (m : Fin (n + 1) →₀ ℕ) (ℓ : ℕ) :
    Finsupp.weight (xWeight n) (m.optionElim ℓ) = Finsupp.weight 1 m := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_option_index _ _ (fun _ => by simp)
    (fun _ _ _ => by simp [add_mul]), Finsupp.some_optionElim, Finsupp.optionElim_apply_none]
  simp

/-- `coneEquiv g` is weighted homogeneous of degree `e` iff `g` is homogeneous of `x`-degree
`e`. -/
theorem isWeightedHomogeneous_coneEquiv_iff {g : (MvPolynomial (Fin (n + 1)) k)[X]} {e : ℕ} :
    MvPolynomial.IsWeightedHomogeneous (xWeight n) (coneEquiv k n g) e ↔ IsXHomogeneous g e := by
  constructor
  · intro h ℓ m hm
    rw [← coeff_coneEquiv] at hm
    have := h hm
    rwa [weight_xWeight_optionElim] at this
  · intro h c hc
    rw [← Finsupp.optionElim_some c, coeff_coneEquiv] at hc
    rw [← Finsupp.optionElim_some c, weight_xWeight_optionElim]
    exact h _ hc

/-! ### Transport of ideals -/

/-- Ideals of `k[x, t]` correspond to ideals of `R[t]` by `comap = map` along the inverse. -/
theorem comap_coneEquiv (B : Ideal (MvPolynomial (Option (Fin (n + 1))) k)) :
    B.comap (coneEquiv k n) = B.map (coneEquiv k n).symm := by
  refine le_antisymm (fun g hg => ?_) (Ideal.map_le_iff_le_comap.2 fun b hb => ?_)
  · simpa using Ideal.mem_map_of_mem (coneEquiv k n).symm (Ideal.mem_comap.1 hg)
  · rw [Ideal.mem_comap, Ideal.mem_comap, AlgEquiv.apply_symm_apply]
    exact hb

theorem comap_map_coneEquiv (I : Ideal (MvPolynomial (Fin (n + 1)) k)[X]) :
    (I.map (coneEquiv k n)).comap (coneEquiv k n) = I :=
  Ideal.comap_map_of_bijective _ (coneEquiv k n).bijective

theorem le_comap_coneEquiv_iff {I : Ideal (MvPolynomial (Fin (n + 1)) k)[X]}
    {B : Ideal (MvPolynomial (Option (Fin (n + 1))) k)} :
    I ≤ B.comap (coneEquiv k n) ↔ I.map (coneEquiv k n) ≤ B :=
  Ideal.map_le_iff_le_comap.symm

theorem comap_coneEquiv_mono {B B' : Ideal (MvPolynomial (Option (Fin (n + 1))) k)}
    (h : B ≤ B') : B.comap (coneEquiv k n) ≤ B'.comap (coneEquiv k n) :=
  Ideal.comap_mono h

theorem comap_coneEquiv_mul (B B' : Ideal (MvPolynomial (Option (Fin (n + 1))) k)) :
    (B * B').comap (coneEquiv k n) = B.comap (coneEquiv k n) * B'.comap (coneEquiv k n) := by
  rw [comap_coneEquiv, comap_coneEquiv, comap_coneEquiv, Ideal.map_mul]

theorem comap_coneEquiv_pow (B : Ideal (MvPolynomial (Option (Fin (n + 1))) k)) (r : ℕ) :
    (B ^ r).comap (coneEquiv k n) = B.comap (coneEquiv k n) ^ r := by
  rw [comap_coneEquiv, comap_coneEquiv, Ideal.map_pow]

theorem comap_coneEquiv_ne_bot {B : Ideal (MvPolynomial (Option (Fin (n + 1))) k)}
    (hB : B ≠ ⊥) : B.comap (coneEquiv k n) ≠ ⊥ := by
  rw [comap_coneEquiv, Ne, Ideal.map_eq_bot_iff_of_injective (coneEquiv k n).symm.injective]
  exact hB

theorem map_coneEquiv_ne_bot {I : Ideal (MvPolynomial (Fin (n + 1)) k)[X]} (hI : I ≠ ⊥) :
    I.map (coneEquiv k n) ≠ ⊥ := by
  rw [Ne, Ideal.map_eq_bot_iff_of_injective (coneEquiv k n).injective]
  exact hI

/-- An ideal generated by elements homogeneous of `x`-degree `≤ D` is generated in weighted degree
`≤ D` after transport to `k[x, t]`. -/
theorem hasWeightedGeneratorsLE_map_span {S : Set (MvPolynomial (Fin (n + 1)) k)[X]} {D : ℕ}
    (hS : ∀ g ∈ S, ∃ e ≤ D, IsXHomogeneous g e) :
    HasWeightedGeneratorsLE (xWeight n) D ((Ideal.span S).map (coneEquiv k n)) := by
  rw [Ideal.map_span]
  refine HasWeightedGeneratorsLE.span ?_
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨e, he, hge⟩ := hS g hg
  exact ⟨e, he, isWeightedHomogeneous_coneEquiv_iff.2 hge⟩

variable (k n) in
/-- The ideals `J_m(φ)` (`obstacleIdeal`) transported to `k[x₀, …, xₙ, t]`, the polynomial ring
in which the test ideals of `lem:test-ideals` are taken. -/
def coneObstacleIdeal (d : ℕ) (φ : ProjBerk k n → ℝ) (m : ℕ) :
    Ideal (MvPolynomial (Option (Fin (n + 1))) k) :=
  (obstacleIdeal k n d φ m).map (coneEquiv k n)

variable {d : ℕ} {φ : ProjBerk k n → ℝ}

theorem comap_coneObstacleIdeal (m : ℕ) :
    (coneObstacleIdeal k n d φ m).comap (coneEquiv k n) = obstacleIdeal k n d φ m :=
  comap_map_coneEquiv _

/-- `J_q(φ)` is generated in `x`-degree `≤ q d`, as an ideal of `k[x, t]`
(blueprint `lem:bj-Jm-basic`, input of `lem:test-ideals`). -/
theorem hasWeightedGeneratorsLE_coneObstacleIdeal (q : ℕ) :
    HasWeightedGeneratorsLE (xWeight n) (q * d) (coneObstacleIdeal k n d φ q) :=
  hasWeightedGeneratorsLE_map_span fun _ hg => ⟨q * d, le_rfl, hg.1⟩

/-- The transported ideals `J_m(φ)` form a graded sequence in `k[x, t]`. -/
theorem coneObstacleIdeal_mul_le (m r : ℕ) :
    coneObstacleIdeal k n d φ m * coneObstacleIdeal k n d φ r ≤
      coneObstacleIdeal k n d φ (m + r) := by
  rw [coneObstacleIdeal, coneObstacleIdeal, ← Ideal.map_mul]
  exact Ideal.map_mono (obstacleIdeal_mul_le m r)

/-- The transported ideals `J_m(φ)` are nonzero for `φ` bounded below. -/
theorem coneObstacleIdeal_ne_bot {C : ℝ} (hC : ∀ v, C ≤ φ v) (m : ℕ) :
    coneObstacleIdeal k n d φ m ≠ ⊥ :=
  map_coneEquiv_ne_bot (obstacleIdeal_ne_bot hC m)

/-! ### Transport of `φ_I` -/

/-- `φ_B` for an ideal `B` of `k[x, t]`, computed in `R[t]`:
`φ_{B.comap coneEquiv}(v) = sup_{G ∈ B} log|coneEquiv⁻¹ G|_{σ(v)}`. -/
theorem phiIdeal_comap_coneEquiv (B : Ideal (MvPolynomial (Option (Fin (n + 1))) k))
    (v : ProjBerk k n) :
    phiIdeal (B.comap (coneEquiv k n)) v =
      ⨆ G ∈ B, Berk.logAbs ((coneEquiv k n).symm G) (gaussExt v) := by
  refine le_antisymm (iSup₂_le fun g hg => ?_) (iSup₂_le fun G hG => le_phiIdeal _ v ?_)
  · refine le_iSup₂_of_le (f := fun G (_ : G ∈ B) =>
      Berk.logAbs ((coneEquiv k n).symm G) (gaussExt v)) (coneEquiv k n g) hg ?_
    rw [AlgEquiv.symm_apply_apply]
  · rw [Ideal.mem_comap, AlgEquiv.apply_symm_apply]
    exact hG

theorem phiIdeal_comap_map_coneEquiv (I : Ideal (MvPolynomial (Fin (n + 1)) k)[X])
    (v : ProjBerk k n) :
    phiIdeal ((I.map (coneEquiv k n)).comap (coneEquiv k n)) v = phiIdeal I v := by
  rw [comap_map_coneEquiv]

/-- `φ_{BB'} = φ_B + φ_{B'}` for ideals of `k[x, t]`. -/
theorem phiIdeal_comap_coneEquiv_mul (B B' : Ideal (MvPolynomial (Option (Fin (n + 1))) k))
    (v : ProjBerk k n) :
    phiIdeal ((B * B').comap (coneEquiv k n)) v =
      phiIdeal (B.comap (coneEquiv k n)) v + phiIdeal (B'.comap (coneEquiv k n)) v := by
  rw [comap_coneEquiv_mul, phiIdeal_mul]

/-- `φ_{B^r} = r φ_B` for ideals of `k[x, t]`. -/
theorem phiIdeal_comap_coneEquiv_pow (B : Ideal (MvPolynomial (Option (Fin (n + 1))) k)) (r : ℕ)
    (v : ProjBerk k n) :
    phiIdeal ((B ^ r).comap (coneEquiv k n)) v = r * phiIdeal (B.comap (coneEquiv k n)) v := by
  rw [comap_coneEquiv_pow, phiIdeal_pow]

/-- **Padding generators** (blueprint `rmk:bj-pn-ep-assembly`, step (b)): if an ideal `B ≠ 0` of
`k[x, t]` is generated by weighted homogeneous elements of `x`-degree `≤ m d`, then
`m⁻¹ φ_B ∈ H^gf_ℚ(d)`, `m > 0`. -/
theorem isRatFS_inv_mul_phiIdeal_comap {m : ℕ} (hm : 0 < m)
    {B : Ideal (MvPolynomial (Option (Fin (n + 1))) k)}
    (hB : HasWeightedGeneratorsLE (xWeight n) (m * d) B) (hne : B ≠ ⊥) :
    IsRatFS (d : ℚ) fun v =>
      (((m : ℝ)⁻¹ : ℝ) : EReal) * phiIdeal (B.comap (coneEquiv k n)) v := by
  obtain ⟨T, rfl, hT⟩ := hB
  refine isRatFS_inv_mul_phiIdeal hm (S := (coneEquiv k n).symm '' T) ?_ ?_
    (comap_coneEquiv_ne_bot hne)
  · rw [comap_coneEquiv, Ideal.map_span]
  · rintro _ ⟨G, hG, rfl⟩ ℓ
    obtain ⟨e, he, hGe⟩ := hT G hG
    rw [← (coneEquiv k n).apply_symm_apply G] at hGe
    exact ⟨e, he, isWeightedHomogeneous_coneEquiv_iff.1 hGe ℓ⟩

/-! ### Asymptotic test ideals of `J_•(φ)` -/

section Asymptotic

variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

/-- `J_m ⊆ B_m` in `R[t]`, for the asymptotic test ideals `B_m = τ(J_•^m)` of the transported
graded sequence (`lem:test-ideals`). -/
theorem obstacleIdeal_le_comap_asymptoticTestIdeal {m : ℕ} (hm : 0 < m) :
    obstacleIdeal k n d φ m ≤
      (asymptoticTestIdeal p (coneObstacleIdeal k n d φ) m).comap (coneEquiv k n) :=
  le_comap_coneEquiv_iff.2 (le_asymptoticTestIdeal (J := coneObstacleIdeal k n d φ) p hm)

/-- `B_m` is generated in `x`-degree `≤ m d` (`lem:test-ideals`, the `ℙⁿ` case of FHX
Lemma 3.2), for `φ` bounded below. -/
theorem hasWeightedGeneratorsLE_asymptoticTestIdeal_coneObstacleIdeal {C : ℝ}
    (hC : ∀ v, C ≤ φ v) (m : ℕ) :
    HasWeightedGeneratorsLE (xWeight n) (m * d)
      (asymptoticTestIdeal p (coneObstacleIdeal k n d φ) m) :=
  HasWeightedGeneratorsLE.asymptoticTestIdeal p coneObstacleIdeal_mul_le
    (fun q _ => coneObstacleIdeal_ne_bot hC q)
    (fun q _ => hasWeightedGeneratorsLE_coneObstacleIdeal q) m

/-- **`u_m = m⁻¹ φ_{B_m} ∈ H^gf_ℚ(d)`** (blueprint `rmk:bj-pn-ep-assembly`, step (b)), for `φ`
bounded below and `m > 0`. -/
theorem isRatFS_asymptoticTestIdeal_coneObstacleIdeal {C : ℝ} (hC : ∀ v, C ≤ φ v) {m : ℕ}
    (hm : 0 < m) :
    IsRatFS (d : ℚ) fun v => (((m : ℝ)⁻¹ : ℝ) : EReal) *
      phiIdeal ((asymptoticTestIdeal p (coneObstacleIdeal k n d φ) m).comap (coneEquiv k n)) v := by
  refine isRatFS_inv_mul_phiIdeal_comap hm
    (hasWeightedGeneratorsLE_asymptoticTestIdeal_coneObstacleIdeal p hC m) fun h => ?_
  have h1 := obstacleIdeal_le_comap_asymptoticTestIdeal (d := d) (φ := φ) p hm
  rw [h, Ideal.comap_bot_of_injective _ (coneEquiv k n).injective, le_bot_iff] at h1
  exact obstacleIdeal_ne_bot hC m h1

/-- Subadditivity `B_{ml} ⊆ B_m^l` in the form `φ_{B_{ml}} ≤ l φ_{B_m}`, for `φ` bounded below. -/
theorem phiIdeal_comap_asymptoticTestIdeal_mul_le {C : ℝ} (hC : ∀ v, C ≤ φ v) (m l : ℕ)
    (v : ProjBerk k n) :
    phiIdeal ((asymptoticTestIdeal p (coneObstacleIdeal k n d φ) (m * l)).comap
        (coneEquiv k n)) v ≤
      l * phiIdeal ((asymptoticTestIdeal p (coneObstacleIdeal k n d φ) m).comap
        (coneEquiv k n)) v := by
  rw [← phiIdeal_comap_coneEquiv_pow]
  exact phiIdeal_mono v (comap_coneEquiv_mono (asymptoticTestIdeal_mul_le p
    coneObstacleIdeal_mul_le (fun q _ => coneObstacleIdeal_ne_bot hC q) m l))

end Asymptotic

end ProjBerk

end EnvelopeProperty
