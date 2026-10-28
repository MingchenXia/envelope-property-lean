/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SmoothConeTheta
import EnvelopeProperty.Projective.SubvarietyGauss

/-!
# Asymptotic test ideals on the punctured cone over a smooth projectively normal variety

Let `k` be a perfect field of characteristic `p`, `X = V(I) ⊆ ℙᴹ` with cone ring `T = S[t]`
(`ProjSubvariety.ConeRing`), and `D : X.ConeTraceData p` the chart cover of the punctured cone by
charts `D_c = T_{s_c}` with `p`-bases `v_c` (`def:sg-charts`, `def:sg-forms`). For a graded
sequence `(J_r)_{r ≥ 1}` of nonzero ideals of `T`, this file defines the asymptotic test ideals
`B_m` of the cone (blueprint `def:sg-test-X`, chapter `smooth-general.tex`, `subsec:sg-cone`) and
proves their properties `lem:sg-test-X`, which replace the global test ideals on the smooth
scheme `X × 𝔸¹` in the proof of Fang–Han–Xia, *The envelope property for unibranch projective
varieties*, Theorem 3.1 (`thm:smooth-EP`, eq. `eq:smooth-test-inclusions`).

## Main definitions

* `ConeTraceData.chartTestIdeal D J c m = B_m(D_c; J_• D_c)`: the asymptotic test ideal
  (`Cartier.IsPBasis.asymptoticTestIdeal`) of the graded sequence `J_• D_c` in the chart `D_c`, for
  its `p`-basis `v_c` (`lem:sg-asymptotic`).
* **`ConeTraceData.testSeq D J m = B_m`** (`def:sg-test-X`): the `f ∈ T` with
  `f ∈ B_m(D_c; J_• D_c)` for every chart `c`.

## Main results (`lem:sg-test-X`)

* (1) `ConeTraceData.exists_theta_le_testSeq`: for every `m` there is `r₀ > 0` such that for every
  `r > 0` divisible by `r₀` and every `e ≫ 0`, with `N = ⌈(m/r) p^e⌉` and
  `Θ = Θ^e_N(J_r) = Φ^e_z(J_r^N M₀) 𝔍₀` (`ConeTraceData.theta`):
  `Θ ⊆ B_m ⊆ Θ^sat` and `B_m D_c = B_m(D_c; J_• D_c)` for all `c`.
* (2) `ConeTraceData.le_testSeq` (`J_m ⊆ B_m` for `m ≥ 1`) and
  `ConeTraceData.testSeq_mul_le_saturation` (`B_{ml} ⊆ (B_m^l)^sat`).
* (3) on `X^an`, with `φ_𝔟 = φ_{𝔟 ∩ R_M[t]}`: `ConeTraceData.exists_phiIdeal_testSeq_eq_theta`
  (`φ_{B_m} = φ_Θ`), `ConeTraceData.phiIdeal_le_testSeq` (`φ_{J_m} ≤ φ_{B_m}`) and
  `ConeTraceData.phiIdeal_testSeq_mul_le` (`φ_{B_{ml}} ≤ l φ_{B_m}`).
* Auxiliary: `ProjSubvariety.phiIdeal_comap_coneMk_pow` (`φ_{𝔟^l} = l φ_𝔟` for ideals of `T`)
  and `ProjSubvariety.phiIdeal_comap_eq_of_le_of_le_saturation`.

## Deviations from the blueprint

* `B_m` is defined for every sequence `J : ℕ → Ideal T` and every `m`; the hypotheses (graded,
  nonzero for `r > 0`) are added where they are used. `J_0` plays no role.
* "for `r` divisible enough and `e ≫ 0`" is stated as `r₀ ∣ r` and `e₀ ≤ e`, with
  `N = ⌈(m/r) p^e⌉₊` computed in `ℚ`, as in
  `Cartier.IsPBasis.exists_asymptoticTestIdeal_eq_frobRoot`.
* (3) is stated on `X^an` for the functions `φ_𝔟 = ProjBerk.phiIdeal (𝔟.comap coneMk)` of the
  preimages in `R_M[t]` (as in `lem:sg-phi-basic`); `φ_{B_m} = φ_Θ` holds on all of `(ℙᴹ)^an`.
-/

open scoped NNReal ENNReal Topology Polynomial

noncomputable section

namespace EnvelopeProperty

open ProjBerk (phiIdeal)

universe u

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}

/-! ### Functions attached to ideals of `T` -/

/-- `φ_{𝔟^l} = l φ_𝔟` on `X^an` for an ideal `𝔟` of `T` (`lem:sg-phi-basic`(1)): `𝔟^l` is the image
of `(𝔟 ∩ R_M[t])^l`, and on `X^an` the kernel `I[t]` of `R_M[t] → T` does not change `φ`. -/
theorem phiIdeal_comap_coneMk_pow (𝔟 : Ideal X.ConeRing) (l : ℕ) (v : X.an) :
    phiIdeal ((𝔟 ^ l).comap X.coneMk) v.1 = l * phiIdeal (𝔟.comap X.coneMk) v.1 := by
  have h : 𝔟 ^ l = ((𝔟.comap X.coneMk) ^ l).map X.coneMk := by
    rw [Ideal.map_pow, Ideal.map_comap_of_surjective _ coneMk_surjective]
  rw [h, Ideal.comap_map_of_surjective' _ coneMk_surjective, phiIdeal_sup_ker_coneMk,
    ProjBerk.phiIdeal_pow]

/-- If `𝔟 ⊆ 𝔠 ⊆ 𝔟^sat`, then `φ_𝔠 = φ_𝔟` (`lem:sg-phi-basic`(1),(2)). -/
theorem phiIdeal_comap_eq_of_le_of_le_saturation {𝔟 𝔠 : Ideal X.ConeRing} (h₁ : 𝔟 ≤ 𝔠)
    (h₂ : 𝔠 ≤ X.saturation 𝔟) (v : ProjBerk k M) :
    phiIdeal (𝔠.comap X.coneMk) v = phiIdeal (𝔟.comap X.coneMk) v :=
  le_antisymm ((ProjBerk.phiIdeal_mono v (Ideal.comap_mono h₂)).trans_eq
      (phiIdeal_comap_saturation 𝔟 v))
    (ProjBerk.phiIdeal_mono v (Ideal.comap_mono h₁))

namespace ConeTraceData

open Cartier

variable {p : ℕ} [hp : Fact p.Prime] [CharP k p] (D : X.ConeTraceData p)

/-! ### The charts -/

theorem algebraMap_chart_injective (c : Fin D.nCharts) :
    Function.Injective (algebraMap X.ConeRing (D.chart c).D) :=
  IsLocalization.injective (D.chart c).D
    (powers_le_nonZeroDivisors_of_noZeroDivisors (D.chart c).s_ne_zero)

/-- `J_• D_c` is graded when `J_•` is. -/
theorem map_chart_mul_le {J : ℕ → Ideal X.ConeRing} (hJ : ∀ m r, J m * J r ≤ J (m + r))
    (c : Fin D.nCharts) (m r : ℕ) :
    (J m).map (algebraMap X.ConeRing (D.chart c).D) *
        (J r).map (algebraMap X.ConeRing (D.chart c).D) ≤
      (J (m + r)).map (algebraMap X.ConeRing (D.chart c).D) := by
  rw [← Ideal.map_mul]
  exact Ideal.map_mono (hJ m r)

/-- `J_q D_c ≠ 0` when `J_q ≠ 0`. -/
theorem map_chart_ne_bot {J : ℕ → Ideal X.ConeRing} (hne : ∀ q, 0 < q → J q ≠ ⊥)
    (c : Fin D.nCharts) (q : ℕ) (hq : 0 < q) :
    (J q).map (algebraMap X.ConeRing (D.chart c).D) ≠ ⊥ := by
  rw [Ne, Ideal.map_eq_bot_iff_of_injective (D.algebraMap_chart_injective c)]
  exact hne q hq

variable [PerfectRing k p]

/-! ### Local and global asymptotic test ideals -/

/-- The asymptotic test ideal `B_m(D_c; J_• D_c)` of the chart `D_c`, with respect to its
`p`-basis `v_c` (`lem:sg-asymptotic`, `def:sg-test-X`). -/
def chartTestIdeal (J : ℕ → Ideal X.ConeRing) (c : Fin D.nCharts) (m : ℕ) :
    Ideal (D.chart c).D :=
  (D.chart c).isPBasis_v.asymptoticTestIdeal
    (fun q => (J q).map (algebraMap X.ConeRing (D.chart c).D)) m

/-- **The asymptotic test ideals of the cone** (`def:sg-test-X`):
`B_m = {f ∈ T : f ∈ B_m(D_c; J_• D_c) for all charts c}`. -/
def testSeq (J : ℕ → Ideal X.ConeRing) (m : ℕ) : Ideal X.ConeRing :=
  ⨅ c, (D.chartTestIdeal J c m).comap (algebraMap X.ConeRing (D.chart c).D)

variable {D}

theorem mem_testSeq {J : ℕ → Ideal X.ConeRing} {m : ℕ} {f : X.ConeRing} :
    f ∈ D.testSeq J m ↔
      ∀ c, algebraMap X.ConeRing (D.chart c).D f ∈ D.chartTestIdeal J c m := by
  simp only [testSeq, Submodule.mem_iInf, Ideal.mem_comap]

theorem testSeq_le_comap (J : ℕ → Ideal X.ConeRing) (m : ℕ) (c : Fin D.nCharts) :
    D.testSeq J m ≤ (D.chartTestIdeal J c m).comap (algebraMap X.ConeRing (D.chart c).D) :=
  iInf_le _ c

variable (D)

/-! ### `lem:sg-test-X`(1) -/

/-- The local test ideals are the localizations of one global trace: for every `m` there is
`r₀ > 0` such that for every `r > 0` divisible by `r₀` and every `e ≫ 0`,
`B_m(D_c; J_• D_c) = Θ^e_N(J_r) D_c` for all `c`, `N = ⌈(m/r) p^e⌉`
(`lem:sg-asymptotic`(2), `lem:sg-test-stable`, `lem:sg-theta-local`). -/
theorem exists_chartTestIdeal_eq_map_theta {J : ℕ → Ideal X.ConeRing}
    (hJ : ∀ m r, J m * J r ≤ J (m + r)) (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, 0 < r → r₀ ∣ r → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ c,
      D.chartTestIdeal J c m = (D.theta e ⌈(m : ℚ) / r * (p : ℚ) ^ e⌉₊ (J r)).map
        (algebraMap X.ConeRing (D.chart c).D) := by
  have H := fun c => (D.chart c).isPBasis_v.exists_asymptoticTestIdeal_eq_frobRoot
    (J := fun q => (J q).map (algebraMap X.ConeRing (D.chart c).D))
    (D.map_chart_mul_le hJ c) (D.map_chart_ne_bot hne c) m
  choose q₀ hq₀ h₀ using H
  refine ⟨∏ c, q₀ c, Finset.prod_pos fun c _ => hq₀ c, fun r hr hdvd => ?_⟩
  have H' := fun c => h₀ c r hr ((Finset.dvd_prod_of_mem q₀ (Finset.mem_univ c)).trans hdvd)
  choose e₀ he₀ using H'
  refine ⟨Finset.univ.sup e₀, fun e he c => ?_⟩
  rw [map_theta_chart]
  exact he₀ c e ((Finset.le_sup (f := e₀) (Finset.mem_univ c)).trans he)

/-- **`lem:sg-test-X`(1)**: for every `m` there is `r₀ > 0` such that for every `r > 0` divisible
by `r₀` and every `e ≫ 0`, with `N = ⌈(m/r) p^e⌉` and `Θ = Θ^e_N(J_r)`: `Θ ⊆ B_m ⊆ Θ^sat` and
`B_m D_c = B_m(D_c; J_• D_c)` for all charts `c`. -/
theorem exists_theta_le_testSeq {J : ℕ → Ideal X.ConeRing} (hJ : ∀ m r, J m * J r ≤ J (m + r))
    (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, 0 < r → r₀ ∣ r → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e →
      D.theta e ⌈(m : ℚ) / r * (p : ℚ) ^ e⌉₊ (J r) ≤ D.testSeq J m ∧
      D.testSeq J m ≤ X.saturation (D.theta e ⌈(m : ℚ) / r * (p : ℚ) ^ e⌉₊ (J r)) ∧
      ∀ c, (D.testSeq J m).map (algebraMap X.ConeRing (D.chart c).D) = D.chartTestIdeal J c m := by
  obtain ⟨r₀, hr₀, h⟩ := D.exists_chartTestIdeal_eq_map_theta hJ hne m
  refine ⟨r₀, hr₀, fun r hr hdvd => ?_⟩
  obtain ⟨e₀, he₀⟩ := h r hr hdvd
  refine ⟨e₀, fun e he => ?_⟩
  set Θ := D.theta e ⌈(m : ℚ) / r * (p : ℚ) ^ e⌉₊ (J r)
  have hloc := he₀ e he
  have h1 : Θ ≤ D.testSeq J m := fun f hf =>
    mem_testSeq.2 fun c => by rw [hloc c]; exact Ideal.mem_map_of_mem _ hf
  refine ⟨h1, fun f hf => ?_, fun c => le_antisymm ?_ ?_⟩
  · refine (D.mem_saturation_iff Θ f).2 fun c => ?_
    rw [← hloc c]
    exact mem_testSeq.1 hf c
  · rw [Ideal.map_le_iff_le_comap]
    exact testSeq_le_comap J m c
  · rw [hloc c]
    exact Ideal.map_mono h1

/-- `B_m D_c = B_m(D_c; J_• D_c)` (`lem:sg-test-X`(1)). -/
theorem map_testSeq {J : ℕ → Ideal X.ConeRing} (hJ : ∀ m r, J m * J r ≤ J (m + r))
    (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) (c : Fin D.nCharts) :
    (D.testSeq J m).map (algebraMap X.ConeRing (D.chart c).D) = D.chartTestIdeal J c m := by
  obtain ⟨r₀, hr₀, h⟩ := D.exists_theta_le_testSeq hJ hne m
  obtain ⟨e₀, he₀⟩ := h r₀ hr₀ dvd_rfl
  exact (he₀ e₀ le_rfl).2.2 c

/-! ### `lem:sg-test-X`(2) -/

/-- **`J_m ⊆ B_m`** for `m ≥ 1` (`lem:sg-test-X`(2), from `lem:sg-asymptotic`(3)). -/
theorem le_testSeq (J : ℕ → Ideal X.ConeRing) {m : ℕ} (hm : 0 < m) : J m ≤ D.testSeq J m :=
  fun _ hf => mem_testSeq.2 fun c =>
    (D.chart c).isPBasis_v.le_asymptoticTestIdeal _ hm (Ideal.mem_map_of_mem _ hf)

/-- **`B_{ml} ⊆ (B_m^l)^sat`** (`lem:sg-test-X`(2)): on every chart,
`B_{ml}(D_c) ⊆ B_m(D_c)^l = (B_m D_c)^l = B_m^l D_c` (`lem:sg-asymptotic`(3)), and `lem:sg-sat`. -/
theorem testSeq_mul_le_saturation {J : ℕ → Ideal X.ConeRing}
    (hJ : ∀ m r, J m * J r ≤ J (m + r)) (hne : ∀ q, 0 < q → J q ≠ ⊥) (m l : ℕ) :
    D.testSeq J (m * l) ≤ X.saturation (D.testSeq J m ^ l) := by
  intro f hf
  refine (D.mem_saturation_iff _ f).2 fun c => ?_
  have h1 := (D.chart c).isPBasis_v.asymptoticTestIdeal_mul_le
    (J := fun q => (J q).map (algebraMap X.ConeRing (D.chart c).D))
    (D.map_chart_mul_le hJ c) (D.map_chart_ne_bot hne c) m l (mem_testSeq.1 hf c)
  rw [Ideal.map_pow, D.map_testSeq hJ hne m c]
  exact h1

/-! ### `lem:sg-test-X`(3) -/

/-- **`φ_{B_m} = φ_Θ`** (`lem:sg-test-X`(3)): for `r` divisible enough and `e ≫ 0`, with
`Θ = Θ^e_N(J_r)`, `N = ⌈(m/r) p^e⌉`, `φ_{B_m} = φ_Θ` on `(ℙᴹ)^an`. -/
theorem exists_phiIdeal_testSeq_eq_theta {J : ℕ → Ideal X.ConeRing}
    (hJ : ∀ m r, J m * J r ≤ J (m + r)) (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, 0 < r → r₀ ∣ r → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ v : ProjBerk k M,
      phiIdeal ((D.testSeq J m).comap X.coneMk) v =
        phiIdeal ((D.theta e ⌈(m : ℚ) / r * (p : ℚ) ^ e⌉₊ (J r)).comap X.coneMk) v := by
  obtain ⟨r₀, hr₀, h⟩ := D.exists_theta_le_testSeq hJ hne m
  refine ⟨r₀, hr₀, fun r hr hdvd => ?_⟩
  obtain ⟨e₀, he₀⟩ := h r hr hdvd
  exact ⟨e₀, fun e he v =>
    phiIdeal_comap_eq_of_le_of_le_saturation (he₀ e he).1 (he₀ e he).2.1 v⟩

/-- **`φ_{J_m} ≤ φ_{B_m}`** for `m ≥ 1` (`lem:sg-test-X`(3)). -/
theorem phiIdeal_le_testSeq (J : ℕ → Ideal X.ConeRing) {m : ℕ} (hm : 0 < m)
    (v : ProjBerk k M) :
    phiIdeal ((J m).comap X.coneMk) v ≤ phiIdeal ((D.testSeq J m).comap X.coneMk) v :=
  ProjBerk.phiIdeal_mono v (Ideal.comap_mono (D.le_testSeq J hm))

/-- **`φ_{B_{ml}} ≤ l φ_{B_m}`** on `X^an` (`lem:sg-test-X`(3)). -/
theorem phiIdeal_testSeq_mul_le {J : ℕ → Ideal X.ConeRing}
    (hJ : ∀ m r, J m * J r ≤ J (m + r)) (hne : ∀ q, 0 < q → J q ≠ ⊥) (m l : ℕ) (v : X.an) :
    phiIdeal ((D.testSeq J (m * l)).comap X.coneMk) v.1 ≤
      l * phiIdeal ((D.testSeq J m).comap X.coneMk) v.1 := by
  calc phiIdeal ((D.testSeq J (m * l)).comap X.coneMk) v.1
      ≤ phiIdeal ((X.saturation (D.testSeq J m ^ l)).comap X.coneMk) v.1 :=
        ProjBerk.phiIdeal_mono _ (Ideal.comap_mono (D.testSeq_mul_le_saturation hJ hne m l))
    _ = phiIdeal ((D.testSeq J m ^ l).comap X.coneMk) v.1 := phiIdeal_comap_saturation _ _
    _ = l * phiIdeal ((D.testSeq J m).comap X.coneMk) v.1 := phiIdeal_comap_coneMk_pow _ l v

end ConeTraceData

end ProjSubvariety

end EnvelopeProperty
