/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.LineFibrePieces
import EnvelopeProperty.Berkovich.Blowup
import EnvelopeProperty.Berkovich.ReesPaperChart
import EnvelopeProperty.ReesChartUniversal
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Local approximants at points of a product of Dedekind domains

This file formalizes `lem:nf-local-approx` of the blueprint chapter `nonflat-route.tex`, the
nonflat route to Fang–Han–Xia, *The envelope property for unibranch projective varieties*,
Proposition 5.22 (`prop:nonflat-norm`; revision 832e086, Section 5,
`sec:normal-local-regularization`; the full proof is in revision d64981e). In the identification
step the function `u ∘ r ∘ p` on the normalized curve `R' = ∏_P D_P` over a line through a rigid
lift must be, near every rigid point `x`, a decreasing limit of functions of Fubini–Study type with
a fixed denominator `g`, `|g|_x ≠ 0` (`EnvelopeProperty.IsNonflatAwayFS`, the hypothesis of
`EnvelopeProperty.eventually_flatNormFun_nonflatEvalPoint_le` in `Berkovich/LineFibrePieces`).
Here `u` is regularizable on the charts `A[s/σ]` of a blowup (`def:nf-chart-regularizable`).

Everything is stated abstractly for a `k`-algebra map `ψ : A → R` (in the application
`A → A_F → R'`).

## Main results

* `IsRegularizable.exists_isNonflatAwayFS_comap`: a regularizable function on `Spec C`, pulled back
  along `χ : C → R_g` and the lift `z ↦ z̃` of `{|g| ≠ 0}` to `(Spec R_g)^an`, is a decreasing limit
  of functions of FS type in `R_g`; `exists_nonflatLocalApprox_of_lift` transports this to
  `u ∘ ψ^an` when `χ ∘ μ = (R → R_g) ∘ ψ` and `u ∘ μ^an ∈ ℛ(Spec C)`.
* **Case A** (`exists_nonflatLocalApprox_away`): from `u|_{Y_{g₀}} ∈ ℛ(Y_{g₀})`, with `g = ψ(g₀)`.
* **Case B** (`exists_nonflatLocalApprox_chart`): from `u ∘ μ_σ ∈ ℛ(A[s/σ])` and divisibility data
  `g ψ(σ') ∈ ψ(σ) R` (`σ' ∈ s`), `ψ(σ)` a non-zero-divisor in `R_g`, through the chart lift
  `nonflat_exists_blowupChart_lift` (`A[s/σ] → T` from `f : A → T` with `f(σ)` regular and
  `f(σ) t_{σ'} = f(σ')`).
* `nonflat_exists_chart_denominator`: for `R = ∏ D_i` a finite product of Dedekind domains and
  `σ₀ ∈ s` with nonzero image in every factor, every point `x` of `(Spec R)^an` has such data with
  `|g|_x ≠ 0`: on the factor `D_i` of `x`, with kernel `p`, choose `σ ∈ s` whose image has minimal
  order in the valuation ring `D_p` (`nonflat_dedekind_local_dvd_total`,
  `nonflat_exists_local_dvd_min`) and let `g` be the product of the denominators, on `D_i`.
* `exists_nonflatLocalApprox` (`lem:nf-local-approx`): the conclusion at every point of
  `(Spec ∏ D_i)^an`, in exactly the form consumed by
  `EnvelopeProperty.eventually_flatNormFun_nonflatEvalPoint_le`.

## Comparison with the blueprint

* The covering hypothesis of `lem:nf-local-approx` (regularizability on principal opens covering
  `Y^an \ Z^an`) is not needed: Case B applies at every point `x`, also off `Z^an`, as soon as some
  `σ₀ ∈ s` has nonzero image in every factor `D_i`, which the blueprint ensures by choosing the line
  admissible for `h · χ_{σ₀}(0)` (`nonflat_apply_ne_zero_of_mul` passes from `φ(χ_{σ₀}(0)) ∈ σ₀ A`
  to `σ₀`). Case A is provided separately (`exists_nonflatLocalApprox_away`).
* The blueprint's choice of `σ` of minimal `ord_x` and of `g' ∈ D \ 𝔪_x` with
  `ψ(A[s/σ]) ⊆ D_{g'}` is replaced by the equivalent divisibility data; the point `x` need not be
  rigid (if its kernel on `D_i` is zero, `D_p` is the fraction field).
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open Berk

/-! ### Pulling back regularizable functions to functions of FS type in a localization -/

section Pullback

variable {k : Type*} [Field k] {C : Type*} [CommRing C] [Algebra k C]
  {R : Type*} [CommRing R] [Algebra k R]

/-- An affine Fubini–Study function on `Spec C`, pulled back along a `k`-algebra map
`χ : C → R_g` and the lifts `z ↦ z̃ ∈ (Spec R_g)^an` of the points with `|g|_z ≠ 0`, is of FS type
in `R_g`: replace each term `(f, a, b)` by `(χ f, a, b)`. -/
theorem FSData.isNonflatAwayFS_of_eq (G : FSData k C) {g : R} (χ : C →ₐ[k] Localization.Away g)
    {W : Berk k R → EReal}
    (hW : ∀ (z : Berk k R) (hz : z.val g ≠ 0), W z = G.eval (comap χ (awayLift g z hz))) :
    IsNonflatAwayFS g W := by
  classical
  refine ⟨G.terms.image fun t => (χ t.1, t.2.1, (t.2.2 : ℝ)), (G.const : ℝ), ?_, ?_⟩
  · intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.1 ht
    exact G.pos t₀ ht₀
  · intro z hz
    rw [hW z hz, FSData.eval, Finset.sup_image]
    congr 1

/-- **Pullback of regularizable functions** (`lem:nf-local-approx`, the last step of both cases):
if `v ∈ ℛ(Spec C)` and `χ : C → R_g`, then `z ↦ v(χ^*(z̃))` is, on `{|g| ≠ 0}`, the limit of a
decreasing sequence of functions of FS type in `R_g` (`IsNonflatAwayFS`). -/
theorem IsRegularizable.exists_isNonflatAwayFS_comap {v : Berk k C → EReal}
    (hv : IsRegularizable v) {g : R} (χ : C →ₐ[k] Localization.Away g) :
    ∃ G : ℕ → Berk k R → EReal, (∀ j, IsNonflatAwayFS g (G j)) ∧
      (∀ z, z.val g ≠ 0 → Antitone fun j => G j z) ∧
      ∀ (z : Berk k R) (hz : z.val g ≠ 0), v (comap χ (awayLift g z hz)) = ⨅ j, G j z := by
  classical
  obtain ⟨-, Gs, hanti, hlim⟩ := hv
  refine ⟨fun j z => if hz : z.val g ≠ 0 then (Gs j).eval (comap χ (awayLift g z hz)) else 0,
    fun j => (Gs j).isNonflatAwayFS_of_eq χ fun z hz => dif_pos hz, fun z hz => ?_,
    fun z hz => ?_⟩
  · simp only [dif_pos hz]
    exact hanti _
  · simp only [dif_pos hz]
    exact hlim _

end Pullback

/-! ### Transport along a lift to a localization -/

section Transport

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
  {R : Type*} [CommRing R] [Algebra k R]

/-- **Local approximants from a lift.** Let `ψ : A → R`, `μ : A → C` and `χ : C → R_g` with
`χ ∘ μ = (R → R_g) ∘ ψ`. If `u ∘ μ^an ∈ ℛ(Spec C)`, then `u ∘ ψ^an` is, on `{|g| ≠ 0}`, the limit
of a decreasing sequence of functions of FS type in `R_g`: for `|g|_z ≠ 0`, `ψ^*(z) = μ^*(χ^*(z̃))`. -/
theorem exists_nonflatLocalApprox_of_lift (ψ : A →ₐ[k] R) {C : Type*} [CommRing C] [Algebra k C]
    (μ : A →ₐ[k] C) {g : R} (χ : C →ₐ[k] Localization.Away g)
    (hχ : χ.comp μ = (IsScalarTower.toAlgHom k R (Localization.Away g)).comp ψ)
    {u : Berk k A → EReal} (hu : IsRegularizable (u ∘ comap μ)) :
    ∃ G : ℕ → Berk k R → EReal, (∀ j, IsNonflatAwayFS g (G j)) ∧
      (∀ z, z.val g ≠ 0 → Antitone fun j => G j z) ∧
      ∀ z, z.val g ≠ 0 → u (comap ψ z) = ⨅ j, G j z := by
  obtain ⟨G, hG, hanti, hlim⟩ := hu.exists_isNonflatAwayFS_comap χ
  refine ⟨G, hG, hanti, fun z hz => ?_⟩
  rw [← hlim z hz]
  change u (comap ψ z) = u (comap μ (comap χ (awayLift g z hz)))
  congr 1
  apply Berk.ext_val
  intro a
  have h := congrArg (fun φ : A →ₐ[k] Localization.Away g => (awayLift g z hz).val (φ a)) hχ
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h
  rw [comap_val_apply, comap_val_apply, comap_val_apply, h, awayLift_val_algebraMap]

/-- **Case A of `lem:nf-local-approx`** (away from the centre): if `u|_{Y_{g₀}} ∈ ℛ(Y_{g₀})`, then
`u ∘ ψ^an` is, on `{|ψ(g₀)| ≠ 0}`, the limit of a decreasing sequence of functions of FS type in
`R_{ψ(g₀)}`, through `A_{g₀} → R_{ψ(g₀)}`. -/
theorem exists_nonflatLocalApprox_away (ψ : A →ₐ[k] R) {u : Berk k A → EReal} {g₀ : A}
    (hu : IsRegularizable fun y : Berk k (Localization.Away g₀) => u (awayComap g₀ y)) :
    ∃ G : ℕ → Berk k R → EReal, (∀ j, IsNonflatAwayFS (ψ g₀) (G j)) ∧
      (∀ z, z.val (ψ g₀) ≠ 0 → Antitone fun j => G j z) ∧
      ∀ z, z.val (ψ g₀) ≠ 0 → u (comap ψ z) = ⨅ j, G j z := by
  refine exists_nonflatLocalApprox_of_lift ψ (IsScalarTower.toAlgHom k A (Localization.Away g₀))
    (Localization.awayMapₐ ψ g₀) ?_ hu
  apply AlgHom.ext
  intro a
  simp [Localization.awayMapₐ, IsLocalization.Away.map]

end Transport

/-! ### Lifting a blowup chart -/

section ChartLift

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]

/-- **Lifting a chart of a blowup.** Let `A` be a domain, `0 ≠ σ ∈ A`, `s ⊆ A` finite and
`f : A → T` a `k`-algebra map such that `f(σ)` is a non-zero-divisor and `f(σ) t_{σ'} = f(σ')` for
some `t_{σ'} ∈ T`, `σ' ∈ s`. Then `f` extends to the chart `A[s/σ] ⊆ Frac A`, sending `σ'/σ` to
`t_{σ'}`. Proof: insert `σ` into the actual original family, whose extra ratio is one,
then specialize the genuine original Rees chart universal map and whole paper chart equivalence. -/
theorem nonflat_exists_blowupChart_lift {T : Type*} [CommRing T] [Algebra k T] (f : A →ₐ[k] T)
    (s : Finset A) {σ : A} (hσ : σ ≠ 0) (hreg : ∀ t : T, f σ * t = 0 → t = 0) {t : A → T}
    (ht : ∀ σ' ∈ s, f σ * t σ' = f σ') :
    ∃ χ : blowupChart s σ →ₐ[k] T, χ.comp (chartMap k s σ) = f := by
  classical
  let s' := insert σ s
  let j : s' := ⟨σ, Finset.mem_insert_self _ _⟩
  let u : s' → T := fun i => if (i : A) = σ then 1 else t i
  have hr : (f σ) ∈ nonZeroDivisors T :=
    ⟨hreg, fun x hx => hreg x (by simpa only [mul_comm] using hx)⟩
  have hu : ∀ i : s', f (i : A) = f σ * u i := by
    intro i
    dsimp only [u]
    split_ifs with hi
    · rw [hi, mul_one]
    · exact (ht i (Finset.mem_of_mem_insert_of_ne i.2 hi)).symm
  have hσK : algebraMap A (FractionRing A) σ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr hσ
  have he : blowupChart s' σ = blowupChart s σ := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨a, ha, rfl⟩
      rcases Finset.mem_insert.mp ha with rfl | ha
      · change algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) a ∈ blowupChart s a
        rw [div_self hσK]
        exact one_mem _
      · exact Algebra.subset_adjoin ⟨a, ha, rfl⟩
    · apply Algebra.adjoin_mono
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨a, Finset.mem_insert_of_mem ha, rfl⟩
  let : Algebra A (ReesPaper.Chart s' j) := ReesChart.chartAlgebra (ReesPaper.family s') j
  let e := (ReesPaper.chartEquiv s' j hσ).trans (Subalgebra.equivOfEq _ _ he)
  let χ := (ReesChart.principalLift (ReesPaper.family s') f.toRingHom j u hr hu).comp e.symm.toRingHom
  have hχA : ∀ a : A, χ (algebraMap A (blowupChart s σ) a) = f a := by
    intro a
    change ReesChart.principalLift (ReesPaper.family s') f.toRingHom j u hr hu
      (e.symm (algebraMap A (blowupChart s σ) a)) = _
    rw [e.symm.commutes, ReesChart.principalLift_algebraMap]
    rfl
  refine ⟨{ χ with commutes' := fun c => ?_ }, ?_⟩
  · change χ (algebraMap k (blowupChart s σ) c) = algebraMap k T c
    rw [IsScalarTower.algebraMap_apply k A (blowupChart s σ), hχA, f.commutes]
  · apply AlgHom.ext
    intro a
    exact hχA a

end ChartLift

/-! ### Case B: through a chart of the blowup -/

section Chart

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]
  {R : Type*} [CommRing R] [Algebra k R]

/-- **Case B of `lem:nf-local-approx`** (through a chart of the blowup), in terms of divisibility
data. Let `0 ≠ σ`, `ψ : A → R` and `g ∈ R` with: `ψ(σ)` is a non-zero-divisor after inverting `g`,
and `g ψ(σ') ∈ ψ(σ) R` for every `σ' ∈ s`. If `u ∘ μ_σ ∈ ℛ(A[s/σ])`, then `u ∘ ψ^an` is, on
`{|g| ≠ 0}`, the limit of a decreasing sequence of functions of FS type in `R_g`, through the lift
`A[s/σ] → R_g`, `σ'/σ ↦ a_{σ'}/g` (`EnvelopeProperty.nonflat_exists_blowupChart_lift`). -/
theorem exists_nonflatLocalApprox_chart (ψ : A →ₐ[k] R) {s : Finset A} {σ : A} (hσ : σ ≠ 0)
    {u : Berk k A → EReal} (hu : IsRegularizable (u ∘ comap (chartMap k s σ))) {g : R}
    (hreg : ∀ b : R, ψ σ * b = 0 → ∃ n : ℕ, g ^ n * b = 0)
    (hdiv : ∀ σ' ∈ s, ∃ a : R, g * ψ σ' = ψ σ * a) :
    ∃ G : ℕ → Berk k R → EReal, (∀ j, IsNonflatAwayFS g (G j)) ∧
      (∀ z, z.val g ≠ 0 → Antitone fun j => G j z) ∧
      ∀ z, z.val g ≠ 0 → u (comap ψ z) = ⨅ j, G j z := by
  classical
  let T := Localization.Away g
  let f : A →ₐ[k] T := (IsScalarTower.toAlgHom k R T).comp ψ
  have hf : ∀ a, f a = algebraMap R T (ψ a) := fun _ => rfl
  choose! a ha using hdiv
  let gs : Submonoid.powers g := ⟨g, Submonoid.mem_powers g⟩
  have hregT : ∀ t : T, f σ * t = 0 → t = 0 := by
    intro t ht
    obtain ⟨⟨b, y⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) t
    simp only at ht ⊢
    rw [hf, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at ht
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := ht
    obtain ⟨n, hn⟩ := hreg (g ^ m * b) (by rw [← hm]; ring)
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨g ^ (n + m), n + m, rfl⟩, ?_⟩
    change g ^ (n + m) * b = 0
    rw [pow_add, mul_assoc]
    exact hn
  have ht : ∀ σ' ∈ s, f σ * IsLocalization.mk' T (a σ') gs = f σ' := by
    intro σ' hσ'
    rw [hf, hf, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, ← ha σ' hσ',
      ← map_mul, mul_comm]
  obtain ⟨χ, hχ⟩ := nonflat_exists_blowupChart_lift f s hσ hregT ht
  exact exists_nonflatLocalApprox_of_lift ψ (chartMap k s σ) χ hχ hu

end Chart

/-! ### Divisibility at a point of a product of Dedekind domains -/

section Dedekind

/-- **Total local divisibility in a Dedekind domain.** For a prime `p` of a Dedekind domain `D` and
`a, b ∈ D`, one of `a, b` divides the other in the local ring `D_p`, a discrete valuation ring (or
the fraction field if `p = 0`): there are `c ∉ p` and `d` with `c b = a d` or `c a = b d`. -/
theorem nonflat_dedekind_local_dvd_total {D : Type*} [CommRing D] [IsDedekindDomain D]
    (p : Ideal D) [p.IsPrime] (a b : D) :
    ∃ c ∉ p, ∃ d, c * b = a * d ∨ c * a = b * d := by
  by_cases hp : p = ⊥
  · subst hp
    by_cases ha : a = 0
    · exact ⟨1, by rw [Ideal.mem_bot]; exact one_ne_zero, 0,
        Or.inr (by rw [ha, mul_zero, mul_zero])⟩
    · exact ⟨a, by rw [Ideal.mem_bot]; exact ha, b, Or.inl rfl⟩
  · let O := Localization.AtPrime p
    have : IsDiscreteValuationRing O :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain D hp O
    have hinj : Function.Injective (algebraMap D O) :=
      IsLocalization.injective O p.primeCompl_le_nonZeroDivisors
    obtain ⟨c', hc'⟩ := ValuationRing.cond (algebraMap D O a) (algebraMap D O b)
    obtain ⟨⟨d, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl c'
    simp only at hc'
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mul_mk'_eq_mk'_of_mul,
      IsLocalization.mk'_eq_iff_eq_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, ← map_mul]
      at hc'
    refine ⟨u, u.2, d, ?_⟩
    rcases hc' with h | h
    · exact Or.inl (by rw [mul_comm]; exact (hinj h).symm)
    · exact Or.inr (by rw [mul_comm]; exact (hinj h).symm)

/-- **A minimal element for local divisibility.** If local divisibility at a prime `p` is total,
every nonempty finite family `f(σ)`, `σ ∈ s`, has a member `f(σ)` dividing all others locally at
`p`: `c f(σ') = f(σ) d` with `c ∉ p`. -/
theorem nonflat_exists_local_dvd_min {D : Type*} [CommRing D] (p : Ideal D) [p.IsPrime]
    (htot : ∀ a b : D, ∃ c ∉ p, ∃ d, c * b = a * d ∨ c * a = b * d) {β : Type*} {s : Finset β}
    (hs : s.Nonempty) (f : β → D) :
    ∃ σ ∈ s, ∀ σ' ∈ s, ∃ c ∉ p, ∃ d, c * f σ' = f σ * d := by
  classical
  have h1 : (1 : D) ∉ p := fun h => (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one p).2 h)
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    refine ⟨a, Finset.mem_singleton_self a, fun σ' hσ' => ⟨1, h1, 1, ?_⟩⟩
    rw [Finset.mem_singleton.1 hσ', one_mul, mul_one]
  | cons a s ha hs ih =>
    obtain ⟨m, hm, hmin⟩ := ih
    obtain ⟨c, hc, d, hcd | hcd⟩ := htot (f m) (f a)
    · refine ⟨m, Finset.mem_cons_of_mem hm, fun σ' hσ' => ?_⟩
      rcases Finset.mem_cons.1 hσ' with rfl | hσ'
      · exact ⟨c, hc, d, hcd⟩
      · exact hmin σ' hσ'
    · refine ⟨a, Finset.mem_cons_self a s, fun σ' hσ' => ?_⟩
      rcases Finset.mem_cons.1 hσ' with rfl | hσ'
      · exact ⟨1, h1, 1, by rw [one_mul, mul_one]⟩
      · obtain ⟨c', hc', d', hcd'⟩ := hmin σ' hσ'
        refine ⟨c * c', fun h => ?_, d * d', ?_⟩
        · rcases (Ideal.IsPrime.mem_or_mem ‹_› h) with h | h
          · exact hc h
          · exact hc' h
        · rw [mul_assoc, hcd', ← mul_assoc, hcd, mul_assoc]

variable {k : Type*} [Field k] {A : Type*} [CommRing A]
variable {ι : Type*} [Finite ι] {D : ι → Type*} [∀ i, CommRing (D i)] [Algebra k (∀ i, D i)]

/-- A point of `(Spec ∏ D_i)^an` lives on one factor: some idempotent `e_i` has `|e_i| ≠ 0`. -/
theorem nonflat_exists_val_single_ne_zero [DecidableEq ι] [∀ i, Nontrivial (D i)]
    (x : Berk k (∀ i, D i)) : ∃ i, x.val (Pi.single i 1) ≠ 0 := by
  have := Fintype.ofFinite ι
  by_contra! h
  have h1 : x.val (∑ i, Pi.single i ((1 : ∀ i, D i) i)) ≤ 0 :=
    Valuation.map_sum_le _ fun i _ => (h i).le
  rw [Finset.univ_sum_single, map_one] at h1
  exact one_ne_zero (le_antisymm h1 zero_le)

/-- **Divisibility data at a point of a product of Dedekind domains** (`lem:nf-local-approx`,
Case B, algebraic part). Let `R = ∏ D_i` be a finite product of Dedekind domains, `ψ : A → R` a ring
map, `s ⊆ A` finite with an element `σ₀` whose image is nonzero in every factor, and `x` a point of
`(Spec R)^an`. Let `D = D_i` be the factor of `x` and `p ⊆ D` its kernel. Choosing `σ ∈ s` with
`ψ(σ)_i` of minimal order in the valuation ring `D_p` gives `g ∈ R`, supported on `D_i`, with
`|g|_x ≠ 0`, such that `ψ(σ)` is a non-zero-divisor after inverting `g` and `g ψ(σ') ∈ ψ(σ) R` for
all `σ' ∈ s`. -/
theorem nonflat_exists_chart_denominator [∀ i, IsDedekindDomain (D i)] (ψ : A →+* ∀ i, D i)
    {s : Finset A} (hs : ∃ σ₀ ∈ s, ∀ i, ψ σ₀ i ≠ 0) (x : Berk k (∀ i, D i)) :
    ∃ σ ∈ s, σ ≠ 0 ∧ ∃ g : ∀ i, D i, x.val g ≠ 0 ∧
      (∀ b, ψ σ * b = 0 → ∃ n : ℕ, g ^ n * b = 0) ∧ ∀ σ' ∈ s, ∃ a, g * ψ σ' = ψ σ * a := by
  classical
  obtain ⟨i, hi⟩ := nonflat_exists_val_single_ne_zero x
  -- the valuation of `x` on the factor `D_i`
  have he1 : x.val (Pi.single i (1 : D i)) = 1 := by
    have h2 : x.val (Pi.single i (1 : D i)) * x.val (Pi.single i 1) =
        x.val (Pi.single i 1) * 1 := by
      rw [← map_mul, ← Pi.single_mul, mul_one, mul_one]
    exact mul_left_cancel₀ hi h2
  let w : Valuation (D i) ℝ≥0 :=
    { toFun := fun d => x.val (Pi.single i d)
      map_zero' := by simp only [Pi.single_zero, map_zero]
      map_one' := he1
      map_mul' := fun c d => by simp only [Pi.single_mul, map_mul]
      map_add_le_max' := fun c d => by
        simp only [Pi.single_add]
        exact x.val.map_add _ _ }
  have hw : ∀ d, w d = x.val (Pi.single i d) := fun _ => rfl
  set p := w.supp
  have hp0 : ∀ c, c ∉ p → c ≠ 0 := fun c hc h => hc (h ▸ p.zero_mem)
  obtain ⟨σ₀, hσ₀s, hσ₀⟩ := hs
  obtain ⟨σ, hσs, hmin⟩ := nonflat_exists_local_dvd_min p (nonflat_dedekind_local_dvd_total p)
    ⟨σ₀, hσ₀s⟩ fun a => ψ a i
  have hσi : ψ σ i ≠ 0 := by
    obtain ⟨c, hc, d, hcd⟩ := hmin σ₀ hσ₀s
    intro h
    simp only [h, zero_mul] at hcd
    exact mul_ne_zero (hp0 c hc) (hσ₀ i) hcd
  have hσ : σ ≠ 0 := by
    rintro rfl
    exact hσi (by rw [map_zero, Pi.zero_apply])
  choose! c hc d hd using hmin
  let g' : D i := ∏ σ' ∈ s, c σ'
  have hg' : g' ∉ p := by
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨σ', hσ', h⟩
    exact hc σ' hσ' h
  refine ⟨σ, hσs, hσ, Pi.single i g', ?_, fun b hb => ⟨1, ?_⟩, fun σ' hσ' =>
    ⟨Pi.single i (d σ' * ∏ σ'' ∈ s.erase σ', c σ''), ?_⟩⟩
  · rw [← hw]
    exact fun h => hg' ((Valuation.mem_supp_iff _ _).2 h)
  · funext j
    rw [pow_one, Pi.mul_apply, Pi.zero_apply]
    by_cases hj : j = i
    · subst hj
      have hb' := congrFun hb j
      rw [Pi.mul_apply, Pi.zero_apply] at hb'
      rw [(mul_eq_zero.1 hb').resolve_left hσi, mul_zero]
    · rw [Pi.single_eq_of_ne hj, zero_mul]
  · funext j
    rw [Pi.mul_apply, Pi.mul_apply]
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, Pi.single_eq_same]
      change (∏ σ'' ∈ s, c σ'') * ψ σ' j = _
      rw [← Finset.mul_prod_erase s c hσ', mul_right_comm, hd σ' hσ']
      ring
    · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, zero_mul, mul_zero]

end Dedekind

/-! ### Local approximants at points of a product of Dedekind domains -/

section Main

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]
variable {ι : Type*} [Finite ι] {D : ι → Type*} [∀ i, CommRing (D i)] [∀ i, IsDedekindDomain (D i)]
  [Algebra k (∀ i, D i)]

/-- **Local approximants at points of a product of Dedekind domains** (`lem:nf-local-approx`).
Let `u` be regularizable on the charts of the blowup of `Spec A` along `(s)` (for every
`0 ≠ σ ∈ s`, `u ∘ μ_σ ∈ ℛ(A[s/σ])`), `R = ∏ D_i` a finite product of Dedekind domains and
`ψ : A → R` a `k`-algebra map such that some `σ₀ ∈ s` has nonzero image in every factor. Then for
every point `x` of `(Spec R)^an` there is `g ∈ R` with `|g|_x ≠ 0` such that `u ∘ ψ^an` is, on
`{|g| ≠ 0}`, the limit of a decreasing sequence of functions of FS type in `R_g`. This is the
hypothesis of `EnvelopeProperty.eventually_flatNormFun_nonflatEvalPoint_le` for `u ∘ ψ^an`. -/
theorem exists_nonflatLocalApprox (ψ : A →ₐ[k] ∀ i, D i) {u : Berk k A → EReal} {s : Finset A}
    (hu : ∀ σ ∈ s, σ ≠ 0 → IsRegularizable (u ∘ comap (chartMap k s σ)))
    (hs : ∃ σ₀ ∈ s, ∀ i, ψ σ₀ i ≠ 0) (x : Berk k (∀ i, D i)) :
    ∃ g : ∀ i, D i, x.val g ≠ 0 ∧ ∃ G : ℕ → Berk k (∀ i, D i) → EReal,
      (∀ j, IsNonflatAwayFS g (G j)) ∧ (∀ z, z.val g ≠ 0 → Antitone fun j => G j z) ∧
      ∀ z, z.val g ≠ 0 → u (comap ψ z) = ⨅ j, G j z := by
  obtain ⟨σ, hσs, hσ, g, hxg, hreg, hdiv⟩ := nonflat_exists_chart_denominator (ψ : A →+* ∀ i, D i)
    hs x
  exact ⟨g, hxg, exists_nonflatLocalApprox_chart ψ hσ (hu σ hσs hσ) hreg hdiv⟩

end Main

section Multiple

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
variable {ι : Type*} {D : ι → Type*} [∀ i, CommRing (D i)] [Algebra k (∀ i, D i)]

/-- The hypothesis of `EnvelopeProperty.exists_nonflatLocalApprox` from a multiple: if `ψ(σ₀ a)`
is nonzero in every factor (in the application `σ₀ a = φ(χ_{σ₀}(0))`, whose image `ι(χ_{σ₀}(0))`
in `Q ⊆ D_i` is nonzero), so is `ψ(σ₀)`. -/
theorem nonflat_apply_ne_zero_of_mul (ψ : A →ₐ[k] ∀ i, D i) {σ₀ a : A}
    (h : ∀ i, ψ (σ₀ * a) i ≠ 0) : ∀ i, ψ σ₀ i ≠ 0 := fun i h0 =>
  h i (by rw [map_mul, Pi.mul_apply, h0, zero_mul])

end Multiple

end EnvelopeProperty
