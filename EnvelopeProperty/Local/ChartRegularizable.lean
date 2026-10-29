/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.LocalRegularization
import EnvelopeProperty.Projective.BlowupDescentCharts

/-!
# Functions regularizable on the charts of a blowup

This file introduces the class of functions to which the nonflat route of the blueprint chapter
`nonflat-route.tex` proves Fang–Han–Xia, *The envelope property for unibranch projective
varieties* (FHX), Propositions 5.22, 5.24 and Theorem 5.25 (`prop:nonflat-norm`,
`prop:projection-step`, `thm:normal-local-regularization`), and proves its closure properties.

A function `u : Y^an → [-∞, ∞)` on `Y = Spec A` (`A` a domain) is **regularizable on the charts
of a blowup** (`IsChartRegularizable u`, blueprint `def:nf-chart-regularizable`) if there is a
finite set `s ⊆ A` containing a nonzero element (the *witness*) such that for every
`g ∈ s \ {0}` the pullback `u ∘ μ_g^an` to the chart `Spec A[s/g]` of the blowup of `Y` along
`(s)` lies in `ℛ(A[s/g])` (FHX Definition 5.7(3)). Here `A[s/g] ⊆ Frac A` is
`EnvelopeProperty.blowupChart s g` and `μ_g^an = comap (chartMap k s g)` is restriction along
`A ⊆ A[s/g]`.

Regularizable functions are decreasing limits of Fubini–Study, hence convex PL, functions, so
these functions are weakly psh in the sense of FHX Definition 5.6 (`IsWeaklyPSHOn`), with the
same blowup as witness. The class is smaller than the class of weakly psh functions of FHX
Proposition 5.22, and it contains the functions to which FHX Corollary 5.26
(`cor:normal-weak-global`) applies Theorem 5.25 (`lem:nf-descent-chart`).

## Main definitions

* `IsChartRegularizable u`: `u` is regularizable on the charts of a blowup
  (`def:nf-chart-regularizable`).

## Main results (`lem:nf-chart-regularizable-closure`)

* `IsChartRegularizable.isWeaklyPSHOn`, `IsChartRegularizable.upperSemicontinuous` (item (1)).
* `IsChartRegularizable.add_isRegularizable`, `IsChartRegularizable.max_isRegularizable` (item
  (2)), with `IsRegularizable.comp_comap_chartMap` (regularizable functions on `Y` pull back to
  every chart: the trivial valuation of the chart lies over that of `Y`); also
  `IsChartRegularizable.add_const`, `IsChartRegularizable.smul`, `IsChartRegularizable.congr`
  and `IsRegularizable.isChartRegularizable` (witness `{1}`).
* `IsChartRegularizable.comp_awayComap` (item (3)): restriction to a principal open `Y_h`, with
  the image of the witness (the chart `A[s/g]` maps to the chart `A_h[s/g]`, `chartAwayMap`).
* `IsChartRegularizable.comp_proj`, `IsChartRegularizable.comp_proj_add_logAbs_X` (item (4)): on
  `Ỹ = Y × 𝔸¹ = Spec A[w]`, `u ∘ p` and `u ∘ p + log|w|`, with witness `C(s)` (the chart `A[s/g]`
  maps to the chart `A[w][C s / C g]`, `chartPolyMap`).
* `isPshClass_isChartRegularizable`: the class is an `IsPshClass`, the closure properties used by
  the projection step (`IsRegularizable.of_projection`).
* `ProjSubvariety.BlowupCenter.isChartRegularizable_descentChartFun` (`lem:nf-descent-chart`):
  the chart functions `u_i` of the psh descent along blowups (FHX Corollary 5.26,
  `thm:pg-psh-descent`) are regularizable on the charts of the blowup along `𝔞_i`; this is
  `ProjSubvariety.BlowupCenter.isRegularizable_descentChartFun_comap_chartMap`.

## Notes

* Every function of the class is finite at the trivial valuation
  (`IsChartRegularizable.triv_ne_bot`): the trivial valuation of each chart lies over the
  trivial valuation of `Y` (`comap_chartMap_triv`) and regularizable functions are finite there
  (`IsRegularizable.triv_ne_bot`). This is what makes the pullbacks in items (2)–(4) not
  identically `-∞` (FHX Lemma 5.11(4)).
* Decreasing limits are not treated: FHX Lemma 5.11(2) (`IsRegularizable.of_antitone`) needs the
  charts to be normal, which blowup charts need not be, and the projection step does not use
  them.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open Berk Polynomial

universe u

/-! ### The class -/

section defs

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]

/-- **Functions regularizable on the charts of a blowup** (`def:nf-chart-regularizable`): for
some finite `s ⊆ A` containing a nonzero element (the witness), the pullback
`u ∘ μ_g^an : (Spec A[s/g])^an → [-∞, ∞)` of `u` to every chart `A[s/g]`, `g ∈ s \ {0}`, of the
blowup of `Spec A` along `(s)` is regularizable (FHX Definition 5.7(3)). -/
def IsChartRegularizable (u : Berk k A → EReal) : Prop :=
  ∃ s : Finset A, (∃ g ∈ s, g ≠ 0) ∧ ∀ g ∈ s, g ≠ 0 →
    IsRegularizable fun y : Berk k (blowupChart s g) => u (comap (chartMap k s g) y)

end defs

/-! ### Closure properties (`lem:nf-chart-regularizable-closure`) -/

section closure

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]
  {u v : Berk k A → EReal}

/-- A function regularizable on the charts of a blowup is finite at the trivial valuation: the
trivial valuation of a chart lies over the trivial valuation of `Y` (`comap_chartMap_triv`), and
regularizable functions are finite there (`IsRegularizable.triv_ne_bot`). -/
theorem IsChartRegularizable.triv_ne_bot (hu : IsChartRegularizable u) :
    u (triv : Berk k A) ≠ ⊥ := by
  obtain ⟨s, ⟨g, hg, hg0⟩, hreg⟩ := hu
  have h := (hreg g hg hg0).triv_ne_bot
  rwa [comap_chartMap_triv] at h

/-- A function regularizable on the charts of a blowup is not identically `-∞`. -/
theorem IsChartRegularizable.exists_ne_bot (hu : IsChartRegularizable u) : ∃ x, u x ≠ ⊥ :=
  ⟨triv, hu.triv_ne_bot⟩

/-- The class is stable under pointwise equality, with the same witness. -/
theorem IsChartRegularizable.congr (hu : IsChartRegularizable u) (h : ∀ x, u x = v x) :
    IsChartRegularizable v := by
  obtain ⟨s, hs, hreg⟩ := hu
  exact ⟨s, hs, fun g hg hg0 => (hreg g hg hg0).congr fun y => h _⟩

/-- **Functions regularizable on the charts of a blowup are weakly psh**
(`lem:nf-chart-regularizable-closure`(1)), with the same blowup as witness: regularizable
functions are locally psh on every open set (`IsRegularizable.isLocallyPSHOn`). -/
theorem IsChartRegularizable.isWeaklyPSHOn (hu : IsChartRegularizable u) :
    IsWeaklyPSHOn Set.univ u := by
  obtain ⟨s, hs, hreg⟩ := hu
  exact ⟨s, hs, fun g hg hg0 =>
    (hreg g hg hg0).isLocallyPSHOn (isOpen_univ.preimage (continuous_comap _))⟩

/-- **Functions regularizable on the charts of a blowup are upper semicontinuous**
(`lem:nf-chart-regularizable-closure`(1)), as weakly psh functions are
(`IsWeaklyPSHOn.upperSemicontinuous`). -/
theorem IsChartRegularizable.upperSemicontinuous [Algebra.FiniteType k A]
    (hu : IsChartRegularizable u) : UpperSemicontinuous u :=
  hu.isWeaklyPSHOn.upperSemicontinuous

/-- **Regularizable functions pull back to every chart of a blowup** (FHX Lemma 5.11(4)): the
pullback is finite at the trivial valuation of the chart, which lies over the trivial valuation of
`Y` (`comap_chartMap_triv`). -/
theorem IsRegularizable.comp_comap_chartMap [Algebra.FiniteType k A] (hv : IsRegularizable v)
    (s : Finset A) (g : A) :
    IsRegularizable fun y : Berk k (blowupChart s g) => v (comap (chartMap k s g) y) :=
  hv.comp_comap (chartMap k s g) ⟨triv, by rw [comap_chartMap_triv]; exact hv.triv_ne_bot⟩

/-- **Regularizable functions are regularizable on the charts of a blowup**, with witness `{1}`
(the blowup along the unit ideal). -/
theorem IsRegularizable.isChartRegularizable [Algebra.FiniteType k A] (hu : IsRegularizable u) :
    IsChartRegularizable u :=
  ⟨{1}, ⟨1, Finset.mem_singleton_self 1, one_ne_zero⟩, fun g _ _ =>
    hu.comp_comap_chartMap {1} g⟩

/-- **Adding a regularizable function** (`lem:nf-chart-regularizable-closure`(2)), with the same
witness: sums of regularizable functions on a chart are regularizable. -/
theorem IsChartRegularizable.add_isRegularizable [Algebra.FiniteType k A]
    (hu : IsChartRegularizable u) (hv : IsRegularizable v) :
    IsChartRegularizable fun x => u x + v x := by
  obtain ⟨s, hs, hreg⟩ := hu
  exact ⟨s, hs, fun g hg hg0 => (hreg g hg hg0).add (hv.comp_comap_chartMap s g)⟩

/-- **The maximum with a regularizable function** (`lem:nf-chart-regularizable-closure`(2)),
with the same witness. -/
theorem IsChartRegularizable.max_isRegularizable [Algebra.FiniteType k A]
    (hu : IsChartRegularizable u) (hv : IsRegularizable v) :
    IsChartRegularizable fun x => max (u x) (v x) := by
  obtain ⟨s, hs, hreg⟩ := hu
  exact ⟨s, hs, fun g hg hg0 => (hreg g hg hg0).sup (hv.comp_comap_chartMap s g)⟩

/-- Adding a real constant, with the same witness. -/
theorem IsChartRegularizable.add_const (hu : IsChartRegularizable u) (c : ℝ) :
    IsChartRegularizable fun x => u x + (c : EReal) := by
  obtain ⟨s, hs, hreg⟩ := hu
  exact ⟨s, hs, fun g hg hg0 => (hreg g hg hg0).add_const c⟩

/-- Multiplication by a positive rational, with the same witness. -/
theorem IsChartRegularizable.smul (hu : IsChartRegularizable u) {c : ℚ} (hc : 0 < c) :
    IsChartRegularizable fun x => ((c : ℝ) : EReal) * u x := by
  obtain ⟨s, hs, hreg⟩ := hu
  exact ⟨s, hs, fun g hg hg0 => (hreg g hg hg0).smul hc⟩

/-- **Functions regularizable on the charts of a blowup form an `IsPshClass`**: they are upper
semicontinuous, and stable under adding, and taking the maximum with, regularizable functions
(`lem:nf-chart-regularizable-closure`(1),(2)). This is the class hypothesis of the projection step
(`IsRegularizable.of_projection`). -/
theorem isPshClass_isChartRegularizable [Algebra.FiniteType k A] :
    IsPshClass (IsChartRegularizable (k := k) (A := A)) where
  usc _ hu := hu.upperSemicontinuous
  add_reg _ _ hu hv := hu.add_isRegularizable hv
  max_reg _ _ hu hv := hu.max_isRegularizable hv

end closure

/-! ### Restriction to principal opens (`lem:nf-chart-regularizable-closure`(3)) -/

section away

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A] {u : Berk k A → EReal} {h : A}

/-- **Restriction to a principal open** (`lem:nf-chart-regularizable-closure`(3)): if `s` is a
witness for `u` on `Y`, its image in `A_h` (`h ≠ 0`) is one for `u|_{Y_h}`. The chart `A[s/g]`
maps to the chart `A_h[s/g]` over `A → A_h` (`chartAwayMap`, `awayComap_comap_chartMap`), and the
pullback of the regularizable `u ∘ μ_g^an` along it is regularizable (FHX Lemma 5.11(4)), being
finite at the trivial valuation. -/
theorem IsChartRegularizable.comp_awayComap (hh : h ≠ 0) [IsDomain (Localization.Away h)]
    (hu : IsChartRegularizable u) :
    IsChartRegularizable fun y : Berk k (Localization.Away h) => u (awayComap h y) := by
  have : Algebra.FiniteType k (Localization.Away h) :=
    finiteType_localizationAway_of_finiteType h
  have htriv := hu.triv_ne_bot
  obtain ⟨s, ⟨g₀, hg₀, hg₀0⟩, hreg⟩ := hu
  refine ⟨s.map (awayEmb hh), ⟨awayEmb hh g₀, Finset.mem_map_of_mem _ hg₀,
    (map_ne_zero_iff _ (algebraMap_away_injective hh)).2 hg₀0⟩, ?_⟩
  intro g' hg' hg'0
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.1 hg'
  have hg0 : g ≠ 0 := fun h0 => hg'0 (by simp [h0])
  have hne : ∃ y, u (comap (chartMap k s g) (comap (chartAwayMap k hh s g) y)) ≠ ⊥ := by
    refine ⟨triv, ?_⟩
    rw [← awayComap_comap_chartMap, comap_chartMap_triv, awayComap_triv]
    exact htriv
  exact ((hreg g hg hg0).comp_comap (chartAwayMap k hh s g) hne).congr fun y =>
    congrArg u (awayComap_comap_chartMap hh s g y).symm

end away

/-! ### Pullback to `Y × 𝔸¹` (`lem:nf-chart-regularizable-closure`(4)) -/

section poly

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A] {u : Berk k A → EReal}

/-- **Pullback to `Ỹ = Y × 𝔸¹`**: if `s` is a witness for `u`, then `C(s)` is one for `u ∘ p`.
The chart `A[s/g]` maps to the chart `A[w][C s / C g]` over `C : A → A[w]` (`chartPolyMap`,
`proj_comap_chartMap`), and the pullback is finite at the trivial valuation. -/
theorem IsChartRegularizable.comp_proj (hu : IsChartRegularizable u) :
    IsChartRegularizable fun z : Berk k A[X] => u (proj z) := by
  have htriv := hu.triv_ne_bot
  have hp : proj (triv : Berk k A[X]) = triv := by
    refine Berk.ext (Valuation.ext fun a => ?_)
    by_cases ha : a = 0
    · rw [ha, map_zero, map_zero]
    · rw [proj_val_apply, triv_val_of_ne_zero ha, triv_val_of_ne_zero (C_ne_zero.2 ha)]
  obtain ⟨s, ⟨g₀, hg₀, hg₀0⟩, hreg⟩ := hu
  refine ⟨s.map ⟨C, C_injective⟩, ⟨C g₀, Finset.mem_map_of_mem _ hg₀, C_ne_zero.2 hg₀0⟩, ?_⟩
  intro g' hg' hg'0
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.1 hg'
  have hg0 : g ≠ 0 := fun h0 => hg'0 (by simp [h0])
  have hne : ∃ y, u (comap (chartMap k s g) (comap (chartPolyMap k s g) y)) ≠ ⊥ := by
    refine ⟨triv, ?_⟩
    rw [← proj_comap_chartMap, comap_chartMap_triv, hp]
    exact htriv
  exact ((hreg g hg hg0).comp_comap (chartPolyMap k s g) hne).congr fun y =>
    congrArg u (proj_comap_chartMap s g y).symm

/-- **`u ∘ p + log|w|` on `Ỹ = Y × 𝔸¹`** (`lem:nf-chart-regularizable-closure`(4)): with witness
`C(s)`, since `log|w|` is regularizable on `Ỹ` (`isRegularizable_logAbs_X`). -/
theorem IsChartRegularizable.comp_proj_add_logAbs_X (hu : IsChartRegularizable u) :
    IsChartRegularizable fun z : Berk k A[X] => u (proj z) + logAbs (X : A[X]) z :=
  hu.comp_proj.add_isRegularizable isRegularizable_logAbs_X

end poly

/-! ### The functions of the descent corollary (`lem:nf-descent-chart`) -/

namespace ProjSubvariety.BlowupCenter

open ProjBerk (QuotChartAlg)

variable {k : Type u} [Field k] {M : ℕ} {V : ProjSubvariety k M} {M' : ℕ} (B : V.BlowupCenter M')
  (i : Fin (M + 1)) [IsDomain (QuotChartAlg V.ideal (MvPolynomial.X i) 1)]

/-- **The chart functions of the psh descent along blowups are regularizable on the charts of a
blowup** (`lem:nf-descent-chart`), with witness `𝔞_i = B.centerSet i`. In the setting of FHX
Corollary 5.26 (`thm:pg-psh-descent`: `k` countable, `φ ∘ μ ∈ PSH(X', (a, 0))`), for `x_i ∉ I` the
function `u_i = (φ - a log|x_i|) ∘ ι_i⁻¹` (`ProjSubvariety.descentChartFun`) pulls back to a
regularizable function on every chart `Spec A_i[𝔞_i/g]`, `g ∈ 𝔞_i \ {0}`
(`isRegularizable_descentChartFun_comap_chartMap`), and `𝔞_i` has a nonzero element
(`exists_mem_centerSet_ne_zero`). -/
theorem isChartRegularizable_descentChartFun [Countable k] {a : ℚ} {φ : V.an → EReal}
    (h : B.IsPSH ![(a : ℝ), 0] (φ ∘ B.proj)) :
    IsChartRegularizable (V.descentChartFun i a φ) :=
  ⟨B.centerSet i, B.exists_mem_centerSet_ne_zero i, fun _ hg hg0 =>
    B.isRegularizable_descentChartFun_comap_chartMap i h hg hg0⟩

end ProjSubvariety.BlowupCenter

end EnvelopeProperty
