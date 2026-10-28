/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.ChartRegularizable
import EnvelopeProperty.Local.LocalRegularizationPositivity

/-!
# The projection step and local regularization for functions regularizable on blowup charts

Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX), Proposition 5.24
(`prop:projection-step`) and Theorem 5.25 (`thm:normal-local-regularization`) for functions that
are regularizable on the charts of a blowup (`IsChartRegularizable`, `def:nf-chart-regularizable`)
in place of weakly psh functions: the blueprint nodes `prop:nf-projection-step` and
`thm:nf-local-regularization` of the chapter `nonflat-route.tex`.

Both are conditional on the conclusion of FHX Proposition 5.22 (`prop:nonflat-norm`) for this
class, recorded here as the temporary hypothesis class `ChartNonflatNorms k`: it is
`NonflatNorms k` (`Local/NonflatImport.lean`) with the class `IsWeaklyPSHOn Set.univ` of weakly
psh functions replaced by `IsChartRegularizable`. It is **not** an axiom: every theorem using it
lists `[ChartNonflatNorms k]` among its hypotheses. It is to be proved by the nonflat route
(`prop:nf-nonflat-norm`); since the class of functions is smaller, it follows from
`NonflatNorms k` (`ChartNonflatNorms.of_nonflatNorms`, via `NormWeights.ofSubclass`).

The statements and proofs mirror the weakly psh versions `IsRegularizable.of_projection_weaklyPSH`
(`Local/ProjectionWeakly.lean`), `IsRegularizable.of_isWeaklyPSHOn`
(`Local/LocalRegularization.lean`) and their variants in `Local/LocalRegularizationFinal.lean` and
`Local/LocalRegularizationPositivity.lean`. Those proofs use of the weakly psh hypothesis only
upper semicontinuity, stability under adding and taking maxima with regularizable functions
(`IsPshClass`), stability under `u ↦ u ∘ p + log|w|` on `Ỹ = Y × 𝔸¹` and under restriction to
principal opens, and FHX Proposition 5.22 for `π × id`; for the class `IsChartRegularizable`
these are `isPshClass_isChartRegularizable`, `IsChartRegularizable.comp_proj_add_logAbs_X`,
`IsChartRegularizable.comp_awayComap` (`lem:nf-chart-regularizable-closure`) and
`ChartNonflatNorms`.

## Main definitions

* `ChartNonflatNorms k`: FHX Proposition 5.22 for functions regularizable on blowup charts, as a
  hypothesis class.

## Main results

* `IsRegularizable.of_projection_chartRegularizable`: FHX Proposition 5.24 for the class
  (`prop:nf-projection-step`).
* `IsRegularizable.of_isChartRegularizable`: FHX Theorem 5.25 for the class
  (`thm:nf-local-regularization`), conditional on `WuRegularization`, `ChartNonflatNorms` and
  `ProjectionPackage`; `IsRegularizable.of_isChartRegularizable_of_isAlgClosed` (without
  `ProjectionPackage`, which is proved), `…_of_convexPLApproximation` and `…_of_localPositivity`
  (with `ConvexPLApproximation`, resp. `LocalPositivity`, in place of `WuRegularization`).
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open Berk Polynomial

universe u v w

/-! ### The hypothesis class -/

section restrict

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
  {B : Type*} [CommRing B] [Algebra k B]

/-- Weights for a class `W'` are weights for every subclass `W ⊆ W'`. -/
def NormWeights.ofSubclass {φ : B →ₐ[k] A} {S : Finset A} {W W' : (Berk k A → EReal) → Prop}
    {d : ℕ} (hWW' : ∀ u, W u → W' u) (N : NormWeights φ S W' d) : NormWeights φ S W d where
  m := N.m
  one_le := N.one_le
  finite := N.finite
  sum_eq := N.sum_eq
  isRegularizable_norm u hu := N.isRegularizable_norm u (hWW' u hu)

end restrict

/-- **Imported (FHX Proposition 5.22, `prop:nonflat-norm`, for functions regularizable on blowup
charts; `prop:nf-nonflat-norm`), temporarily.** This is `NonflatNorms k` with the class of weakly
psh functions replaced by `IsChartRegularizable`: for every normal affine variety
`Y = Spec A` over the countable algebraically closed trivially valued field `k`, every principal
open `S = Spec B ⊆ 𝔸ⁿ` (`n ≥ 1`), every finite surjective generically étale `π = Spec φ : Y → S`
and every closed `Z = V(S) ⊊ Y`, there are weights `m_y ≥ 1` with
`∑_{π(y)=s} m_y = d = genericDegree φ` such that the weighted norm `N_π u = ∑ m_y u(y)` of every
`u` regularizable on the charts of a blowup, of logarithmic growth, and regularizable on principal
opens covering `Y \ Z`, is regularizable on `S`. See `Local/NonflatImport.lean` for the encoding. -/
class ChartNonflatNorms (k : Type u) [Field k] [IsAlgClosed k] [Countable k] : Prop where
  exists_normWeights : ∀ (A : Type v) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [IsIntegrallyClosed A] (B : Type w) [CommRing B] [Algebra k B]
    (n : ℕ), 1 ≤ n → IsAffineSpacePrincipalOpen k B n →
    ∀ φ : B →ₐ[k] A, Function.Injective φ → (φ : B →+* A).Finite →
      IsGenericallyEtale (φ : B →+* A) →
    ∀ S : Finset A, (∃ f ∈ S, f ≠ 0) →
      Nonempty (NormWeights φ S IsChartRegularizable (genericDegree (φ : B →+* A)))

/-- The weights of FHX Proposition 5.22 for functions regularizable on blowup charts, from
`ChartNonflatNorms`. -/
theorem ChartNonflatNorms.nonempty_normWeights {k : Type u} [Field k] [IsAlgClosed k]
    [Countable k] [ChartNonflatNorms.{u, v, w} k] {A : Type v} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [IsIntegrallyClosed A] {B : Type w} [CommRing B]
    [Algebra k B] {n : ℕ} (hn : 1 ≤ n) (hB : IsAffineSpacePrincipalOpen k B n) (φ : B →ₐ[k] A)
    (hinj : Function.Injective φ) (hfin : (φ : B →+* A).Finite)
    (het : IsGenericallyEtale (φ : B →+* A)) (S : Finset A) (hS : ∃ f ∈ S, f ≠ 0) :
    Nonempty (NormWeights φ S IsChartRegularizable (genericDegree (φ : B →+* A))) :=
  ChartNonflatNorms.exists_normWeights A B n hn hB φ hinj hfin het S hS

/-- `NonflatNorms` (FHX Proposition 5.22 for weakly psh functions) implies `ChartNonflatNorms`:
functions regularizable on the charts of a blowup are weakly psh
(`IsChartRegularizable.isWeaklyPSHOn`). -/
instance (priority := 100) ChartNonflatNorms.of_nonflatNorms {k : Type u} [Field k]
    [IsAlgClosed k] [Countable k] [NonflatNorms.{u, v, w} k] : ChartNonflatNorms.{u, v, w} k where
  exists_normWeights _ _ _ _ _ _ _ _ _ _ hn hB φ hinj hfin het S hS :=
    let ⟨N⟩ := NonflatNorms.nonempty_normWeights hn hB φ hinj hfin het S hS
    ⟨N.ofSubclass fun _ hu => hu.isWeaklyPSHOn⟩

/-! ### The projection step (`prop:nf-projection-step`) -/

section projection

variable {k : Type u} [Field k] [IsAlgClosed k] [Countable k] [ChartNonflatNorms.{u, v, w} k]
  [WuRegularization.{u, v} k]
  {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
  [IsIntegrallyClosed A] {B : Type w} [CommRing B] [Algebra k B]

/-- **The projection step for functions regularizable on blowup charts** (FHX Proposition 5.24,
`prop:projection-step`, in the form `prop:nf-projection-step`), conditional on FHX Proposition
5.22 for this class (`ChartNonflatNorms k`) and on the imported FHX Lemma 5.11(5),(6)
(`WuRegularization k`).

Let `Y = Spec A` be a normal affine variety, `S = Spec B` a principal open of `𝔸ⁿ` (`hB`), and
`π = Spec φ` finite (`hfin`), surjective (`hinj`) and generically étale (`het`). Let `Z = V(S) ⊊ Y`
(`hS`) with `π|_Z` a closed immersion (`hZimm`), and `f₁ + f₂ = 1` with `f₂ = 0` on `Z^an` and
`f₁ = 0` on `π⁻¹(π(Z^an)) \ Z^an` (`Z'` closed). If `u` is regularizable on the charts of a blowup,
of logarithmic growth and regularizable on principal opens covering `Y \ Z`, then `u` is
regularizable. As `IsRegularizable.of_projection_weaklyPSH`, with
`isPshClass_isChartRegularizable` and `IsChartRegularizable.comp_proj_add_logAbs_X`
(`lem:nf-chart-regularizable-closure`) and `ChartNonflatNorms` for `π × id` and `Z × 𝔸¹`. -/
theorem IsRegularizable.of_projection_chartRegularizable {n : ℕ}
    (hB : IsAffineSpacePrincipalOpen k B n) (φ : B →ₐ[k] A) (hinj : Function.Injective φ)
    (hfin : (φ : B →+* A).Finite) (het : IsGenericallyEtale (φ : B →+* A)) (S : Finset A)
    (hS : ∃ f ∈ S, f ≠ 0)
    (hZimm : Function.Surjective
      ((Ideal.Quotient.mk (Ideal.span (S : Set A))).comp (φ : B →+* A)))
    {f₁ f₂ : A} (hf : f₁ + f₂ = 1)
    (hf₂ : ∀ y : Berk k A, (∀ f ∈ S, y.val f = 0) → y.val f₂ = 0)
    (hf₁ : ∀ y y' : Berk k A, (∀ f ∈ S, y.val f = 0) → comap φ y' = comap φ y →
      (∃ f ∈ S, y'.val f ≠ 0) → y'.val f₁ = 0)
    {u : Berk k A → EReal} (hu : IsChartRegularizable u) (hlog : HasLogGrowth u)
    (hcover : ∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y)) :
    IsRegularizable u := by
  have := hB.finiteType
  -- the conclusion of FHX Proposition 5.22 for `π × id` and `Z × 𝔸¹`
  obtain ⟨N'⟩ := ChartNonflatNorms.nonempty_normWeights (k := k) (A := A[X]) (B := B[X])
    (Nat.le_add_left 1 n) hB.polynomial (mapAlgHom φ) (map_injective _ hinj)
    (finite_mapAlgHom hfin) (isGenericallyEtale_mapRingHom het) (S.map ⟨C, C_injective⟩)
    (by
      obtain ⟨f, hfS, hf0⟩ := hS
      exact ⟨C f, Finset.mem_map_of_mem _ hfS, C_ne_zero.2 hf0⟩)
  exact IsRegularizable.of_projection φ hfin.to_isIntegral S hS hZimm hf hf₂ hf₁
    isPshClass_isChartRegularizable isPshClass_isChartRegularizable N' hu
    hu.comp_proj_add_logAbs_X hlog hcover

end projection

/-! ### Local regularization (`thm:nf-local-regularization`) -/

section main

variable {k : Type u} [Field k] [IsAlgClosed k] [Countable k] [WuRegularization.{u, v} k]
  [ChartNonflatNorms.{u, v, u} k] [ProjectionPackage.{u, v} k]
  {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
  [IsIntegrallyClosed A]

/-- **Local regularization for functions regularizable on blowup charts** (FHX Theorem 5.25,
`thm:normal-local-regularization`, in the form `thm:nf-local-regularization`), conditional on FHX
Lemma 5.11(5),(6) (`WuRegularization k`), FHX Proposition 5.22 for this class
(`ChartNonflatNorms k`) and the algebraic geometry of Lemma 5.23 and of the proof of Theorem 5.25
(`ProjectionPackage k`).

Let `Y = Spec A` be a normal affine variety and `Z = V(S) ⊊ Y` (`hS`). If `u` is regularizable on
the charts of a blowup, of logarithmic growth, and regularizable on principal opens covering
`Y^an \ Z^an`, then `u` is regularizable. The proof is that of `IsRegularizable.of_isWeaklyPSHOn`:
restrictions to principal opens stay in the class (`IsChartRegularizable.comp_awayComap`), and the
projection step `IsRegularizable.of_projection_chartRegularizable` replaces
`IsRegularizable.of_projection_weaklyPSH`. -/
theorem IsRegularizable.of_isChartRegularizable (S : Finset A) (hS : ∃ f ∈ S, f ≠ 0)
    {u : Berk k A → EReal} (hu : IsChartRegularizable u) (hlog : HasLogGrowth u)
    (hcover : ∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y)) :
    IsRegularizable u := by
  classical
  -- `G`: the `g` with `u` regularizable on `Y_g`; `W = V(I)` is the complement of their union
  set G : Set A := {g | IsRegularizable fun y : Berk k (Localization.Away g) => u (awayComap g y)}
    with hG
  set I : Ideal A := (Ideal.span G).radical with hI
  have hGI : ∀ g ∈ G, g ∈ I := fun g hg => Ideal.le_radical (Ideal.subset_span hg)
  -- points of `Y^an` off `W^an` lie in some `Y_g^an`, `g ∈ G`
  have hcovI : ∀ x : Berk k A, ¬ I ≤ x.val.supp →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y) := by
    intro x hx
    by_contra hcon
    push Not at hcon
    refine hx ((Ideal.IsPrime.radical_le_iff inferInstance).2 (Ideal.span_le.2 fun g hg => ?_))
    rw [SetLike.mem_coe, Valuation.mem_supp_iff]
    by_contra hxg
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact hxg (map_zero _)
    exact hcon g hg0 hxg hg
  by_cases htop : I = ⊤
  · -- `Σ = Y`: regularizability is local
    refine IsRegularizable.of_cover_principal hu.upperSemicontinuous hlog fun x => hcovI x ?_
    rw [htop, top_le_iff]
    exact Ideal.IsPrime.ne_top inferInstance
  exfalso
  -- `W ≠ Y`
  have hbot : I ≠ ⊥ := by
    obtain ⟨f, hfS, hf0⟩ := hS
    refine fun hbot => hf0 ?_
    have hfI : f ∈ I := by
      rw [hI, Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro P ⟨hGP, hP⟩
      by_contra hfP
      obtain ⟨x, hx⟩ := Berk.exists_supp_eq (k := k) P
      have hxf : x.val f ≠ 0 := by
        rwa [Ne, ← Valuation.mem_supp_iff, hx]
      obtain ⟨g, -, hxg, hg⟩ := hcover x ⟨f, hfS, hxf⟩
      exact hxg ((Valuation.mem_supp_iff _ _).1 (hx ▸ hGP (Ideal.subset_span hg)))
    rwa [hbot, Ideal.mem_bot] at hfI
  -- the algebraic-geometry package
  obtain ⟨D⟩ := ProjectionPackage.nonempty (k := k) (Ideal.radical_isRadical _) hbot htop
  obtain ⟨P₀, hP₀, hIP₀, hhP₀⟩ := D.exists_prime
  have hh : D.h ≠ 0 := fun h0 => hhP₀ (h0 ▸ P₀.zero_mem)
  have := isDomain_localizationAway hh
  have := isIntegrallyClosed_localizationAway hh
  set Ah := Localization.Away D.h
  -- a finite generating set of `I A_h`
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian I : I.FG)
  set S' : Finset Ah := T.map (awayEmb hh)
  have hS'span : Ideal.span (S' : Set Ah) = I.map (algebraMap A Ah) := by
    rw [← hT, Ideal.map_span, Finset.coe_map]
    rfl
  have hS' : ∃ f ∈ S', f ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hbot ?_
    rw [← hT, Ideal.span_eq_bot]
    intro t ht
    exact algebraMap_away_injective hh
      ((hcon _ (Finset.mem_map_of_mem _ ht)).trans (map_zero _).symm)
  have hsupp : ∀ y : Berk k Ah, (∀ f ∈ S', y.val f = 0) → I.map (algebraMap A Ah) ≤ y.val.supp :=
    fun y hy => hS'span ▸ Ideal.span_le.2 fun f hf => (Valuation.mem_supp_iff _ _).2 (hy f hf)
  -- `u` is regularizable on `D(h)`
  have hreg : IsRegularizable fun y : Berk k Ah => u (awayComap D.h y) := by
    refine IsRegularizable.of_projection_chartRegularizable (B := Localization.Away D.h₀)
      ⟨D.h₀, D.h₀_ne_zero, ⟨AlgEquiv.refl⟩⟩ D.φ D.injective D.finite D.genericallyEtale S' hS'
      (by rw [hS'span]; exact D.closedImmersion) D.add_eq_one ?_ ?_ (hu.comp_awayComap hh)
      (hlog.comp_comap _) ?_
    · -- `f₂ = 0` on `Z^an`
      intro y hy
      rw [← Valuation.mem_supp_iff]
      exact (Ideal.IsPrime.radical_le_iff inferInstance).2 (hsupp y hy) D.f₂_mem
    · -- `f₁ = 0` on `π⁻¹(π(Z^an)) \ Z^an`
      intro y y' hy hyy' hy'
      rw [← Valuation.mem_supp_iff]
      refine D.f₁_mem _ _ inferInstance inferInstance (hsupp y hy) (fun hle => ?_) ?_
      · obtain ⟨f, hf, hy'f⟩ := hy'
        exact hy'f ((Valuation.mem_supp_iff _ _).1 (hle (hS'span ▸ Ideal.subset_span hf)))
      · rw [← supp_comap, ← supp_comap, hyy']
    · -- the cover of `D(h) \ Z`
      rintro x ⟨f, hf, hxf⟩
      have hx : ¬ I ≤ (awayComap D.h x).val.supp := by
        intro hle
        refine hxf ((Valuation.mem_supp_iff _ _).1 ?_)
        have hle' : I.map (algebraMap A Ah) ≤ x.val.supp := by
          rw [Ideal.map_le_iff_le_comap]
          rw [awayComap_eq, supp_comap] at hle
          exact hle
        exact hle' (hS'span ▸ Ideal.subset_span hf)
      obtain ⟨g, hg0, hxg, hg⟩ := hcovI _ hx
      have hxg' : x.val (algebraMap A Ah g) ≠ 0 := hxg
      refine ⟨algebraMap A Ah g, fun h0 => hxg' (h0 ▸ map_zero _), hxg', ?_⟩
      exact IsRegularizable.comp_awayComap_algebraMap hh hg0 hg
  -- so `D(h) ⊆ Σ`, contradicting `D(h) ∩ W ≠ ∅`
  exact hhP₀ (hIP₀ (hGI _ hreg))

end main

/-! ### Variants with the proved and the reduced hypotheses -/

/-- **FHX Theorem 5.25 for functions regularizable on blowup charts**
(`thm:nf-local-regularization`), conditional only on `WuRegularization` and `ChartNonflatNorms`:
`ProjectionPackage` holds over every algebraically closed field
(`ProjectionExistence.toProjectionPackage`, `projectionExistence_of_isAlgClosed`). -/
theorem IsRegularizable.of_isChartRegularizable_of_isAlgClosed {k : Type u} [Field k]
    [IsAlgClosed k] [Countable k] [WuRegularization.{u, v} k] [ChartNonflatNorms.{u, v, u} k]
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [IsIntegrallyClosed A] (S : Finset A) (hS : ∃ f ∈ S, f ≠ 0) {u : Berk k A → EReal}
    (hu : IsChartRegularizable u) (hlog : HasLogGrowth u)
    (hcover : ∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y)) :
    IsRegularizable u :=
  IsRegularizable.of_isChartRegularizable S hS hu hlog hcover

/-- **FHX Theorem 5.25 for functions regularizable on blowup charts**, conditional only on
`ConvexPLApproximation` (approximation of convex PL functions standard at infinity,
`thm:wu-pl-approx`, which implies `WuRegularization`) and `ChartNonflatNorms`. -/
theorem IsRegularizable.of_isChartRegularizable_of_convexPLApproximation {k : Type u} [Field k]
    [IsAlgClosed k] [Countable k] [ConvexPLApproximation.{u, v} k]
    [ChartNonflatNorms.{u, v, u} k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [IsIntegrallyClosed A] (S : Finset A) (hS : ∃ f ∈ S, f ≠ 0)
    {u : Berk k A → EReal} (hu : IsChartRegularizable u) (hlog : HasLogGrowth u)
    (hcover : ∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y)) :
    IsRegularizable u :=
  IsRegularizable.of_isChartRegularizable_of_isAlgClosed S hS hu hlog hcover

/-- **FHX Theorem 5.25 for functions regularizable on blowup charts**, conditional only on FHX
Lemma 5.5 (`LocalPositivity`, which implies `ConvexPLApproximation`) and `ChartNonflatNorms`. -/
theorem IsRegularizable.of_isChartRegularizable_of_localPositivity {k : Type u} [Field k]
    [IsAlgClosed k] [Countable k] [LocalPositivity.{u} k] [ChartNonflatNorms.{u, v, u} k]
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [IsIntegrallyClosed A] (S : Finset A) (hS : ∃ f ∈ S, f ≠ 0) {u : Berk k A → EReal}
    (hu : IsChartRegularizable u) (hlog : HasLogGrowth u)
    (hcover : ∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y)) :
    IsRegularizable u :=
  IsRegularizable.of_isChartRegularizable_of_convexPLApproximation S hS hu hlog hcover

end EnvelopeProperty
