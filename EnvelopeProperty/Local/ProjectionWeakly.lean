/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.NonflatImport

/-!
# The projection step for weakly psh functions

Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Proposition 5.24
(`prop:projection-step`) for weakly psh functions, conditional only on FHX Proposition 5.22
(`prop:nonflat-norm`, the hypothesis class `NonflatNorms k`) and on the imported Lemma 5.11(5),(6)
(`WuRegularization k`).

Let `Y = Spec A` be a normal affine variety, `S = Spec B ⊆ 𝔸ⁿ` a principal open,
`π = Spec φ : Y → S` finite surjective generically étale, and `Z = V(S) ⊊ Y` such that `π|_Z` is
a closed immersion and `Z' = π⁻¹(π(Z)) \ Z` is closed. If `u` is weakly psh of logarithmic growth
and regularizable on principal opens covering `Y \ Z`, then `u` is regularizable.

`IsRegularizable.of_projection` (in `EnvelopeProperty.Local.ProjectionStep`) proves this for an
abstract class `W` of functions, given the conclusion of Proposition 5.22 for
`π × id : Ỹ = Y × 𝔸¹ → S × 𝔸¹` and `Z × 𝔸¹` as a hypothesis `N'`, and a class `W'` on `Ỹ`
containing `u ∘ p + log|w|`. Here `W` and `W'` are the weakly psh functions
(`isPshClass_isWeaklyPSHOn_univ`), and all the data on `Ỹ` are derived:

* `S × 𝔸¹ = Spec B[X]` is a principal open of `𝔸ⁿ⁺¹`
  (`IsAffineSpacePrincipalOpen.polynomial`: `B[X] ≅ k[x]_h[X] ≅ k[x, x_{n+1}]_h`);
* `A[X]` is a normal domain of finite type (Mathlib instances);
* `mapAlgHom φ : B[X] → A[X]` is injective, finite (`finite_mapAlgHom`) and generically étale
  (`isGenericallyEtale_mapRingHom`: `B[X]_h ≅ B_h[X] → A_{φ h}[X] ≅ A[X]_{φ h}` is the base
  change of `B_h → A_{φ h}` along `B_h → B_h[X]`);
* `u ∘ p` is weakly psh on `Ỹ` (`IsWeaklyPSHOn.comp_proj`: the blowup witness `s` of `u` gives the
  witness `C(s)` on `A[X]`, whose chart `A[X][C s / C g]` receives `A[s/g]`, `chartPolyMap`), and
  so is `u ∘ p + log|w|` (`log|w|` is regularizable, `isRegularizable_logAbs_X`);
* `N'` is the instance of `NonflatNorms` for `mapAlgHom φ` and `C(S)`.

## Main results

* `IsRegularizable.of_projection_weaklyPSH`: FHX Proposition 5.24 for weakly psh functions.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open Berk Polynomial

universe u v w

/-! ### `S × 𝔸¹` is a principal open of `𝔸ⁿ⁺¹` -/

section affine

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]

/-- If `S = Spec B` is a principal open of `𝔸ⁿ`, then `S × 𝔸¹ = Spec B[X]` is a principal open of
`𝔸ⁿ⁺¹`: `B[X] ≅ (k[x]_h)[X] ≅ (k[x][X])_{C h} ≅ k[x, x_{n+1}]_h`. -/
theorem IsAffineSpacePrincipalOpen.polynomial {n : ℕ} (hB : IsAffineSpacePrincipalOpen k B n) :
    IsAffineSpacePrincipalOpen k B[X] (n + 1) := by
  obtain ⟨h, hh0, ⟨e⟩⟩ := hB
  let E := MvPolynomial.finSuccEquiv k n
  refine ⟨E.symm (C h), (map_ne_zero_iff _ E.symm.injective).2 (C_ne_zero.2 hh0), ⟨?_⟩⟩
  letI : Algebra (MvPolynomial (Fin n) k)[X] (Localization.Away h)[X] := Polynomial.algebra _ _
  have : IsLocalization (Submonoid.powers (C h)) (Localization.Away h)[X] := by
    have := Polynomial.isLocalization (Submonoid.powers h) (Localization.Away h)
    rwa [Submonoid.map_powers] at this
  have hE : Submonoid.map E (Submonoid.powers (E.symm (C h))) = Submonoid.powers (C h) := by
    rw [Submonoid.map_powers, AlgEquiv.apply_symm_apply]
  exact (mapAlgEquiv e).trans
    (IsLocalization.algEquivOfAlgEquiv (Localization.Away (E.symm (C h)))
      (Localization.Away h)[X] E hE).symm

end affine

/-! ### `π × id` is finite and generically étale -/

section etale

/-- Étale ring homomorphisms are stable under composition (universe polymorphic). -/
theorem etale_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {f : R →+* S}
    {g : S →+* T} (hf : f.Etale) (hg : g.Etale) : (g.comp f).Etale := by
  algebraize [f, g, g.comp f]
  exact Algebra.Etale.comp R S T

/-- If `R → S` is étale, so is `R[X] → S[X]` (base change along `R → R[X]`). -/
theorem etale_mapRingHom {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : f.Etale) :
    (mapRingHom f).Etale := by
  algebraize [f]
  let : Algebra R[X] S[X] := Polynomial.algebra _ _
  have : Algebra.Etale R[X] S[X] :=
    Algebra.Etale.of_equiv (Algebra.IsPushout.equiv R R[X] S S[X])
  exact (RingHom.etale_algebraMap).2 this

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B]

/-- **`π × id` is generically étale** if `π` is: if `B_h → A_{φ h}` is étale, so is
`B[X]_{C h} → A[X]_{C (φ h)}`, which is `B_h[X] → A_{φ h}[X]` up to isomorphism. -/
theorem isGenericallyEtale_mapRingHom {φ : B →+* A} (hφ : IsGenericallyEtale φ) :
    IsGenericallyEtale (mapRingHom φ) := by
  obtain ⟨h, hh0, het⟩ := hφ
  refine ⟨C h, C_ne_zero.2 hh0, ?_⟩
  let Bh := Localization.Away h
  let Ah := Localization.Away (φ h)
  let : Algebra B[X] Bh[X] := Polynomial.algebra _ _
  let : Algebra A[X] Ah[X] := Polynomial.algebra _ _
  have : IsLocalization (Submonoid.powers (C h)) Bh[X] := by
    have := Polynomial.isLocalization (Submonoid.powers h) Bh
    rwa [Submonoid.map_powers] at this
  have : IsLocalization (Submonoid.powers (mapRingHom φ (C h))) Ah[X] := by
    have := Polynomial.isLocalization (Submonoid.powers (φ h)) Ah
    rw [coe_mapRingHom, map_C]
    rwa [Submonoid.map_powers] at this
  let e₁ := IsLocalization.algEquiv (Submonoid.powers (C h)) (Localization.Away (C h)) Bh[X]
  let e₂ := IsLocalization.algEquiv (Submonoid.powers (mapRingHom φ (C h))) Ah[X]
    (Localization.Away (mapRingHom φ (C h)))
  have key : Localization.awayMap (mapRingHom φ) (C h) = (e₂ : Ah[X] →+* _).comp
      ((mapRingHom (Localization.awayMap φ h)).comp (e₁ : _ →+* Bh[X])) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (C h)) (RingHom.ext fun p => ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.commutes]
    have h1 : (algebraMap B[X] Bh[X]) p = p.map (algebraMap B Bh) := rfl
    have h2 : (Localization.awayMap φ h).comp (algebraMap B Bh) = (algebraMap A Ah).comp φ :=
      IsLocalization.map_comp _
    have h3 : (p.map φ).map (algebraMap A Ah) = algebraMap A[X] Ah[X] (p.map φ) := rfl
    rw [h1, coe_mapRingHom (f := Localization.awayMap φ h), Polynomial.map_map, h2,
      ← Polynomial.map_map, h3, AlgEquiv.commutes]
    exact IsLocalization.map_eq _ _
  rw [key]
  exact etale_comp (etale_comp (RingHom.Etale.of_bijective e₁.bijective) (etale_mapRingHom het))
    (RingHom.Etale.of_bijective e₂.bijective)

/-- **`π × id` is finite** if `π` is: `B[X] → A[X]` is integral (`isIntegral_mapAlgHom`) and of
finite type (`A[X]` is of finite type over `k`). -/
theorem finite_mapAlgHom {k : Type*} [Field k] [Algebra k A] [Algebra k B]
    [Algebra.FiniteType k A] {φ : B →ₐ[k] A} (hφ : (φ : B →+* A).Finite) :
    ((mapAlgHom φ : B[X] →ₐ[k] A[X]) : B[X] →+* A[X]).Finite := by
  refine RingHom.IsIntegral.to_finite (isIntegral_mapAlgHom hφ.to_isIntegral) ?_
  refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap k B[X]) ?_
  rw [AlgHom.comp_algebraMap]
  exact RingHom.finiteType_algebraMap.2 inferInstance

end etale

/-! ### Weakly psh functions pull back to `Y × 𝔸¹` -/

section chart

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]

/-- The map `Frac A → Frac A[X]` induced by `C : A → A[X]`. -/
abbrev fracC : FractionRing A →+* FractionRing A[X] :=
  IsFractionRing.map (j := (C : A →+* A[X])) C_injective

theorem fracC_algebraMap (a : A) :
    fracC (algebraMap A (FractionRing A) a) = algebraMap A[X] (FractionRing A[X]) (C a) :=
  IsLocalization.map_eq _ _

/-- `C : Frac A → Frac A[X]` maps the chart `A[s/g]` into the chart `A[X][C s / C g]`. -/
theorem fracC_mem_blowupChart (s : Finset A) (g : A) {z : FractionRing A}
    (hz : z ∈ blowupChart s g) :
    fracC z ∈ blowupChart (s.map ⟨C, C_injective⟩) (C g) := by
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨h, hh, rfl⟩ := hz
    rw [map_div₀, fracC_algebraMap, fracC_algebraMap]
    exact Algebra.subset_adjoin ⟨C h, Finset.mem_map_of_mem _ hh, rfl⟩
  | algebraMap a =>
    rw [fracC_algebraMap]
    exact Subalgebra.algebraMap_mem _ (C a)
  | add z w _ _ hz hw => rw [map_add]; exact Subalgebra.add_mem _ hz hw
  | mul z w _ _ hz hw => rw [map_mul]; exact Subalgebra.mul_mem _ hz hw

variable (k) in
/-- The map of charts `A[s/g] → A[X][C s / C g]` over `C : A → A[X]`: the chart of the blowup of
`Ỹ = Y × 𝔸¹` along `C(s)` maps to the chart of the blowup of `Y` along `s`. -/
def chartPolyMap (s : Finset A) (g : A) :
    blowupChart s g →ₐ[k] blowupChart (s.map ⟨C, C_injective⟩) (C g) where
  toRingHom := (fracC.comp (blowupChart s g).val.toRingHom).codRestrict _
    fun z => fracC_mem_blowupChart s g z.2
  commutes' c := by
    refine Subtype.ext ?_
    change fracC ((algebraMap k (blowupChart s g) c : FractionRing A)) =
      ((algebraMap k (blowupChart (s.map ⟨C, C_injective⟩) (C g)) c : FractionRing A[X]))
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap,
      IsScalarTower.algebraMap_apply k A (FractionRing A), fracC_algebraMap,
      IsScalarTower.algebraMap_apply k A[X] (FractionRing A[X]), Polynomial.algebraMap_apply]

theorem chartPolyMap_chartMap (s : Finset A) (g : A) (a : A) :
    chartPolyMap k s g (chartMap k s g a) = chartMap k (s.map ⟨C, C_injective⟩) (C g) (C a) :=
  Subtype.ext (fracC_algebraMap a)

/-- The square `p ∘ μ̃ = μ ∘ (chart map)` on analytifications. -/
theorem proj_comap_chartMap (s : Finset A) (g : A)
    (y : Berk k (blowupChart (s.map ⟨C, C_injective⟩) (C g))) :
    proj (comap (chartMap k (s.map ⟨C, C_injective⟩) (C g)) y) =
      comap (chartMap k s g) (comap (chartPolyMap k s g) y) :=
  ext_val fun a => by
    simp only [proj_val_apply, comap_val_apply, chartPolyMap_chartMap]

/-- **Weakly psh functions pull back to `Ỹ = Y × 𝔸¹`**: if `s` is a blowup witness for `u`, then
`C(s)` is one for `u ∘ p`, the charts of the blowup of `Ỹ` mapping to those of `Y`. -/
theorem IsWeaklyPSHOn.comp_proj {u : Berk k A → EReal} (hu : IsWeaklyPSHOn Set.univ u) :
    IsWeaklyPSHOn Set.univ fun z : Berk k A[X] => u (proj z) := by
  obtain ⟨s, ⟨g₀, hg₀, hg₀0⟩, hloc⟩ := hu
  refine ⟨s.map ⟨C, C_injective⟩, ⟨C g₀, Finset.mem_map_of_mem _ hg₀, C_ne_zero.2 hg₀0⟩, ?_⟩
  intro g' hg' hg'0
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.1 hg'
  have hg0 : g ≠ 0 := fun h => hg'0 (by simp [h])
  have := (hloc g hg hg0).comp_comap (chartPolyMap k s g)
  simp only [Set.preimage_univ] at this ⊢
  exact (congrArg (IsLocallyPSHOn Set.univ)
    (funext fun y => congrArg u (proj_comap_chartMap s g y))).mpr this

variable [Algebra.FiniteType k A]

/-- `log|w|` is regularizable on `Ỹ = Y × 𝔸¹`. -/
theorem isRegularizable_logAbs_X :
    IsRegularizable (logAbs (X : A[X]) : Berk k A[X] → EReal) := by
  have hs := isRegularizable_finsetSup_fsTerm (k := k) (A := A[X])
    (s := {((X : A[X]), (1 : ℚ), (0 : ℚ))}) (by simp)
    ⟨triv, by
      rw [Finset.sup_singleton]
      simp only [fsTerm, Rat.cast_one, EReal.coe_one, one_mul, Rat.cast_zero,
        EReal.coe_zero, add_zero]
      rw [Ne, logAbs_eq_bot_iff, triv_val_of_ne_zero X_ne_zero]
      exact one_ne_zero⟩
  refine hs.congr fun w => ?_
  rw [Finset.sup_singleton]
  simp [fsTerm]

/-- `u ∘ p + log|w|` is weakly psh on `Ỹ = Y × 𝔸¹` if `u` is weakly psh on `Y`. -/
theorem IsWeaklyPSHOn.comp_proj_add_logAbs_X {u : Berk k A → EReal}
    (hu : IsWeaklyPSHOn Set.univ u) :
    IsWeaklyPSHOn Set.univ fun z : Berk k A[X] => u (proj z) + logAbs (X : A[X]) z :=
  hu.comp_proj.add_isRegularizable isRegularizable_logAbs_X

end chart

/-! ### The projection step -/

section main

variable {k : Type u} [Field k] [IsAlgClosed k] [Countable k] [NonflatNorms.{u, v, w} k]
  [WuRegularization.{u, v} k]
  {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
  [IsIntegrallyClosed A] {B : Type w} [CommRing B] [Algebra k B]

/-- **The projection step for weakly psh functions** (FHX Proposition 5.24,
`prop:projection-step`), conditional on FHX Proposition 5.22 (`NonflatNorms k`) and on the
imported FHX Lemma 5.11(5),(6) (`WuRegularization k`).

Let `Y = Spec A` be a normal affine variety, `S = Spec B` a principal open of `𝔸ⁿ` (`hB`), and
`π = Spec φ` finite (`hfin`), surjective (`hinj`) and generically étale (`het`). Let `Z = V(S) ⊊ Y`
(`hS`) with `π|_Z` a closed immersion (`hZimm`), and `f₁ + f₂ = 1` with `f₂ = 0` on `Z^an` and
`f₁ = 0` on `π⁻¹(π(Z^an)) \ Z^an` (`Z'` closed). If `u` is weakly psh (with a blowup witness), of
logarithmic growth and regularizable on principal opens covering `Y \ Z`, then `u` is
regularizable. -/
theorem IsRegularizable.of_projection_weaklyPSH {n : ℕ} (hB : IsAffineSpacePrincipalOpen k B n)
    (φ : B →ₐ[k] A) (hinj : Function.Injective φ) (hfin : (φ : B →+* A).Finite)
    (het : IsGenericallyEtale (φ : B →+* A)) (S : Finset A) (hS : ∃ f ∈ S, f ≠ 0)
    (hZimm : Function.Surjective
      ((Ideal.Quotient.mk (Ideal.span (S : Set A))).comp (φ : B →+* A)))
    {f₁ f₂ : A} (hf : f₁ + f₂ = 1)
    (hf₂ : ∀ y : Berk k A, (∀ f ∈ S, y.val f = 0) → y.val f₂ = 0)
    (hf₁ : ∀ y y' : Berk k A, (∀ f ∈ S, y.val f = 0) → comap φ y' = comap φ y →
      (∃ f ∈ S, y'.val f ≠ 0) → y'.val f₁ = 0)
    {u : Berk k A → EReal} (hu : IsWeaklyPSHOn Set.univ u) (hlog : HasLogGrowth u)
    (hcover : ∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y)) :
    IsRegularizable u := by
  have := hB.finiteType
  -- the conclusion of FHX Proposition 5.22 for `π × id` and `Z × 𝔸¹`
  obtain ⟨N'⟩ := NonflatNorms.nonempty_normWeights (k := k) (A := A[X]) (B := B[X])
    (Nat.le_add_left 1 n) hB.polynomial (mapAlgHom φ) (map_injective _ hinj)
    (finite_mapAlgHom hfin) (isGenericallyEtale_mapRingHom het) (S.map ⟨C, C_injective⟩)
    (by
      obtain ⟨f, hfS, hf0⟩ := hS
      exact ⟨C f, Finset.mem_map_of_mem _ hfS, C_ne_zero.2 hf0⟩)
  exact IsRegularizable.of_projection φ hfin.to_isIntegral S hS hZimm hf hf₂ hf₁
    isPshClass_isWeaklyPSHOn_univ isPshClass_isWeaklyPSHOn_univ N' hu
    hu.comp_proj_add_logAbs_X hlog hcover

end main

end EnvelopeProperty
