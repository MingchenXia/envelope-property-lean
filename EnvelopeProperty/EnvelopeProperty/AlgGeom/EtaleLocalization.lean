/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localizing finite, injective and étale ring maps away from an element

Universe polymorphic versions of the facts that a ring map `f : R → S` which is étale (resp. finite,
injective) stays so after localizing away from `r ∈ R` (that is, after restricting
`Spec S → Spec R` to the preimage of `D(r)`), and that étaleness of the map
`R_r → S_{f r}` does not depend on the chosen models of the localizations. Mathlib's
`RingHom.LocalizationAwayPreserves` is stated for rings in a single universe; here `R` and `S` may
live in different universes, as in FHX Lemma 5.23 (`lem:projection-existence`), where
`R = k[x₁, …, xₙ]_{h₀}` and `S` is a localization of the coordinate ring `A` of the variety.

These are used to shrink the projection `π : U → S` of FHX Lemma 5.23 to `π⁻¹(S_g) → S_g` in the
proof of FHX Theorem 5.25 (`thm:normal-local-regularization`).
-/

namespace EnvelopeProperty

section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- Étale ring maps compose (universe polymorphic). -/
theorem ringHom_etale_comp {f : R →+* S} {g : S →+* T} (hf : f.Etale) (hg : g.Etale) :
    (g.comp f).Etale := by
  algebraize [f, g, g.comp f]
  exact Algebra.Etale.comp R S T

/-- An étale map stays étale when composed on both sides with ring isomorphisms. -/
theorem ringHom_etale_comp_ringEquiv {R' S' : Type*} [CommRing R'] [CommRing S'] {f : R →+* S}
    (hf : f.Etale) (e₁ : R' ≃+* R) (e₂ : S ≃+* S') :
    ((e₂ : S →+* S').comp (f.comp (e₁ : R' →+* R))).Etale :=
  ringHom_etale_comp (ringHom_etale_comp (RingHom.Etale.of_bijective e₁.bijective) hf)
    (RingHom.Etale.of_bijective e₂.bijective)

end

section away

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R)
  (R' S' : Type*) [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S']
  [IsLocalization.Away r R'] [IsLocalization.Away (f r) S']

/-- The localized map `R_r → S_{f r}` extends `f`. -/
theorem away_map_algebraMap (x : R) :
    IsLocalization.Away.map R' S' f r (algebraMap R R' x) = algebraMap S S' (f x) := by
  simp [IsLocalization.Away.map]

/-- **Étaleness is preserved by localization away from an element** (universe polymorphic): if
`f : R → S` is étale, so is `R_r → S_{f r}`. -/
theorem etale_away_map (hf : f.Etale) : (IsLocalization.Away.map R' S' f r).Etale := by
  let := f.toAlgebra
  let ψ := IsLocalization.Away.map R' S' f r
  let := ψ.toAlgebra
  let : Algebra R S' := ((algebraMap S S').comp f).toAlgebra
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun x =>
    (away_map_algebraMap f r R' S' x).symm
  have : Algebra.Etale R S := hf
  have : IsLocalization ((Submonoid.powers r).map (algebraMap R S)) S' := by
    rw [Submonoid.map_powers]; exact ‹IsLocalization.Away (f r) S'›
  have : Algebra.FormallyEtale R' S' :=
    Algebra.FormallyEtale.localization_map (Submonoid.powers r) (S := S) (Rₘ := R') (Sₘ := S')
  have : Algebra.FinitePresentation R' S' := by
    have h₁ : Algebra.FinitePresentation S S' := IsLocalization.Away.finitePresentation (f r)
    have h₂ : Algebra.FinitePresentation R S' := .trans R S S'
    have h₃ : Algebra.FiniteType R R' :=
      have := IsLocalization.Away.finitePresentation (R := R) (S := R') r
      .of_finitePresentation
    have : (ψ.comp (algebraMap R R')).FinitePresentation := by
      rw [show ψ.comp (algebraMap R R') = algebraMap R S' from
        RingHom.ext fun x => away_map_algebraMap f r R' S' x]
      exact RingHom.finitePresentation_algebraMap.mpr h₂
    exact RingHom.FinitePresentation.of_comp_finiteType (algebraMap R R') this
      (RingHom.finiteType_algebraMap.mpr h₃)
  exact Algebra.Etale.mk

/-- **Finiteness is preserved by localization away from an element** (universe polymorphic). -/
theorem finite_away_map (hf : f.Finite) : (IsLocalization.Away.map R' S' f r).Finite := by
  let := f.toAlgebra
  let ψ := IsLocalization.Away.map R' S' f r
  let := ψ.toAlgebra
  let : Algebra R S' := ((algebraMap S S').comp f).toAlgebra
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun x =>
    (away_map_algebraMap f r R' S' x).symm
  have : Module.Finite R S := hf
  have : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers r)) S' := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact ‹IsLocalization.Away (f r) S'›
  exact Module.Finite.of_isLocalization R S (Submonoid.powers r)

/-- **Injectivity is preserved by localization away from an element.** -/
theorem injective_away_map (hf : Function.Injective f) :
    Function.Injective (IsLocalization.Away.map R' S' f r) := by
  exact IsLocalization.map_injective_of_injective (Submonoid.powers r) R' S' hf

/-- **Surjectivity onto a quotient is preserved by localization**: if `R → S / J` is surjective,
so is `R_r → S_{f r} / J S_{f r}`. -/
theorem surjective_quotient_away_map (J : Ideal S)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp f)) :
    Function.Surjective ((Ideal.Quotient.mk (J.map (algebraMap S S'))).comp
      (IsLocalization.Away.map R' S' f r)) := by
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers (f r)) y
  obtain ⟨b, hb⟩ := hsurj (Ideal.Quotient.mk J x)
  have hbx : f b - x ∈ J := Ideal.Quotient.eq.mp hb
  set ψ := IsLocalization.Away.map R' S' f r
  refine ⟨algebraMap R R' b * IsLocalization.Away.invSelf r ^ n, ?_⟩
  simp only [RingHom.comp_apply]
  rw [Ideal.Quotient.eq]
  have hu : IsUnit (algebraMap S S' (f r ^ n)) :=
    IsLocalization.map_units S' (⟨f r ^ n, n, rfl⟩ : Submonoid.powers (f r))
  have hinv : ψ (IsLocalization.Away.invSelf r) * algebraMap S S' (f r) = 1 := by
    rw [← away_map_algebraMap f r R' S' r, ← map_mul, mul_comm,
      IsLocalization.Away.mul_invSelf, map_one]
  have hmap : ψ (algebraMap R R' b * IsLocalization.Away.invSelf r ^ n) *
      algebraMap S S' (f r ^ n) = algebraMap S S' (f b) := by
    rw [map_mul, map_pow, away_map_algebraMap, map_pow, mul_assoc, ← mul_pow, hinv, one_pow,
      mul_one]
  have hy : y * algebraMap S S' (f r ^ n) = algebraMap S S' x := hx
  have key : (ψ (algebraMap R R' b * IsLocalization.Away.invSelf r ^ n) - y) *
      algebraMap S S' (f r ^ n) = algebraMap S S' (f b - x) := by
    rw [sub_mul, hmap, hy, map_sub]
  have hmem : algebraMap S S' (f b - x) ∈ J.map (algebraMap S S') := Ideal.mem_map_of_mem _ hbx
  rw [← key] at hmem
  obtain ⟨u, hu'⟩ := hu
  have := Ideal.mul_mem_right (↑u⁻¹ : S') _ hmem
  rwa [← hu', mul_assoc, Units.mul_inv, mul_one] at this

end away

section models

variable {A B : Type*} [CommRing A] [CommRing B]

/-- **Étaleness of a localized map does not depend on the models of the localizations.** Let
`φ : B → A` and `c ∈ B`; let `R₁, R₂` be localizations of `B` away from `c` and `S₁, S₂`
localizations of `A` away from `φ c`, with maps `ψᵢ : Rᵢ → Sᵢ` extending `φ`. If `ψ₁` is étale,
so is `ψ₂` (they differ by isomorphisms). -/
theorem etale_of_isLocalization_away (φ : B →+* A) (c : B)
    (R₁ S₁ R₂ S₂ : Type*) [CommRing R₁] [CommRing S₁] [CommRing R₂] [CommRing S₂]
    [Algebra B R₁] [Algebra A S₁] [Algebra B R₂] [Algebra A S₂]
    [IsLocalization.Away c R₁] [IsLocalization.Away (φ c) S₁]
    [IsLocalization.Away c R₂] [IsLocalization.Away (φ c) S₂]
    (ψ₁ : R₁ →+* S₁) (ψ₂ : R₂ →+* S₂) (h₁ : ψ₁.comp (algebraMap B R₁) = (algebraMap A S₁).comp φ)
    (h₂ : ψ₂.comp (algebraMap B R₂) = (algebraMap A S₂).comp φ) (het : ψ₁.Etale) : ψ₂.Etale := by
  let eR := IsLocalization.algEquiv (Submonoid.powers c) R₂ R₁
  let eS := IsLocalization.algEquiv (Submonoid.powers (φ c)) S₁ S₂
  have key : ψ₂ = (eS.toRingEquiv : S₁ →+* S₂).comp (ψ₁.comp (eR.toRingEquiv : R₂ →+* R₁)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers c) (RingHom.ext fun x => ?_)
    have e₁ := congrArg (· x) h₁
    have e₂ := congrArg (· x) h₂
    simp only [RingHom.comp_apply] at e₁ e₂ ⊢
    rw [e₂]
    change _ = eS (ψ₁ (eR (algebraMap B R₂ x)))
    rw [AlgEquiv.commutes, e₁, AlgEquiv.commutes]
  rw [key]
  exact ringHom_etale_comp_ringEquiv het eR.toRingEquiv eS.toRingEquiv

end models

end EnvelopeProperty
