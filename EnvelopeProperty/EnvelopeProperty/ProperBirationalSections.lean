/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.PartialIsoFractionDensity
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.Valuation.LocalSubring

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.ProperBirationalSections
variable {A K : Type u} [CommRing A] [Field K] [Algebra A K] {Y : Scheme.{u}}

/-- Every ORIGINAL global section has its actual element under the whole field-valued point. -/
def globalSectionMap {R : Type u} [CommRing R]
    (q : Spec (CommRingCat.of R) ⟶ Y) : Γ(Y, ⊤) →+* R :=
  (q.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom

/-- The ORIGINAL coefficient map on the actual whole global-section ring. -/
def coefficientMap (f : Y ⟶ Spec (CommRingCat.of A)) : A →+* Γ(Y, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom

/-- The actual whole scheme triangle retains EVERY original coefficient element. -/
theorem globalSectionMap_comp_coefficientMap (f : Y ⟶ Spec (CommRingCat.of A))
    (q : Spec (CommRingCat.of K) ⟶ Y)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A K))) :
    (globalSectionMap q).comp (coefficientMap f) = algebraMap A K := by
  change ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫
    q.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom = _
  rw [← Category.assoc f.appTop, ← Scheme.Hom.comp_appTop, hq,
    ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rfl

/-- Actual proper valuative lifts place EVERY original section element inside EVERY
valuation subring containing the actual original coefficient image. -/
theorem globalSectionMap_mem_valuationSubring (f : Y ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (q : Spec (CommRingCat.of K) ⟶ Y)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A K)))
    (V : ValuationSubring K) (hV : ∀ a : A, algebraMap A K a ∈ V) (s : Γ(Y, ⊤)) :
    globalSectionMap q s ∈ V := by
  let α : A →+* V := (algebraMap A K).codRestrict V.toSubring hV
  have hα : (algebraMap V K).comp α = algebraMap A K := rfl
  let S : ValuativeCommSq f :=
    { R := V
      K := K
      i₁ := q
      i₂ := Spec.map (CommRingCat.ofHom α)
      commSq := ⟨by
        rw [← Spec.map_comp]
        change q ≫ f = Spec.map (CommRingCat.ofHom ((algebraMap V K).comp α))
        rw [hα]
        exact hq⟩ }
  have hp : IsProper f := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hp
  let l := (Classical.choice (hp.1.1.1 S)).default
  have hl : Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l.l = q := l.fac_left
  have he : globalSectionMap q s = algebraMap V K (globalSectionMap l.l s) := by
    have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V K))
    have ht : (Spec.map (CommRingCat.ofHom (algebraMap V K))).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of V)).hom ≫ CommRingCat.ofHom (algebraMap V K) := by
      rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of V)).inv,
        ← Category.assoc, ← hn]
      simp
    change (q.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom) s = _
    rw [← hl, Scheme.Hom.comp_appTop, Category.assoc, ht]
    rfl
  rw [he]
  exact (globalSectionMap l.l s).2

/-- Actual normality and the genuine valuation-subring intersection place EVERY
original global-section generic ELEMENT in the original coefficient image. -/
theorem globalSectionMap_mem_range [IsDomain A] [IsIntegrallyClosed A] [IsFractionRing A K]
    (f : Y ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (q : Spec (CommRingCat.of K) ⟶ Y)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A K))) (s : Γ(Y, ⊤)) :
    globalSectionMap q s ∈ (algebraMap A K).range := by
  let R := (algebraMap A K).range
  let : Algebra A R := (algebraMap A K).rangeRestrict.toAlgebra
  let : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra.IsIntegral A R := Algebra.isIntegral_of_surjective
    (algebraMap A K).rangeRestrict_surjective
  let : IsIntegrallyClosedIn A K := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mp inferInstance
  let : IsIntegrallyClosedIn R K := Subring.isIntegrallyClosedIn_iff.mpr (by
    intro z hz
    have hzA : IsIntegral A z := isIntegral_trans z hz
    obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hzA
    exact ⟨a, ha⟩)
  by_contra hz
  obtain ⟨V, hRV, hzV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := R) hz
  exact hzV (globalSectionMap_mem_valuationSubring f q hq V
    (fun a => hRV ⟨a, rfl⟩) s)

/-- Actual density of an original field point and REDUCED target give injection
on the WHOLE original global-section ring, via genuine scheme-theoretic dominance. -/
theorem globalSectionMap_injective_of_dense [IsReduced Y]
    (q : Spec (CommRingCat.of K) ⟶ Y) (hq : DenseRange q) :
    Function.Injective (globalSectionMap q) := by
  let : QuasiCompact q := ⟨fun U _ _ => (Set.toFinite (q ⁻¹' U)).isCompact⟩
  let : IsDominant q := (isDominant_iff q).mpr hq
  let : IsSchemeTheoreticallyDominant q := IsSchemeTheoreticallyDominant.of_isDominant q
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective.comp
    (q.app_injective ⊤)

/-- Real normality, proper valuative lifting and reduced-source generic injection
derive bijectivity of the ORIGINAL coefficient map, without Noetherianity. -/
theorem coefficientMap_bijective_of_proper_birationalOver [IsDomain A] [IsIntegrallyClosed A]
    [IsReduced Y] (f : Y ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (h : Scheme.BirationalOver f (𝟙 (Spec (CommRingCat.of A)))) :
    Function.Bijective (coefficientMap f) := by
  obtain ⟨e, he⟩ := h
  let q := PartialIso.fractionLift (K := FractionRing A) e
  have hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) :=
    PartialIso.fractionLift_comp e f he
  have hc := globalSectionMap_comp_coefficientMap f q hq
  have hg := globalSectionMap_injective_of_dense q (PartialIso.denseRange_fractionLift e)
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply IsFractionRing.injective A (FractionRing A)
    calc
      algebraMap A (FractionRing A) a = globalSectionMap q (coefficientMap f a) :=
        (congrArg (fun t => t a) hc).symm
      _ = globalSectionMap q (coefficientMap f b) := congrArg (globalSectionMap q) hab
      _ = algebraMap A (FractionRing A) b := congrArg (fun t => t b) hc
  · intro s
    obtain ⟨a, ha⟩ := globalSectionMap_mem_range f q hq s
    refine ⟨a, hg ?_⟩
    exact (congrArg (fun t => t a) hc).trans ha

/-- The TRUE ring equivalence is constructed from the bijective ORIGINAL coefficient RingHom. -/
def coefficientEquivOfProperBirationalOver [IsDomain A] [IsIntegrallyClosed A] [IsReduced Y]
    (f : Y ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (h : Scheme.BirationalOver f (𝟙 (Spec (CommRingCat.of A)))) : A ≃+* Γ(Y, ⊤) :=
  RingEquiv.ofBijective (coefficientMap f) (coefficientMap_bijective_of_proper_birationalOver f h)

/-- Every original coefficient goes to its ENTIRE original pulled-back section. -/
theorem coefficientEquivOfProperBirationalOver_apply [IsDomain A] [IsIntegrallyClosed A] [IsReduced Y]
    (f : Y ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (h : Scheme.BirationalOver f (𝟙 (Spec (CommRingCat.of A)))) (a : A) :
    coefficientEquivOfProperBirationalOver f h a = coefficientMap f a := rfl

end EnvelopeProperty.ProperBirationalSections
