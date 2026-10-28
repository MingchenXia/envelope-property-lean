/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.ReducedComponents
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Artinian.Module

noncomputable section
namespace EnvelopeProperty.ReducedComponents
variable {R : Type*} [CommRing R] (M : Submonoid R) (E : Type*) [CommRing E]
  [Algebra R E] [IsLocalization M E] [IsArtinianRing E]
include E

/-- Each genuinely surviving original minimal prime gives its actual generic maximal prime. -/
def localizationMaximal
    (hd : ∀ p : Index (⊥ : Ideal R), Disjoint (M : Set R) (p.1 : Set R))
    (p : Index (⊥ : Ideal R)) : MaximalSpectrum E := by
  have hp : (p.1.map (algebraMap R E)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M E p.1 p.2.isPrime (hd p)
  exact ⟨p.1.map (algebraMap R E), (IsArtinianRing.isPrime_iff_isMaximal _).mp hp⟩

/-- Whole ideal contraction distinguishes every surviving original component. -/
theorem localizationMaximal_injective
    (hd : ∀ p : Index (⊥ : Ideal R), Disjoint (M : Set R) (p.1 : Set R)) :
    Function.Injective (localizationMaximal M E hd) := by
  intro p q he
  apply Subtype.ext
  have h := congrArg (fun m : MaximalSpectrum E => m.asIdeal.under R) he
  change (p.1.map (algebraMap R E)).under R = (q.1.map (algebraMap R E)).under R at h
  rwa [IsLocalization.under_map_of_isPrime_disjoint M E p.2.isPrime (hd p),
    IsLocalization.under_map_of_isPrime_disjoint M E q.2.isPrime (hd q)] at h

/-- Every actual Artinian localization factor comes from a genuine original minimal prime. -/
theorem localizationMaximal_surjective
    (hd : ∀ p : Index (⊥ : Ideal R), Disjoint (M : Set R) (p.1 : Set R)) :
    Function.Surjective (localizationMaximal M E hd) := by
  intro m
  have hm : m.asIdeal ∈ minimalPrimes E := IsArtinianRing.mem_minimalPrimes bot_le
  have hp : m.asIdeal.under R ∈ minimalPrimes R := by
    rw [← Set.mem_preimage, ← IsLocalization.minimalPrimes_map M E (⊥ : Ideal R)]
    simpa only [Ideal.map_bot] using hm
  refine ⟨⟨m.asIdeal.under R, hp⟩, ?_⟩
  apply MaximalSpectrum.ext
  change (m.asIdeal.under R).map (algebraMap R E) = m.asIdeal
  exact IsLocalization.map_under M E m.asIdeal

/-- The actual original minimal components are exactly all genuine generic maximal factors. -/
def localizationMaximalEquiv
    (hd : ∀ p : Index (⊥ : Ideal R), Disjoint (M : Set R) (p.1 : Set R)) :
    Index (⊥ : Ideal R) ≃ MaximalSpectrum E :=
  Equiv.ofBijective (localizationMaximal M E hd)
    ⟨localizationMaximal_injective M E hd, localizationMaximal_surjective M E hd⟩

/-- Actual Artinian generic factors make the entire surviving original component index finite. -/
theorem localizationIndex_finite
    (hd : ∀ p : Index (⊥ : Ideal R), Disjoint (M : Set R) (p.1 : Set R)) :
    Finite (Index (⊥ : Ideal R)) :=
  Finite.of_injective (localizationMaximal M E hd) (localizationMaximal_injective M E hd)

/-- The intersection of the actual localized original minimal ideals is exactly the generic nilradical. -/
theorem iInf_localizedMinimal_eq_nilradical
    (hd : ∀ p : Index (⊥ : Ideal R), Disjoint (M : Set R) (p.1 : Set R)) :
    (⨅ p : Index (⊥ : Ideal R), p.1.map (algebraMap R E)) = nilradical E := by
  rw [IsArtinianRing.nilradical_eq_iInf E, ← sInf_range, ← sInf_range]
  apply congrArg sInf
  ext J
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨localizationMaximal M E hd p, rfl⟩
  · rintro ⟨m, rfl⟩
    obtain ⟨p, hp⟩ := localizationMaximal_surjective M E hd m
    exact ⟨p, congrArg MaximalSpectrum.asIdeal hp⟩

set_option backward.isDefEq.respectTransparency false in
/-- Genuine reduction of the Artinian generic fibre gives the whole original-component quotient product. -/
def localizationReducedEquivPi [IsReduced E]
    (hd : ∀ p : Index (⊥ : Ideal R), Disjoint (M : Set R) (p.1 : Set R)) :
    E ≃ₐ[E] ∀ p : Index (⊥ : Ideal R), E ⧸ p.1.map (algebraMap R E) := by
  let : Finite (Index (⊥ : Ideal R)) := localizationIndex_finite M E hd
  have h : (⨅ p : Index (⊥ : Ideal R), p.1.map (algebraMap R E)) = ⊥ :=
    (iInf_localizedMinimal_eq_nilradical M E hd).trans (nilradical_eq_zero E)
  let e : E ≃ₐ[E] E ⧸ ⨅ p : Index (⊥ : Ideal R), p.1.map (algebraMap R E) :=
    (AlgEquiv.quotientBot E E).symm.trans (Ideal.quotientEquivAlgOfEq E h.symm)
  have hcop : Pairwise (fun p q : Index (⊥ : Ideal R) =>
      IsCoprime (p.1.map (algebraMap R E)) (q.1.map (algebraMap R E))) := by
    intro p q hpq
    exact MaximalSpectrum.isCoprime_of_ne
      (I := localizationMaximal M E hd p) (J := localizationMaximal M E hd q)
      (fun hp => hpq (localizationMaximal_injective M E hd hp))
  let f : (E ⧸ ⨅ p : Index (⊥ : Ideal R), p.1.map (algebraMap R E)) ≃ₐ[E]
      (∀ p : Index (⊥ : Ideal R), E ⧸ p.1.map (algebraMap R E)) :=
    { toRingEquiv := Ideal.quotientInfRingEquivPiQuotient
        (fun p : Index (⊥ : Ideal R) => p.1.map (algebraMap R E)) hcop
      commutes' := fun _ => rfl }
  exact e.trans f

/-- The whole generic component comparison preserves every original function in every actual factor. -/
theorem localizationReducedEquivPi_algebraMap [IsReduced E]
    (hd : ∀ p : Index (⊥ : Ideal R), Disjoint (M : Set R) (p.1 : Set R)) (r : R)
    (p : Index (⊥ : Ideal R)) :
    localizationReducedEquivPi M E hd (algebraMap R E r) p =
      Ideal.Quotient.mk (p.1.map (algebraMap R E)) (algebraMap R E r) := rfl

end EnvelopeProperty.ReducedComponents
