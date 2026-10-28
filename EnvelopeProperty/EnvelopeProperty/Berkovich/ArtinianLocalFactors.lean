/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import EnvelopeProperty.Berkovich.LocalAlgebraNorm

/-!
# Genuine nonreduced Artinian localization factors

A positive nilradical exponent and the proved maximal-power Chinese remainder
map give an actual whole-ring product decomposition. Constructed local
idempotents and nilpotent inverse corrections verify that each power quotient
is the actual localization at its maximal ideal. No reducedness or separability
hypothesis is imposed.

The product preserves arbitrary commutative coefficient algebras. A finite
algebra over a field gives this decomposition without an additional Artinian
assumption; all actual local factors are finite. Their local residue fields
are canonically the maximal quotients, so genuine local lengths and residue
degrees recover the factor dimensions and the whole dimension sum.
-/

open scoped Classical
noncomputable section
namespace EnvelopeProperty
namespace ArtinianFactors
variable (E : Type*) [CommRing E] [IsArtinianRing E]

theorem exists_positive_nilradical_pow_eq_bot :
    ∃ n : ℕ, 0 < n ∧ nilradical E ^ n = ⊥ := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := E)
  refine ⟨n + 1, Nat.zero_lt_succ n, ?_⟩
  change nilradical E ^ n = ⊥ at hn
  rw [pow_succ, hn]
  simp

def exponent : ℕ := (exists_positive_nilradical_pow_eq_bot E).choose

theorem exponent_pos : 0 < exponent E :=
  (exists_positive_nilradical_pow_eq_bot E).choose_spec.1

theorem nilradical_pow_exponent : nilradical E ^ exponent E = ⊥ :=
  (exists_positive_nilradical_pow_eq_bot E).choose_spec.2

abbrev PowerFactor (m : MaximalSpectrum E) := E ⧸ m.asIdeal ^ exponent E

def powerEquiv : E ≃ₐ[E] ∀ m : MaximalSpectrum E, PowerFactor E m :=
  (AlgEquiv.quotientBot E E).symm.trans
    ((Ideal.quotientEquivAlgOfEq E (nilradical_pow_exponent E).symm).trans
      (IsArtinianRing.quotNilradicalPowEquivPi E (exponent E)))

@[simp]
theorem powerEquiv_apply (a : E) (m : MaximalSpectrum E) :
    powerEquiv E a m = algebraMap E (PowerFactor E m) a := rfl

def localIdempotent (m : MaximalSpectrum E) : E := by
  classical
  exact (powerEquiv E).symm (Pi.single m 1)

@[simp]
theorem powerEquiv_localIdempotent (m : MaximalSpectrum E) :
    powerEquiv E (localIdempotent E m) = Pi.single m 1 := by
  classical
  exact (powerEquiv E).apply_symm_apply _


theorem localIdempotent_not_mem (m : MaximalSpectrum E) :
    localIdempotent E m ∉ m.asIdeal := by
  intro hm
  have hclass : algebraMap E (PowerFactor E m) (localIdempotent E m) = 1 := by
    simpa only [powerEquiv_apply, Pi.single_eq_same] using
      congrFun (powerEquiv_localIdempotent E m) m
  have hdiff : localIdempotent E m - 1 ∈ m.asIdeal ^ exponent E := Ideal.Quotient.eq.mp hclass
  have hdiff' : localIdempotent E m - 1 ∈ m.asIdeal :=
    Ideal.pow_le_self (Nat.ne_of_gt (exponent_pos E)) hdiff
  apply m.isMaximal.isPrime.one_notMem
  simpa only [sub_sub_cancel] using m.asIdeal.sub_mem hm hdiff'

theorem localIdempotent_mul_eq_zero (m : MaximalSpectrum E) {a : E}
    (ha : a ∈ m.asIdeal ^ exponent E) : localIdempotent E m * a = 0 := by
  apply (powerEquiv E).injective
  ext n
  simp only [map_mul, Pi.mul_apply, map_zero, Pi.zero_apply]
  rw [powerEquiv_localIdempotent]
  by_cases hnm : n = m
  · subst n
    rw [Pi.single_eq_same, one_mul, powerEquiv_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  · rw [Pi.single_eq_of_ne hnm, zero_mul]

theorem powerFactor_isUnit_of_not_mem (m : MaximalSpectrum E) {s : E}
    (hs : s ∉ m.asIdeal) : IsUnit (algebraMap E (PowerFactor E m) s) := by
  let : Field (E ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  have hs' : Ideal.Quotient.mk m.asIdeal s ≠ 0 :=
    fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((Ideal.Quotient.mk m.asIdeal s)⁻¹)
  have hdiff : a * s - 1 ∈ m.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, map_one, ha, inv_mul_cancel₀ hs', sub_self]
  have hnil : IsNilpotent (algebraMap E (PowerFactor E m) (a * s - 1)) := by
    refine ⟨exponent E, ?_⟩
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hdiff (exponent E))
  have hu : IsUnit (algebraMap E (PowerFactor E m) a * algebraMap E (PowerFactor E m) s) := by
    convert hnil.isUnit_one_add using 1
    rw [map_sub, map_mul, map_one]
    ring
  obtain ⟨u, hu⟩ := hu
  refine isUnit_iff_exists_inv.mpr
    ⟨algebraMap E (PowerFactor E m) a * (↑(u⁻¹) : PowerFactor E m), ?_⟩
  calc
    algebraMap E (PowerFactor E m) s *
        (algebraMap E (PowerFactor E m) a * (↑(u⁻¹) : PowerFactor E m)) =
        (algebraMap E (PowerFactor E m) a * algebraMap E (PowerFactor E m) s) * ↑(u⁻¹) := by ring
    _ = (u : PowerFactor E m) * ↑(u⁻¹) := by rw [← hu]
    _ = 1 := by simp

instance powerFactor_isLocalization (m : MaximalSpectrum E) :
    IsLocalization m.asIdeal.primeCompl (PowerFactor E m) where
  map_units s := powerFactor_isUnit_of_not_mem E m s.2
  surj z := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨(a, 1), by simpa using ha.symm⟩
  exists_of_eq {a b} h := by
    refine ⟨⟨localIdempotent E m, localIdempotent_not_mem E m⟩, ?_⟩
    have hz := localIdempotent_mul_eq_zero E m (Ideal.Quotient.eq.mp h)
    rwa [mul_sub, sub_eq_zero] at hz

/-- Actual maximal-power quotient is the genuine local factor. -/
def powerFactorLocalizationEquiv (m : MaximalSpectrum E) :
    PowerFactor E m ≃ₐ[E] Localization.AtPrime m.asIdeal :=
  IsLocalization.algEquiv m.asIdeal.primeCompl (PowerFactor E m) (Localization.AtPrime m.asIdeal)

@[simp]
theorem powerFactorLocalizationEquiv_algebraMap (m : MaximalSpectrum E) (a : E) :
    powerFactorLocalizationEquiv E m (algebraMap E (PowerFactor E m) a) =
      algebraMap E (Localization.AtPrime m.asIdeal) a :=
  (powerFactorLocalizationEquiv E m).commutes a

/-- Genuine local factors of a nonreduced Artinian ring. -/
def localizationEquiv : E ≃ₐ[E] ∀ m : MaximalSpectrum E, Localization.AtPrime m.asIdeal :=
  (powerEquiv E).trans (AlgEquiv.piCongrRight fun m => powerFactorLocalizationEquiv E m)

@[simp]
theorem localizationEquiv_apply (a : E) (m : MaximalSpectrum E) :
    localizationEquiv E a m = algebraMap E (Localization.AtPrime m.asIdeal) a := by
  change powerFactorLocalizationEquiv E m (powerEquiv E a m) = _
  rw [powerEquiv_apply, powerFactorLocalizationEquiv_algebraMap]

end ArtinianFactors

/-- The actual Artinian localization product preserves arbitrary coefficient algebras. -/
def artinianLocalizationEquiv (R E : Type*) [CommRing R] [CommRing E]
    [Algebra R E] [IsArtinianRing E] :
    E ≃ₐ[R] ∀ m : MaximalSpectrum E, Localization.AtPrime m.asIdeal :=
  (ArtinianFactors.localizationEquiv E).restrictScalars R

@[simp]
theorem artinianLocalizationEquiv_apply (R E : Type*) [CommRing R] [CommRing E]
    [Algebra R E] [IsArtinianRing E] (a : E) (m : MaximalSpectrum E) :
    artinianLocalizationEquiv R E a m = algebraMap E (Localization.AtPrime m.asIdeal) a :=
  ArtinianFactors.localizationEquiv_apply E a m

/-- Artinian localization is an actual surjective image, so coefficient-module finiteness descends. -/
theorem artinianLocalization_moduleFinite (R E : Type*) [CommRing R] [CommRing E]
    [Algebra R E] [IsArtinianRing E] [Module.Finite R E] (m : MaximalSpectrum E) :
    Module.Finite R (Localization.AtPrime m.asIdeal) :=
  Module.Finite.of_surjective
    (IsScalarTower.toAlgHom R E (Localization.AtPrime m.asIdeal)).toLinearMap
    (IsArtinianRing.localization_surjective m.asIdeal.primeCompl (Localization.AtPrime m.asIdeal))

/-- A finite algebra over a field gives the actual local product without an Artinian assumption. -/
def finiteAlgebraLocalizationEquiv (H E : Type*) [Field H] [CommRing E] [Algebra H E]
    [FiniteDimensional H E] :
    E ≃ₐ[H] ∀ m : MaximalSpectrum E, Localization.AtPrime m.asIdeal := by
  let : IsArtinianRing E := IsArtinianRing.of_finite H E
  exact artinianLocalizationEquiv H E

@[simp]
theorem finiteAlgebraLocalizationEquiv_apply (H E : Type*) [Field H] [CommRing E] [Algebra H E]
    [FiniteDimensional H E] (a : E) (m : MaximalSpectrum E) :
    finiteAlgebraLocalizationEquiv H E a m = algebraMap E (Localization.AtPrime m.asIdeal) a :=
by
  let : IsArtinianRing E := IsArtinianRing.of_finite H E
  exact ArtinianFactors.localizationEquiv_apply E a m

/-- Genuine local factors of a finite field algebra are finite over that same field. -/
instance finiteAlgebraLocalization_moduleFinite (H E : Type*) [Field H] [CommRing E]
    [Algebra H E] [FiniteDimensional H E] (m : MaximalSpectrum E) :
    Module.Finite H (Localization.AtPrime m.asIdeal) := by
  let : IsArtinianRing E := IsArtinianRing.of_finite H E
  exact artinianLocalization_moduleFinite H E m

/-- The actual local residue field is the maximal quotient, preserving arbitrary coefficients. -/
def artinianLocalizationResidueEquiv (R E : Type*) [CommRing R] [CommRing E] [Algebra R E]
    (m : MaximalSpectrum E) :
    IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal) ≃ₐ[R] E ⧸ m.asIdeal :=
  (AlgEquiv.ofBijective (Algebra.ofId (E ⧸ m.asIdeal) m.asIdeal.ResidueField)
    m.asIdeal.bijective_algebraMap_quotient_residueField).symm.restrictScalars R

@[simp]
theorem artinianLocalizationResidueEquiv_apply (R E : Type*) [CommRing R] [CommRing E]
    [Algebra R E] (m : MaximalSpectrum E) (a : E) :
    artinianLocalizationResidueEquiv R E m
      (IsLocalRing.residue (Localization.AtPrime m.asIdeal)
        (algebraMap E (Localization.AtPrime m.asIdeal) a)) = Ideal.Quotient.mk m.asIdeal a := by
  change (AlgEquiv.ofBijective (Algebra.ofId (E ⧸ m.asIdeal) m.asIdeal.ResidueField)
    m.asIdeal.bijective_algebraMap_quotient_residueField).symm
      (algebraMap E m.asIdeal.ResidueField a) = _
  rw [IsScalarTower.algebraMap_apply E (E ⧸ m.asIdeal) m.asIdeal.ResidueField]
  exact (AlgEquiv.ofBijective (Algebra.ofId (E ⧸ m.asIdeal) m.asIdeal.ResidueField)
    m.asIdeal.bijective_algebraMap_quotient_residueField).symm.commutes _

/-- Local-factor dimension is actual local length times the original maximal-quotient degree. -/
theorem finrank_finiteAlgebraLocalization (H E : Type*) [Field H] [CommRing E] [Algebra H E]
    [FiniteDimensional H E] (m : MaximalSpectrum E) :
    Module.finrank H (Localization.AtPrime m.asIdeal) =
      (Module.length (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal)).toNat *
        Module.finrank H (E ⧸ m.asIdeal) := by
  rw [finrank_eq_length_mul_residue_finrank (K := H)]
  rw [(artinianLocalizationResidueEquiv H E m).toLinearEquiv.finrank_eq]

/-- A finite field algebra has a genuinely finite maximal-index set, including the empty case. -/
theorem finiteAlgebraMaximalSpectrumFinite (H E : Type*) [Field H] [CommRing E] [Algebra H E]
    [FiniteDimensional H E] : (Set.univ : Set (MaximalSpectrum E)).Finite := by
  let : IsArtinianRing E := IsArtinianRing.of_finite H E
  exact Set.toFinite _

/-- The actual finite local-factor dimensions add up to the original algebra dimension. -/
theorem sum_finrank_finiteAlgebraLocalization (H E : Type*) [Field H] [CommRing E] [Algebra H E]
    [FiniteDimensional H E] :
    ∑ m ∈ (finiteAlgebraMaximalSpectrumFinite H E).toFinset,
      Module.finrank H (Localization.AtPrime m.asIdeal) = Module.finrank H E := by
  classical
  let : IsArtinianRing E := IsArtinianRing.of_finite H E
  let : Fintype (MaximalSpectrum E) := Fintype.ofFinite _
  have hf : (finiteAlgebraMaximalSpectrumFinite H E).toFinset = Finset.univ := by
    ext m
    simp
  rw [hf, ← Module.finrank_pi_fintype]
  exact (finiteAlgebraLocalizationEquiv H E).toLinearEquiv.finrank_eq.symm

end EnvelopeProperty
