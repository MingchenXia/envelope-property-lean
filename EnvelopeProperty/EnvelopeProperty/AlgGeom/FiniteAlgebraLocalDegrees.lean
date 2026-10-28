import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.LocalRing.ResidueField.Instances

/-! # The true residue-weighted local degrees of the SAME finite field algebra -/
open Module IsLocalRing
noncomputable section
universe u
namespace EnvelopeProperty.FiniteAlgebraLocalDegrees
variable {k : Type u} [Field k]

/-- The original field dimension of a local finite algebra is its ACTUAL
local length times the ACTUAL original residue-field degree. -/
theorem local_finrank_eq_length_mul_residue_finrank (B : Type u) [CommRing B]
    [IsLocalRing B] [Algebra k B] [Module.Finite k B] :
    Module.finrank k B = (Module.length B B).toNat * Module.finrank k (ResidueField B) := by
  let : IsLocalHom (algebraMap k B) :=
    ⟨fun a ha => by
      apply isUnit_iff_ne_zero.mpr
      intro hz
      subst a
      simp at ha⟩
  have h := IsLocalRing.length_restrictScalars k B B
  have hr : Module.length k (ResidueField B) =
      Module.length (ResidueField k) (ResidueField B) :=
    Module.length_eq_of_surjective (residue_surjective (R := k))
  rw [← hr, Module.length_eq_finrank, Module.length_eq_finrank] at h
  have hn := congrArg ENat.toNat h
  simpa using hn

/-- The SAME finite original algebra's whole field dimension is the actual
finite sum of its ACTUAL residue-weighted localization lengths. -/
theorem finrank_eq_sum_local_length_mul_residue_finrank (A : Type u) [CommRing A]
    [Algebra k A] [Module.Finite k A] :
    (Module.finrank k A : ℕ) = ∑ᶠ p : PrimeSpectrum A,
      (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)).toNat *
        Module.finrank k (ResidueField (Localization.AtPrime p.asIdeal)) := by
  let : IsArtinianRing A := IsArtinianRing.of_finite k A
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, IsArtinianRing.finrank_eq_sum_primeSpectrum A k]
  apply Finset.sum_congr rfl
  intro p _
  let : Module.Finite k (Localization.AtPrime p.asIdeal) :=
    Module.Finite.of_surjective (Algebra.algHom k A (Localization.AtPrime p.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))
  exact local_finrank_eq_length_mul_residue_finrank (k := k) (Localization.AtPrime p.asIdeal)

end EnvelopeProperty.FiniteAlgebraLocalDegrees
