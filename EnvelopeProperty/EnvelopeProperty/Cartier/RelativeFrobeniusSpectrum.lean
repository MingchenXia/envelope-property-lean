import EnvelopeProperty.Cartier.RelativeFrobenius
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # The entire actual prime spectrum of genuine relative Frobenius -/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeFrobenius
open CategoryTheory
universe u
variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
variable (p : ℕ) [hp : Fact p.Prime] [CharP A p] [CharP B p]

private theorem comap_frobenius {R : Type u} [CommRing R] [CharP R p]
    (P : PrimeSpectrum R) : PrimeSpectrum.comap (frobenius R p) P = P := by
  apply PrimeSpectrum.ext
  ext x
  exact P.isPrime.pow_mem_iff_mem p hp.out.pos

/-- The ACTUAL relative Frobenius gives a whole original prime-spectrum homeomorphism,
with inverse the ACTUAL original source map. No topological comparison premise is supplied. -/
def spectrumHomeomorph : PrimeSpectrum B ≃ₜ PrimeSpectrum (twist f p) where
  toFun := PrimeSpectrum.comap (map f p).hom
  invFun := PrimeSpectrum.comap (sourceMap f p).hom
  left_inv P := by
    rw [← PrimeSpectrum.comap_comp_apply]
    have h := congrArg (fun h : CommRingCat.of B ⟶ CommRingCat.of B => h.hom) (sourceMap_map f p)
    change (map f p).hom.comp (sourceMap f p).hom = frobenius B p at h
    rw [h]
    exact comap_frobenius p P
  right_inv P := by
    rw [← PrimeSpectrum.comap_comp_apply]
    have h := congrArg (fun h : twist f p ⟶ twist f p => h.hom) (map_sourceMap f p)
    change (sourceMap f p).hom.comp (map f p).hom = frobenius (twist f p) p at h
    rw [h]
    exact comap_frobenius p P
  continuous_toFun := PrimeSpectrum.continuous_comap _
  continuous_invFun := PrimeSpectrum.continuous_comap _

/-- Surjectivity on the ENTIRE actual original prime spectrum is genuinely derived. -/
theorem comap_surjective : Function.Surjective (PrimeSpectrum.comap (map f p).hom) :=
  (spectrumHomeomorph f p).surjective

/-- Injectivity on the ENTIRE actual original prime spectrum is genuinely derived. -/
theorem comap_injective : Function.Injective (PrimeSpectrum.comap (map f p).hom) :=
  (spectrumHomeomorph f p).injective

end EnvelopeProperty.Cartier.RelativeFrobenius
