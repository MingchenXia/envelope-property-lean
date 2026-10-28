/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumFinite
import EnvelopeProperty.Berkovich.SpectrumQuotient

/-!
# Exact images and point existence for integral seminorm maps

For an integral ring homomorphism, a real seminorm point lifts exactly when
its support contains the homomorphism's kernel. Lying over makes its genuine
completed residue-field tensor fibre nonzero; the proved maximal-support fibre
classification then supplies an actual lift. The image is the kernel zero locus,
and injective integral maps give surjective pullback.

Every prescribed-base relative version follows by retaining all coefficient
values. No original field, trivial norm, finite type, or completeness hypothesis
is imposed. No unrestricted scalar base-change extension is asserted.
-/

open scoped NNReal Topology TensorProduct
open Classical

noncomputable section

namespace EnvelopeProperty.Berkovich

namespace Spectrum

variable {A B : Type*} [CommRing A] [CommRing B]

section Algebra

variable [Algebra A B]

/-- Lying over and the faithful scalar extension to the genuine completed residue
field make every unobstructed integral tensor fibre nonzero. -/
theorem nontrivial_fibre [Algebra.IsIntegral A B] (x : Spectrum A)
    (hx : RingHom.ker (algebraMap A B) ≤ x.val.supp) : Nontrivial (H x ⊗[A] B) := by
  obtain ⟨Q, _, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.val.supp (⊥ : Ideal B)
    (by rwa [← RingHom.ker_eq_comap_bot])
  have : Nontrivial (x.ResidueField ⊗[A] B) :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap ⟨x.val.supp, inferInstance⟩).2
      ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQp⟩
  have : Nontrivial (H x ⊗[x.ResidueField] (x.ResidueField ⊗[A] B)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left (R := x.ResidueField)
      (H x) (x.ResidueField ⊗[A] B) (algebraMap x.ResidueField (x.ResidueField ⊗[A] B)).injective
  exact (Algebra.TensorProduct.cancelBaseChange A x.ResidueField (H x) (H x)
    B).symm.toAlgHom.toRingHom.domain_nontrivial

/-- A maximal ideal of the nonzero completed tensor fibre yields an actual point
over every unobstructed point of an integral algebra map. -/
theorem exists_comap_eq [Algebra.IsIntegral A B] (x : Spectrum A)
    (hx : RingHom.ker (algebraMap A B) ≤ x.val.supp) :
    ∃ y : Spectrum B, comap (algebraMap A B) y = x := by
  have := nontrivial_fibre (B := B) x hx
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (H x ⊗[A] B)
  obtain ⟨y, _⟩ := (fibreToMaximalSpectrum_bijective (B := B) x).2 ⟨m, hm⟩
  exact ⟨y.1, y.2⟩

end Algebra

/-- Arbitrary integral ring homomorphisms admit points above exactly the supports
containing their kernels. This is the constructive existence direction. -/
theorem exists_comap_eq_of_isIntegral (φ : A →+* B) (hφ : φ.IsIntegral)
    (x : Spectrum A) (hx : RingHom.ker φ ≤ x.val.supp) :
    ∃ y : Spectrum B, comap φ y = x := by
  let : Algebra A B := φ.toAlgebra
  let : Algebra.IsIntegral A B := ⟨hφ⟩
  exact exists_comap_eq x hx

/-- The kernel containment is both necessary and sufficient for integral point existence. -/
theorem exists_comap_eq_iff_of_isIntegral (φ : A →+* B) (hφ : φ.IsIntegral) (x : Spectrum A) :
    (∃ y : Spectrum B, comap φ y = x) ↔ RingHom.ker φ ≤ x.val.supp := by
  refine ⟨?_, exists_comap_eq_of_isIntegral φ hφ x⟩
  rintro ⟨y, rfl⟩ a ha
  change y.val (φ a) = 0
  rw [RingHom.mem_ker.1 ha, map_zero]

/-- The image of an integral spectral pullback is precisely its kernel zero locus. -/
theorem range_comap_of_isIntegral (φ : A →+* B) (hφ : φ.IsIntegral) :
    Set.range (comap φ) = zeroLocus (RingHom.ker φ) := by
  ext x
  exact exists_comap_eq_iff_of_isIntegral φ hφ x

/-- An injective integral ring homomorphism induces a surjective map of seminorm spectra. -/
theorem comap_surjective_of_isIntegral (φ : A →+* B) (hφ : φ.IsIntegral)
    (hinj : Function.Injective φ) : Function.Surjective (comap φ) := fun x =>
  exists_comap_eq_of_isIntegral φ hφ x (by
    rw [(RingHom.injective_iff_ker_eq_bot φ).1 hinj]
    exact bot_le)

end Spectrum

namespace RelativeSpectrum

variable {R : Type*} [CommRing R] {v : Valuation R ℝ≥0}
    {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Integral absolute point existence automatically preserves every prescribed
base value under an algebra homomorphism. -/
theorem exists_comap_eq_of_isIntegral (φ : A →ₐ[R] B) (hφ : φ.toRingHom.IsIntegral)
    (x : RelativeSpectrum v A) (hx : RingHom.ker φ.toRingHom ≤ x.1.val.supp) :
    ∃ y : RelativeSpectrum v B, comap φ y = x := by
  obtain ⟨y, hy⟩ := Spectrum.exists_comap_eq_of_isIntegral φ.toRingHom hφ x.1 hx
  let z : RelativeSpectrum v B := ⟨y, fun r => by
    have h := congrArg (fun t : Spectrum A => t.val (algebraMap R A r)) hy
    change y.val (φ (algebraMap R A r)) = x.1.val (algebraMap R A r) at h
    rw [φ.commutes] at h
    exact h.trans (x.2 r)⟩
  exact ⟨z, Subtype.ext hy⟩

/-- The same exact kernel obstruction characterizes relative integral images. -/
theorem exists_comap_eq_iff_of_isIntegral (φ : A →ₐ[R] B) (hφ : φ.toRingHom.IsIntegral)
    (x : RelativeSpectrum v A) :
    (∃ y : RelativeSpectrum v B, comap φ y = x) ↔ RingHom.ker φ.toRingHom ≤ x.1.val.supp := by
  refine ⟨?_, exists_comap_eq_of_isIntegral φ hφ x⟩
  rintro ⟨y, rfl⟩ a ha
  change y.1.val (φ.toRingHom a) = 0
  rw [RingHom.mem_ker.1 ha, map_zero]

/-- The image of a relative integral map is its actual relative kernel zero locus. -/
theorem range_comap_of_isIntegral (φ : A →ₐ[R] B) (hφ : φ.toRingHom.IsIntegral) :
    Set.range (comap (v := v) φ) = zeroLocus v (RingHom.ker φ.toRingHom) := by
  ext x
  exact exists_comap_eq_iff_of_isIntegral φ hφ x

/-- Injective integral algebra homomorphisms give surjectivity over every prescribed base. -/
theorem comap_surjective_of_isIntegral (φ : A →ₐ[R] B) (hφ : φ.toRingHom.IsIntegral)
    (hinj : Function.Injective φ) : Function.Surjective (comap (v := v) φ) := fun x =>
  exists_comap_eq_of_isIntegral φ hφ x (by
    rw [(RingHom.injective_iff_ker_eq_bot φ.toRingHom).1 hinj]
    exact bot_le)

end RelativeSpectrum

end EnvelopeProperty.Berkovich
