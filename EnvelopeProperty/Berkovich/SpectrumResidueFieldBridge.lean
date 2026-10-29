/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.ResidueField
import EnvelopeProperty.Berkovich.SpectrumResidueField
import EnvelopeProperty.Berkovich.SpectrumBridge

/-!
# The paper's completed residue fields specialize the general construction

Forgetting the prescribed trivial valuation preserves the point's valuation
exactly. The support residue fields, their induced absolute values, and their
completed normed fields are consequently canonically identical. The ring
equivalences below preserve the original-ring maps, norms, and arbitrary algebra
pullback maps. No additional hypothesis or valuation-extension result is used.
-/

noncomputable section

namespace EnvelopeProperty.Berk

open Berkovich

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- The support residue field is unchanged by forgetting the prescribed base valuation. -/
def residueFieldSpectrumEquiv (x : Berk k A) :
    x.ResidueField ≃+* Spectrum.ResidueField x.toSpectrum := RingEquiv.refl _

@[simp]
theorem residueFieldSpectrumEquiv_algebraMap (x : Berk k A) (a : A) :
    residueFieldSpectrumEquiv x (algebraMap A x.ResidueField a) =
      algebraMap A (Spectrum.ResidueField x.toSpectrum) a := rfl

@[simp]
theorem residueValuation_toSpectrum (x : Berk k A) :
    Spectrum.residueValuation x.toSpectrum = x.residueValuation := rfl

@[simp]
theorem residueAbs_toSpectrum (x : Berk k A) :
    Spectrum.residueAbs x.toSpectrum = x.residueAbs := rfl

/-- Both completed residue fields complete exactly the same absolute-valued field. -/
def completedResidueFieldSpectrumEquiv (x : Berk k A) :
    H x ≃+* Spectrum.H x.toSpectrum := RingEquiv.refl _

@[simp]
theorem norm_completedResidueFieldSpectrumEquiv (x : Berk k A) (z : H x) :
    ‖completedResidueFieldSpectrumEquiv x z‖ = ‖z‖ := rfl

/-- The canonical completed-field identification is an isometry. -/
theorem isometry_completedResidueFieldSpectrumEquiv (x : Berk k A) :
    Isometry (completedResidueFieldSpectrumEquiv x) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_completedResidueFieldSpectrumEquiv x)

@[simp]
theorem completedResidueFieldSpectrumEquiv_residueToH (x : Berk k A) (z : x.ResidueField) :
    completedResidueFieldSpectrumEquiv x (x.residueToH z) =
      Spectrum.residueToH x.toSpectrum (residueFieldSpectrumEquiv x z) := rfl

@[simp]
theorem completedResidueFieldSpectrumEquiv_toH (x : Berk k A) (a : A) :
    completedResidueFieldSpectrumEquiv x (x.toH a) = Spectrum.toH x.toSpectrum a := rfl

section Pullback

variable {B : Type*} [CommRing B] [Algebra k B]

/-- The paper pullback equality gives the actual underlying ring-spectrum equality. -/
theorem toSpectrum_comap_eq (φ : A →ₐ[k] B) {x : Berk k A} {y : Berk k B}
    (h : comap φ y = x) : Spectrum.comap φ.toRingHom y.toSpectrum = x.toSpectrum :=
  congrArg toSpectrum h

/-- Canonical residue-field identifications commute with the actual pullback embeddings. -/
theorem residueFieldSpectrumEquiv_map (φ : A →ₐ[k] B) {x : Berk k A} {y : Berk k B}
    (h : comap φ y = x) (z : x.ResidueField) :
    residueFieldSpectrumEquiv y (ResidueField.map φ h z) =
      Spectrum.ResidueField.map φ.toRingHom (toSpectrum_comap_eq φ h)
        (residueFieldSpectrumEquiv x z) := rfl

/-- Canonical completed-field identifications commute with the actual completed embeddings. -/
theorem completedResidueFieldSpectrumEquiv_map (φ : A →ₐ[k] B)
    {x : Berk k A} {y : Berk k B} (h : comap φ y = x) (z : H x) :
    completedResidueFieldSpectrumEquiv y (H.map φ h z) =
      Spectrum.H.map φ.toRingHom (toSpectrum_comap_eq φ h)
        (completedResidueFieldSpectrumEquiv x z) := rfl

end Pullback

end EnvelopeProperty.Berk
