/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeAffineCompletedFibre
import EnvelopeProperty.Berkovich.SpectrumFibreTopology
import EnvelopeProperty.Berkovich.SpectrumBridge
import EnvelopeProperty.Berkovich.SpectrumResidueFieldBridge
import EnvelopeProperty.Projective.BlowupChart

/-!
# Completed residue fields of affine charts in a blowup fibre

The fibre of an actual affine algebra morphism over a paper Berkovich point
is homeomorphic to the relative spectrum of its completed-residue-field
tensor algebra. This supplies the affine identifications used in
`lem:fc-fibre-model` of the fibre-constancy blueprint. Both maps retain the
whole original seminorm, not only its support. Comparison with the global
bigraded blowup model is a separate obligation.
-/

open scoped NNReal Topology TensorProduct
open Topology
noncomputable section
namespace EnvelopeProperty
universe u
namespace Berk
variable {k A C : Type u} [Field k] [CommRing A] [CommRing C]
    [Algebra k A] [Algebra k C] [Algebra A C] [IsScalarTower k A C]

/-- Forgetting the trivial coefficient prescription gives a homeomorphism
on a fibre: the prescription is forced by its base point. -/
def fcAbsoluteFibreHomeomorph (x : Berk k A) :
    {y : Berk k C // comap (IsScalarTower.toAlgHom k A C) y = x} ≃ₜ
      Berkovich.Spectrum.Fibre (B := C) x.toSpectrum where
  toFun y := ⟨y.1.toSpectrum, congrArg toSpectrum y.2⟩
  invFun z := ⟨
    { val := z.1.val
      val_algebraMap := by
        intro c hc
        have h := congrArg (fun t : Berkovich.Spectrum A => t.val (algebraMap k A c)) z.2
        change z.1.val (algebraMap A C (algebraMap k A c)) = x.val (algebraMap k A c) at h
        rw [← IsScalarTower.algebraMap_apply k A C] at h
        exact h.trans (x.val_algebraMap c hc) }, by
      apply Berk.ext
      apply Valuation.ext
      intro a
      exact congrArg (fun t : Berkovich.Spectrum A => t.val a) z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_toSpectrum.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Berk.continuous_iff.mpr
    intro c
    exact (Berkovich.Spectrum.continuous_abs c).comp continuous_subtype_val

/-- The genuine completed-field tensor algebra models the whole affine
analytic fibre, including its topology and prescribed coefficient norm. -/
def fcCompletedFibreHomeomorph (x : Berk k A) :
    Berkovich.RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] C) ≃ₜ
      {y : Berk k C // comap (IsScalarTower.toAlgHom k A C) y = x} :=
  (Berkovich.Spectrum.fibreHomeomorph x.toSpectrum).trans
    (fcAbsoluteFibreHomeomorph x).symm

/-- The completed-field fibre chart retains every original algebra value. -/
@[simp]
theorem fcCompletedFibreHomeomorph_val (x : Berk k A)
    (z : Berkovich.RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] C))
    (c : C) :
    (fcCompletedFibreHomeomorph x z).1.val c = z.1.val ((1 : H x) ⊗ₜ[A] c) := rfl

/-- Scalar factors in the completed tensor fibre have their actual norm. -/
theorem fcCompletedFibreHomeomorph_val_tmul (x : Berk k A)
    (z : Berkovich.RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] C))
    (h : H x) (c : C) :
    z.1.val (h ⊗ₜ[A] c) = ‖h‖₊ * (fcCompletedFibreHomeomorph x z).1.val c :=
  Berkovich.Spectrum.fibreRestrict_val_tmul x.toSpectrum z h c

/-- The actual completed-fibre chart map into the original affine space. -/
def fcCompletedFibreInclusion (x : Berk k A)
    (z : Berkovich.RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] C)) :
    Berk k C := (fcCompletedFibreHomeomorph x z).1

@[fun_prop]
theorem continuous_fcCompletedFibreInclusion (x : Berk k A) :
    Continuous (fcCompletedFibreInclusion (C := C) x) :=
  continuous_subtype_val.comp (fcCompletedFibreHomeomorph x).continuous

/-- The completed-field *scheme-theoretic* affine pullback, with its actual
structure map and norm, models the original paper analytic fibre. -/
def fcNativeCompletedFibreHomeomorph (x : Berk k A) :
    Berkovich.RelativeSchemeValuedPoint (NormedField.valuation (K := H x))
      (Berkovich.SchemeCompletedFibre.affineStructureMap (B := C) x.toSpectrum) ≃ₜ
      {y : Berk k C // comap (IsScalarTower.toAlgHom k A C) y = x} :=
  (Berkovich.SchemeCompletedFibre.affineTensorRelativeHomeomorph (B := C) x.toSpectrum).trans
    (fcCompletedFibreHomeomorph x)

/-- The whole native point underlying the paper fibre comparison is the
actual projection from the same scheme-theoretic completed-field pullback. -/
theorem fcNativeCompletedFibreHomeomorph_projection (x : Berk k A)
    (y : Berkovich.RelativeSchemeValuedPoint (NormedField.valuation (K := H x))
      (Berkovich.SchemeCompletedFibre.affineStructureMap (B := C) x.toSpectrum)) :
    (fcNativeCompletedFibreHomeomorph x y).1.toSpectrum =
      Berkovich.SchemeValuedPoint.spectrumHomeomorph
        (Berkovich.SchemeValuedPoint.map
          (Berkovich.SchemeCompletedFibre.affineProjection (B := C) x.toSpectrum) y.1) := by
  have he := congrArg (fun z => Berkovich.SchemeValuedPoint.spectrumHomeomorph z)
    (Berkovich.SchemeCompletedFibre.affineFibreHomeomorph_apply (B := C) x.toSpectrum y)
  simp only [Berkovich.SchemeCompletedFibre.affineFibreHomeomorph] at he
  change Berkovich.SchemeValuedPoint.spectrumHomeomorph
    (Berkovich.SchemeValuedPoint.spectrumHomeomorph.symm
      ((Berkovich.Spectrum.fibreHomeomorph x.toSpectrum)
        ((Berkovich.SchemeCompletedFibre.affineTensorRelativeHomeomorph
          (B := C) x.toSpectrum) y)).1) = _ at he
  rw [Homeomorph.apply_symm_apply] at he
  exact he

end Berk
namespace ProjSubvariety.BlowupCenter
variable {k : Type*} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (B : V.BlowupCenter M')

/-- Every analytic blowup fibre is compact, since the total blowup space is
compact Hausdorff and its projection is continuous. -/
theorem fc_isCompact_fibre (t : V.an) : IsCompact (B.proj ⁻¹' {t}) :=
  (isClosed_singleton.preimage B.continuous_proj).isCompact

end ProjSubvariety.BlowupCenter
end EnvelopeProperty
