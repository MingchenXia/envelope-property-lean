/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.IntegralResidueLocalization
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace EnvelopeProperty

set_option backward.isDefEq.respectTransparency false in
/-- The ENTIRE residue map of an actual Spec morphism is conjugate to the original ideal residue map by the genuine stalk residue isomorphisms. -/
theorem specMap_residueFieldMap_eq {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (q : PrimeSpectrum B) :
    ((Spec.map (CommRingCat.ofHom f)).residueFieldMap q).hom =
      (Scheme.Spec.residueFieldIso (CommRingCat.of B) q).inv.hom.comp
        ((Ideal.ResidueField.map (q.comap f).asIdeal q.asIdeal f rfl).comp
          (Scheme.Spec.residueFieldIso (CommRingCat.of A) (q.comap f)).hom.hom) := by
  have he := Scheme.localRingHom_comp_stalkIso (CommRingCat.ofHom f) q
  have h := congrArg CommRingCat.Hom.hom he
  apply Ideal.Quotient.ringHom_ext
  ext s
  exact congrArg (IsLocalRing.residue ((Spec (CommRingCat.of B)).presheaf.stalk q))
    (RingHom.congr_fun h s).symm

end EnvelopeProperty

namespace EnvelopeProperty
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Genuine original prime injection and original residue pure inseparability imply the ACTUAL universally injective scheme morphism. -/
theorem universallyInjective_specMap_of_prime_and_residue {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hinj : Function.Injective (PrimeSpectrum.comap f))
    (hres : ∀ q : PrimeSpectrum B,
      (Ideal.ResidueField.map (q.comap f).asIdeal q.asIdeal f rfl).IsPurelyInseparable) :
    UniversallyInjective (Spec.map (CommRingCat.ofHom f)) := by
  apply ((tfae_universallyInjective (Spec.map (CommRingCat.ofHom f))).out 2 0).mp
  refine ⟨hinj, fun q => ?_⟩
  erw [specMap_residueFieldMap_eq f (q : PrimeSpectrum B)]
  let eA := (Scheme.Spec.residueFieldIso (CommRingCat.of A) (q.comap f)).commRingCatIsoToRingEquiv
  let eB := (Scheme.Spec.residueFieldIso (CommRingCat.of B) q).commRingCatIsoToRingEquiv
  have hA : eA.toRingHom.IsPurelyInseparable := isPurelyInseparable_of_surjective_fieldHom _ eA.surjective
  have hB : eB.symm.toRingHom.IsPurelyInseparable := isPurelyInseparable_of_surjective_fieldHom _ eB.symm.surjective
  exact (hA.comp (hres q)).comp hB

end EnvelopeProperty
