import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # The TRUE native stalk and residue maps of actual spectrum localizations -/
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.SpecLocalizationStalks
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S]
include M

/-- The SAME original induced local ring map of any actual localization is
bijective at EVERY original prime; no chosen stalk isomorphism is supplied. -/
theorem localRingHom_bijective (q : PrimeSpectrum S) :
    Function.Bijective (Localization.localRingHom
      (q.comap (algebraMap R S)).asIdeal q.asIdeal (algebraMap R S) rfl) := by
  let P := q.comap (algebraMap R S)
  let T := Localization.AtPrime q.asIdeal
  let : IsLocalization.AtPrime T P.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M T q.asIdeal
  exact IsLocalization.bijective P.asIdeal.primeCompl
    (Localization.localRingHom P.asIdeal q.asIdeal (algebraMap R S) rfl)
    (by
      ext r
      exact (Localization.localRingHom_to_map P.asIdeal q.asIdeal (algebraMap R S) rfl r).trans
        (IsScalarTower.algebraMap_apply R S T r).symm)

/-- The native original spectrum morphism has actual isomorphisms on ALL
original stalks, with the SAME native stalkMap and original point. -/
theorem stalkMap_isIso (q : PrimeSpectrum S) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap q) := by
  let g := Localization.localRingHom
    (q.comap (algebraMap R S)).asIdeal q.asIdeal (algebraMap R S) rfl
  let : IsIso (CommRingCat.ofHom g) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (localRingHom_bijective M q)
  rw [← Scheme.localRingHom_comp_stalkIso]
  change IsIso ((Spec.stalkIso (.of R) (q.comap (algebraMap R S))).hom ≫
    CommRingCat.ofHom g ≫ (Spec.stalkIso (.of S) q).inv)
  infer_instance

/-- Every SAME original native residue-field map of the localization
morphism is an isomorphism, internally derived from its actual stalk map. -/
theorem residueFieldMap_isIso (q : PrimeSpectrum S) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap R S))).residueFieldMap q) := by
  let := stalkMap_isIso M q
  let : IsLocalRing ((Spec (.of S)).presheaf.stalk q) :=
    (Spec (.of S)).toLocallyRingedSpace.isLocalRing q
  let : IsLocalRing ((Spec (.of R)).presheaf.stalk ((Spec.map
      (CommRingCat.ofHom (algebraMap R S))) q)) :=
    (Spec (.of R)).toLocallyRingedSpace.isLocalRing _
  exact (IsLocalRing.ResidueField.mapEquiv
    (asIso ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap q)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

end EnvelopeProperty.SpecLocalizationStalks
