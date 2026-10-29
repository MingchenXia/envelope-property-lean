/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.IntegralClosureLocalization
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.RingHom.PurelyInseparable

noncomputable section
namespace EnvelopeProperty
/-- Pure inseparability of an actual surjective field comparison, used only for genuine residue equivalences. -/
theorem isPurelyInseparable_of_surjective_fieldHom {F E : Type*} [Field F] [Field E]
    (f : F →+* E) (hf : Function.Surjective f) : f.IsPurelyInseparable := by
  let : Algebra F E := f.toAlgebra
  exact ⟨algebraMap_isIntegral_iff.mp (f.isIntegral_of_surjective hf), fun x _ => hf x⟩


variable {A B T : Type*} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [hIntegral : Algebra.IsIntegral A B]
  (p : Ideal A) [p.IsPrime] [Algebra B T]
  [hLoc : IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) T] [hT : IsLocalRing T]
  (q : Ideal B) [q.IsPrime] (hq : q.under A = p)
include p hq hIntegral hLoc hT

/-- The TRUE original prime localization is constructed from integral maximality and actual units. -/
theorem isLocalization_atPrime_of_local_baseLocalization : IsLocalization q.primeCompl T := by
  let M := Algebra.algebraMapSubmonoid B p.primeCompl
  have hM : M ≤ q.primeCompl := by
    rintro _ ⟨a, ha, rfl⟩ hqa
    apply ha
    change a ∈ p
    rw [← hq]
    exact hqa
  have hd : Disjoint (M : Set B) (q : Set B) := by
    apply Set.disjoint_left.mpr
    exact fun b hb hq => hM hb hq
  have hm : q.map (algebraMap B T) = IsLocalRing.maximalIdeal T :=
    IsLocalRing.eq_maximalIdeal (prime_map_isMaximal_of_base_localization p q hq)
  have hc : (IsLocalRing.maximalIdeal T).under B = q := by
    rw [← hm]
    exact IsLocalization.under_map_of_isPrime_disjoint M T inferInstance hd
  apply IsLocalization.of_le M q.primeCompl hM
  intro b hb
  apply IsLocalRing.notMem_maximalIdeal.mp
  change b ∉ (IsLocalRing.maximalIdeal T).under B
  rwa [hc]

/-- The genuine original B_q is WHOLE coefficient-preservingly equivalent to the actual local base localization. -/
def baseLocalizationAtPrimeEquiv : Localization.AtPrime q ≃ₐ[B] T := by
  let : IsLocalization q.primeCompl T := isLocalization_atPrime_of_local_baseLocalization p q hq
  exact IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) T

/-- Every original coefficient follows its genuine localization comparison. -/
@[simp]
theorem baseLocalizationAtPrimeEquiv_algebraMap (b : B) :
    baseLocalizationAtPrimeEquiv (T := T) p q hq (algebraMap B (Localization.AtPrime q) b) =
      algebraMap B T b := (baseLocalizationAtPrimeEquiv (T := T) p q hq).commutes b

private local instance baseLocalizationEquivLocal :
    IsLocalHom (baseLocalizationAtPrimeEquiv (T := T) p q hq).toRingHom :=
  isLocalHom_of_leftInverse (baseLocalizationAtPrimeEquiv (T := T) p q hq).symm.toRingHom
    (baseLocalizationAtPrimeEquiv (T := T) p q hq).left_inv

/-- The ACTUAL localized original coefficient map is local by composition of real local maps. -/
def baseLocalizationHom : Localization.AtPrime p →+* T :=
  (baseLocalizationAtPrimeEquiv (T := T) p q hq).toRingHom.comp
    (Localization.localRingHom p q (algebraMap A B) hq.symm)

private local instance baseLocalizationHomLocal :
    IsLocalHom (baseLocalizationHom (T := T) p q hq) :=
  inferInstanceAs (IsLocalHom ((baseLocalizationAtPrimeEquiv (T := T) p q hq).toRingHom.comp
    (Localization.localRingHom p q (algebraMap A B) hq.symm)))

/-- The WHOLE localized coefficient map is the genuine universal localization map, not merely equal on supports. -/
theorem baseLocalizationHom_eq_map :
    baseLocalizationHom (T := T) p q hq =
      IsLocalization.map (T := Algebra.algebraMapSubmonoid B p.primeCompl) T (algebraMap A B)
        (show p.primeCompl ≤ (Algebra.algebraMapSubmonoid B p.primeCompl).comap (algebraMap A B) from
          p.primeCompl.le_comap_map) := by
  apply IsLocalization.ringHom_ext p.primeCompl
  apply RingHom.ext
  intro a
  change baseLocalizationAtPrimeEquiv (T := T) p q hq
    (Localization.localRingHom p q (algebraMap A B) hq.symm
      (algebraMap A (Localization.AtPrime p) a)) = _
  rw [Localization.localRingHom_to_map, baseLocalizationAtPrimeEquiv_algebraMap]
  exact (IsLocalization.map_eq (M := p.primeCompl) (S := Localization.AtPrime p)
    (T := Algebra.algebraMapSubmonoid B p.primeCompl) (Q := T)
    (g := algebraMap A B)
    (show p.primeCompl ≤ (Algebra.algebraMapSubmonoid B p.primeCompl).comap (algebraMap A B) from
      p.primeCompl.le_comap_map) a).symm

/-- The complete original residue square follows the true whole local maps. -/
theorem residueFieldMap_baseLocalizationHom :
    IsLocalRing.ResidueField.map (baseLocalizationHom (T := T) p q hq) =
      (IsLocalRing.ResidueField.mapEquiv (baseLocalizationAtPrimeEquiv (T := T) p q hq).toRingEquiv).toRingHom.comp
        (Ideal.ResidueField.map p q (algebraMap A B) hq.symm) :=
  IsLocalRing.ResidueField.map_comp _ _

/-- The actual original residue extension inherits pure inseparability through the TRUE residue square. -/
theorem residueFieldMap_isPurelyInseparable_of_local_baseLocalization
    (h : (IsLocalRing.ResidueField.map (baseLocalizationHom (T := T) p q hq)).IsPurelyInseparable) :
    (Ideal.ResidueField.map p q (algebraMap A B) hq.symm).IsPurelyInseparable := by
  let e := IsLocalRing.ResidueField.mapEquiv (baseLocalizationAtPrimeEquiv (T := T) p q hq).toRingEquiv
  have he : e.symm.toRingHom.IsPurelyInseparable :=
    isPurelyInseparable_of_surjective_fieldHom _ e.symm.surjective
  have hc := h.comp he
  have hh : e.symm.toRingHom.comp (IsLocalRing.ResidueField.map (baseLocalizationHom (T := T) p q hq)) =
      Ideal.ResidueField.map p q (algebraMap A B) hq.symm := by
    rw [residueFieldMap_baseLocalizationHom]
    ext x
    exact e.symm_apply_apply _
  rwa [hh] at hc

end EnvelopeProperty
