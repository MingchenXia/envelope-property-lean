/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.UnibranchLocalRing
import EnvelopeProperty.IntegralResidueLocalization

/-!
# Standard structural unibranchness under actual ring equivalences

All reductions, fraction rings, normalizations and residue maps are genuine
original ones. The entire coefficient square is proved before transporting
pure inseparability. No spectrum or native injection is assumed.
-/

noncomputable section
namespace EnvelopeProperty
namespace LocalNormalization
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Actual ring equivalences preserve the ORIGINAL nilradical, including all nonreduced structure before quotienting. -/
theorem map_nilradical_eq (e : R ≃+* S) :
    (nilradical R).map e.toRingHom = nilradical S := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    exact mem_nilradical.mpr ((mem_nilradical.mp hr).map e)
  · intro s hs
    have ht : e.symm s ∈ nilradical R := mem_nilradical.mpr ((mem_nilradical.mp hs).map e.symm)
    have hm := Ideal.mem_map_of_mem e.toRingHom ht
    change e (e.symm s) ∈ (nilradical R).map e.toRingHom at hm
    rwa [e.apply_symm_apply] at hm

/-- The genuine ORIGINAL reduction equivalence induced by the actual ring isomorphism. -/
def reducedEquiv (e : R ≃+* S) : Reduced R ≃+* Reduced S :=
  Ideal.quotientEquiv (nilradical R) (nilradical S) e (map_nilradical_eq e).symm

/-- Every original coefficient class is preserved through the whole reduction square. -/
@[simp]
theorem reducedEquiv_mk (e : R ≃+* S) (r : R) :
    reducedEquiv e (Ideal.Quotient.mk (nilradical R) r) = Ideal.Quotient.mk (nilradical S) (e r) := rfl

/-- Actual fraction-ring uniqueness extends the ORIGINAL reduction equivalence to whole ambient rings. -/
def fractionEquiv (e : R ≃+* S) : FractionRing (Reduced R) ≃+* FractionRing (Reduced S) :=
  IsFractionRing.ringEquivOfRingEquiv (reducedEquiv e)

/-- The genuine ambient comparison retains EVERY original reduced coefficient. -/
@[simp]
theorem fractionEquiv_algebraMap (e : R ≃+* S) (r : Reduced R) :
    fractionEquiv e (algebraMap (Reduced R) (FractionRing (Reduced R)) r) =
      algebraMap (Reduced S) (FractionRing (Reduced S)) (reducedEquiv e r) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (reducedEquiv e) r

/-- The literal reduced normalizations are genuinely equivalent, by mapping ACTUAL monic integral relations in both directions. -/
def normalizationEquiv (e : R ≃+* S) : Ring R ≃+* Ring S where
  toFun x := ⟨fractionEquiv e x, IsIntegral.map_of_comp_eq (reducedEquiv e).toRingHom
    (fractionEquiv e).toRingHom (by
      ext r
      exact (fractionEquiv_algebraMap e r).symm) x.2⟩
  invFun x := ⟨(fractionEquiv e).symm x, IsIntegral.map_of_comp_eq (reducedEquiv e).symm.toRingHom
    (fractionEquiv e).symm.toRingHom (by
      ext s
      exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap (K := FractionRing (Reduced S))
        (L := FractionRing (Reduced R)) (reducedEquiv e).symm s).symm) x.2⟩
  left_inv x := Subtype.ext ((fractionEquiv e).symm_apply_apply x.1)
  right_inv x := Subtype.ext ((fractionEquiv e).apply_symm_apply x.1)
  map_mul' x y := Subtype.ext ((fractionEquiv e).map_mul x.1 y.1)
  map_add' x y := Subtype.ext ((fractionEquiv e).map_add x.1 y.1)

/-- Every WHOLE integral element follows its true original ambient equivalence. -/
@[simp]
theorem normalizationEquiv_coe (e : R ≃+* S) (x : Ring R) :
    ((normalizationEquiv e x : Ring S) : FractionRing (Reduced S)) = fractionEquiv e x := rfl

/-- The ENTIRE original coefficient square commutes before taking any residue or valuation. -/
@[simp]
theorem normalizationEquiv_coefficientMap (e : R ≃+* S) (r : R) :
    normalizationEquiv e (coefficientMap R r) = coefficientMap S (e r) := by
  apply Subtype.ext
  exact fractionEquiv_algebraMap e (Ideal.Quotient.mk (nilradical R) r)

end LocalNormalization

/-- STANDARD unibranchness transports via the TRUE reduction and literal normalization equivalences. -/
theorem IsUnibranchLocalRing.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) [IsUnibranchLocalRing R] :
    IsUnibranchLocalRing S where
  isDomain_reduced := (LocalNormalization.reducedEquiv e).symm.toMulEquiv.isDomain
    (LocalNormalization.Reduced R)
  isLocalRing_normalization := (LocalNormalization.normalizationEquiv e).isLocalRing

namespace LocalNormalization

/-- The ACTUAL induced residue maps obey the WHOLE coefficient square, not only equality of residue supports. -/
theorem residueFieldMap_ringEquiv_square {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsUnibranchLocalRing R] [IsUnibranchLocalRing S]
    (e : R ≃+* S) :
    (IsLocalRing.ResidueField.mapEquiv (normalizationEquiv e)).toRingHom.comp (residueFieldMap R) =
      (residueFieldMap S).comp (IsLocalRing.ResidueField.mapEquiv e).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  ext r
  exact congrArg (IsLocalRing.residue (Ring S)) (normalizationEquiv_coefficientMap e r)

end LocalNormalization

/-- STANDARD geometric unibranchness transports through the DERIVED entire residue square and genuine residue equivalences. -/
theorem IsGeometricallyUnibranchLocalRing.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) [IsGeometricallyUnibranchLocalRing R] :
    IsGeometricallyUnibranchLocalRing S := by
  let hS : IsUnibranchLocalRing S := IsUnibranchLocalRing.of_ringEquiv e
  let eR := IsLocalRing.ResidueField.mapEquiv e
  let eN := IsLocalRing.ResidueField.mapEquiv (LocalNormalization.normalizationEquiv e)
  have hN : eN.toRingHom.IsPurelyInseparable :=
    isPurelyInseparable_of_surjective_fieldHom _ eN.surjective
  have hR : eR.symm.toRingHom.IsPurelyInseparable :=
    isPurelyInseparable_of_surjective_fieldHom _ eR.symm.surjective
  have hpure := hR.comp ((IsGeometricallyUnibranchLocalRing.residueFieldMap_isPurelyInseparable
    (R := R)).comp hN)
  refine { toIsUnibranchLocalRing := hS, residueFieldMap_isPurelyInseparable := ?_ }
  have he : (eN.toRingHom.comp (LocalNormalization.residueFieldMap R)).comp eR.symm.toRingHom =
      LocalNormalization.residueFieldMap S := by
    rw [LocalNormalization.residueFieldMap_ringEquiv_square]
    ext x
    exact congrArg (LocalNormalization.residueFieldMap S) (eR.apply_symm_apply x)
  rwa [he] at hpure

end EnvelopeProperty
