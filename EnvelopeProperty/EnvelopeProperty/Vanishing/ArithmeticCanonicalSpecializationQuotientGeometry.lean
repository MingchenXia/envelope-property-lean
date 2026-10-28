import EnvelopeProperty.Vanishing.ArithmeticCanonicalSpecializationGeometry

/-! # The actual quotient closed fibre and its localization residue field

The quotient and the localization residue field are distinct native types.
Their actual coefficient equivalence constructs a fibre scheme isomorphism
retaining the same original-family projection.
-/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalSpecializationQuotientGeometry

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (P : Ideal R) [P.IsMaximal]

/-- The actual quotient-to-localization-residue coefficient isomorphism. -/
def quotientResidueEquiv : (R ⧸ P) ≃+* P.ResidueField :=
  RingEquiv.ofBijective (algebraMap (R ⧸ P) P.ResidueField)
    P.bijective_algebraMap_quotient_residueField

theorem quotientResidueEquiv_mk (r : R) :
    quotientResidueEquiv P (Ideal.Quotient.mk P r) = algebraMap R P.ResidueField r :=
  P.algebraMap_quotient_residueField_mk r

/-- Its spectrum is the actual scalar isomorphism in the opposite direction. -/
def residueSpecIso : Spec (.of P.ResidueField) ≅ Spec (.of (R ⧸ P)) :=
  Scheme.Spec.mapIso (quotientResidueEquiv P).toCommRingCatIso.op

theorem residueSpecIso_hom_base :
    (residueSpecIso P).hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) =
      Spec.map (CommRingCat.ofHom (algebraMap R P.ResidueField)) := by
  change Spec.map (CommRingCat.ofHom (quotientResidueEquiv P).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  ext r
  exact quotientResidueEquiv_mk P r

theorem residueSpecIso_inv_base :
    (residueSpecIso P).inv ≫ Spec.map (CommRingCat.ofHom (algebraMap R P.ResidueField)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) := by
  rw [← residueSpecIso_hom_base P, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

variable {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))

private opaque fibreIsoData :
    {e : Limits.pullback p (Spec.map (CommRingCat.ofHom (algebraMap R P.ResidueField))) ≅
        Limits.pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))) //
      e.hom ≫ Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))) =
        Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R P.ResidueField)))} := by
  let bQ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))
  let bκ := Spec.map (CommRingCat.ofHom (algebraMap R P.ResidueField))
  let h : Limits.pullback p bκ ⟶ Limits.pullback p bQ :=
    Limits.pullback.lift (Limits.pullback.fst p bκ)
      (Limits.pullback.snd p bκ ≫ (residueSpecIso P).hom) (by
        rw [Category.assoc, residueSpecIso_hom_base]
        exact Limits.pullback.condition)
  let i : Limits.pullback p bQ ⟶ Limits.pullback p bκ :=
    Limits.pullback.lift (Limits.pullback.fst p bQ)
      (Limits.pullback.snd p bQ ≫ (residueSpecIso P).inv) (by
        rw [Category.assoc, residueSpecIso_inv_base]
        exact Limits.pullback.condition)
  let e : Limits.pullback p bκ ≅ Limits.pullback p bQ :=
    { hom := h, inv := i,
      hom_inv_id := by
        apply Limits.pullback.hom_ext <;>
          simp [h, i, Category.assoc]
      inv_hom_id := by
        apply Limits.pullback.hom_ext <;>
          simp [h, i, Category.assoc] }
  exact ⟨e, Limits.pullback.lift_fst _ _ _⟩

/-- The actual native localization-residue fibre is isomorphic to the
actual quotient fibre; no fibre comparison certificate is supplied. -/
def residueFibreIso :
    Limits.pullback p (Spec.map (CommRingCat.ofHom (algebraMap R P.ResidueField))) ≅
      Limits.pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))) :=
  (fibreIsoData P p).val

theorem residueFibreIso_fst :
    (residueFibreIso P p).hom ≫
        Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))) =
      Limits.pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R P.ResidueField))) :=
  (fibreIsoData P p).property

end EnvelopeProperty.Vanishing.ArithmeticCanonicalSpecializationQuotientGeometry
