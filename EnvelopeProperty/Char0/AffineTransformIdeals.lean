/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.MonomialIsoOpen

/-!
# Actual affine-chart transform ideals

The native affine ideal identities of the SNC chart producers are identified
with the normalized ideal of the actual pulled-back centre on its literal
spectrum. This supplies the input of the boundary-open producer.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory
open scoped Classical

universe u

variable {R : Type u} [CommRing R]

/-- Normalizing the actual sheaf associated to a ring ideal returns that ring ideal. -/
theorem idealOfSpecSheaf_specIdealSheaf (I : Ideal R) : idealOfSpecSheaf (specIdealSheaf I) = I := by
  rw [idealOfSpecSheaf, specIdealSheaf_ideal_top, Ideal.map_map, ← CommRingCat.hom_comp,
    Iso.inv_hom_id, CommRingCat.hom_id, Ideal.map_id]

variable {Y : Scheme.{u}}

/-- The actual affine spectrum chart computes the original native ideal, without an affine
ideal-presentation hypothesis. -/
theorem idealOfSpecSheaf_comap_fromSpec (J : Y.IdealSheafData) (U : Y.affineOpens) :
    idealOfSpecSheaf (J.comap U.2.fromSpec) = J.ideal U := by
  rw [Scheme.IdealSheafData.comap_fromSpec]
  exact idealOfSpecSheaf_specIdealSheaf _

/-- The normalized actual transform along the canonical affine chart is its native ideal. -/
theorem idealOfSpecSheaf_comap_fromSpec_comp (π : Y ⟶ Spec (.of R))
    (J : (Spec (.of R)).IdealSheafData) (U : Y.affineOpens) :
    idealOfSpecSheaf (J.comap (U.2.fromSpec ≫ π)) = (J.comap π).ideal U := by
  rw [Scheme.IdealSheafData.comap_comp, idealOfSpecSheaf_comap_fromSpec]

/-- The canonical affine chart's base morphism is induced by the actual original section map. -/
theorem fromSpec_comp_eq_specMap_sectionsHom (π : Y ⟶ Spec (.of R)) (U : Y.affineOpens) :
    U.2.fromSpec ≫ π = Spec.map (CommRingCat.ofHom (sectionsHom π U.1)) := by
  have hU : IsAffineOpen U.1 := U.2
  change hU.fromSpec ≫ π = _
  apply (cancel_epi hU.isoSpec.hom).mp
  rw [← Category.assoc, hU.isoSpec_hom_fromSpec]
  exact (isoSpec_hom_specMap_sectionsHom π U).symm

/-- The native affine monomial identity gives exactly the normalized actual transform input of
the boundary-open construction. -/
theorem idealOfSpecSheaf_comap_specMap_sectionsHom (π : Y ⟶ Spec (.of R))
    (J : (Spec (.of R)).IdealSheafData) (U : Y.affineOpens) :
    idealOfSpecSheaf (J.comap (Spec.map (CommRingCat.ofHom (sectionsHom π U.1)))) =
      (J.comap π).ideal U := by
  rw [← fromSpec_comp_eq_specMap_sectionsHom, idealOfSpecSheaf_comap_fromSpec_comp]

/-- The native affine SNC identity directly produces étaleness of the actual boundary
complement over the original affine base, with no separate projection/ideal certificates. -/
theorem etale_native_boundary_of_monomial_transform (π : Y ⟶ Spec (.of R))
    (J : (Spec (.of R)).IdealSheafData) [IsIso (π ∣_ J.support.compl)] (U : Y.affineOpens)
    {ι : Type*} [Fintype ι] (p : ι → Γ(Y, U.1)) (e : ι → ℕ)
    (hJ : (J.comap π).ideal U = Ideal.span {∏ i, p i ^ e i}) :
    letI : Algebra R Γ(Y, U.1) := (sectionsHom π U.1).toAlgebra
    (algebraMap R (Localization.Away (∏ i, p i))).Etale := by
  let _ : Algebra R Γ(Y, U.1) := (sectionsHom π U.1).toAlgebra
  have hU : IsAffineOpen U.1 := U.2
  have hnorm : idealOfSpecSheaf
      (J.comap (Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y, U.1))))) =
        Ideal.span {∏ i, p i ^ e i} := by
    change idealOfSpecSheaf (J.comap (Spec.map (CommRingCat.ofHom (sectionsHom π U.1)))) = _
    rw [idealOfSpecSheaf_comap_specMap_sectionsHom, hJ]
  exact etale_algebraMap_boundary_of_monomial_transform
    (S := Localization.Away (∏ i, p i)) π hU.fromSpec
      (fromSpec_comp_eq_specMap_sectionsHom π U) J p e hnorm

end EnvelopeProperty.Char0
