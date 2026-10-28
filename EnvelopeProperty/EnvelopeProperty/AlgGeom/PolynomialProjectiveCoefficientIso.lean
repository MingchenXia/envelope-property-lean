import EnvelopeProperty.AlgGeom.SymmetricProjectiveEmbedding
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Whole original polynomial projective schemes under actual coefficient isomorphisms -/

open CategoryTheory AlgebraicGeometry MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.PolynomialProjectiveCoefficientIso
variable {R S : Type u} [CommRing R] [CommRing S] {ι : Type} (e : R ≃+* S)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual original coefficient map preserves EVERY original polynomial degree. -/
def gradedMap : homogeneousSubmodule ι R →+*ᵍ homogeneousSubmodule ι S where
  __ := MvPolynomial.map e.toRingHom
  map_mem := fun h => h.map e.toRingHom

private theorem map_surjective : Function.Surjective (gradedMap (ι := ι) e) :=
  (MvPolynomial.mapEquiv ι e).surjective

set_option backward.isDefEq.respectTransparency false in
/-- The genuine coefficient isomorphism gives both entire original native scheme inverse maps. -/
def iso : Proj (homogeneousSubmodule ι S) ≅ Proj (homogeneousSubmodule ι R) where
  hom := Proj.map (gradedMap e)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (map_surjective e))
  inv := Proj.map (gradedMap e.symm)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (map_surjective e.symm))
  hom_inv_id := by
    rw [← Proj.map_comp]
    have h : (gradedMap (ι := ι) e).comp (gradedMap e.symm) =
        GradedRingHom.id (homogeneousSubmodule ι S) := by
      apply DFunLike.ext
      intro x
      exact (MvPolynomial.mapEquiv ι e).apply_symm_apply x
    simpa only [h] using (Proj.map_id (𝒜 := homogeneousSubmodule ι S))
  inv_hom_id := by
    rw [← Proj.map_comp]
    have h : (gradedMap (ι := ι) e.symm).comp (gradedMap e) =
        GradedRingHom.id (homogeneousSubmodule ι R) := by
      apply DFunLike.ext
      intro x
      exact (MvPolynomial.mapEquiv ι e).symm_apply_apply x
    simpa only [h] using (Proj.map_id (𝒜 := homogeneousSubmodule ι R))

private theorem degreeZero_coefficient :
    CommRingCat.ofHom (algebraMap R (homogeneousSubmodule ι R 0)) ≫
        CommRingCat.ofHom (ModularCurves.gradedRingHomZero (gradedMap (ι := ι) e)) =
      CommRingCat.ofHom e.toRingHom ≫
        CommRingCat.ofHom (algebraMap S (homogeneousSubmodule ι S 0)) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply Subtype.ext
  exact MvPolynomial.map_C e.toRingHom r

set_option backward.isDefEq.respectTransparency false in
/-- The entire original coefficient structural diagram commutes exactly. -/
theorem iso_structure :
    (iso (ι := ι) e).hom ≫ homogeneousProjπ =
      homogeneousProjπ ≫ Spec.map (CommRingCat.ofHom e.toRingHom) := by
  unfold iso homogeneousProjπ
  rw [← Category.assoc, ModularCurves.map_comp_toSpecZero, Category.assoc,
    ← Spec.map_comp, degreeZero_coefficient, Spec.map_comp, Category.assoc]

end EnvelopeProperty.PolynomialProjectiveCoefficientIso
