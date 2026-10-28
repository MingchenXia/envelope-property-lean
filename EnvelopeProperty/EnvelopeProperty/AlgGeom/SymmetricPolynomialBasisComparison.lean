import EnvelopeProperty.AlgGeom.SymmetricProjectiveEmbedding
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-! # Whole projective-bundle comparison from an actual original basis -/

open CategoryTheory AlgebraicGeometry MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.SymmetricPolynomialBasisComparison

variable {R M : Type u} {ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
  (b : Module.Basis ι R M)
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem toPolynomial_mem {d : ℕ} {x : SymmetricAlgebra R M}
    (hx : x ∈ SymmetricAlgebra.grading R M d) :
    SymmetricAlgebra.equivMvPolynomial b x ∈ homogeneousSubmodule ι R d := by
  have h1 : (LinearMap.range (SymmetricAlgebra.ι R M)).map
      (SymmetricAlgebra.equivMvPolynomial b).toLinearMap ≤ homogeneousSubmodule ι R 1 := by
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    have hm : m ∈ Submodule.span R (Set.range b) := b.span_eq ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨i, rfl⟩ := hm
      change SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι R M (b i)) ∈ _
      rw [SymmetricAlgebra.equivMvPolynomial_ι_apply]
      exact isHomogeneous_X R i
    | zero => simp only [map_zero]; exact zero_mem _
    | add m n _ _ hm hn => rw [map_add, map_add]; exact add_mem hm hn
    | smul r m _ hm => rw [map_smul, map_smul]; exact Submodule.smul_mem _ r hm
  have hd : (SymmetricAlgebra.grading R M d).map
      (SymmetricAlgebra.equivMvPolynomial b).toLinearMap ≤ homogeneousSubmodule ι R d := by
    change ((LinearMap.range (SymmetricAlgebra.ι R M)) ^ d).map
      (SymmetricAlgebra.equivMvPolynomial b).toAlgHom.toLinearMap ≤ _
    rw [Submodule.map_pow, ← homogeneousSubmodule_one_pow R d]
    exact pow_le_pow_left' h1 d
  exact hd ⟨x, hx, rfl⟩

/-- The original algebra basis isomorphism preserves ALL original homogeneous degrees. -/
def toPolynomial : SymmetricAlgebra.grading R M →+*ᵍ homogeneousSubmodule ι R where
  __ := (SymmetricAlgebra.equivMvPolynomial b).toRingHom
  map_mem := toPolynomial_mem b

/-- The actual inverse is the original whole polynomial presentation. -/
def toSymmetric : homogeneousSubmodule ι R →+*ᵍ SymmetricAlgebra.grading R M :=
  SymmetricProjectiveEmbedding.gradedPolynomialMap b

private theorem forward_surjective : Function.Surjective (toPolynomial b) :=
  (SymmetricAlgebra.equivMvPolynomial b).surjective

private theorem backward_surjective : Function.Surjective (toSymmetric b) :=
  SymmetricProjectiveEmbedding.gradedPolynomialMap_surjective b b.span_eq

private theorem backward_apply (x : MvPolynomial ι R) :
    toSymmetric b x = (SymmetricAlgebra.equivMvPolynomial b).symm x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Genuine whole original native schemes are isomorphic, with both actual inverse maps. -/
def iso : Proj (homogeneousSubmodule ι R) ≅ affineProjectiveBundle R M where
  hom := Proj.map (toPolynomial b)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (forward_surjective b))
  inv := Proj.map (toSymmetric b)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (backward_surjective b))
  hom_inv_id := by
    rw [← Proj.map_comp]
    have h : (toPolynomial b).comp (toSymmetric b) =
        GradedRingHom.id (homogeneousSubmodule ι R) := by
      apply DFunLike.ext
      intro x
      exact (SymmetricAlgebra.equivMvPolynomial b).apply_symm_apply x
    simpa only [h] using (Proj.map_id (𝒜 := homogeneousSubmodule ι R))
  inv_hom_id := by
    rw [← Proj.map_comp]
    have h : (toSymmetric b).comp (toPolynomial b) =
        GradedRingHom.id (SymmetricAlgebra.grading R M) := by
      apply DFunLike.ext
      intro x
      exact (SymmetricAlgebra.equivMvPolynomial b).symm_apply_apply x
    simpa only [h] using (Proj.map_id (𝒜 := SymmetricAlgebra.grading R M))

set_option backward.isDefEq.respectTransparency false in
/-- The entire original coefficient projection is retained by the genuine basis isomorphism. -/
theorem iso_structure {n : ℕ} (b : Module.Basis (Fin (n + 1)) R M) :
    (iso b).hom ≫ affineProjectiveBundle.π R M = homogeneousProjπ := by
  apply (cancel_epi (iso b).inv).mp
  rw [Iso.inv_hom_id_assoc]
  exact (SymmetricProjectiveEmbedding.embedding_structure b b.span_eq).symm

end EnvelopeProperty.SymmetricPolynomialBasisComparison
