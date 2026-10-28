/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CommonProperModelGraph
import EnvelopeProperty.AlgGeom.ProjectiveBlowupSequence
import DeJongAlterations.Geometry.Segre
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Genuine finite projectivity of the SAME product and SAME common model

Actual closed polynomial embeddings of the two original models are combined
by their actual product morphism and the existing genuine native Segre map.
The original coefficient ring and structural morphism are retained exactly.
No projectivity or embedding certificate for the product/common model is given.

Blueprint: `projective-factorization-products.tex`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

namespace EnvelopeProperty.ProjectiveFactorizationProducts

universe u

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual product of two original finite projective factorizations has
an internally constructed finite projective factorization over the SAME ring. -/
theorem pullback (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))
    (hf : IsProjectiveFactorization f) (hg : IsProjectiveFactorization g) :
    IsProjectiveFactorization (Limits.pullback.fst f g ≫ f) := by
  obtain ⟨m, i, hi, hif⟩ := (ProjectiveBlowupSequence.isProjectiveOver_iff f).mpr hf
  obtain ⟨n, j, hj, hjg⟩ := (ProjectiveBlowupSequence.isProjectiveOver_iff g).mpr hg
  let δ : Limits.pullback f g ⟶ DeJongAlterations.Geometry.Segre.projectiveProduct R m n :=
    Limits.pullback.map f g (DeJongAlterations.projectiveSpaceStructure R m)
      (DeJongAlterations.projectiveSpaceStructure R n) i j (𝟙 _)
      ((Category.comp_id f).trans hif.symm) ((Category.comp_id g).trans hjg.symm)
  have hδ : IsClosedImmersion δ :=
    MorphismProperty.pullbackMap (C := Scheme.{u}) (P := @IsClosedImmersion) hi hj hif.symm hjg.symm
  let : IsClosedImmersion δ := hδ
  apply (ProjectiveBlowupSequence.isProjectiveOver_iff _).mp
  refine ⟨DeJongAlterations.Algebra.Segre.dimension m n,
    δ ≫ DeJongAlterations.Geometry.Segre.segre R m n, inferInstance, ?_⟩
  rw [Category.assoc, DeJongAlterations.Geometry.Segre.segre_structure, ← Category.assoc]
  have hfst : δ ≫ Limits.pullback.fst (DeJongAlterations.projectiveSpaceStructure R m)
      (DeJongAlterations.projectiveSpaceStructure R n) = Limits.pullback.fst f g ≫ i :=
    by simp only [δ, Limits.pullback.map, Limits.pullback.lift_fst]
  rw [hfst, Category.assoc, hif]

end ProjectiveFactorizationProducts

namespace CommonProperModelGraph

universe u

/-- The SAME actual common graph has true finite projectivity over the original ring,
derived from the two original projective factorizations and actual closed graph embedding. -/
theorem model_isProjectiveFactorization {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))
    (e : X.PartialIso Y) (he : e.IsOver f g)
    (hf : IsProjectiveFactorization f) (hg : IsProjectiveFactorization g) :
    IsProjectiveFactorization (firstProjection f g e he ≫ f) := by
  have h := (ProjectiveFactorizationProducts.pullback f g hf hg).comp_isClosedImmersion
    (embedding f g e he) (embedding_isClosedImmersion f g e he)
  simpa only [firstProjection, Category.assoc] using h

end CommonProperModelGraph
end EnvelopeProperty
