/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.PartialIsoFullRestriction
import EnvelopeProperty.AlgGeom.SchemeDominantImageFactorization
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual common proper models from the prescribed whole birational graph

The SAME scheme-theoretic graph image gives both actual proper maps and both
full-open isomorphisms. No refinement or modification certificate is assumed.
The input partial isomorphism is the original common-open model data.
Equivariance, projectivity, and normalization are subsequent obligations.

Blueprint: `common-proper-model-graph.tex`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace EnvelopeProperty.CommonProperModelGraph

universe u

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (e : X.PartialIso Y) (he : e.IsOver f g)

/-- The actual graph on the prescribed original common open. -/
def graph : e.source.toScheme ⟶ pullback f g :=
  pullback.lift e.source.ι (e.iso.hom ≫ e.target.ι)
    (by simpa only [Category.assoc] using (Eq.symm he))

@[reassoc (attr := simp)]
theorem graph_fst : graph f g e he ≫ pullback.fst _ _ = e.source.ι := by
  unfold graph
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graph_snd : graph f g e he ≫ pullback.snd _ _ = e.iso.hom ≫ e.target.ι := by
  unfold graph
  exact pullback.lift_snd _ _ _

private local instance graphImmersion [IsSeparated g] : IsImmersion (graph f g e he) := by
  have : IsImmersion (graph f g e he ≫ pullback.fst _ _) := by
    rw [graph_fst]
    infer_instance
  exact IsImmersion.of_comp _ (pullback.fst _ _)

private local instance graphQuasiCompact [IsSeparated g] [QuasiCompact e.source.ι] :
    QuasiCompact (graph f g e he) := by
  have : QuasiCompact (graph f g e he ≫ pullback.fst _ _) := by
    rw [graph_fst]
    infer_instance
  exact QuasiCompact.of_comp _ (pullback.fst _ _)

/-- The SAME actual kernel-image closed subscheme of the product. -/
def model : Scheme.{u} := (graph f g e he).image

/-- The canonical factor of the ORIGINAL common-open graph. -/
def inclusion : e.source.toScheme ⟶ model f g e he := (graph f g e he).toImage

/-- The actual original closed graph embedding. -/
def embedding : model f g e he ⟶ pullback f g := (graph f g e he).imageι

/-- The actual first comparison map to the entire original model. -/
def firstProjection : model f g e he ⟶ X := embedding f g e he ≫ pullback.fst _ _

/-- The actual second comparison map to the entire original model. -/
def secondProjection : model f g e he ⟶ Y := embedding f g e he ≫ pullback.snd _ _

set_option backward.isDefEq.respectTransparency false in
theorem embedding_isClosedImmersion : IsClosedImmersion (embedding f g e he) := by
  dsimp only [embedding]
  infer_instance

private local instance embeddingClosed : IsClosedImmersion (embedding f g e he) :=
  embedding_isClosedImmersion f g e he

set_option backward.isDefEq.respectTransparency false in
/-- The actual common open is a genuine open subscheme of the common model. -/
theorem inclusion_isOpenImmersion [IsSeparated g] [QuasiCompact e.source.ι] :
    IsOpenImmersion (inclusion f g e he) := by
  let : IsImmersion (graph f g e he) := graphImmersion f g e he
  let : QuasiCompact (graph f g e he) := graphQuasiCompact f g e he
  dsimp only [inclusion]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The ORIGINAL common-open map is dense in the actual common model. -/
theorem inclusion_isDominant [IsSeparated g] [QuasiCompact e.source.ι] :
    IsDominant (inclusion f g e he) := by
  let : QuasiCompact (graph f g e he) := graphQuasiCompact f g e he
  dsimp only [inclusion]
  infer_instance

@[reassoc (attr := simp)]
theorem inclusion_embedding : inclusion f g e he ≫ embedding f g e he = graph f g e he :=
  (graph f g e he).toImage_imageι

@[reassoc (attr := simp)]
theorem inclusion_firstProjection : inclusion f g e he ≫ firstProjection f g e he = e.source.ι := by
  rw [firstProjection, inclusion_embedding_assoc, graph_fst]

@[reassoc (attr := simp)]
theorem inclusion_secondProjection : inclusion f g e he ≫ secondProjection f g e he =
    e.iso.hom ≫ e.target.ι := by
  rw [secondProjection, inclusion_embedding_assoc, graph_snd]

/-- The whole original structural triangle, with the same original maps. -/
theorem structure_triangle : firstProjection f g e he ≫ f = secondProjection f g e he ≫ g := by
  rw [firstProjection, secondProjection, Category.assoc, Category.assoc, pullback.condition]

/-- Properness of the second original model derives properness of the FIRST comparison. -/
theorem firstProjection_isProper [IsProper g] :
    IsProper (firstProjection f g e he) := by
  dsimp only [firstProjection]
  infer_instance

/-- Properness of the first original model derives properness of the SECOND comparison. -/
theorem secondProjection_isProper [IsProper f] :
    IsProper (secondProjection f g e he) := by
  dsimp only [secondProjection]
  infer_instance

/-- Integrality of the actual common graph is derived from the original integral model. -/
theorem model_isIntegral [IsIntegral X] [IsSeparated g] [QuasiCompact e.source.ι] :
    IsIntegral (model f g e he) := by
  let : Nonempty e.source := e.dense_source.nonempty.to_subtype
  exact SchemeDominantImageFactorization.image_isIntegral (graph f g e he)

end EnvelopeProperty.CommonProperModelGraph
