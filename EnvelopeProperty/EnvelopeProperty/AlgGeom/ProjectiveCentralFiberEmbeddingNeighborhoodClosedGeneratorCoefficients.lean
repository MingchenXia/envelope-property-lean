import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedPartial

/-! # The same lifted-generator map over the original coefficient ring -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorCoefficients
open GeneratedLineProjectiveMap GeneratedLineProjectiveAffineMap SchemeGeneratedLineCoefficients
open DeJongAlterations.Geometry.FiniteProjective DeJongAlterations.Geometry.BlowupProjectiveEmbedding

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

/-- The actual whole native tuple retains every coordinate under the original
coefficient-base composition. -/
theorem affineTupleMap_comp_coefficient (r : R →+* A) (s : A →+* B)
    {m : ℕ} (a : Fin (m + 1) → B) (ha : Ideal.span (Set.range a) = ⊤) :
    affineTupleMap s a ha ≫ projectiveCoefficientMap r m =
      affineTupleMap (s.comp r) a ha := by
  simp only [affineTupleMap, affineProjectiveMap, Category.assoc,
    projectiveCoefficientMap_comp]

private theorem baseCoefficients_specMap {X : Scheme.{u}}
    (r : R →+* A) (p : X ⟶ Spec (CommRingCat.of A)) :
    baseCoefficients (p ≫ Spec.map (CommRingCat.ofHom r)) = (baseCoefficients p).comp r := by
  apply RingHom.ext
  intro c
  simp only [baseCoefficients, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]
  have h := congrArg (fun a : CommRingCat.of R ⟶ Γ(Spec (CommRingCat.of A), ⊤) => a.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom r))
  exact congrArg p.appTop.hom h.symm

private theorem affineMap_comp_coefficient {X : Scheme.{u}} [IsAffine X]
    {L : X.Modules} (r : R →+* A) (p : X ⟶ Spec (CommRingCat.of A))
    (G : L.GeneratingSections) [Fintype G.I] (e : L ≅ Scheme.Modules.unitObj X) :
    affineMap p G e ≫ projectiveCoefficientMap r (Fintype.card G.I) =
      affineMap (p ≫ Spec.map (CommRingCat.ofHom r)) G e := by
  dsimp only [affineMap]
  rw [Category.assoc, affineTupleMap_comp_coefficient, baseCoefficients_specMap]

/-- The WHOLE actual generated map over the original coefficient ring is
EXACTLY the SAME map followed by its actual projective coefficient morphism.
The finite original index and its padding are unchanged internally. -/
theorem projectiveMap_comp_coefficient {X : Scheme.{u}} {L : X.Modules}
    (r : R →+* A) (p : X ⟶ Spec (CommRingCat.of A)) (hL : Scheme.Modules.IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] :
    projectiveMap p hL G ≫ projectiveCoefficientMap r (Fintype.card G.I) =
      projectiveMap (p ≫ Spec.map (CommRingCat.ofHom r)) hL G := by
  apply (GeneratedLineFramedAffineCover.framedCover L hL).hom_ext
  intro V
  let : IsAffine V.1.1.toScheme := V.1.2
  let : Fintype (ClosedProjectiveGlobalGeneration.pullback_generatingSections V.1.1.ι G).I :=
    (inferInstance : Fintype G.I)
  change V.1.1.ι ≫ (projectiveMap p hL G ≫ projectiveCoefficientMap r _) =
    V.1.1.ι ≫ projectiveMap (p ≫ Spec.map (CommRingCat.ofHom r)) hL G
  have hlocal : chartMap p G V ≫ projectiveCoefficientMap r (Fintype.card G.I) =
      chartMap (p ≫ Spec.map (CommRingCat.ofHom r)) G V := by
    change affineMap (V.1.1.ι ≫ p)
        (ClosedProjectiveGlobalGeneration.pullback_generatingSections V.1.1.ι G)
        (GeneratedLineFramedAffineCover.frame L V) ≫ projectiveCoefficientMap r _ =
      affineMap (V.1.1.ι ≫ (p ≫ Spec.map (CommRingCat.ofHom r)))
        (ClosedProjectiveGlobalGeneration.pullback_generatingSections V.1.1.ι G)
        (GeneratedLineFramedAffineCover.frame L V)
    simpa only [Category.assoc] using affineMap_comp_coefficient r (V.1.1.ι ≫ p)
      (ClosedProjectiveGlobalGeneration.pullback_generatingSections V.1.1.ι G)
      (GeneratedLineFramedAffineCover.frame L V)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ projectiveCoefficientMap r (Fintype.card G.I))
      (projectiveMap_restrict p hL G V)).trans
        (hlocal.trans (projectiveMap_restrict
          (p ≫ Spec.map (CommRingCat.ofHom r)) hL G V).symm))

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorCoefficients
