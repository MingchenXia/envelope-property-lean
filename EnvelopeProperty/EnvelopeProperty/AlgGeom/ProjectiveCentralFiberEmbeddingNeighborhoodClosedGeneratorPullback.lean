import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedPartial

/-! # The same actual generated projective map retains affine source pullback -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorPullback
open GeneratedLineProjectiveMap GeneratedLineProjectiveAffineMap GeneratedLineLocalCoefficients
open GeneratedLineFramedAffineCover SchemeGeneratedLineCoefficients SchemeLineSectionEvaluation
open DeJongAlterations.Geometry.FiniteProjective

/-- Every SAME original generator coefficient is derived through the actual
source pullback and its canonical original pulled local frame. -/
theorem localCoefficient_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    {L : X.Modules} (G : L.GeneratingSections) (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ unitObj U.toScheme) (i : G.I) :
    localCoefficient (ClosedProjectiveGlobalGeneration.pullback_generatingSections g G)
        (g ⁻¹ᵁ U) (localPullbackFrame g U e) i =
      (g ∣_ U).appTop.hom (localCoefficient G U e i) := by
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections g G
  let V := g ⁻¹ᵁ U
  let E := localPullbackFrame g U e
  have hs : pullbackSectionHom V.ι
      (pullbackSectionHom g (SchemeGeneratingSectionsUnit.generatorHom G i)) ≫ E.hom =
      ModularCurves.unitEndomorphismOfTopSection
        ((g ∣_ U).appTop.hom (localCoefficient G U e i)) := by
    dsimp only [E, localPullbackFrame, Iso.trans_hom, Iso.app_hom]
    rw [← Category.assoc, pullbackSectionHom_comp,
      frameViaFactor_sectionHom_scalar (g ∣_ U) U.ι (V.ι ≫ g)
        (morphismRestrict_ι g U) e (SchemeGeneratingSectionsUnit.generatorHom G i)
        (localCoefficient G U e i) (localCoefficient_scalar G U e i)]
  have hl := localCoefficient_scalar H V E i
  have hgen : SchemeGeneratingSectionsUnit.generatorHom H i =
      pullbackSectionHom g (SchemeGeneratingSectionsUnit.generatorHom G i) :=
    SchemeGeneratingSectionsUnit.generatorHom_pullback g G i
  rw [hgen] at hl
  have hv := congrArg sectionAtOne (hl.symm.trans hs)
  exact (topSectionHom_app_top_apply_one _ _).symm.trans
    (hv.trans (topSectionHom_app_top_apply_one _ _))

private instance pullbackIndexFintype {X Y : Scheme.{u}} (g : Y ⟶ X)
    {L : X.Modules} (G : L.GeneratingSections) [Fintype G.I] :
    Fintype (ClosedProjectiveGlobalGeneration.pullback_generatingSections g G).I :=
  (inferInstance : Fintype G.I)

private theorem localMap_pullback {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (g : Y ⟶ X) [IsAffineHom g] {L : X.Modules}
    (p : X ⟶ Spec (CommRingCat.of R)) (G : L.GeneratingSections) [Fintype G.I]
    (U : X.AffineZariskiSite)
    (e : (Scheme.Modules.pullback U.1.ι).obj L ≅ unitObj U.1.toScheme) :
    (g ∣_ U.1) ≫ localMap p G U e =
      localMap (g ≫ p) (ClosedProjectiveGlobalGeneration.pullback_generatingSections g G)
        ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩ (localPullbackFrame g U.1 e) := by
  let V : Y.AffineZariskiSite := ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine V.1.toScheme := V.2
  let f := g ∣_ U.1
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections g G
  let E := localPullbackFrame g U.1 e
  let a := paddedCoefficients (localCoefficient G U.1 e)
  let b := paddedCoefficients (localCoefficient H V.1 E)
  let ha : Ideal.span (Set.range a) = ⊤ := span_paddedCoefficients_eq_top _
    (span_coefficients_eq_top (ClosedProjectiveGlobalGeneration.pullback_generatingSections U.1.ι G) e)
  let hb : Ideal.span (Set.range b) = ⊤ := span_paddedCoefficients_eq_top _
    (span_coefficients_eq_top (ClosedProjectiveGlobalGeneration.pullback_generatingSections V.1.ι H) E)
  have hc : b = fun j => f.appTop.hom (a j) :=
    (congrArg paddedCoefficients (funext (localCoefficient_pullback g G U.1 e))).trans
      (paddedCoefficients_map (localCoefficient G U.1 e) f.appTop.hom)
  have hb' : Ideal.span (Set.range (fun j => f.appTop.hom (a j))) = ⊤ := by
    rw [← hc]
    exact hb
  have hn := affineTupleMap_naturality (baseCoefficients (U.1.ι ≫ p)) a ha f.appTop.hom hb'
  rw [CommRingCat.ofHom_hom] at hn
  have ho : f ≫ (U.1.ι ≫ p) = V.1.ι ≫ (g ≫ p) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ p) (morphismRestrict_ι g U.1)).trans
        (Category.assoc _ _ _))
  have hr : f.appTop.hom.comp (baseCoefficients (U.1.ι ≫ p)) =
      baseCoefficients (V.1.ι ≫ (g ≫ p)) :=
    (baseCoefficients_naturality f (U.1.ι ≫ p)).symm.trans (congrArg baseCoefficients ho)
  change f ≫ (U.1.toScheme.isoSpec.hom ≫
      affineTupleMap (baseCoefficients (U.1.ι ≫ p)) a ha) =
    V.1.toScheme.isoSpec.hom ≫ affineTupleMap (baseCoefficients (V.1.ι ≫ (g ≫ p))) b hb
  have hiso := Scheme.isoSpec_hom_naturality f
  have htuple := affineTupleMap_congr hr hc.symm hb' hb
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun morph => morph ≫ affineTupleMap (baseCoefficients (U.1.ι ≫ p)) a ha)
      hiso.symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun q => V.1.toScheme.isoSpec.hom ≫ q) hn).trans
            (congrArg (fun q => V.1.toScheme.isoSpec.hom ≫ q) htuple))))

/-- Every actual affine source morphism preserves the ENTIRE original
projective map of the SAME finite generators, original index and padding. -/
theorem projectiveMap_pullback {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (g : Y ⟶ X) [IsAffineHom g] {L : X.Modules}
    (p : X ⟶ Spec (CommRingCat.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] :
    g ≫ projectiveMap p hL G =
      projectiveMap (g ≫ p) (hL.pullback g)
        (ClosedProjectiveGlobalGeneration.pullback_generatingSections g G) := by
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections g G
  let C : Y.OpenCover := Scheme.Cover.mkOfCovers (FramedAffineSite L)
    (fun V => (g ⁻¹ᵁ V.1.1).toScheme) (fun V => (g ⁻¹ᵁ V.1.1).ι) (by
      intro y
      obtain ⟨U, hy, e⟩ := exists_framed_affine L hL (g y)
      exact ⟨⟨U, e⟩, ⟨y, hy⟩, rfl⟩)
  apply C.hom_ext
  intro V
  let W : Y.AffineZariskiSite := ⟨g ⁻¹ᵁ V.1.1, V.1.2.preimage g⟩
  let E := localPullbackFrame g V.1.1 (frame L V)
  change W.1.ι ≫ (g ≫ projectiveMap p hL G) =
    W.1.ι ≫ projectiveMap (g ≫ p) (hL.pullback g) H
  have ht := projectiveMap_on_frame p hL G V.1 (frame L V)
  have hs := projectiveMap_on_frame (g ≫ p) (hL.pullback g) H W E
  have hl := localMap_pullback g p G V.1 (frame L V)
  exact (Category.assoc _ _ _).symm.trans
    (((congrArg (fun a => a ≫ projectiveMap p hL G)
      (morphismRestrict_ι g V.1.1)).symm.trans (Category.assoc _ _ _)).trans
        ((congrArg (fun a => (g ∣_ V.1.1) ≫ a) ht).trans (hl.trans hs.symm)))

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorPullback
