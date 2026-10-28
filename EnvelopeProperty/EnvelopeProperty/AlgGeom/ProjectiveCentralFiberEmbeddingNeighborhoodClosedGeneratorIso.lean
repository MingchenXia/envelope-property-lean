import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorCoefficients

/-! # Actual whole line isomorphisms preserve the same original generator map -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorIso
open GeneratedLineProjectiveMap GeneratedLineProjectiveAffineMap GeneratedLineLocalCoefficients
open GeneratedLineFramedAffineCover SchemeGeneratedLineCoefficients SchemeLineSectionEvaluation

/-- Literal equality of the original index and all actual generator Homs
identifies the WHOLE original generating family, not just its cardinality. -/
theorem generatingSections_eq_of_generatorHom {X : Scheme.{u}} {L : X.Modules}
    (G H : L.GeneratingSections) (hI : G.I = H.I)
    (h : ∀ i : G.I, SchemeGeneratingSectionsUnit.generatorHom G i =
      SchemeGeneratingSectionsUnit.generatorHom H (hI ▸ i)) : G = H := by
  cases G with
  | mk I s hG =>
    cases H with
    | mk J t hH =>
      dsimp only at hI
      cases hI
      have hπ : L.freeHomEquiv.symm s = L.freeHomEquiv.symm t := by
        apply Sigma.hom_ext
        intro i
        exact h i
      have hst : s = t := L.freeHomEquiv.symm.injective hπ
      cases hst
      rfl

private instance isoHomEpi {X : Scheme.{u}} {L M : X.Modules} (E : L ≅ M) :
    Epi E.hom where
  left_cancellation g h heq := by
    simpa only [← Category.assoc, E.inv_hom_id, Category.id_comp] using
      congrArg (fun a => E.inv ≫ a) heq

private abbrev isoImageFamily {X : Scheme.{u}} {L M : X.Modules}
    (G : L.GeneratingSections) (E : L ≅ M) : M.GeneratingSections := by
  exact @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _ G E.hom
    (isoHomEpi (X := X) E)

private instance ofEpiIndexFintype {X : Scheme.{u}} {L M : X.Modules}
    (G : L.GeneratingSections) [Fintype G.I] (E : L ≅ M) :
    Fintype (isoImageFamily G E).I := (inferInstance : Fintype G.I)

private theorem localCoefficient_ofEpi_iso {X : Scheme.{u}} {L M : X.Modules}
    (G : L.GeneratingSections) (E : L ≅ M) (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ unitObj U.toScheme) (i : G.I) :
    localCoefficient (isoImageFamily G E) U
        (((Scheme.Modules.pullback U.ι).mapIso E).symm ≪≫ e) i =
      localCoefficient G U e i := by
  let : Epi E.hom := isoHomEpi (X := X) E
  let eM := ((Scheme.Modules.pullback U.ι).mapIso E).symm ≪≫ e
  have hs : pullbackSectionHom U.ι
      (SchemeGeneratingSectionsUnit.generatorHom (isoImageFamily G E) i) ≫ eM.hom =
      pullbackSectionHom U.ι (SchemeGeneratingSectionsUnit.generatorHom G i) ≫ e.hom := by
    rw [SchemeGeneratingSectionsUnit.generatorHom_ofEpi]
    change ((pullbackUnitIso U.ι).inv ≫
        (Scheme.Modules.pullback U.ι).map
          (SchemeGeneratingSectionsUnit.generatorHom G i ≫ E.hom)) ≫
        (((Scheme.Modules.pullback U.ι).mapIso E).inv ≫ e.hom) =
      ((pullbackUnitIso U.ι).inv ≫ (Scheme.Modules.pullback U.ι).map
        (SchemeGeneratingSectionsUnit.generatorHom G i)) ≫ e.hom
    rw [Functor.map_comp]
    change ((pullbackUnitIso U.ι).inv ≫
        ((Scheme.Modules.pullback U.ι).map (SchemeGeneratingSectionsUnit.generatorHom G i) ≫
          ((Scheme.Modules.pullback U.ι).mapIso E).hom)) ≫
        (((Scheme.Modules.pullback U.ι).mapIso E).inv ≫ e.hom) = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hl := localCoefficient_scalar (isoImageFamily G E) U eM i
  have hr := localCoefficient_scalar G U e i
  have hv := congrArg sectionAtOne (hl.symm.trans (hs.trans hr))
  exact (topSectionHom_app_top_apply_one _ _).symm.trans
    (hv.trans (topSectionHom_app_top_apply_one _ _))

/-- A WHOLE actual line isomorphism retains the entire generated map of the
SAME original finite generator family, including its exact index and padding. -/
theorem projectiveMap_of_iso {R : Type u} [CommRing R] {X : Scheme.{u}}
    {L M : X.Modules} (p : X ⟶ Spec (CommRingCat.of R))
    (hL : IsInvertible L) (hM : IsInvertible M)
    (G : L.GeneratingSections) [Fintype G.I] (E : L ≅ M) :
    projectiveMap p hM (isoImageFamily G E) = projectiveMap p hL G := by
  let H := isoImageFamily G E
  let : Fintype H.I := (inferInstance : Fintype G.I)
  apply (framedCover L hL).hom_ext
  intro V
  let : IsAffine V.1.1.toScheme := V.1.2
  let eM := ((Scheme.Modules.pullback V.1.1.ι).mapIso E).symm ≪≫ frame L V
  change V.1.1.ι ≫ projectiveMap p hM H = V.1.1.ι ≫ projectiveMap p hL G
  have hl := projectiveMap_on_frame p hM H V.1 eM
  have hr := projectiveMap_on_frame p hL G V.1 (frame L V)
  have hc : paddedCoefficients (localCoefficient H V.1.1 eM) =
      paddedCoefficients (localCoefficient G V.1.1 (frame L V)) :=
    congrArg paddedCoefficients (funext (localCoefficient_ofEpi_iso G E V.1.1 (frame L V)))
  have hlocal : localMap p H V.1 eM = localMap p G V.1 (frame L V) := by
    change V.1.1.toScheme.isoSpec.hom ≫
        DeJongAlterations.Geometry.FiniteProjective.affineTupleMap
          (baseCoefficients (V.1.1.ι ≫ p))
          (paddedCoefficients (localCoefficient H V.1.1 eM)) _ =
      V.1.1.toScheme.isoSpec.hom ≫
        DeJongAlterations.Geometry.FiniteProjective.affineTupleMap
          (baseCoefficients (V.1.1.ι ≫ p))
          (paddedCoefficients (localCoefficient G V.1.1 (frame L V))) _
    exact congrArg (fun a => V.1.1.toScheme.isoSpec.hom ≫ a)
      (DeJongAlterations.Geometry.FiniteProjective.affineTupleMap_congr rfl hc _ _)
  exact hl.trans (hlocal.trans hr.symm)

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorIso
