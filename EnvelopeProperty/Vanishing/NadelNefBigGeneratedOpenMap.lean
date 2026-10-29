import EnvelopeProperty.Vanishing.NadelNefBigOpenMapFrames
import EnvelopeProperty.AlgGeom.GeneratedLineProjectiveMap
import EnvelopeProperty.AlgGeom.SchemeLineSectionFactorization
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelNefBigGeneratedOpenMap
open NadelNefBigOpenMapFrames GeneratedLineProjectiveMap GeneratedLineProjectiveAffineMap
open SchemeGeneratedLineCoefficients SchemeGeneratingSectionsUnit SchemeLineSectionEvaluation
open SchemeLineSectionFactorization

private theorem coefficient_top {X : Scheme.{u}} {M : X.Modules} (G : M.GeneratingSections)
    (e : M ≅ unitObj X) (i : G.I) :
    coefficient G e i = ((generatorHom G i ≫ e.hom).val.app (op ⊤)).hom (1 : Γ(X, ⊤)) :=
  coefficient_apply G e i

theorem projectiveMap_on_affine_openMap {R : Type u} [CommRing R] {T V : Scheme.{u}}
    [IsAffine T] (j : T ⟶ V) [IsOpenImmersion j] (p : V ⟶ Spec (.of R))
    (M : V.Modules) (hM : IsInvertible M) (G : M.GeneratingSections) [Fintype G.I]
    (e : (pullback j).obj M ≅ unitObj T) :
    j ≫ projectiveMap p hM G =
      affineMap (j ≫ p) (ClosedProjectiveGlobalGeneration.pullback_generatingSections j G) e := by
  let U : V.AffineZariskiSite := ⟨j.opensRange, isAffineOpen_opensRange j⟩
  let : IsAffine U.1.toScheme := U.2
  let r : T ⟶ U.1.toScheme := j.isoOpensRange.hom
  let GU := ClosedProjectiveGlobalGeneration.pullback_generatingSections U.1.ι G
  let GT := ClosedProjectiveGlobalGeneration.pullback_generatingSections r GU
  let GJ := ClosedProjectiveGlobalGeneration.pullback_generatingSections j G
  let : Fintype GU.I := (inferInstance : Fintype G.I)
  let : Fintype GT.I := (inferInstance : Fintype G.I)
  let : Fintype GJ.I := (inferInstance : Fintype G.I)
  let eU := frameOnImage j M e
  let En := (pullback r).mapIso eU ≪≫ pullbackUnitIso r
  have he : En = imageComparison j M ≪≫ e := frameOnImage_pullback j M e
  have hgen (i : G.I) : generatorHom GT i ≫ (imageComparison j M).hom = generatorHom GJ i := by
    have hr : generatorHom GT i = pullbackSectionHom r (generatorHom GU i) :=
      generatorHom_pullback r GU i
    have hu : generatorHom GU i = pullbackSectionHom U.1.ι (generatorHom G i) :=
      generatorHom_pullback U.1.ι G i
    have hj : generatorHom GJ i = pullbackSectionHom j (generatorHom G i) :=
      generatorHom_pullback j G i
    calc
      _ = pullbackSectionHom r (generatorHom GU i) ≫ (imageComparison j M).hom :=
        congrArg (fun a => a ≫ (imageComparison j M).hom) hr
      _ = pullbackSectionHom r (pullbackSectionHom U.1.ι (generatorHom G i)) ≫
          (imageComparison j M).hom :=
        congrArg (fun a => pullbackSectionHom r a ≫ (imageComparison j M).hom) hu
      _ = pullbackSectionHom j (generatorHom G i) :=
        pullbackSectionHom_factor r U.1.ι j j.isoOpensRange_hom_ι (generatorHom G i)
      _ = generatorHom GJ i := hj.symm
  have hc (i : G.I) : coefficient GT En i = coefficient GJ e i := by
    have hcomp : generatorHom GT i ≫ En.hom = generatorHom GJ i ≫ e.hom := by
      calc
        _ = generatorHom GT i ≫ (imageComparison j M ≪≫ e).hom :=
          congrArg (fun E => generatorHom GT i ≫ E.hom) he
        _ = (generatorHom GT i ≫ (imageComparison j M).hom) ≫ e.hom :=
          (Category.assoc _ _ _).symm
        _ = generatorHom GJ i ≫ e.hom := congrArg (fun a => a ≫ e.hom) (hgen i)
    exact (coefficient_top GT En i).trans
      ((congrArg (fun a : unitObj T ⟶ unitObj T =>
        (a.val.app (op ⊤)).hom (1 : Γ(T, ⊤))) hcomp).trans (coefficient_top GJ e i).symm)
  have hU := projectiveMap_on_frame p hM G U eU
  change U.1.ι ≫ projectiveMap p hM G = affineMap (U.1.ι ≫ p) GU eU at hU
  have hbase : r ≫ (U.1.ι ≫ p) = j ≫ p :=
    (Category.assoc r U.1.ι p).symm.trans (congrArg (fun a => a ≫ p) j.isoOpensRange_hom_ι)
  have hstart : j ≫ projectiveMap p hM G = r ≫ (U.1.ι ≫ projectiveMap p hM G) := by
    rw [← Category.assoc, j.isoOpensRange_hom_ι]
  have hsecond : r ≫ (U.1.ι ≫ projectiveMap p hM G) = r ≫ affineMap (U.1.ι ≫ p) GU eU :=
    congrArg (fun a => r ≫ a) hU
  have hthird : r ≫ affineMap (U.1.ι ≫ p) GU eU = affineMap (r ≫ (U.1.ι ≫ p)) GT En :=
    affineMap_naturality r (U.1.ι ≫ p) GU eU
  have hlast : affineMap (r ≫ (U.1.ι ≫ p)) GT En = affineMap (j ≫ p) GJ e := by
    change T.isoSpec.hom ≫ _ = T.isoSpec.hom ≫ _
    apply congrArg (fun a => T.isoSpec.hom ≫ a)
    exact Alterations.Geometry.FiniteProjective.affineTupleMap_congr
      (congrArg baseCoefficients hbase) (congrArg paddedCoefficients (funext hc)) _ _
  exact hstart.trans (hsecond.trans (hthird.trans hlast))
end EnvelopeProperty.Vanishing.NadelNefBigGeneratedOpenMap
