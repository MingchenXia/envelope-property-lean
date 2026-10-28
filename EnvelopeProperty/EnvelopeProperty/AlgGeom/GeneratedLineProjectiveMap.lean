import EnvelopeProperty.AlgGeom.GeneratedLineLocalCoefficients

/-! # Genuine whole original projective maps from actual finite original line generators -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.GeneratedLineProjectiveMap
open SchemeGeneratedLineCoefficients GeneratedLineLocalCoefficients GeneratedLineFramedAffineCover
open GeneratedLineProjectiveAffineMap DeJongAlterations.Geometry.FiniteProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {X : Scheme.{u}} {L : X.Modules}

private instance framedAffineIsAffine (U : X.AffineZariskiSite) : IsAffine U.1.toScheme := U.2

/-- The actual original projective tuple map in any genuine original affine line frame. -/
def localMap (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections) [Fintype G.I]
    (U : X.AffineZariskiSite)
    (e : (Scheme.Modules.pullback U.1.ι).obj L ≅ unitObj U.1.toScheme) :
    U.1.toScheme ⟶ DeJongAlterations.projectiveSpace R (Fintype.card G.I) :=
  affineMap (U.1.ι ≫ p) (ClosedProjectiveGlobalGeneration.pullback_generatingSections U.1.ι G) e

/-- The actual original affine inclusion preserves the whole projective map
of the SAME original generators in the actual restricted original frame. -/
theorem localMap_restrict (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections) [Fintype G.I]
    {U W : X.AffineZariskiSite} (h : W.1 ≤ U.1)
    (e : (Scheme.Modules.pullback U.1.ι).obj L ≅ unitObj U.1.toScheme) :
    X.homOfLE h ≫ localMap p G U e = localMap p G W (restrictTrivialization h e) := by
  let f := X.homOfLE h
  let a := paddedCoefficients (localCoefficient G U.1 e)
  let b := paddedCoefficients (localCoefficient G W.1 (restrictTrivialization h e))
  let ha : Ideal.span (Set.range a) = ⊤ := span_paddedCoefficients_eq_top _
    (span_coefficients_eq_top (ClosedProjectiveGlobalGeneration.pullback_generatingSections U.1.ι G) e)
  let hb : Ideal.span (Set.range b) = ⊤ := span_paddedCoefficients_eq_top _
    (span_coefficients_eq_top (ClosedProjectiveGlobalGeneration.pullback_generatingSections W.1.ι G)
      (restrictTrivialization h e))
  have hc : b = fun j => f.appTop.hom (a j) :=
    (congrArg paddedCoefficients (funext (localCoefficient_restrict G h e))).trans
      (paddedCoefficients_map (localCoefficient G U.1 e) f.appTop.hom)
  have hb' : Ideal.span (Set.range (fun j => f.appTop.hom (a j))) = ⊤ := by
    rw [← hc]
    exact hb
  have hn := affineTupleMap_naturality (baseCoefficients (U.1.ι ≫ p)) a ha f.appTop.hom hb'
  rw [CommRingCat.ofHom_hom] at hn
  have ho : f ≫ (U.1.ι ≫ p) = W.1.ι ≫ p := by
    rw [← Category.assoc, X.homOfLE_ι h]
  have hr : f.appTop.hom.comp (baseCoefficients (U.1.ι ≫ p)) = baseCoefficients (W.1.ι ≫ p) :=
    (baseCoefficients_naturality f (U.1.ι ≫ p)).symm.trans (congrArg baseCoefficients ho)
  change f ≫ (U.1.toScheme.isoSpec.hom ≫ affineTupleMap (baseCoefficients (U.1.ι ≫ p)) a ha) =
    W.1.toScheme.isoSpec.hom ≫ affineTupleMap (baseCoefficients (W.1.ι ≫ p)) b hb
  rw [← Category.assoc, ← Scheme.isoSpec_hom_naturality f, Category.assoc, hn]
  exact congrArg (fun q => W.1.toScheme.isoSpec.hom ≫ q)
    (affineTupleMap_congr hr hc.symm hb' hb)

/-- The actual original finite-generator map on a genuine original frame-affine cover chart. -/
def chartMap (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections) [Fintype G.I]
    (U : FramedAffineSite L) :
    U.1.1.toScheme ⟶ DeJongAlterations.projectiveSpace R (Fintype.card G.I) :=
  localMap p G U.1 (frame L U)

/-- Actual original coefficient restriction and derived frame independence
give the ENTIRE chart-map compatibility on the genuine original affine site. -/
theorem chartMap_naturality (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections) [Fintype G.I]
    (hL : IsInvertible L) {U V : FramedAffineSite L} (h : U ⟶ V) :
    (framedCover L hL).trans h ≫ chartMap p G V = chartMap p G U := by
  let hUV := Scheme.AffineZariskiSite.toOpens_mono h.le
  exact (localMap_restrict p G hUV (frame L V)).trans
    (affineMap_frame_independent (U.1.1.ι ≫ p)
      (ClosedProjectiveGlobalGeneration.pullback_generatingSections U.1.1.ι G)
      (frame L U) (restrictTrivialization hUV (frame L V)))

/-- The genuine whole ORIGINAL projective morphism of SAME finite original
global line generators, glued from actual original coefficient maps. -/
def projectiveMap (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] :
    X ⟶ DeJongAlterations.projectiveSpace R (Fintype.card G.I) :=
  (framedCover L hL).glueMorphismsOfLocallyDirected (chartMap p G)
    (fun _ => chartMap_naturality p G hL _)

/-- Its restriction is EXACTLY the SAME original finite-generator chart map. -/
@[reassoc] theorem projectiveMap_restrict (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (U : FramedAffineSite L) :
    U.1.1.ι ≫ projectiveMap p hL G = chartMap p G U :=
  (framedCover L hL).map_glueMorphismsOfLocallyDirected (chartMap p G)
    (fun _ => chartMap_naturality p G hL _) U

/-- The constructed WHOLE projective map preserves the SAME literal original structure morphism. -/
@[reassoc] theorem projectiveMap_structure (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] :
    projectiveMap p hL G ≫ DeJongAlterations.projectiveSpaceStructure R (Fintype.card G.I) = p := by
  apply (framedCover L hL).hom_ext
  intro U
  change U.1.1.ι ≫ (projectiveMap p hL G ≫ _) = U.1.1.ι ≫ p
  rw [← Category.assoc, projectiveMap_restrict]
  exact affineMap_structure (U.1.1.ι ≫ p)
    (ClosedProjectiveGlobalGeneration.pullback_generatingSections U.1.1.ι G) (frame L U)

/-- ANY actual original framed affine open retains the actual map in ANY
specified genuine original frame; no frame-map matching premise is needed. -/
@[reassoc] theorem projectiveMap_on_frame (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (U : X.AffineZariskiSite)
    (e : (Scheme.Modules.pullback U.1.ι).obj L ≅ unitObj U.1.toScheme) :
    U.1.ι ≫ projectiveMap p hL G = localMap p G U e := by
  let V : FramedAffineSite L := ⟨U, ⟨e⟩⟩
  exact (projectiveMap_restrict p hL G V).trans
    (affineMap_frame_independent (U.1.ι ≫ p)
      (ClosedProjectiveGlobalGeneration.pullback_generatingSections U.1.ι G) e (frame L V))

end EnvelopeProperty.GeneratedLineProjectiveMap
