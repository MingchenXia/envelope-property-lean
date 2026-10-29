import EnvelopeProperty.AlgGeom.CyclicSectionSNCAdaptedRoundedDiagram

/-! # The actual rounded cover of the original line section

The actual constructed chart diagram and its internally proved cartesian
projection transformation feed native relative gluing over the internally
generated original adapted cover. No matching/cocycle/pullback or normality
certificate is supplied to this construction.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Modules
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.CyclicSectionSNCOriginalRoundedGluing
open CanonicalGeometry CyclicSectionSNCAdaptedFramedAtlas
open CyclicSectionSNCAdaptedRoundedCharts CyclicSectionSNCAdaptedRoundedDiagram
variable {X : Scheme.{u}} [IsIntegral X]
variable (L : X.Modules) (hL : IsInvertible L) (n : ℕ)
variable (s : unitObj X ⟶ bundleTensorPower L n)
variable {k : Type u} [Field k] [PerfectField k]
variable (f : X ⟶ Spec (CommRingCat.of k)) (d : ℕ) [SmoothOfRelativeDimension d f]
variable {F : Scheme.DivisorFamily X} (hF : F.IsSnc) (a : F.ι → ℕ)
variable (hJF : LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L n)
  (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n) s = ∏ i, F.component i ^ a i)
  (hn : 0 < n)

/-- Native gluing consumes precisely the internally constructed actual original rounded diagram. -/
def nativeRelativeGluingData :
    letI := atlasCover_locallyDirected L hL n s f d hF a hJF
    Scheme.Cover.RelativeGluingData (atlasCover L hL n s f d hF a hJF) := by
  letI := atlasCover_locallyDirected L hL n s f d hF a hJF
  exact
    { functor := diagram (L := L) (s := s) (F := F) (a := a) hn
      natTrans :=
        { app := fun c => projection c hn
          naturality := fun _ _ h => chartMap_projection h hn }
      equifibered := by
        intro c e h
        exact chartMap_isPullback h hn }

/-- The native scheme colimit of the SAME actual original rounded charts. -/
def gluedScheme : Scheme.{u} := by
  letI := atlasCover_locallyDirected L hL n s f d hF a hJF
  exact (nativeRelativeGluingData L hL n s f d hF a hJF hn).glued

/-- The actual morphism of the original rounded cover to the SAME original base. -/
def gluedProjection : gluedScheme L hL n s f d hF a hJF hn ⟶ X := by
  letI := atlasCover_locallyDirected L hL n s f d hF a hJF
  exact (nativeRelativeGluingData L hL n s f d hF a hJF hn).toBase

/-- The actual original rounded charts form the native open cover of the SAME global rounded scheme. -/
def roundedCover : (gluedScheme L hL n s f d hF a hJF hn).OpenCover := by
  letI := atlasCover_locallyDirected L hL n s f d hF a hJF
  exact (nativeRelativeGluingData L hL n s f d hF a hJF hn).cover

/-- The native actual chart inclusion of the SAME literal original Spec M. -/
def chartι (c : Chart L n s F a) : chart c hn ⟶ gluedScheme L hL n s f d hF a hJF hn := by
  letI := atlasCover_locallyDirected L hL n s f d hF a hJF
  exact (nativeRelativeGluingData L hL n s f d hF a hJF hn).cover.f c

instance chartι_isOpenImmersion (c : Chart L n s F a) :
    IsOpenImmersion (chartι L hL n s f d hF a hJF hn c) := by
  let := atlasCover_locallyDirected L hL n s f d hF a hJF
  exact inferInstanceAs (IsOpenImmersion
    ((nativeRelativeGluingData L hL n s f d hF a hJF hn).cover.f c))

/-- The ENTIRE actual original chart/base triangle follows from native gluing. -/
theorem chartι_projection (c : Chart L n s F a) :
    chartι L hL n s f d hF a hJF hn c ≫ gluedProjection L hL n s f d hF a hJF hn =
      projection c hn ≫ (chartAffine c).1.ι := by
  let := atlasCover_locallyDirected L hL n s f d hF a hJF
  exact (nativeRelativeGluingData L hL n s f d hF a hJF hn).ι_toBase c

/-- The WHOLE actual original transition is compatible with its actual native colimit inclusions. -/
theorem chartMap_chartι {c e : Chart L n s F a} (h : c ⟶ e) :
    chartMap h hn ≫ chartι L hL n s f d hF a hJF hn e =
      chartι L hL n s f d hF a hJF hn c := by
  let := atlasCover_locallyDirected L hL n s f d hF a hJF
  exact (nativeRelativeGluingData L hL n s f d hF a hJF hn).cover.trans_map h

/-- Each SAME literal actual rounded chart is cartesian over its SAME original affine open. -/
theorem isPullback_chartι (c : Chart L n s F a) :
    IsPullback (projection c hn) (chartι L hL n s f d hF a hJF hn c)
      (chartAffine c).1.ι (gluedProjection L hL n s f d hF a hJF hn) := by
  let := atlasCover_locallyDirected L hL n s f d hF a hJF
  exact (nativeRelativeGluingData L hL n s f d hF a hJF hn).isPullback_natTrans_ι_toBase c

/-- The native canonical isomorphism from the literal Spec M chart to the ACTUAL inverse-image open. -/
def chartPreimageIso (c : Chart L n s F a) : chart c hn ≅
    ((gluedProjection L hL n s f d hF a hJF hn) ⁻¹ᵁ (chartAffine c).1).toScheme :=
  (isPullback_chartι L hL n s f d hF a hJF hn c).isoIsPullback _ _
    (isPullback_morphismRestrict (gluedProjection L hL n s f d hF a hJF hn) (chartAffine c).1)

/-- The ENTIRE canonical preimage-chart isomorphism preserves the SAME original actual chart projection. -/
theorem chartPreimageIso_base (c : Chart L n s F a) :
    (chartPreimageIso L hL n s f d hF a hJF hn c).hom ≫
      (gluedProjection L hL n s f d hF a hJF hn ∣_ (chartAffine c).1) = projection c hn :=
  IsPullback.isoIsPullback_hom_fst _ _
    (isPullback_chartι L hL n s f d hF a hJF hn c)
    (isPullback_morphismRestrict (gluedProjection L hL n s f d hF a hJF hn) (chartAffine c).1)

/-- The WHOLE canonical preimage-chart inclusion agrees with the original native colimit inclusion. -/
theorem chartPreimageIso_ι (c : Chart L n s F a) :
    (chartPreimageIso L hL n s f d hF a hJF hn c).hom ≫
      ((gluedProjection L hL n s f d hF a hJF hn) ⁻¹ᵁ (chartAffine c).1).ι =
        chartι L hL n s f d hF a hJF hn c :=
  IsPullback.isoIsPullback_hom_snd _ _
    (isPullback_chartι L hL n s f d hF a hJF hn c)
    (isPullback_morphismRestrict (gluedProjection L hL n s f d hF a hJF hn) (chartAffine c).1)

end EnvelopeProperty.CyclicSectionSNCOriginalRoundedGluing
