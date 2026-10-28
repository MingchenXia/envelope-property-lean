import EnvelopeProperty.AlgGeom.CyclicSectionSNCAdaptedRoundedFunctoriality
import EnvelopeProperty.AlgGeom.CyclicSectionSNCAffineInjectiveBaseChange
import Mathlib.AlgebraicGeometry.RelativeGluing

/-! # The actual cartesian rounded diagram over the original adapted atlas

The same actual chart rings and constructed whole arrows form a native scheme
functor. Its original projections are cartesian by the actual coefficient
pushout, actual gauge/frame isomorphism, and original affine identifications.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Modules
attribute [local instance] OreLocalization.instAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.CyclicSectionSNCAdaptedRoundedDiagram
open CyclicSectionSNCAdaptedFramedAtlas CyclicSectionSNCAdaptedFramedUnits
open CyclicSectionSNCAdaptedRoundedCharts CyclicSectionSNCAdaptedRoundedTransitions
open CyclicSectionSNCAdaptedRoundedFunctoriality

private theorem spec_equiv_scalar {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r
  exact e.commutes r

private theorem inverse_square {C : Type*} [Category C] {A B D E : C}
    (e : A ≅ B) (f : D ≅ E) (r : B ⟶ E) (s : A ⟶ D)
    (h : e.hom ≫ r = s ≫ f.hom) : r ≫ f.inv = e.inv ≫ s := by
  rw [← cancel_epi e.hom]
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc] using
    congrArg (fun k => k ≫ f.inv) h

variable {X : Scheme.{u}} [IsIntegral X]
variable {L : X.Modules} {n : ℕ} {s : unitObj X ⟶ CanonicalGeometry.bundleTensorPower L n}
variable {F : Scheme.DivisorFamily X} {a : F.ι → ℕ}

/-- The actual literal coefficient-extension model at the SAME original chart arrow. -/
abbrev restrictedChart {c d : Chart L n s F a} (h : c ⟶ d) (hn : 0 < n) : Scheme.{u} := by
  letI := coefficientDomain c
  exact Spec (CommRingCat.of (CyclicSectionSNCNormalizationRounded.roundedAlgebra n a
    (restriction h (chartUnit d)) (fun j => restriction h (chartBranches d j)) hn
    (fun j => (map_ne_zero_iff _ (restriction_injective h)).mpr (chart_branches_nonzero d j))))

/-- The actual comparison isomorphism points from the SAME original chart to its actual coefficient-extension model. -/
def comparisonIso {c d : Chart L n s F a} (h : c ⟶ d) (hn : 0 < n) :
    chart c hn ≅ restrictedChart h hn := by
  letI := coefficientDomain c
  exact Scheme.Spec.mapIso (roundedComparison h hn).toRingEquiv.toCommRingCatIso.op

/-- The actual original chart map is the spectrum of the WHOLE constructed rounded ring map. -/
def chartMap {c d : Chart L n s F a} (h : c ⟶ d) (hn : 0 < n) : chart c hn ⟶ chart d hn :=
  Spec.map (CommRingCat.ofHom (roundedMap h hn))

/-- Its whole actual factorization is the derived chart comparison followed by actual coefficient extension. -/
theorem chartMap_factorization {c d : Chart L n s F a} (h : c ⟶ d) (hn : 0 < n) :
    letI := coefficientDomain c
    letI := coefficientDomain d
    letI := restrictionAlgebra h
    chartMap h hn = (comparisonIso h hn).hom ≫
      CyclicSectionSNCAffineInjectiveBaseChange.coefficientSpecMap
        (R := coefficientRing d) (A := coefficientRing c) n a
        (chartUnit d) (chartBranches d) hn (chart_branches_nonzero d) (restriction_injective h) := by
  let := coefficientDomain c
  let := coefficientDomain d
  let := restrictionAlgebra h
  change Spec.map
    (CommRingCat.ofHom
      (CyclicSectionSNCInjectiveBaseChange.roundedMap (restriction_injective h) n a (chartUnit d)
        (chartBranches d) hn (chart_branches_nonzero d)).toRingHom ≫
      CommRingCat.ofHom (roundedComparison h hn).toRingHom) = _
  exact Spec.map_comp _ _

/-- The actual chart arrow is cartesian over the SAME original section-ring spectra. -/
theorem chartMap_affine_isPullback {c d : Chart L n s F a} (h : c ⟶ d) (hn : 0 < n) :
    IsPullback (chartMap h hn) (affineProjection c hn) (affineProjection d hn)
      (Spec.map (CommRingCat.ofHom (restriction h))) := by
  let := coefficientDomain c
  let := coefficientDomain d
  let := restrictionAlgebra h
  let p := CyclicSectionSNCAffineRoundedCover.projection n a
    (restriction h (chartUnit d)) (fun j => restriction h (chartBranches d j)) hn
    (fun j => (map_ne_zero_iff _ (restriction_injective h)).mpr (chart_branches_nonzero d j))
  have hi : IsPullback (comparisonIso h hn).hom (affineProjection c hn) p
      (𝟙 (Spec (CommRingCat.of (coefficientRing c)))) :=
    IsPullback.of_horiz_isIso ⟨by
      change Spec.map (CommRingCat.ofHom (roundedComparison h hn).toRingHom) ≫ p =
        affineProjection c hn ≫ 𝟙 _
      rw [Category.comp_id]
      change Spec.map (CommRingCat.ofHom (roundedComparison h hn).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (coefficientRing c) _)) =
          Spec.map (CommRingCat.ofHom (algebraMap (coefficientRing c) _))
      exact spec_equiv_scalar (roundedComparison h hn)⟩
  have hp := CyclicSectionSNCAffineInjectiveBaseChange.isPullback_projection
    (R := coefficientRing d) (A := coefficientRing c) n a
    (chartUnit d) (chartBranches d) hn (chart_branches_nonzero d) (restriction_injective h)
  change IsPullback (chartMap h hn) (affineProjection c hn)
    (CyclicSectionSNCAffineRoundedCover.projection (R := coefficientRing d) n a
      (chartUnit d) (chartBranches d) hn (chart_branches_nonzero d))
    (Spec.map (CommRingCat.ofHom (algebraMap (coefficientRing d) (coefficientRing c))))
  simpa only [Category.id_comp, ← chartMap_factorization h hn] using hi.paste_horiz hp.flip

omit [IsIntegral X] in
/-- The native original affine identifications respect the TRUE original coefficient restriction. -/
theorem affine_naturality {c d : Chart L n s F a} (h : c ⟶ d) :
    (chartAffine c).2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (restriction h)) =
      X.homOfLE h.hom.le ≫ (chartAffine d).2.isoSpec.hom := by
  have he := Scheme.Opens.toSpecΓ_SpecMap_presheaf_map
    (chartAffine c).1 (chartAffine d).1 h.hom.le
  rw [show X.presheaf.map (homOfLE h.hom.le).op = X.presheaf.map h.hom.op from
    X.presheaf.congr_map (Subsingleton.elim _ _)] at he
  exact he

omit [IsIntegral X] in
/-- The entire inverse-identification square commutes for the same original open inclusion. -/
theorem affine_inv_naturality {c d : Chart L n s F a} (h : c ⟶ d) :
    Spec.map (CommRingCat.ofHom (restriction h)) ≫ (chartAffine d).2.isoSpec.inv =
      (chartAffine c).2.isoSpec.inv ≫ X.homOfLE h.hom.le :=
  inverse_square (chartAffine c).2.isoSpec (chartAffine d).2.isoSpec _ _ (affine_naturality h)

/-- EVERY actual original chart square is cartesian over the actual original affine opens. -/
theorem chartMap_isPullback {c d : Chart L n s F a} (h : c ⟶ d) (hn : 0 < n) :
    IsPullback (chartMap h hn) (projection c hn) (projection d hn) (X.homOfLE h.hom.le) := by
  exact (chartMap_affine_isPullback h hn).of_iso (Iso.refl _) (Iso.refl _)
    (chartAffine c).2.isoSpec.symm (chartAffine d).2.isoSpec.symm
    (by simp) (by simp [projection]) (by simp [projection]) (affine_inv_naturality h)

theorem chartMap_projection {c d : Chart L n s F a} (h : c ⟶ d) (hn : 0 < n) :
    chartMap h hn ≫ projection d hn = projection c hn ≫ X.homOfLE h.hom.le :=
  (chartMap_isPullback h hn).w

theorem chartMap_id (c : Chart L n s F a) (hn : 0 < n) : chartMap (𝟙 c) hn = 𝟙 _ := by
  simp only [chartMap, roundedMap_id, CommRingCat.ofHom_id, Spec.map_id]

theorem chartMap_comp {c d e : Chart L n s F a} (h : c ⟶ d) (k : d ⟶ e) (hn : 0 < n) :
    chartMap h hn ≫ chartMap k hn = chartMap (h ≫ k) hn := by
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp, chartMap] using
    congrArg (fun f : roundedRing e hn →+* roundedRing c hn => Spec.map (CommRingCat.ofHom f))
      (roundedMap_comp h k hn)

/-- The SAME actual original chart objects and actual whole maps form a native scheme functor. -/
def diagram (hn : 0 < n) : Chart L n s F a ⥤ Scheme.{u} where
  obj c := chart c hn
  map h := chartMap h hn
  map_id c := chartMap_id c hn
  map_comp h k := (chartMap_comp h k hn).symm

/-- The actual original affine opens form the SAME original base diagram. -/
def baseDiagram : Chart L n s F a ⥤ Scheme.{u} where
  obj c := (chartAffine c).1.toScheme
  map h := X.homOfLE h.hom.le
  map_id _c := Scheme.homOfLE_rfl _ _
  map_comp h k := (Scheme.homOfLE_homOfLE X h.hom.le k.hom.le).symm

/-- The actual scalar projections to the original affine opens are a native natural transformation. -/
def projectionNatTrans (hn : 0 < n) : diagram hn ⟶ baseDiagram (L := L) (s := s) (F := F) (a := a) where
  app c := projection c hn
  naturality _ _ h := chartMap_projection h hn

/-- Native equifiberedness follows from every already constructed actual chart pullback. -/
theorem projectionNatTrans_equifibered (hn : 0 < n) : (projectionNatTrans (L := L) (s := s) (F := F) (a := a) hn).Equifibered := by
  intro c d h
  exact chartMap_isPullback h hn

end EnvelopeProperty.CyclicSectionSNCAdaptedRoundedDiagram
