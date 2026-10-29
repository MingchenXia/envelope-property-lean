/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeAtlas
import EnvelopeProperty.Berkovich.SchemeRelativeValuedPoints

/-!
# Actual native prescribed-base affine atlas

Actual section values identify each genuine affine support open with the
relative spectrum of its section ring for the coefficient action derived
from the scheme structure morphism. Commuting open immersions preserve the
exact fixed base point and are genuine open embeddings. Actual support-open
gluing and the true canonical cover by all affine opens reconstruct the
independently defined prescribed-base native point space.

The base ring and prescribed real seminorm are arbitrary. No unrelated
section-ring algebra action, finite cover, separatedness, arbitrary-scheme
Hausdorff condition, analytic structure sheaf or model-center map is assumed
or asserted.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite

universe u
noncomputable section

namespace EnvelopeProperty.Berkovich.SchemeValuedPoint

variable {X : Scheme.{u}}

/-- The actual open-inclusion residue map and global section isomorphism preserve all section values. -/
theorem eval_map_ι_topIso (U : X.Opens) (y : SchemeValuedPoint U.toScheme) (s : Γ(X, U)) :
    eval (map U.ι y) U y.point.2 s = eval y ⊤ trivial (U.topIso.inv s) := by
  have hres := eval_restrict (map U.ι y) U (U.ι ''ᵁ ⊤) U.ι_image_top.le
    (Set.mem_image_of_mem U.ι trivial) s
  have hs : X.presheaf.map (homOfLE U.ι_image_top.le).op s =
      (U.ι.appIso ⊤).inv (U.topIso.inv s) := by
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl
  exact hres.symm.trans
    ((congrArg (eval (map U.ι y) (U.ι ''ᵁ ⊤) (Set.mem_image_of_mem U.ι trivial)) hs).trans
      (eval_map_appIso_inv U.ι y ⊤ trivial (U.topIso.inv s)))

/-- The genuine affine-open section-ring homeomorphism preserves every original section value. -/
theorem affineOpenSpectrumHomeomorph_val_apply {U : X.Opens} (hU : IsAffineOpen U)
    (y : {y : SchemeValuedPoint X // y.point ∈ U}) (s : Γ(X, U)) :
    (affineOpenSpectrumHomeomorph hU y).val s = eval y.1 U y.2 s := by
  obtain ⟨z, rfl⟩ := (restrictionHomeomorph U).surjective y
  have hchart : affineOpenSpectrumHomeomorph hU (restrictionHomeomorph U z) =
      spectrumHomeomorph (isoHomeomorph hU.isoSpec z) := by
    change spectrumHomeomorph (isoHomeomorph hU.isoSpec
      ((restrictionHomeomorph U).symm (restrictionHomeomorph U z))) = _
    rw [Homeomorph.symm_apply_apply]
  rw [hchart, spectrumHomeomorph_val_apply, isoHomeomorph_apply, evalTop_map]
  have hs : hU.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(X, U)).inv s) = U.topIso.inv s := by
    rw [hU.isoSpec_hom_appTop, CommRingCat.comp_apply]
    apply congrArg U.topIso.inv
    exact congrArg (fun g => g s) (Scheme.ΓSpecIso Γ(X, U)).inv_hom_id
  exact (congrArg (eval z ⊤ trivial) hs).trans (eval_map_ι_topIso U z s).symm

section Relative

variable {R : Type u} [CommRing R]

/-- Derived section coefficients evaluate as the actual original coefficient at the mapped native base point. -/
theorem eval_sectionBaseMap (f : X ⟶ Spec (CommRingCat.of R)) (y : SchemeValuedPoint X)
    (U : X.Opens) (hy : y.point ∈ U) (r : R) :
    eval y U hy (sectionBaseMap f U r) =
      eval (map f y) ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) :=
  (eval_restrict y ⊤ U le_top hy (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))).trans
    (evalTop_map f y ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)).symm

/-- All actual local coefficient values determine exactly the whole prescribed native base point. -/
theorem mem_relativeLocus_iff_sectionCoefficients (v : Valuation R ℝ≥0)
    (f : X ⟶ Spec (CommRingCat.of R)) (y : SchemeValuedPoint X)
    (U : X.Opens) (hy : y.point ∈ U) :
    y ∈ relativeLocus v f ↔ ∀ r, eval y U hy (sectionBaseMap f U r) = v r := by
  constructor
  · intro h r
    rw [eval_sectionBaseMap, show map f y = basePoint v from h, basePoint_eval]
  · intro h
    apply (spectrumHomeomorph (A := R)).injective
    apply Spectrum.ext_val
    intro r
    rw [spectrumHomeomorph_val_apply, spectrumHomeomorph_val_apply, basePoint_eval]
    exact (eval_sectionBaseMap f y U hy r).symm.trans (h r)

end Relative

end EnvelopeProperty.Berkovich.SchemeValuedPoint

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X Y : Scheme.{u}}
variable {fX : X ⟶ Spec (CommRingCat.of R)} {fY : Y ⟶ Spec (CommRingCat.of R)}

/-- Reorder the genuine support-open and exact prescribed-base conditions. -/
def supportRelativeHomeomorph (U : X.Opens) (f : X ⟶ Spec (CommRingCat.of R)) :
    {z : {y : SchemeValuedPoint X // y.point ∈ U} //
      z.1 ∈ SchemeValuedPoint.relativeLocus v f} ≃ₜ
        {y : RelativeSchemeValuedPoint v f // y.1.point ∈ U} where
  toFun z := ⟨⟨z.1.1, z.2⟩, z.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- An actual commuting open immersion identifies precisely the relative native support-open locus. -/
def openImmersionHomeomorph (g : X ⟶ Y) [IsOpenImmersion g] (hg : g ≫ fY = fX) :
    RelativeSchemeValuedPoint v fX ≃ₜ
      {y : RelativeSchemeValuedPoint v fY // y.1.point ∈ g.opensRange} :=
  ((SchemeValuedPoint.openImmersionHomeomorph g).subtype (fun y => by
    change (SchemeValuedPoint.map fX y = SchemeValuedPoint.basePoint v) ↔
      (SchemeValuedPoint.map fY (SchemeValuedPoint.map g y) = SchemeValuedPoint.basePoint v)
    rw [← SchemeValuedPoint.map_comp, hg])).trans
      (supportRelativeHomeomorph g.opensRange fY)

@[simp]
theorem openImmersionHomeomorph_apply_coe (g : X ⟶ Y) [IsOpenImmersion g]
    (hg : g ≫ fY = fX) (y : RelativeSchemeValuedPoint v fX) :
    (openImmersionHomeomorph g hg y : RelativeSchemeValuedPoint v fY) = map g hg y := rfl

/-- The relative native image of an open immersion is exactly its genuine support-open locus. -/
theorem range_map_of_isOpenImmersion (g : X ⟶ Y) [IsOpenImmersion g] (hg : g ≫ fY = fX) :
    Set.range (map (v := v) g hg) = {y : RelativeSchemeValuedPoint v fY | y.1.point ∈ g.opensRange} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (openImmersionHomeomorph g hg x).2
  · intro hy
    obtain ⟨x, hx⟩ := (openImmersionHomeomorph (v := v) g hg).surjective ⟨y, hy⟩
    exact ⟨x, congrArg Subtype.val hx⟩

/-- Native prescribed-base open immersion maps are genuine open embeddings. -/
theorem isOpenEmbedding_map_of_isOpenImmersion (g : X ⟶ Y) [IsOpenImmersion g]
    (hg : g ≫ fY = fX) : IsOpenEmbedding (map (v := v) g hg) := by
  have hopen : IsOpen {y : RelativeSchemeValuedPoint v fY | y.1.point ∈ g.opensRange} :=
    (SchemeValuedPoint.isOpen_point_preimage g.opensRange).preimage continuous_subtype_val
  exact hopen.isOpenEmbedding_subtypeVal.comp (openImmersionHomeomorph g hg).isOpenEmbedding

/-- Genuine open-subscheme restriction over the original base, with the derived structure morphism. -/
def restrictionHomeomorph (U : X.Opens) (f : X ⟶ Spec (CommRingCat.of R)) :
    RelativeSchemeValuedPoint v (U.ι ≫ f) ≃ₜ
      {y : RelativeSchemeValuedPoint v f // y.1.point ∈ U} :=
  (openImmersionHomeomorph (v := v) (fY := f) U.ι rfl).trans
    (Homeomorph.setCongr (by rw [Scheme.Opens.opensRange_ι]))

@[simp]
theorem restrictionHomeomorph_apply_coe (U : X.Opens) (f : X ⟶ Spec (CommRingCat.of R))
    (y : RelativeSchemeValuedPoint v (U.ι ≫ f)) :
    (restrictionHomeomorph U f y : RelativeSchemeValuedPoint v f) = map U.ι rfl y := rfl

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- Genuine affine local-section evaluation is an exact prescribed-base homeomorphism for the derived action. -/
def affineOpenSpectrumHomeomorph {U : X.Opens} (hU : IsAffineOpen U) :
    letI := SchemeValuedPoint.sectionBaseAlgebra f U
    {y : RelativeSchemeValuedPoint v f // y.1.point ∈ U} ≃ₜ RelativeSpectrum v Γ(X, U) := by
  letI := SchemeValuedPoint.sectionBaseAlgebra f U
  exact (supportRelativeHomeomorph U f).symm.trans
    ((SchemeValuedPoint.affineOpenSpectrumHomeomorph hU).subtype (fun y => by
      change y.1 ∈ SchemeValuedPoint.relativeLocus v f ↔
        ∀ r, (SchemeValuedPoint.affineOpenSpectrumHomeomorph hU y).val
          (SchemeValuedPoint.sectionBaseMap f U r) = v r
      simp only [SchemeValuedPoint.affineOpenSpectrumHomeomorph_val_apply]
      exact SchemeValuedPoint.mem_relativeLocus_iff_sectionCoefficients v f y.1 U y.2))

/-- The relative affine chart evaluates every genuine original local section. -/
@[simp]
theorem affineOpenSpectrumHomeomorph_val_apply {U : X.Opens} (hU : IsAffineOpen U)
    (y : {y : RelativeSchemeValuedPoint v f // y.1.point ∈ U}) (s : Γ(X, U)) :
    (affineOpenSpectrumHomeomorph hU y).1.val s = SchemeValuedPoint.eval y.1.1 U y.2 s :=
  SchemeValuedPoint.affineOpenSpectrumHomeomorph_val_apply hU _ s

/-- The relative chart is the actual local-section spectrum evaluation map on its whole domain. -/
theorem affineOpenSpectrumHomeomorph_eq_sectionSpectrum {U : X.Opens} (hU : IsAffineOpen U)
    (y : {y : RelativeSchemeValuedPoint v f // y.1.point ∈ U}) :
    affineOpenSpectrumHomeomorph hU y = sectionSpectrum y.1 U y.2 := by
  apply Subtype.ext
  exact Spectrum.ext_val (fun s => affineOpenSpectrumHomeomorph_val_apply hU y s)

/-- The inverse relative chart preserves the actual ambient native affine representative. -/
@[simp]
theorem affineOpenSpectrumHomeomorph_symm_coe {U : X.Opens} (hU : IsAffineOpen U)
    (x : letI := SchemeValuedPoint.sectionBaseAlgebra f U; RelativeSpectrum v Γ(X, U)) :
    ((affineOpenSpectrumHomeomorph hU).symm x).1.1 =
      ((SchemeValuedPoint.affineOpenSpectrumHomeomorph hU).symm x.1 : SchemeValuedPoint X) := rfl

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable {ι : Type u}

/-- An actual scheme open gives an open in the native exact prescribed-base subspace. -/
def supportOpens (v : Valuation R ℝ≥0) (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) :
    TopologicalSpace.Opens (RelativeSchemeValuedPoint v f) :=
  ⟨{y | y.1.point ∈ U}, (SchemeValuedPoint.isOpen_point_preimage U).preimage continuous_subtype_val⟩

/-- Actual topological gluing data of relative native support opens. -/
def openCoverGlueData (v : Valuation R ℝ≥0) (f : X ⟶ Spec (CommRingCat.of R))
    (U : ι → X.Opens) : TopCat.GlueData.{u} :=
  TopCat.GlueData.ofOpenSubsets (fun i => supportOpens v f (U i))

/-- Genuine topological gluing of the native relative support-open family. -/
abbrev OpenCoverGlued (v : Valuation R ℝ≥0) (f : X ⟶ Spec (CommRingCat.of R))
    {ι : Type u} (U : ι → X.Opens) := (openCoverGlueData v f U).toGlueData.glued

/-- A genuine scheme-open cover covers every native point extending the prescribed base seminorm. -/
theorem iUnion_supportOpens (v : Valuation R ℝ≥0) (f : X ⟶ Spec (CommRingCat.of R))
    (U : ι → X.Opens) (hU : (⋃ i, (U i : Set X)) = Set.univ) :
    (⋃ i, (supportOpens v f (U i) : Set (RelativeSchemeValuedPoint v f))) = Set.univ := by
  change (⋃ i, (fun y : RelativeSchemeValuedPoint v f => y.1.point) ⁻¹' (U i : Set X)) = _
  rw [← Set.preimage_iUnion, hU, Set.preimage_univ]

/-- Actual prescribed-base point gluing of a genuine scheme-open cover. -/
def openCoverGlueHomeomorph (v : Valuation R ℝ≥0) (f : X ⟶ Spec (CommRingCat.of R))
    (U : ι → X.Opens) (hU : (⋃ i, (U i : Set X)) = Set.univ) :
    OpenCoverGlued v f U ≃ₜ RelativeSchemeValuedPoint v f :=
  TopCat.GlueData.openCoverGlueHomeo (fun i => supportOpens v f (U i)) (iUnion_supportOpens v f U hU)

/-- Parametrize an actual relative affine gluing piece using its genuinely derived coefficient action. -/
def affineChartInclusion (v : Valuation R ℝ≥0) (f : X ⟶ Spec (CommRingCat.of R))
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (i : ι)
    (x : letI := SchemeValuedPoint.sectionBaseAlgebra f (U i); RelativeSpectrum v Γ(X, U i)) :
    OpenCoverGlued v f U :=
  (openCoverGlueData v f U).toGlueData.ι i ((affineOpenSpectrumHomeomorph (hU i)).symm x)

@[fun_prop]
theorem continuous_affineChartInclusion (v : Valuation R ℝ≥0) (f : X ⟶ Spec (CommRingCat.of R))
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (i : ι) :
    Continuous (affineChartInclusion v f U hU i) :=
  ((openCoverGlueData v f U).toGlueData.ι i).hom.continuous.comp
    (affineOpenSpectrumHomeomorph (hU i)).symm.continuous

/-- Actual relative gluing preserves the entire ambient native point of each affine representative. -/
@[simp]
theorem openCoverGlueHomeomorph_affineChartInclusion (v : Valuation R ℝ≥0)
    (f : X ⟶ Spec (CommRingCat.of R)) (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⋃ i, (U i : Set X)) = Set.univ) (i : ι)
    (x : letI := SchemeValuedPoint.sectionBaseAlgebra f (U i); RelativeSpectrum v Γ(X, U i)) :
    openCoverGlueHomeomorph v f U hcover (affineChartInclusion v f U hU i x) =
      ((affineOpenSpectrumHomeomorph (hU i)).symm x : RelativeSchemeValuedPoint v f) := by
  change TopCat.GlueData.fromOpenSubsetsGlue (fun i => supportOpens v f (U i))
    ((openCoverGlueData v f U).toGlueData.ι i ((affineOpenSpectrumHomeomorph (hU i)).symm x)) = _
  exact TopCat.GlueData.ι_fromOpenSubsetsGlue_apply _ _ _

/-- Prescribed-base spectra with the true local coefficient action are open embeddings into the gluing. -/
theorem isOpenEmbedding_affineChartInclusion (v : Valuation R ℝ≥0)
    (f : X ⟶ Spec (CommRingCat.of R)) (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (i : ι) :
    IsOpenEmbedding (affineChartInclusion v f U hU i) :=
  ((openCoverGlueData v f U).ι_isOpenEmbedding i).comp
    (affineOpenSpectrumHomeomorph (hU i)).symm.isOpenEmbedding

/-- Two actual relative affine representatives glue exactly when their whole native points agree. -/
theorem affineChartInclusion_eq_iff (v : Valuation R ℝ≥0) (f : X ⟶ Spec (CommRingCat.of R))
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⋃ i, (U i : Set X)) = Set.univ) (i j : ι)
    (x : letI := SchemeValuedPoint.sectionBaseAlgebra f (U i); RelativeSpectrum v Γ(X, U i))
    (y : letI := SchemeValuedPoint.sectionBaseAlgebra f (U j); RelativeSpectrum v Γ(X, U j)) :
    affineChartInclusion v f U hU i x = affineChartInclusion v f U hU j y ↔
      ((affineOpenSpectrumHomeomorph (hU i)).symm x : RelativeSchemeValuedPoint v f) =
      ((affineOpenSpectrumHomeomorph (hU j)).symm y : RelativeSchemeValuedPoint v f) := by
  constructor
  · intro h
    simpa only [openCoverGlueHomeomorph_affineChartInclusion] using
      congrArg (openCoverGlueHomeomorph v f U hcover) h
  · intro h
    apply (openCoverGlueHomeomorph v f U hcover).injective
    simpa only [openCoverGlueHomeomorph_affineChartInclusion] using h

/-- The actual relative affine section-ring pieces jointly cover their true topological gluing. -/
theorem affineChartInclusion_jointly_surjective (v : Valuation R ℝ≥0)
    (f : X ⟶ Spec (CommRingCat.of R)) (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (x : OpenCoverGlued v f U) :
    ∃ (i : ι) (y : letI := SchemeValuedPoint.sectionBaseAlgebra f (U i); RelativeSpectrum v Γ(X, U i)),
      affineChartInclusion v f U hU i y = x := by
  obtain ⟨i, z, rfl⟩ := (openCoverGlueData v f U).ι_jointly_surjective x
  refine ⟨i, affineOpenSpectrumHomeomorph (hU i) z, ?_⟩
  exact congrArg ((openCoverGlueData v f U).toGlueData.ι i)
    ((affineOpenSpectrumHomeomorph (hU i)).symm_apply_apply z)

/-- All genuine affine opens canonically reconstruct the native prescribed-base point space of every scheme. -/
def canonicalAffineGlueHomeomorph (v : Valuation R ℝ≥0) (f : X ⟶ Spec (CommRingCat.of R)) :
    OpenCoverGlued v f (SchemeValuedPoint.canonicalAffineOpens X) ≃ₜ RelativeSchemeValuedPoint v f :=
  openCoverGlueHomeomorph v f (SchemeValuedPoint.canonicalAffineOpens X)
    (SchemeValuedPoint.iUnion_canonicalAffineOpens X)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
