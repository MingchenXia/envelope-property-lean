/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeOpenImmersion
import Mathlib.Topology.Gluing

/-!
# Genuine affine point-space gluing of actual schemes

Any actual scheme-open cover gives native support opens and genuine TopCat
point-space gluing. Affine pieces are parametrized by spectra of their actual
section rings, via open restriction, the genuine affine scheme isomorphism,
and the independently proved native affine homeomorphism.

The pieces are open embeddings, jointly cover the glued space, and identify
precisely representatives of the same whole native point. All actual affine
opens give a canonical covering atlas for every scheme. No analytic structure
sheaf, coherent-sheaf gluing or general Hausdorff assertion is supplied here.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite

universe u
noncomputable section

namespace EnvelopeProperty.Berkovich.SchemeValuedPoint

variable {X : Scheme.{u}}

/-- An actual scheme open gives its native support-open inverse image. -/
def supportOpens (U : X.Opens) : TopologicalSpace.Opens (SchemeValuedPoint X) :=
  ⟨(fun y => y.point) ⁻¹' U, isOpen_point_preimage U⟩

variable {ι : Type u}

/-- Genuine topological gluing data of a family of actual native support opens. -/
def openCoverGlueData (U : ι → X.Opens) : TopCat.GlueData.{u} :=
  TopCat.GlueData.ofOpenSubsets (fun i => supportOpens (U i))

/-- The actual topological gluing of the native support-open family. -/
abbrev OpenCoverGlued (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens) :=
  (openCoverGlueData U).toGlueData.glued

/-- A genuine scheme open cover also covers its native valued-point space. -/
theorem iUnion_supportOpens (U : ι → X.Opens) (hU : (⋃ i, (U i : Set X)) = Set.univ) :
    (⋃ i, (supportOpens (U i) : Set (SchemeValuedPoint X))) = Set.univ := by
  change (⋃ i, (fun y : SchemeValuedPoint X => y.point) ⁻¹' (U i : Set X)) = _
  rw [← Set.preimage_iUnion, hU, Set.preimage_univ]

/-- Genuine gluing of any scheme-open cover recovers the native valued-point space. -/
def openCoverGlueHomeomorph (U : ι → X.Opens) (hU : (⋃ i, (U i : Set X)) = Set.univ) :
    OpenCoverGlued X U ≃ₜ SchemeValuedPoint X :=
  TopCat.GlueData.openCoverGlueHomeo (fun i => supportOpens (U i)) (iUnion_supportOpens U hU)

/-- An actual affine open is canonically parametrized by its genuine section-ring spectrum. -/
def affineOpenSpectrumHomeomorph {U : X.Opens} (hU : IsAffineOpen U) :
    {y : SchemeValuedPoint X // y.point ∈ U} ≃ₜ Spectrum Γ(X, U) :=
  (restrictionHomeomorph U).symm.trans
    ((isoHomeomorph hU.isoSpec).trans spectrumHomeomorph)

/-- The affine representative in the ambient space is the actual open-inclusion point map. -/
@[simp]
theorem affineOpenSpectrumHomeomorph_symm_coe {U : X.Opens} (hU : IsAffineOpen U)
    (x : Spectrum Γ(X, U)) :
    (affineOpenSpectrumHomeomorph hU |>.symm x : SchemeValuedPoint X) =
      map U.ι ((isoHomeomorph hU.isoSpec).symm (spectrumHomeomorph.symm x)) :=
  restrictionHomeomorph_apply_coe U _

/-- Parametrize a gluing piece by the seminorm spectrum of its actual affine section ring. -/
def affineChartInclusion (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (i : ι) (x : Spectrum Γ(X, U i)) : OpenCoverGlued X U :=
  (openCoverGlueData U).toGlueData.ι i ((affineOpenSpectrumHomeomorph (hU i)).symm x)

@[fun_prop]
theorem continuous_affineChartInclusion (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (i : ι) :
    Continuous (affineChartInclusion U hU i) :=
  ((openCoverGlueData U).toGlueData.ι i).hom.continuous.comp
    (affineOpenSpectrumHomeomorph (hU i)).symm.continuous

/-- The actual gluing homeomorphism preserves the ambient native affine representative. -/
@[simp]
theorem openCoverGlueHomeomorph_affineChartInclusion (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⋃ i, (U i : Set X)) = Set.univ)
    (i : ι) (x : Spectrum Γ(X, U i)) :
    openCoverGlueHomeomorph U hcover (affineChartInclusion U hU i x) =
      ((affineOpenSpectrumHomeomorph (hU i)).symm x : SchemeValuedPoint X) := by
  change TopCat.GlueData.fromOpenSubsetsGlue (fun i => supportOpens (U i))
    ((openCoverGlueData U).toGlueData.ι i ((affineOpenSpectrumHomeomorph (hU i)).symm x)) = _
  exact TopCat.GlueData.ι_fromOpenSubsetsGlue_apply _ _ _

/-- The genuine affine section-ring parametrizations are open embeddings in the glued point space. -/
theorem isOpenEmbedding_affineChartInclusion (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (i : ι) :
    IsOpenEmbedding (affineChartInclusion U hU i) :=
  ((openCoverGlueData U).ι_isOpenEmbedding i).comp
    (affineOpenSpectrumHomeomorph (hU i)).symm.isOpenEmbedding

/-- The gluing identifies exactly those affine representatives with the same whole native point. -/
theorem affineChartInclusion_eq_iff (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⋃ i, (U i : Set X)) = Set.univ) (i j : ι)
    (x : Spectrum Γ(X, U i)) (y : Spectrum Γ(X, U j)) :
    affineChartInclusion U hU i x = affineChartInclusion U hU j y ↔
      ((affineOpenSpectrumHomeomorph (hU i)).symm x : SchemeValuedPoint X) =
      ((affineOpenSpectrumHomeomorph (hU j)).symm y : SchemeValuedPoint X) := by
  constructor
  · intro h
    simpa only [openCoverGlueHomeomorph_affineChartInclusion] using
      congrArg (openCoverGlueHomeomorph U hcover) h
  · intro h
    apply (openCoverGlueHomeomorph U hcover).injective
    simpa only [openCoverGlueHomeomorph_affineChartInclusion] using h

/-- The actual affine section-ring pieces jointly cover the genuine glued space. -/
theorem affineChartInclusion_jointly_surjective (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (x : OpenCoverGlued X U) :
    ∃ (i : ι) (y : Spectrum Γ(X, U i)), affineChartInclusion U hU i y = x := by
  obtain ⟨i, z, rfl⟩ := (openCoverGlueData U).ι_jointly_surjective x
  refine ⟨i, affineOpenSpectrumHomeomorph (hU i) z, ?_⟩
  exact congrArg ((openCoverGlueData U).toGlueData.ι i)
    ((affineOpenSpectrumHomeomorph (hU i)).symm_apply_apply z)

/-- Every genuine affine open is an index of the canonical native affine atlas. -/
abbrev AffineAtlasIndex (X : Scheme.{u}) := X.affineOpens

/-- The actual scheme open selected by an index of the canonical affine atlas. -/
def canonicalAffineOpens (X : Scheme.{u}) (i : AffineAtlasIndex X) : X.Opens := i.1

theorem isAffineOpen_canonicalAffineOpens (X : Scheme.{u}) (i : AffineAtlasIndex X) :
    IsAffineOpen (canonicalAffineOpens X i) := i.2

/-- All actual affine opens cover every scheme, without any finiteness or separatedness condition. -/
theorem iUnion_canonicalAffineOpens (X : Scheme.{u}) :
    (⋃ i : AffineAtlasIndex X, (canonicalAffineOpens X i : Set X)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := x) trivial
  exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩

/-- The canonical genuine affine atlas glues to the native valued-point space of every scheme. -/
def canonicalAffineGlueHomeomorph (X : Scheme.{u}) :
    OpenCoverGlued X (canonicalAffineOpens X) ≃ₜ SchemeValuedPoint X :=
  openCoverGlueHomeomorph (canonicalAffineOpens X) (iUnion_canonicalAffineOpens X)

end EnvelopeProperty.Berkovich.SchemeValuedPoint
