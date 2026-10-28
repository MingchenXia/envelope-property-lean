/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeComparison

/-!
# Absolute native polynomial Proj and normalized graded seminorms

The actual canonical native point map is a homeomorphism without fixing its
coefficient seminorm. Whole genuine coordinate charts prove both bijectivity
and both continuous directions, so no absolute compactness or boundedness is
assumed. Restricting to any prescribed coefficient seminorm yields exactly
the existing genuine relative comparison. All native residues still come
from the actual degree-zero projective stalk, not the affine cone field.
-/

open scoped Classical NNReal Topology
open Topology AlgebraicGeometry EnvelopeProperty.ProjBerk
universe u
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.Berkovich.NormalizedProjectiveSpectrum
variable {R : Type u} [CommRing R] {n : ℕ}

/-- The canonical absolute native point agrees with the whole true coordinate-chart inverse. -/
theorem nativePoint_onChart (j : Fin (n + 1)) (x : chartOpen (R := R) j) :
    nativePoint x.1 =
      ((nativeAbsoluteCoordinateHomeomorph j).symm (coordinateChartHomeomorph j x)).1 := by
  have he : nativeAbsoluteCoordinateHomeomorph j ⟨nativePoint x.1, x.2⟩ =
      coordinateChartHomeomorph j x := by
    apply Spectrum.ext_val
    intro a
    rw [nativeAbsoluteCoordinateHomeomorph_val_apply]
    exact nativePoint_eval_coordinateChart x.1 j x.2 a
  have hi := congrArg (nativeAbsoluteCoordinateHomeomorph j).symm he
  exact congrArg Subtype.val ((Homeomorph.symm_apply_apply _ _).symm.trans hi)

/-- True whole native coordinate charts determine the entire absolute normalized seminorm. -/
theorem nativePoint_injective : Function.Injective (nativePoint (R := R) (n := n)) := by
  intro x y h
  obtain ⟨j, hx⟩ := exists_mem_chartOpen x
  have hp := congrArg SchemeValuedPoint.point h
  change nativeSupport x = nativeSupport y at hp
  have hy : y ∈ chartOpen j := by
    change nativeSupport y ∈ nativeCoordinateOpen j
    rw [← hp]
    exact hx
  have he : (nativeAbsoluteCoordinateHomeomorph j).symm (coordinateChartHomeomorph j ⟨x, hx⟩) =
      (nativeAbsoluteCoordinateHomeomorph j).symm (coordinateChartHomeomorph j ⟨y, hy⟩) := by
    apply Subtype.ext
    exact (nativePoint_onChart j ⟨x, hx⟩).symm.trans (h.trans (nativePoint_onChart j ⟨y, hy⟩))
  exact congrArg Subtype.val ((coordinateChartHomeomorph j).injective
    ((nativeAbsoluteCoordinateHomeomorph j).symm.injective he))

/-- Every actual absolute native projective point is recovered by a genuine coordinate Gauss inverse. -/
theorem nativePoint_surjective : Function.Surjective (nativePoint (R := R) (n := n)) := by
  intro y
  have hcov : y.point ∈ ⨆ j : Fin (n + 1), nativeCoordinateOpen (R := R) j := by
    rw [iSup_nativeCoordinateOpen_eq_top]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  let x := (coordinateChartHomeomorph j).symm (nativeAbsoluteCoordinateHomeomorph j ⟨y, hj⟩)
  refine ⟨x.1, ?_⟩
  rw [nativePoint_onChart j x]
  simp only [x, Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]

/-- Genuine source coordinate-open formulas give global absolute continuity. -/
@[fun_prop]
theorem continuous_nativePoint : Continuous (nativePoint (R := R) (n := n)) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hx⟩ := exists_mem_chartOpen x
  have hc : Continuous fun z : chartOpen (R := R) j => nativePoint z.1 := by
    have ht : Continuous fun z : chartOpen (R := R) j =>
        ((nativeAbsoluteCoordinateHomeomorph j).symm (coordinateChartHomeomorph j z)).1 :=
      continuous_subtype_val.comp ((nativeAbsoluteCoordinateHomeomorph j).symm.continuous.comp
        (coordinateChartHomeomorph j).continuous)
    exact ht.congr (fun z => (nativePoint_onChart j z).symm)
  exact (continuousOn_iff_continuous_domRestrict.mpr hc).continuousAt
    ((isOpen_chartOpen j).mem_nhds hx)

/-- The genuine whole-point absolute bijection, before asserting its inverse continuity. -/
def nativeEquiv : NormalizedProjectiveSpectrum R n ≃ SchemeValuedPoint (NativeProjectiveScheme R n) :=
  Equiv.ofBijective nativePoint ⟨nativePoint_injective, nativePoint_surjective⟩

/-- The absolute inverse is the genuine normalized Gauss inverse on every actual native coordinate chart. -/
theorem nativeEquiv_symm_onChart (j : Fin (n + 1))
    (y : {y : SchemeValuedPoint (NativeProjectiveScheme R n) // y.point ∈ nativeCoordinateOpen j}) :
    nativeEquiv.symm y.1 =
      ((coordinateChartHomeomorph j).symm (nativeAbsoluteCoordinateHomeomorph j y)).1 := by
  apply nativeEquiv.injective
  rw [Equiv.apply_symm_apply]
  change y.1 = nativePoint ((coordinateChartHomeomorph j).symm (nativeAbsoluteCoordinateHomeomorph j y)).1
  rw [nativePoint_onChart]
  simp only [Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]

/-- Actual target coordinate-open inverse formulas prove global inverse continuity without compactness. -/
@[fun_prop]
theorem continuous_nativeEquiv_symm : Continuous (nativeEquiv (R := R) (n := n)).symm := by
  rw [continuous_iff_continuousAt]
  intro y
  have hcov : y.point ∈ ⨆ j : Fin (n + 1), nativeCoordinateOpen (R := R) j := by
    rw [iSup_nativeCoordinateOpen_eq_top]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  have hc : Continuous fun z : {y : SchemeValuedPoint (NativeProjectiveScheme R n) //
      y.point ∈ nativeCoordinateOpen j} => nativeEquiv.symm z.1 := by
    have ht : Continuous fun z : {y : SchemeValuedPoint (NativeProjectiveScheme R n) //
        y.point ∈ nativeCoordinateOpen j} =>
        ((coordinateChartHomeomorph j).symm (nativeAbsoluteCoordinateHomeomorph j z)).1 :=
      continuous_subtype_val.comp ((coordinateChartHomeomorph j).symm.continuous.comp
        (nativeAbsoluteCoordinateHomeomorph j).continuous)
    exact ht.congr (fun z => (nativeEquiv_symm_onChart j z).symm)
  exact (continuousOn_iff_continuous_domRestrict.mpr hc).continuousAt
    ((SchemeValuedPoint.isOpen_point_preimage (nativeCoordinateOpen j)).mem_nhds hj)

/-- The canonical absolute native point map is genuinely a homeomorphism, proved by both actual chart directions. -/
def nativeAbsoluteHomeomorph :
    NormalizedProjectiveSpectrum R n ≃ₜ SchemeValuedPoint (NativeProjectiveScheme R n) where
  toEquiv := nativeEquiv
  continuous_toFun := continuous_nativePoint
  continuous_invFun := continuous_nativeEquiv_symm

/-- The absolute homeomorphism retains the canonical actual projective stalk-residue point. -/
@[simp]
theorem nativeAbsoluteHomeomorph_apply (x : NormalizedProjectiveSpectrum R n) :
    nativeAbsoluteHomeomorph x = nativePoint x := rfl

/-- The entire actual homogeneous scheme support is preserved by the absolute comparison. -/
@[simp]
theorem nativeAbsoluteHomeomorph_point (x : NormalizedProjectiveSpectrum R n) :
    (nativeAbsoluteHomeomorph x).point = nativeSupport x := rfl

/-- Whole actual native and normalized coordinate charts commute in the absolute comparison. -/
theorem nativeAbsoluteHomeomorph_chart (j : Fin (n + 1)) (x : chartOpen (R := R) j) :
    nativeAbsoluteCoordinateHomeomorph j ⟨nativeAbsoluteHomeomorph x.1, x.2⟩ =
      coordinateChartHomeomorph j x := by
  apply Spectrum.ext_val
  intro a
  rw [nativeAbsoluteCoordinateHomeomorph_val_apply]
  exact nativePoint_eval_coordinateChart x.1 j x.2 a

/-- Prescribed whole native base membership is exactly every original coefficient value condition. -/
theorem nativeAbsoluteHomeomorph_mem_relativeLocus (v : Valuation R ℝ≥0)
    (x : NormalizedProjectiveSpectrum R n) :
    nativeAbsoluteHomeomorph x ∈ SchemeValuedPoint.relativeLocus v nativeStructureMap ↔
      ∀ r, x.1.val (MvPolynomial.C r) = v r := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := RelativeNormalizedProjectiveSpectrum.nativePoint_surjective v ⟨nativePoint x, h⟩
    have he : nativePoint z.1 = nativePoint x := congrArg Subtype.val hz
    have hx := nativePoint_injective he
    intro r
    simpa only [hx] using z.2 r
  · intro h
    exact RelativeNormalizedProjectiveSpectrum.nativePoint_mem_relativeLocus v ⟨x, h⟩

/-- Restrict the actual absolute comparison to any prescribed whole base seminorm. -/
def nativeAbsoluteRelativeHomeomorph (v : Valuation R ℝ≥0) :
    RelativeNormalizedProjectiveSpectrum v n ≃ₜ
      RelativeSchemeValuedPoint v (nativeStructureMap (R := R) (n := n)) :=
  nativeAbsoluteHomeomorph.subtype (fun x => (nativeAbsoluteHomeomorph_mem_relativeLocus v x).symm)

/-- Absolute restriction is exactly the already proved genuine relative homeomorphism. -/
theorem nativeAbsoluteRelativeHomeomorph_eq (v : Valuation R ℝ≥0) :
    nativeAbsoluteRelativeHomeomorph (n := n) v = RelativeNormalizedProjectiveSpectrum.nativeHomeomorph v := by
  apply Homeomorph.ext
  intro x
  rfl

end EnvelopeProperty.Berkovich.NormalizedProjectiveSpectrum
