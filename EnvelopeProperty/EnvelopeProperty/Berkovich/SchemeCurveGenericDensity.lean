/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.CurveGenericDensity
import EnvelopeProperty.FiniteTypeFieldPoint
import EnvelopeProperty.Berkovich.SchemeRelativeAtlas
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Topology.KrullDimension

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {F : Type u} [Field F] {X : Scheme.{u}} [IsIntegral X]

omit [IsIntegral X] in
/-- The actual original affine section ring inherits the original scheme dimension. -/
theorem affineOpen_krullDimLE_one_of_topologicalKrullDim_le_one
    (hX : topologicalKrullDim X ≤ 1) {U : X.Opens} (hU : IsAffineOpen U) :
    Ring.KrullDimLE 1 Γ(X, U) := by
  rw [Ring.krullDimLE_iff, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)]
  change topologicalKrullDim (Spec Γ(X, U)) ≤ 1
  rw [← IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
  exact (topologicalKrullDim_subspace_le X U).trans hX

/-- EVERY original native point on any integral locally finite-type curve is approximated by actual generic-support native points. -/
theorem dense_genericSupport_of_integral_curve (v : Valuation F ℝ≥0)
    (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f]
    (hX : topologicalKrullDim X ≤ 1) :
    Dense {y : RelativeSchemeValuedPoint v f | y.1.point = genericPoint X} := by
  intro x
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top x.1.point)
  have : Nonempty U := ⟨⟨x.1.point, hxU⟩⟩
  let A := Γ(X, U)
  let : Algebra F A := (FiniteTypePoint.affineBaseMap f hU).toAlgebra
  have : Algebra.FiniteType F A :=
    RingHom.finiteType_algebraMap.mp (FiniteTypePoint.affineBaseMap_finiteType f hU)
  have : Ring.KrullDimLE 1 A :=
    affineOpen_krullDimLE_one_of_topologicalKrullDim_le_one hX hU
  let fA := Spec.map (CommRingCat.ofHom (algebraMap F A))
  have hg : hU.fromSpec ≫ f = fA := (FiniteTypePoint.affineBaseMap_spec f hU).symm
  have hxrange : x ∈ Set.range (map (v := v) hU.fromSpec hg) := by
    rw [range_map_of_isOpenImmersion hU.fromSpec hg, hU.opensRange_fromSpec]
    exact hxU
  obtain ⟨z, rfl⟩ := hxrange
  have hz := dense_genericSupport_affine_of_dimension_le_one (C := A) v z
  have hc := mem_closure_image (continuous_map hU.fromSpec hg).continuousAt hz
  apply closure_mono ?_ hc
  rintro _ ⟨y, hy, rfl⟩
  change hU.fromSpec y.1.point = genericPoint X
  have hp : y.1.point = genericPoint (Spec (CommRingCat.of A)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hy
  rw [hp]
  exact genericPoint_eq_of_isOpenImmersion hU.fromSpec

/-- EVERY actual nonempty Zariski open of the original curve has genuinely dense native image. -/
theorem denseRange_map_open_of_integral_curve (v : Valuation F ℝ≥0)
    (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f]
    (hX : topologicalKrullDim X ≤ 1) (V : X.Opens) [Nonempty V] :
    DenseRange (map (v := v) (fX := V.ι ≫ f) V.ι rfl) := by
  apply (dense_genericSupport_of_integral_curve v f hX).mono
  intro y hy
  rw [range_map_of_isOpenImmersion V.ι rfl, Scheme.Opens.opensRange_ι]
  change y.1.point ∈ V
  rw [hy]
  exact ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr
    (by simpa using ‹Nonempty V›)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
