import EnvelopeProperty.Alterations.Geometry.NodeFamilyFibres
import EnvelopeProperty.Alterations.Algebra.NodeFamilyDimension
import EnvelopeProperty.Alterations.Geometry.FiberDimension

/-!
# Node Family Dimension

Exact dimension of the actual scheme-theoretic node fibres. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Alterations.Geometry.NodeFamilyDimension

open Algebra.NodeBlowupChart NodeFamilyFlat NodeFamilyFibres

universe u

variable {A : Type u} [CommRing A]

/-- Every actual native node fibre has whole-space Krull dimension exactly one. -/
theorem nodeFiber_dimension (t : A) (p : PrimeSpectrum A) :
    FiberDimension.fiberDimension (nodeMorphism t) p = 1 := by
  unfold FiberDimension.fiberDimension
  rw [IsHomeomorph.topologicalKrullDim_eq _ (nodeFiberIso t p).hom.homeomorph.isHomeomorph]
  change topologicalKrullDim (PrimeSpectrum
    (Node p.asIdeal.ResidueField (algebraMap A p.asIdeal.ResidueField t))) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact Algebra.NodeFamilyDimension.node_ringKrullDim _ _

end Alterations.Geometry.NodeFamilyDimension
