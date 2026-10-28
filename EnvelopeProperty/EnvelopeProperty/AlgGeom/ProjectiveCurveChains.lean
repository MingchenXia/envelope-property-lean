import EnvelopeProperty.AlgGeom.SchemeCurveChains
import Hironaka.Scheme.ProjectiveBundle.Defs

/-!
# Genuine projective curves in the connected scheme curve-chain theorem

Every actual closed curve in an actual projective scheme is projective by
composing its closed immersion with the original projective factorization.
Thus the general checked curve chains retain actual projective source curves.
-/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u

namespace EnvelopeProperty.FcProjectiveCurveChains

variable {C X S : Scheme.{u}}

/-- Compose the actual closed immersion with the actual original projective
factorization. The resulting morphism is projective in the full projective
bundle sense; no projectivity certificate for the curve is assumed. -/
theorem isProjective_closedImmersion_comp (i : C ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) [IsProjective f] : IsProjective (i ≫ f) := by
  obtain ⟨E, hE, hEt, j, hj, hjf⟩ := (inferInstance : IsProjective f).exists_isClosedImmersion
  have : IsClosedImmersion j := hj
  constructor
  refine ⟨E, hE, hEt, i ≫ j, inferInstance, ?_⟩
  rw [Category.assoc, hjf]

/-- An actual closed integral curve of global dimension one in the original
scheme, with an actual projective structure over the original base. -/
def ProjectiveCurveStep (f : X ⟶ S) (x y : X) : Prop :=
  ∃ (C : Scheme.{u}) (i : C ⟶ X), IsClosedImmersion i ∧ IsIntegral C ∧
    topologicalKrullDim C = 1 ∧ IsProjective (i ≫ f) ∧ x ∈ Set.range i ∧ y ∈ Set.range i

/-- A genuine finite chain of actual projective irreducible closed curves. -/
def ProjectiveCurveChain (f : X ⟶ S) (x y : X) : Prop :=
  Relation.ReflTransGen (ProjectiveCurveStep f) x y

theorem projectiveCurveStep_of_curveStep (f : X ⟶ S) [IsProjective f]
    {x y : X} (hxy : FcSchemeCurveChains.CurveStep x y) : ProjectiveCurveStep f x y := by
  obtain ⟨C, i, hi, hC, hd, hx, hy⟩ := hxy
  have : IsClosedImmersion i := hi
  exact ⟨C, i, hi, hC, hd, isProjective_closedImmersion_comp i f, hx, hy⟩

theorem projectiveCurveChain_of_curveChain (f : X ⟶ S) [IsProjective f]
    {x y : X} (hxy : FcSchemeCurveChains.CurveChain x y) : ProjectiveCurveChain f x y := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _hxy hyz ih => exact ih.tail (projectiveCurveStep_of_curveStep f hyz)

/-- The complete projective clause of the source curve-chain theorem: every
two closed points of an actual connected projective finite-type scheme over an
algebraically closed field are joined by ACTUAL projective closed integral
curves of entire global dimension one in that ORIGINAL scheme. -/
theorem projectiveCurveChain_of_connected_finiteType
    {F : Type u} [Field F] [IsAlgClosed F] (f : X ⟶ Spec (CommRingCat.of F))
    [FiniteType f] [IsProjective f] [PreconnectedSpace X]
    (x y : X) (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set X)) :
    ProjectiveCurveChain f x y := by
  exact projectiveCurveChain_of_curveChain f
    (FcSchemeCurveChains.curveChain_of_connected_finiteType f x y hx hy)

end EnvelopeProperty.FcProjectiveCurveChains
