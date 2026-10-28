import EnvelopeProperty.AlgGeom.ProjectiveCurveChains
import EnvelopeProperty.Berkovich.SchemeFiniteTypeSurjective

/-! # Actual closed curve-chain intermediates and genuine original native support lifts -/

open scoped NNReal Classical Topology
open Topology CategoryTheory AlgebraicGeometry
noncomputable section
universe u

namespace EnvelopeProperty.FcProjectiveCurveChains

variable {F : Type u} [Field F] {X : Scheme.{u}}

/-- The original chain constructs a chain through actual CLOSED original
points, retaining the same genuine projective curve witnesses. -/
theorem closed_chain_of_projectiveCurveChain
    (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f]
    {x y : X} (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set X))
    (h : ProjectiveCurveChain f x y) :
    Relation.ReflTransGen
      (fun a b => ProjectiveCurveStep f a b ∧ IsClosed ({a} : Set X) ∧ IsClosed ({b} : Set X)) x y := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have aux (z : X) (hz : ProjectiveCurveChain f x z) : ∀ w ∈ closure ({z} : Set X),
      IsClosed ({w} : Set X) → Relation.ReflTransGen
        (fun a b => ProjectiveCurveStep f a b ∧ IsClosed ({a} : Set X) ∧ IsClosed ({b} : Set X)) x w := by
    induction hz with
    | refl =>
      intro w hw _
      have hwx : w = x := Set.mem_singleton_iff.mp (hx.closure_eq ▸ hw)
      subst w
      exact Relation.ReflTransGen.refl
    | @tail z t _ hzt ih =>
      intro w hw hwc
      obtain ⟨v, hv, hvc⟩ := nonempty_inter_closedPoints
        (show (closure ({z} : Set X)).Nonempty from ⟨z, subset_closure (by simp)⟩)
        isClosed_closure.isLocallyClosed
      obtain ⟨C, i, hi, hC, hd, hp, hzC, htC⟩ := hzt
      have : IsClosedImmersion i := hi
      have hzc : closure ({z} : Set X) ⊆ Set.range i :=
        closure_minimal (Set.singleton_subset_iff.mpr hzC) i.isClosedEmbedding.isClosed_range
      have htc : closure ({t} : Set X) ⊆ Set.range i :=
        closure_minimal (Set.singleton_subset_iff.mpr htC) i.isClosedEmbedding.isClosed_range
      exact (ih v hv hvc).tail ⟨⟨C, i, hi, hC, hd, hp, hzc hv, htc hw⟩, hvc, hwc⟩
  exact aux y h y (subset_closure (by simp)) hy

/-- Connected original projective finite-type schemes construct actual
projective curve chains with every original intermediate point closed. -/
theorem closed_projectiveCurveChain_of_connected_finiteType
    [IsAlgClosed F] (f : X ⟶ Spec (CommRingCat.of F))
    [FiniteType f] [IsProjective f] [PreconnectedSpace X]
    (x y : X) (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set X)) :
    Relation.ReflTransGen
      (fun a b => ProjectiveCurveStep f a b ∧ IsClosed ({a} : Set X) ∧ IsClosed ({b} : Set X)) x y :=
  closed_chain_of_projectiveCurveChain f hx hy
    (projectiveCurveChain_of_connected_finiteType f x y hx hy)

end EnvelopeProperty.FcProjectiveCurveChains

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {F : Type u} [NormedField F] [IsUltrametricDist F] {X : Scheme.{u}}

/-- The literal singleton closed subscheme and the actual whole native lift
theorem construct a prescribed-base point at any original closed support. -/
theorem exists_nativePoint_of_isClosed_support
    (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ y : RelativeSchemeValuedPoint (NormedField.valuation (K := F)) f, y.1.point = x := by
  let Z : TopologicalSpace.Closeds X := ⟨{x}, hx⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hxI : x ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact Set.mem_singleton x
  obtain ⟨z, hz⟩ := hxI
  let g := I.subschemeι ≫ f
  have hs : Function.Surjective g := by
    intro p
    exact ⟨z, Subsingleton.elim _ _⟩
  let v := NormedField.valuation (K := F)
  let b : RelativeSchemeValuedPoint v (𝟙 (Spec (CommRingCat.of F))) :=
    ⟨SchemeValuedPoint.basePoint v, SchemeValuedPoint.map_id _⟩
  obtain ⟨y, _⟩ := map_surjective_of_locallyOfFiniteType
    (fX := g) (fY := 𝟙 (Spec (CommRingCat.of F))) g
    (by simp only [Category.comp_id, g]) hs b
  refine ⟨map (fX := g) (fY := f) I.subschemeι rfl y, ?_⟩
  have hpoint : I.subschemeι y.1.point ∈ Set.range I.subschemeι := ⟨_, rfl⟩
  rw [I.range_subschemeι] at hpoint
  exact Set.mem_singleton_iff.mp hpoint

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
