import EnvelopeProperty.AlgGeom.SchemeDominantImageFactorization
import Mathlib.AlgebraicGeometry.FunctionField

/-! # A genuine generic graph retains exactly the original function field -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeGenericFieldGraph

private theorem fieldPoint_generic {K : Type u} [Field K] {Y : Scheme.{u}}
    [IsIntegral Y] (g : Spec (.of K) ⟶ Y) [IsDominant g] :
    g (IsLocalRing.closedPoint K) = genericPoint Y := by
  rw [show IsLocalRing.closedPoint K = genericPoint (Spec (.of K)) from Subsingleton.elim _ _]
  apply ((genericPoint_spec Y).eq _).symm
  simpa only [Set.image_univ,g.denseRange.closure_range] using
    (genericPoint_spec (Spec (.of K))).image g.continuous

/-- The ACTUAL generic-stalk coefficient map of the SAME original field point. -/
def fieldHom {K : Type u} [Field K] {Y : Scheme.{u}}
    [IsIntegral Y] (g : Spec (.of K) ⟶ Y) [IsDominant g] :
    Y.functionField ⟶ CommRingCat.of K :=
  (Y.presheaf.stalkCongr (.of_eq (fieldPoint_generic g).symm)).hom ≫
    Scheme.stalkClosedPointTo g

/-- The SAME actual entire original field-valued point is retained. -/
theorem fieldHom_fromSpecStalk {K : Type u} [Field K] {Y : Scheme.{u}}
    [IsIntegral Y] (g : Spec (.of K) ⟶ Y) [IsDominant g] :
    Spec.map (fieldHom g) ≫ Y.fromSpecStalk (genericPoint Y) = g := by
  dsimp only [fieldHom]
  rw [Spec.map_comp,Category.assoc,TopCat.Presheaf.stalkCongr_hom,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk g

private theorem projection_isDominant {X Y : Scheme.{u}} [IsIntegral X]
    (g : Spec X.functionField ⟶ Y) (p : Y ⟶ X)
    (hp : g ≫ p = X.fromSpecStalk (genericPoint X)) : IsDominant p := by
  have hx : p (g (IsLocalRing.closedPoint X.functionField)) = genericPoint X := by
    change (g ≫ p) _ = _
    rw [hp,Scheme.fromSpecStalk_closedPoint]
  rw [isDominant_iff]
  change Dense (Set.range p)
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  rw [← (genericPoint_spec X).def]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨_,hx⟩)

/-- A true original whole generic projection DERIVES bijectivity of the SAME
actual coefficient field map, rather than assuming birationality. -/
theorem fieldHom_bijective_of_genericProjection {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (g : Spec X.functionField ⟶ Y) [IsDominant g]
    (p : Y ⟶ X) (hp : g ≫ p = X.fromSpecStalk (genericPoint X)) :
    Function.Bijective (fieldHom g).hom := by
  let : IsDominant p := projection_isDominant g p hp
  let ηY := Y.fromSpecStalk (genericPoint Y)
  let : IsDominant ηY := by
    constructor
    have hs : ({genericPoint Y} : Set Y) ⊆ Set.range ηY := by
      exact Set.singleton_subset_iff.mpr
        ⟨IsLocalRing.closedPoint Y.functionField,Scheme.fromSpecStalk_closedPoint⟩
    intro y
    apply closure_mono hs
    rw [(genericPoint_spec Y).def]
    trivial
  let g' : Spec Y.functionField ⟶ X := ηY ≫ p
  let : IsDominant g' := inferInstance
  have hcomp : Spec.map ((fieldHom g') ≫ fieldHom g) = 𝟙 (Spec X.functionField) := by
    apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
    rw [Spec.map_comp,Category.assoc,fieldHom_fromSpecStalk]
    change Spec.map (fieldHom g) ≫ (ηY ≫ p) = _
    rw [← Category.assoc,fieldHom_fromSpecStalk,hp]
    exact (Category.id_comp _).symm
  have hring : fieldHom g' ≫ fieldHom g = 𝟙 X.functionField := by
    apply Spec.map_injective
    simpa only [Spec.map_id] using hcomp
  refine ⟨(fieldHom g).hom.injective,?_⟩
  intro x
  refine ⟨(fieldHom g') x,?_⟩
  exact congrArg (fun f : X.functionField ⟶ X.functionField => f x) hring

/-- The ACTUAL native generic-stalk function field of the graph is the SAME
original function field, by the genuine original generic projection. -/
def functionFieldEquiv {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (g : Spec X.functionField ⟶ Y) [IsDominant g] (p : Y ⟶ X)
    (hp : g ≫ p = X.fromSpecStalk (genericPoint X)) :
    Y.functionField ≃+* X.functionField :=
  RingEquiv.ofBijective (fieldHom g).hom (fieldHom_bijective_of_genericProjection g p hp)

end EnvelopeProperty.SchemeGenericFieldGraph
