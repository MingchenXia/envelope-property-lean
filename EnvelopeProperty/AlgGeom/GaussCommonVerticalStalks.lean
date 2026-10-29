import EnvelopeProperty.AlgGeom.GaussRegularSurfaceValuationOrders
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Stalk

/-! # The SAME original component generic stalk from every original point

The actual scheme generization map, actual component equation, and localization
universal property construct the ring comparison. No localization, DVR, norm,
valuation, or native-point comparison certificate is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open scoped Classical

universe u
namespace EnvelopeProperty.GaussCommonVerticalStalks

variable {Y : Scheme.{u}} [IsIntegral Y] {η p : Y}

/-- The original structure-sheaf map for the actual original generization. -/
def generizationMap (h : η ⤳ p) : Y.presheaf.stalk p →+* Y.presheaf.stalk η :=
  (Y.presheaf.stalkSpecializes h).hom

/-- The SAME original generic stalk is the localization under its actual map. -/
theorem generization_isLocalization (h : η ⤳ p) :
    letI : Algebra (Y.presheaf.stalk p) (Y.presheaf.stalk η) := (generizationMap h).toAlgebra
    IsLocalization.AtPrime (Y.presheaf.stalk η)
      ((maximalIdeal (Y.presheaf.stalk η)).comap (generizationMap h)) := by
  let : Algebra (Y.presheaf.stalk p) (Y.presheaf.stalk η) := (generizationMap h).toAlgebra
  let P := (maximalIdeal (Y.presheaf.stalk η)).comap (generizationMap h)
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  have hηV : η ∈ V := h.mem_open V.isOpen hpV
  let : Algebra Γ(Y,V) (Y.presheaf.stalk η) := (Y.presheaf.germ V η hηV).hom.toAlgebra
  have := hV.isLocalization_stalk ⟨η,hηV⟩
  have hcomm (a : Γ(Y,V)) :
      generizationMap h (Y.presheaf.germ V p hpV a) = Y.presheaf.germ V η hηV a := by
    exact congrArg (fun φ : Γ(Y,V) ⟶ Y.presheaf.stalk η => φ a)
      (Y.presheaf.germ_stalkSpecializes hpV h)
  have hfield : (algebraMap (Y.presheaf.stalk η) Y.functionField).comp (generizationMap h) =
      algebraMap (Y.presheaf.stalk p) Y.functionField := by
    change (Y.presheaf.stalkSpecializes h ≫ Y.presheaf.stalkSpecializes
      ((genericPoint_spec Y).specializes trivial)).hom = _
    rw [Y.presheaf.stalkSpecializes_comp]
    rfl
  have hinj : Function.Injective (generizationMap h) := by
    intro a b hab
    apply IsFractionRing.injective (Y.presheaf.stalk p) Y.functionField
    have he := congrArg (algebraMap (Y.presheaf.stalk η) Y.functionField) hab
    simpa only [← RingHom.comp_apply, hfield] using he
  change IsLocalization P.primeCompl (Y.presheaf.stalk η)
  exact {
    map_units := fun s => by
      change IsUnit (generizationMap h s)
      have hs : generizationMap h s ∉ maximalIdeal (Y.presheaf.stalk η) := s.2
      simpa only [mem_maximalIdeal, mem_nonunits_iff, not_not] using hs
    surj := fun d => by
      obtain ⟨⟨a,b⟩, hab⟩ :=
        IsLocalization.surj (hV.primeIdealOf ⟨η,hηV⟩).asIdeal.primeCompl d
      have hb : Y.presheaf.germ V p hpV b ∉ P := by
        change generizationMap h (Y.presheaf.germ V p hpV b) ∉
          maximalIdeal (Y.presheaf.stalk η)
        rw [hcomm]
        have hu := IsLocalization.map_units (Y.presheaf.stalk η) b
        change IsUnit (Y.presheaf.germ V η hηV b) at hu
        simpa only [mem_maximalIdeal, mem_nonunits_iff, not_not] using hu
      refine ⟨⟨Y.presheaf.germ V p hpV a, ⟨Y.presheaf.germ V p hpV b,hb⟩⟩,?_⟩
      change d * generizationMap h (Y.presheaf.germ V p hpV b) =
        generizationMap h (Y.presheaf.germ V p hpV a)
      change d * Y.presheaf.germ V η hηV b = Y.presheaf.germ V η hηV a at hab
      simpa only [hcomm] using hab
    exists_of_eq := fun he => by
      refine ⟨1,?_⟩
      simpa only [OneMemClass.coe_one, one_mul] using hinj he }

variable {C : Scheme.{u}} (i : C ⟶ Y) [IsClosedImmersion i] [IsIntegral C] (x : C)

omit [IsIntegral Y] [IsClosedImmersion i] in
private theorem componentSpecializes : i (genericPoint C) ⤳ i x :=
  i.base.hom.map_specializes ((genericPoint_spec C).specializes trivial)

omit [IsIntegral Y] in
/-- The original component equation identifies the actual generization prime. -/
theorem component_generizationPrime (π : Y.presheaf.stalk (i x))
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) :
    (maximalIdeal (Y.presheaf.stalk (i (genericPoint C)))).comap
      (generizationMap (componentSpecializes i x)) = Ideal.span {π} := by
  have hηker := ker_eq_maximalIdeal (i.stalkMap (genericPoint C)).hom
    (i.stalkMap_surjective (genericPoint C))
  ext s
  change generizationMap (componentSpecializes i x) s ∈
    maximalIdeal (Y.presheaf.stalk (i (genericPoint C))) ↔ s ∈ Ideal.span {π}
  rw [← hηker]
  change i.stalkMap (genericPoint C)
    (Y.presheaf.stalkSpecializes (componentSpecializes i x) s) = 0 ↔ _
  rw [i.stalkSpecializes_stalkMap_apply]
  change algebraMap (C.presheaf.stalk x) C.functionField (i.stalkMap x s) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective (C.presheaf.stalk x) C.functionField)]
  change s ∈ RingHom.ker (i.stalkMap x).hom ↔ _
  rw [hker]

/-- The SAME actual vertical localization is the SAME original component generic stalk. -/
def componentStalkEquiv (π : Y.presheaf.stalk (i x)) (hπ : Prime π)
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) :
    GaussRegularSurfaceValuationOrders.verticalRing π hπ ≃+*
      Y.presheaf.stalk (i (genericPoint C)) := by
  letI : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  letI : Algebra (Y.presheaf.stalk (i x)) (Y.presheaf.stalk (i (genericPoint C))) :=
    (generizationMap (componentSpecializes i x)).toAlgebra
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk (i (genericPoint C))) (Ideal.span {π}) := by
    simpa only [component_generizationPrime i x π hker] using
      generization_isLocalization (componentSpecializes i x)
  exact (IsLocalization.algEquiv (Ideal.span {π}).primeCompl
    (GaussRegularSurfaceValuationOrders.verticalRing π hπ)
    (Y.presheaf.stalk (i (genericPoint C)))).toRingEquiv

/-- EVERY original stalk coefficient retains its actual specialization image. -/
theorem componentStalkEquiv_coefficient (π : Y.presheaf.stalk (i x)) (hπ : Prime π)
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) (s : Y.presheaf.stalk (i x)) :
    componentStalkEquiv i x π hπ hker
      (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ s) =
      generizationMap (componentSpecializes i x) s := by
  let : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  let : Algebra (Y.presheaf.stalk (i x)) (Y.presheaf.stalk (i (genericPoint C))) :=
    (generizationMap (componentSpecializes i x)).toAlgebra
  have : IsLocalization.AtPrime (Y.presheaf.stalk (i (genericPoint C))) (Ideal.span {π}) := by
    simpa only [component_generizationPrime i x π hker] using
      generization_isLocalization (componentSpecializes i x)
  exact (IsLocalization.algEquiv (Ideal.span {π}).primeCompl
    (GaussRegularSurfaceValuationOrders.verticalRing π hπ)
    (Y.presheaf.stalk (i (genericPoint C)))).commutes s

/-- No DVR certificate on the original component generic stalk is an input. -/
theorem componentStalk_isDVR [IsNoetherianRing (Y.presheaf.stalk (i x))]
    (π : Y.presheaf.stalk (i x)) (hπ : Prime π)
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) :
    IsDiscreteValuationRing (Y.presheaf.stalk (i (genericPoint C))) := by
  let : IsDiscreteValuationRing (GaussRegularSurfaceValuationOrders.verticalRing π hπ) :=
    GaussRegularSurfaceValuationOrders.vertical_isDVR π hπ
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (componentStalkEquiv i x π hπ hker)

end EnvelopeProperty.GaussCommonVerticalStalks
