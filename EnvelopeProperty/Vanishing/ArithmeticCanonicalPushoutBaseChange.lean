import EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutDifferential

/-! # The universal-square map is the original arithmetic fibre differential -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutDifferential

open CanonicalGeometry ArithmeticCanonicalGlobal

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

theorem fiberCoefficientSquare :
    CoefficientSquare (CommRingCat.ofHom (algebraMap R S)) f
      (ArithmeticCanonicalGlobalBaseChange.fiberStructure S f)
      (ArithmeticCanonicalGlobalBaseChange.fiberProjection S f) :=
  ArithmeticCanonicalGlobalBaseChange.fiberConstantsSquare S f

/-- The raw comparison is equality of the original universal maps. -/
theorem cotangentPresheafMap_baseChange :
    cotangentPresheafMap (CommRingCat.ofHom (algebraMap R S)) f
        (ArithmeticCanonicalGlobalBaseChange.fiberStructure S f)
        (ArithmeticCanonicalGlobalBaseChange.fiberProjection S f)
        (fiberCoefficientSquare S f) =
      ArithmeticCanonicalGlobalBaseChange.cotangentPresheafMap S f := by
  apply (relativePresheafHomEquiv f _).injective
  ext U a
  exact (cotangentPresheafMap_d (CommRingCat.ofHom (algebraMap R S)) f
    (ArithmeticCanonicalGlobalBaseChange.fiberStructure S f)
    (ArithmeticCanonicalGlobalBaseChange.fiberProjection S f)
    (fiberCoefficientSquare S f) U.unop a).trans
      (ArithmeticCanonicalGlobalBaseChange.cotangentPresheafMap_d S f U.unop a).symm

theorem exteriorPresheafMap_baseChange (q : ℕ) :
    exteriorPresheafMap (CommRingCat.ofHom (algebraMap R S)) f
        (ArithmeticCanonicalGlobalBaseChange.fiberStructure S f)
        (ArithmeticCanonicalGlobalBaseChange.fiberProjection S f)
        (fiberCoefficientSquare S f) q =
      ArithmeticCanonicalGlobalBaseChange.exteriorPresheafMap S f q := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.Hom.ext
  apply LinearMap.ext_on (exteriorPower.ιMulti_span
    (X.presheaf.obj U) q ((relativeCotangentPresheaf f).obj U))
  rintro _ ⟨m, rfl⟩
  have h₁ := exteriorComponent_wedge (CommRingCat.ofHom (algebraMap R S)) f
    (ArithmeticCanonicalGlobalBaseChange.fiberStructure S f)
    (ArithmeticCanonicalGlobalBaseChange.fiberProjection S f)
    (fiberCoefficientSquare S f) q U m
  have h₂ := ArithmeticCanonicalGlobalBaseChange.exteriorComponent_wedge S f q U m
  refine h₁.trans (Eq.trans ?_ h₂.symm)
  congr 1

/-- Both actual sheafification units give the same whole fibre map. -/
theorem exteriorSheafPushMap_baseChange (q : ℕ) :
    exteriorSheafPushMap (CommRingCat.ofHom (algebraMap R S)) f
        (ArithmeticCanonicalGlobalBaseChange.fiberStructure S f)
        (ArithmeticCanonicalGlobalBaseChange.fiberProjection S f)
        (fiberCoefficientSquare S f) q =
      ArithmeticCanonicalGlobalBaseChange.exteriorSheafPushMap S f q := by
  unfold exteriorSheafPushMap ArithmeticCanonicalGlobalBaseChange.exteriorSheafPushMap
  rw [exteriorPresheafMap_baseChange]

/-- The whole map is the same native adjoint, not an isomorphic replacement. -/
theorem exteriorPullbackMap_baseChange (q : ℕ) :
    exteriorPullbackMap (CommRingCat.ofHom (algebraMap R S)) f
        (ArithmeticCanonicalGlobalBaseChange.fiberStructure S f)
        (ArithmeticCanonicalGlobalBaseChange.fiberProjection S f)
        (fiberCoefficientSquare S f) q =
      ArithmeticCanonicalGlobalBaseChange.exteriorPullbackMap S f q := by
  unfold exteriorPullbackMap ArithmeticCanonicalGlobalBaseChange.exteriorPullbackMap
  rw [exteriorSheafPushMap_baseChange]

end EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutDifferential
