import EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutSquare
import EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutBaseChange

/-! # The original map of arithmetic fibres under an open immersion -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutOpenCompatibility

open ArithmeticCanonicalGlobal ArithmeticCanonicalGlobalBaseChange

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    {X V : Scheme.{u}} (f : X ⟶ Spec (.of R)) (g : V ⟶ X)

/-- The genuine map between the two original categorical arithmetic fibres. -/
def fiberMap : fiberScheme S (g ≫ f) ⟶ fiberScheme S f :=
  Limits.pullback.map (g ≫ f) (baseMap (R := R) S) f (baseMap (R := R) S)
    g (𝟙 _) (𝟙 _) (by simp) (by simp)

theorem fiberMap_fst :
    fiberMap S f g ≫ fiberProjection S f = fiberProjection S (g ≫ f) ≫ g := by
  simp [fiberMap, fiberProjection, Limits.pullback.map]

theorem fiberMap_snd :
    fiberMap S f g ≫ fiberStructure S f = fiberStructure S (g ≫ f) := by
  simp [fiberMap, fiberStructure, Limits.pullback.map]

/-- The original square over the open immersion is itself cartesian. -/
theorem fiberMap_isPullback :
    IsPullback (fiberProjection S (g ≫ f)) (fiberMap S f g) g (fiberProjection S f) := by
  have houter : IsPullback (fiberProjection S (g ≫ f))
      (fiberMap S f g ≫ fiberStructure S f) (g ≫ f) (baseMap (R := R) S) := by
    rw [fiberMap_snd]
    exact IsPullback.of_hasPullback _ _
  exact houter.of_bot (fiberMap_fst S f g).symm (IsPullback.of_hasPullback _ _)

instance [IsOpenImmersion g] : IsOpenImmersion (fiberMap S f g) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (fiberMap_isPullback S f g)
    (inferInstance : IsOpenImmersion g)

/-- The source comparison retains both original projections and the actual
native composition and equality isomorphisms. -/
def sourceCompIso (q : ℕ) :
    (Scheme.Modules.pullback (fiberMap S f g)).obj
        ((Scheme.Modules.pullback (fiberProjection S f)).obj (relativeExteriorSheaf f q)) ≅
      (Scheme.Modules.pullback (fiberProjection S (g ≫ f))).obj
        ((Scheme.Modules.pullback g).obj (relativeExteriorSheaf f q)) :=
  (Scheme.Modules.pullbackComp (fiberMap S f g) (fiberProjection S f)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (fiberMap_fst S f g)).app _ ≪≫
      ((Scheme.Modules.pullbackComp (fiberProjection S (g ≫ f)) g).app _).symm

/-- The target comparison uses the actual open pullback and the original
second-projection equation, without changing the fibre structure. -/
def targetOpenIso [IsOpenImmersion g] (q : ℕ) :
    (Scheme.Modules.pullback (fiberMap S f g)).obj
        (relativeExteriorSheaf (fiberStructure S f) q) ≅
      relativeExteriorSheaf (fiberStructure S (g ≫ f)) q :=
  ArithmeticCanonicalGlobalRestriction.exteriorPullbackIso
      (fiberStructure S f) (fiberMap S f g) q ≪≫
    eqToIso (congrArg (fun h => relativeExteriorSheaf h q) (fiberMap_snd S f g))

theorem fiberOpenCoefficientSquare :
    ArithmeticCanonicalPushoutDifferential.CoefficientSquare (𝟙 (CommRingCat.of S))
      (fiberStructure S f) (fiberStructure S (g ≫ f)) (fiberMap S f g) := by
  apply ArithmeticCanonicalPushoutDifferential.coefficientSquare_of_structuralSquare
  simpa using fiberMap_snd S f g

end EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutOpenCompatibility
