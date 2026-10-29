import EnvelopeProperty.Vanishing.ArithmeticOriginalLineGenerated
import EnvelopeProperty.AlgGeom.ClosedProjectiveGlobalGeneration
import EnvelopeProperty.AlgGeom.CartierDualEvaluation
import ModularCurves.Picard.InvertibleSheafLocallyFree

/-! # A projective expression for the actual original line

Finite generation is derived on the actual original closed projective scheme.
The resulting two-twist expression retains L itself, without replacing it by
any positive tensor power.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open Scheme.Modules
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLineExpression
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] [IsDomain R]

/-- Tensor cancellation uses the genuine original dual evaluation, with no
supplied inverse line or cancellation certificate. -/
def untwistIso {X : Scheme.{u}} {A L B : X.Modules}
    (hB : IsInvertible B) (e : A ≅ L ⊗ B) : A ⊗ dualObj B ≅ L :=
  (e ⊗ᵢ Iso.refl (dualObj B)) ≪≫ α_ L B (dualObj B) ≪≫
    (Iso.refl L ⊗ᵢ hB.monoidalEvaluationIso) ≪≫ ρ_ L

/-- An original invertible line on the original closed projective scheme has
an actual two-projective-twist expression; the original line is not powered.
The generated morphism and both comparison isomorphisms are constructed. -/
theorem exists_original_line_expression {d : ℕ} {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (j : X ⟶ Alterations.projectiveSpace R d)
    [IsClosedImmersion j] (L : X.Modules) (hL : IsInvertible L) :
    ∃ (N b : ℕ) (g : X ⟶ Alterations.projectiveSpace R b)
      (_e : (Scheme.Modules.pullback g).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (b + 1)) 1) ≅
          L ⊗ (Scheme.Modules.pullback j).obj
            (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) (N : ℤ)))
      (_eL : (Scheme.Modules.pullback g).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (b + 1)) 1) ⊗
          dualObj ((Scheme.Modules.pullback j).obj
            (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) (N : ℤ))) ≅ L),
      g ≫ Alterations.projectiveSpaceStructure R b = p := by
  let : L.IsQuasicoherent := hL.isQuasicoherent
  let : L.IsFinitePresentation := hL.isFinitePresentation
  let : L.IsFiniteType := inferInstance
  obtain ⟨N, hN⟩ := ClosedProjectiveGlobalGeneration.exists_eventual_generatingSections
    j L (0 : Fin (d + 1))
  obtain ⟨G, hG⟩ := hN N le_rfl
  let B := (Scheme.Modules.pullback j).obj
    (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) (N : ℤ))
  have hB : IsInvertible B :=
    (coordinateHyperplaneTwist_isInvertible (0 : Fin (d + 1)) (N : ℤ)).pullback j
  have hM : IsInvertible (L ⊗ B) :=
    (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
  obtain ⟨b, g, e, hg⟩ := ArithmeticOriginalLineGenerated.exists_projective_morphism p hM G hG
  exact ⟨N, b, g, e, untwistIso hB e, hg⟩

end EnvelopeProperty.Vanishing.ArithmeticOriginalLineExpression
