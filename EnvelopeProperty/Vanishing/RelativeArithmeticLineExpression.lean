import EnvelopeProperty.Vanishing.ArithmeticOriginalLineExpression

/-! # The original line is expressed over separate field and relative bases

Serre generation uses the original relative projective embedding over the
arbitrary ring R.  The same finite global generators are projectivized over
the original field k.  This retains the original line without imposing a
domain hypothesis on R or properness over k.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open Scheme.Modules
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticLineExpression
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra

/-- Actual relative Serre generators give a whole-line expression whose
generated projective morphism lies over the original field.  The original
relative base is an arbitrary commutative ring. -/
theorem exists_original_line_expression
    {k R : Type u} [Field k] [CommRing R] {d : ℕ} {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (j : X ⟶ Alterations.projectiveSpace R d)
    [hj : IsClosedImmersion j] (L : X.Modules) (hL : IsInvertible L) :
    ∃ (N b : ℕ) (h : X ⟶ Alterations.projectiveSpace k b)
      (_e : (Scheme.Modules.pullback h).obj
        (coordinateHyperplaneTwist (R := k) (0 : Fin (b + 1)) 1) ≅
          L ⊗ (Scheme.Modules.pullback j).obj
            (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) (N : ℤ)))
      (_eL : (Scheme.Modules.pullback h).obj
        (coordinateHyperplaneTwist (R := k) (0 : Fin (b + 1)) 1) ⊗
          dualObj ((Scheme.Modules.pullback j).obj
            (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) (N : ℤ))) ≅ L),
      h ≫ Alterations.projectiveSpaceStructure k b = p := by
  have hQL : L.IsQuasicoherent := hL.isQuasicoherent
  have hFP : L.IsFinitePresentation := hL.isFinitePresentation
  have hFT : L.IsFiniteType :=
    @SheafOfModules.instIsFiniteTypeOfIsFinitePresentation _ _ _ _ _ _ L hFP
  obtain ⟨N, hN⟩ :=
    @ClosedProjectiveGlobalGeneration.exists_eventual_generatingSections
      R _ (Fin (d + 1)) _ X j hj L hQL hFT (0 : Fin (d + 1))
  obtain ⟨G, hG⟩ := hN N le_rfl
  let B := (Scheme.Modules.pullback j).obj
    (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) (N : ℤ))
  have hB : IsInvertible B :=
    (coordinateHyperplaneTwist_isInvertible (0 : Fin (d + 1)) (N : ℤ)).pullback j
  have hM : IsInvertible (L ⊗ B) :=
    (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
  obtain ⟨b, h, e, hh⟩ :=
    ArithmeticOriginalLineGenerated.exists_projective_morphism p hM G hG
  exact ⟨N, b, h, e, ArithmeticOriginalLineExpression.untwistIso hB e, hh⟩

end EnvelopeProperty.Vanishing.RelativeArithmeticLineExpression
