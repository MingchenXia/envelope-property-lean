import EnvelopeProperty.AlgGeom.NativeRealNumericalClasses
import EnvelopeProperty.AlgGeom.NativeRealPicardOperations

/-! # Actual original numerical line arithmetic and genuine simultaneously generated representatives -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.NativeRealNumericalClasses
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]

private theorem tensorInvertible {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) : IsInvertible (L ⊗ M) :=
  (hL.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso L M)

/-- The SAME actual WHOLE original line isomorphism preserves its actual numerical class. -/
theorem lineClass_eq_of_iso {L M : X.Modules} (hL : IsInvertible L) (hM : IsInvertible M) (e : L ≅ M) :
    lineClass p L hL = lineClass p M hM :=
  congrArg (projection p) (NativeRealPicard.lineClass_eq_of_iso hL hM e)

/-- The SAME original unit line has zero in the SAME original actual numerical quotient. -/
@[simp]
theorem lineClass_unit : lineClass p (unitObj X) (isInvertible_unit (X := X)) = 0 := by
  change projection p (NativeRealPicard.lineClass _ _) = 0
  rw [NativeRealPicard.lineClass_unit, map_zero]

/-- The SAME original actual tensor product is genuine addition of original numerical classes. -/
theorem lineClass_tensor (L M : X.Modules) (hL : IsInvertible L) (hM : IsInvertible M) :
    lineClass p (L ⊗ M) (tensorInvertible hL hM) = lineClass p L hL + lineClass p M hM := by
  exact (congrArg (projection p) (NativeRealPicard.lineClass_tensor L M hL hM)).trans
    ((projection p).map_add _ _)

/-- The SAME original actual dual gives the genuine negative original numerical class. -/
theorem lineClass_dual (L : X.Modules) (hL : IsInvertible L) :
    lineClass p (dualObj L) hL.dual = -lineClass p L hL := by
  exact (congrArg (projection p) (NativeRealPicard.lineClass_dual L hL)).trans
    ((projection p).map_neg _)

/-- Every WHOLE actual original quotient-of-lines isomorphism gives EXACT original numerical subtraction. -/
theorem lineClass_quotient {L M T : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) (hT : IsInvertible T) (e : L ≅ M ⊗ dualObj T) :
    lineClass p L hL = lineClass p M hM - lineClass p T hT := by
  exact (congrArg (projection p) (NativeRealPicard.lineClass_quotient hL hM hT e)).trans
    ((projection p).map_sub _ _)

/-- EVERY actual original numerical class has internally produced finite original line
representatives with ONE actual common denominator and ALL actual numerator/denominator
finite global generators. No generation or desired numerical-family certificate is supplied. -/
theorem exists_simultaneous_generated_line_sum (θ : Space p) :
    ∃ s : Finset {L : X.Modules // IsInvertible L},
      ∃ a : {L : X.Modules // IsInvertible L} → ℝ,
        ∃ T : X.Modules, ∃ hT : IsInvertible T, ∃ H : T.GeneratingSections,
          H.IsFiniteType ∧
            (∀ L ∈ s, ∃ G : (L.val ⊗ T).GeneratingSections, G.IsFiniteType) ∧
              θ = ∑ L ∈ s, a L •
                (lineClass p (L.val ⊗ T) (tensorInvertible L.property hT) - lineClass p T hT) := by
  classical
  obtain ⟨s, a, hθ⟩ := exists_finite_line_sum p θ
  obtain ⟨T, hT, H, hH, h⟩ := ProjectiveGeneratedLineClasses.exists_simultaneous_generated_quotients p
    (ProjectiveFactorizationRingIso.of_isProjective p)
    (fun L : s => L.val.val) (fun L => L.val.property)
  refine ⟨s, a, T, hT, H, hH, ?_, ?_⟩
  · intro L hLs
    obtain ⟨G, hG, _⟩ := h ⟨L, hLs⟩
    exact ⟨G, hG⟩
  · rw [hθ]
    apply Finset.sum_congr rfl
    intro L hLs
    obtain ⟨_, _, ⟨e⟩⟩ := h ⟨L, hLs⟩
    exact congrArg (fun z => a L • z)
      (lineClass_quotient p L.property (tensorInvertible L.property hT) hT e)

end EnvelopeProperty.NativeRealNumericalClasses
