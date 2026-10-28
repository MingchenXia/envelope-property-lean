/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeGaussScalarLifts
import EnvelopeProperty.Berkovich.CompleteAlgebraicClosure

/-!
# An actual nontrivial complete algebraically closed scalar extension

The radius-one-half original Gauss completed residue field and its actual
completed algebraic closure give a genuine field extension in the original
universe, with every original norm preserved and an explicit element of norm2.
-/

open scoped Classical NNReal Polynomial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable (F : Type u) [NormedField F] [IsUltrametricDist F]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual Gauss completed coefficient extension is normed over its original field. -/
instance fcGaussFieldNormedAlgebra (r : ℝ≥0) :
    NormedAlgebra F (fcGaussField (NormedField.valuation (K := F)) r) where
  norm_smul_le c a := by
    rw [Algebra.smul_def, norm_mul]
    have hc : ‖algebraMap F (fcGaussField (NormedField.valuation (K := F)) r) c‖ = ‖c‖ :=
      congrArg (fun q : ℝ≥0 => (q : ℝ))
        (fcGaussField_val_algebraMap (NormedField.valuation (K := F)) r c)
    rw [hc]

/-- The actual completed algebraic closure of the original radius-one-half Gauss field. -/
def fcNontrivialScalarField : Type u :=
  EnvelopeProperty.CompleteAlgebraicClosure (fcGaussField (NormedField.valuation (K := F)) (1 / 2))

instance fcNontrivialScalarFieldNormed : NormedField (fcNontrivialScalarField F) :=
  inferInstanceAs (NormedField (EnvelopeProperty.CompleteAlgebraicClosure
    (fcGaussField (NormedField.valuation (K := F)) (1 / 2))))

instance fcNontrivialScalarFieldComplete : CompleteSpace (fcNontrivialScalarField F) :=
  inferInstanceAs (CompleteSpace (EnvelopeProperty.CompleteAlgebraicClosure
    (fcGaussField (NormedField.valuation (K := F)) (1 / 2))))

instance fcNontrivialScalarFieldUltrametric : IsUltrametricDist (fcNontrivialScalarField F) :=
  inferInstanceAs (IsUltrametricDist (EnvelopeProperty.CompleteAlgebraicClosure
    (fcGaussField (NormedField.valuation (K := F)) (1 / 2))))

instance fcNontrivialScalarFieldAlgClosed : IsAlgClosed (fcNontrivialScalarField F) :=
  inferInstanceAs (IsAlgClosed (EnvelopeProperty.CompleteAlgebraicClosure
    (fcGaussField (NormedField.valuation (K := F)) (1 / 2))))

instance fcNontrivialScalarFieldGaussAlgebra :
    Algebra (fcGaussField (NormedField.valuation (K := F)) (1 / 2)) (fcNontrivialScalarField F) :=
  inferInstanceAs (Algebra (fcGaussField (NormedField.valuation (K := F)) (1 / 2))
    (EnvelopeProperty.CompleteAlgebraicClosure
      (fcGaussField (NormedField.valuation (K := F)) (1 / 2))))

instance fcNontrivialScalarFieldGaussNormedAlgebra :
    NormedAlgebra (fcGaussField (NormedField.valuation (K := F)) (1 / 2)) (fcNontrivialScalarField F) :=
  inferInstanceAs (NormedAlgebra (fcGaussField (NormedField.valuation (K := F)) (1 / 2))
    (EnvelopeProperty.CompleteAlgebraicClosure
      (fcGaussField (NormedField.valuation (K := F)) (1 / 2))))

instance fcNontrivialScalarFieldAlgebra : Algebra F (fcNontrivialScalarField F) :=
  ((algebraMap (fcGaussField (NormedField.valuation (K := F)) (1 / 2)) (fcNontrivialScalarField F)).comp
    (algebraMap F (fcGaussField (NormedField.valuation (K := F)) (1 / 2)))).toAlgebra

instance fcNontrivialScalarFieldTower :
    IsScalarTower F (fcGaussField (NormedField.valuation (K := F)) (1 / 2)) (fcNontrivialScalarField F) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The actual composite field extension preserves every original coefficient norm. -/
theorem fcNontrivialScalarField_val_algebraMap (c : F) :
    NormedField.valuation (K := fcNontrivialScalarField F)
      (algebraMap F (fcNontrivialScalarField F) c) = NormedField.valuation (K := F) c := by
  change ‖algebraMap (fcGaussField (NormedField.valuation (K := F)) (1 / 2)) (fcNontrivialScalarField F)
    (algebraMap F (fcGaussField (NormedField.valuation (K := F)) (1 / 2)) c)‖₊ = ‖c‖₊
  rw [nnnorm_algebraMap']
  exact fcGaussField_val_algebraMap (NormedField.valuation (K := F)) (1 / 2) c

instance fcNontrivialScalarFieldNormedAlgebra : NormedAlgebra F (fcNontrivialScalarField F) where
  norm_smul_le c a := by
    rw [Algebra.smul_def, norm_mul]
    have hc : ‖algebraMap F (fcNontrivialScalarField F) c‖ = ‖c‖ :=
      congrArg (fun q : ℝ≥0 => (q : ℝ)) (fcNontrivialScalarField_val_algebraMap F c)
    rw [hc]

/-- The inverse original Gauss coordinate gives an explicit element of norm2. -/
theorem fcNontrivialScalarField_exists_one_lt_norm :
    ∃ c : fcNontrivialScalarField F, 1 < ‖c‖ := by
  refine ⟨(algebraMap (fcGaussField (NormedField.valuation (K := F)) (1 / 2))
    (fcNontrivialScalarField F)
    (Spectrum.toH (fcGaussBasePoint (NormedField.valuation (K := F)) (1 / 2)).1 Polynomial.X))⁻¹, ?_⟩
  rw [norm_inv, norm_algebraMap']
  rw [Spectrum.norm_toH]
  have hX : (fcGaussBasePoint (NormedField.valuation (K := F)) (1 / 2)).1.val Polynomial.X =
      (1 / 2 : ℝ≥0) := gauss_val_X (self (NormedField.valuation (K := F))) (1 / 2)
  rw [hX]
  norm_num

/-- The same constructed field carries the genuine nontrivially normed field
structure, retaining exactly its previously defined original norm. -/
instance fcNontrivialScalarFieldNontriviallyNormed : NontriviallyNormedField (fcNontrivialScalarField F) := by
  let c := (fcNontrivialScalarField_exists_one_lt_norm F).choose
  have hc : 1 < ‖c‖ := (fcNontrivialScalarField_exists_one_lt_norm F).choose_spec
  exact NontriviallyNormedField.ofNormNeOne ⟨c,
    (norm_pos_iff.mp (lt_trans zero_lt_one hc)), ne_of_gt hc⟩

/-- The genuinely valued algebraic closure remains algebraic over its
original complete base field, by the actual coefficient-preserving WithAbs equivalence. -/
instance fcValuedAlgebraicClosure_isAlgebraic
    (K : Type u) [NormedField K] [CompleteSpace K] [IsUltrametricDist K] :
    Algebra.IsAlgebraic K (EnvelopeProperty.ValuedAlgebraicClosure K) := by
  let e : EnvelopeProperty.ValuedAlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    WithAbs.algEquiv K _
  exact Algebra.IsAlgebraic.of_injective e.toAlgHom e.injective

end EnvelopeProperty.Berkovich.RelativeSpectrum
