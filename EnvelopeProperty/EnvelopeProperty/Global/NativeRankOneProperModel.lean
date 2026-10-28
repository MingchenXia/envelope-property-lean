import EnvelopeProperty.Global.NativeRankOneChartComparison
import EnvelopeProperty.Global.SmoothModelEP
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! # The SAME original rank-one native model is proper over its original field

The degree-zero result used from SmoothModelEP itself has only original
algebraic closedness/model hypotheses; no smooth envelope or resolution
assumption is used here.
-/
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.MultiModel
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

private local instance nativeRankOneZeroTower : IsScalarTower k (X.nativeTotalGrading 0) X.S where
  smul_assoc a b p := by
    change (a • (b : X.S)) * p = a • ((b : X.S) * p)
    exact smul_mul_assoc a (b : X.S) p

/-- Original finite generation derives finite generation over the actual degree-zero ring. -/
theorem nativeRankOne_finiteType_zero : Algebra.FiniteType (X.nativeTotalGrading 0) X.S := by
  let : Algebra.FiniteType k X.S := (Subalgebra.fg_iff_finiteType X.S).mp X.fg
  exact Algebra.FiniteType.of_restrictScalars_finiteType k (X.nativeTotalGrading 0) X.S

/-- The SAME original field inclusion into native degree zero is injective. -/
theorem nativeRankOneCoefficients_injective : Function.Injective X.nativeRankOneCoefficients := by
  intro a b hab
  apply FaithfulSMul.algebraMap_injective k (MvPolynomial (Fin 1) K)
  exact congrArg (fun z : X.nativeTotalGrading 0 => ((z : X.S) : MvPolynomial (Fin 1) K)) hab

/-- Actual original degree zero is the original coefficient field, by original M2 and algebraic closedness. -/
theorem nativeRankOneCoefficients_surjective [IsAlgClosed k] :
    Function.Surjective X.nativeRankOneCoefficients := by
  intro z
  let f : K := (((z : X.S) : MvPolynomial (Fin 1) K).coeff 0)
  have hp : ((z : X.S) : MvPolynomial (Fin 1) K) = monomial 0 f := by
    simpa only [Finsupp.single_zero] using rankOne_homogeneous_eq_monomial 0
      ((z : X.S) : MvPolynomial (Fin 1) K) ((X.mem_nativeTotalGrading 0 _).mp z.property)
  have hf : f ∈ X.piece 0 := by
    change monomial 0 f ∈ X.S
    rw [← hp]
    exact (z : X.S).property
  obtain ⟨a, ha⟩ := X.exists_algebraMap_eq_of_mem_piece_zero hf
  refine ⟨a, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change algebraMap k (MvPolynomial (Fin 1) K) a = ((z : X.S) : MvPolynomial (Fin 1) K)
  rw [MvPolynomial.algebraMap_apply, ha, hp, MvPolynomial.C_apply]

/-- This actual whole ring isomorphism has the SAME original coefficient inclusion as its forward map. -/
def nativeRankOneCoefficientEquiv [IsAlgClosed k] : k ≃+* X.nativeTotalGrading 0 :=
  RingEquiv.ofBijective X.nativeRankOneCoefficients
    ⟨X.nativeRankOneCoefficients_injective, X.nativeRankOneCoefficients_surjective⟩

/-- Native Proj is genuinely proper over its actual original degree-zero ring. -/
theorem nativeRankOne_toSpecZero_isProper : IsProper (Proj.toSpecZero X.nativeTotalGrading) := by
  let := X.nativeRankOne_finiteType_zero
  infer_instance

/-- The SAME original rank-one structure morphism is actually proper over the original field. -/
instance nativeRankOneStructure_isProper [IsAlgClosed k] : IsProper X.nativeRankOneStructure := by
  let := X.nativeRankOne_toSpecZero_isProper
  let : IsIso (Spec.map (CommRingCat.ofHom (R := k) (S := X.nativeTotalGrading 0)
      X.nativeRankOneCoefficients)) := by
    change IsIso (Scheme.Spec.mapIso
      ((RingEquiv.toCommRingCatIso (R := k) (S := X.nativeTotalGrading 0)
        X.nativeRankOneCoefficientEquiv).op)).hom
    infer_instance
  change IsProper (Proj.toSpecZero X.nativeTotalGrading ≫
    Spec.map (CommRingCat.ofHom (R := k) (S := X.nativeTotalGrading 0) X.nativeRankOneCoefficients))
  infer_instance

end EnvelopeProperty.MultiModel
