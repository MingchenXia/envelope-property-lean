import EnvelopeProperty.Global.Model
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.AlgHom
import Mathlib.LinearAlgebra.DFinsupp

/-! # Actual native total-degree grading of the original model algebra

For arbitrary rank this is the total grading only.  The Proj of a higher-rank
total grading is not asserted to be the original multiprojective model.
The rank-one case and the original diagonal Veronese provide the intended
native projective geometry in subsequent constructions.
-/
open scoped Classical
open MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.MultiModel
variable {k K : Type u} [Field k] [Field K] [Algebra k K] {r : ℕ} (X : MultiModel k K r)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every actual total homogeneous component of the SAME original S lies in S. -/
theorem homogeneousComponent_mem_model (d : ℕ) (p : X.S) :
    MvPolynomial.homogeneousComponent d (p : MvPolynomial (Fin r) K) ∈ X.S := by
  rw [MvPolynomial.homogeneousComponent_apply]
  exact X.S.sum_mem fun a _ => X.isGraded _ p.2 a

/-- The actual original algebra's native total homogeneous submodule. -/
def nativeTotalGrading (d : ℕ) : Submodule k X.S :=
  ((MvPolynomial.homogeneousSubmodule (Fin r) K d).restrictScalars k).comap X.S.val.toLinearMap

/-- The grading retains literal original polynomial homogeneity. -/
theorem mem_nativeTotalGrading (d : ℕ) (p : X.S) :
    p ∈ X.nativeTotalGrading d ↔ (p : MvPolynomial (Fin r) K).IsHomogeneous d := Iff.rfl

instance nativeTotalGrading_gradedMonoid : SetLike.GradedMonoid X.nativeTotalGrading where
  one_mem := by
    change (1 : MvPolynomial (Fin r) K).IsHomogeneous 0
    exact MvPolynomial.isHomogeneous_one (Fin r) K
  mul_mem := by
    intro i j p q hp hq
    exact hp.mul hq

private def nativeTotalComponent (d : ℕ) (p : X.S) : X.S :=
  ⟨MvPolynomial.homogeneousComponent d (p : MvPolynomial (Fin r) K),
    X.homogeneousComponent_mem_model d p⟩

/-- The actual original model algebra is the internal sum of its actual total homogeneous pieces. -/
theorem nativeTotalGrading_isInternal : DirectSum.IsInternal X.nativeTotalGrading := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · have hind := (DirectSum.Decomposition.isInternal
      (fun d => (MvPolynomial.homogeneousSubmodule (Fin r) K d).restrictScalars k)).submodule_iSupIndep
    rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero] at hind ⊢
    intro s v hv hsum i hi
    apply Subtype.ext
    apply hind s (fun a => (v a : MvPolynomial (Fin r) K)) hv _ i hi
    simpa only [map_sum, map_zero, Subalgebra.val_apply] using
      congrArg (fun p : X.S => X.S.val p) hsum
  · apply top_unique
    intro p _
    have hsum : p = ∑ n ∈ Finset.range ((p : MvPolynomial (Fin r) K).totalDegree + 1),
        X.nativeTotalComponent n p := by
      apply Subtype.ext
      change X.S.val p = X.S.val _
      rw [map_sum]
      exact (MvPolynomial.sum_homogeneousComponent (p : MvPolynomial (Fin r) K)).symm
    rw [hsum]
    apply Submodule.sum_mem
    intro n _
    apply Submodule.mem_iSup_of_mem n
    exact MvPolynomial.homogeneousComponent_isHomogeneous n (p : MvPolynomial (Fin r) K)

/-- The SAME original model algebra carries its genuine native total-degree graded algebra. -/
instance nativeTotalGradedAlgebra : GradedAlgebra X.nativeTotalGrading :=
  X.nativeTotalGrading_isInternal.gradedAlgebra

/-- The actual original model inclusion preserves the ENTIRE native homogeneous grading. -/
def nativeTotalInclusion : X.nativeTotalGrading →ₐᵍ[k]
    (fun d => (MvPolynomial.homogeneousSubmodule (Fin r) K d).restrictScalars k) where
  __ := X.S.val
  map_mem := fun h => h

/-- Every native homogeneous component is the SAME original whole polynomial component. -/
theorem nativeTotalGrading_decompose_val (d : ℕ) (p : X.S) :
    ((DirectSum.decompose X.nativeTotalGrading p d : X.S) : MvPolynomial (Fin r) K) =
      MvPolynomial.homogeneousComponent d (p : MvPolynomial (Fin r) K) := by
  have h := _root_.map_directSumDecompose X.nativeTotalGrading
    (fun n => (MvPolynomial.homogeneousSubmodule (Fin r) K n).restrictScalars k)
    X.nativeTotalInclusion (x := p) (i := d)
  exact h.trans (MvPolynomial.decomposition.decompose'_apply
    (p : MvPolynomial (Fin r) K) d)

end EnvelopeProperty.MultiModel
