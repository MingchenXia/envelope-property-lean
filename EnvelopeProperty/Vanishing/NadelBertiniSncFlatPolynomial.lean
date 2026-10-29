import EnvelopeProperty.Vanishing.NadelBertiniSncFlatAffine
import EnvelopeProperty.Vanishing.NadelBertiniSncLinearRegular
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # The actual polynomial parameter fibre is the original source chart ring

All scalar actions are the ORIGINAL coefficient map and ORIGINAL tuple evaluation.
The whole tensor fibre equivalence preserves every original chart coefficient,
parameter variable, and the same original linear-combination equation.
-/
noncomputable section
open scoped TensorProduct
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniSncFlatPolynomial
open MvPolynomial NadelBertiniLinearSmooth
variable {k C : Type u} [CommRing k] [CommRing C] [Algebra k C] {S : Type}

/-- The actual original parameter-to-chart polynomial coefficient map. -/
def coefficientMap : MvPolynomial S k →+* MvPolynomial S C :=
  MvPolynomial.map (algebraMap k C)

/-- The actual whole chart polynomial evaluated at the same original tuple. -/
def chartEvaluation (a : S → k) : MvPolynomial S C →+* C :=
  MvPolynomial.eval₂Hom (RingHom.id C) (fun i => algebraMap k C (a i))

/-- The ENTIRE original coefficient/evaluation square commutes. -/
theorem chartEvaluation_comp_coefficientMap (a : S → k) :
    (chartEvaluation (C := C) a).comp coefficientMap =
      (algebraMap k C).comp (MvPolynomial.eval a) := by
  ext x <;> simp [coefficientMap, chartEvaluation]

/-- The original actual tensor fibre evaluation map. -/
def evaluationMap (a : S → k) :
    letI : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
    letI : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
      (coefficientMap (k := k) (C := C)).toAlgebra
    k ⊗[MvPolynomial S k] MvPolynomial S C →+* C := by
  letI : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
  letI : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
    (coefficientMap (k := k) (C := C)).toAlgebra
  letI : Algebra (MvPolynomial S k) C :=
    ((algebraMap k C).comp (MvPolynomial.eval a)).toAlgebra
  let f : k →ₐ[MvPolynomial S k] C :=
    { toRingHom := algebraMap k C, commutes' := fun _ => rfl }
  let g : MvPolynomial S C →ₐ[MvPolynomial S k] C :=
    { toRingHom := chartEvaluation a
      commutes' := fun p => congrArg (fun f : MvPolynomial S k →+* C => f p)
        (chartEvaluation_comp_coefficientMap a) }
  exact (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom

/-- Every WHOLE original pure tensor has its actual expected evaluation. -/
theorem evaluationMap_tmul (a : S → k) (r : k) (F : MvPolynomial S C) :
    letI : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
    letI : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
      (coefficientMap (k := k) (C := C)).toAlgebra
    evaluationMap a (r ⊗ₜ[MvPolynomial S k] F) =
      algebraMap k C r * chartEvaluation a F := rfl

/-- The actual inverse candidate retains every original chart-ring coefficient. -/
def constantMap (a : S → k) :
    letI : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
    letI : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
      (coefficientMap (k := k) (C := C)).toAlgebra
    C →+* k ⊗[MvPolynomial S k] MvPolynomial S C := by
  letI : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
  letI : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
    (coefficientMap (k := k) (C := C)).toAlgebra
  exact (Algebra.TensorProduct.includeRight (R := MvPolynomial S k)
    (A := k) (B := MvPolynomial S C)).toRingHom.comp MvPolynomial.C

/-- The original tensor balancing relation restores each actual parameter variable. -/
theorem tensor_variable (a : S → k) (i : S) :
    letI : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
    letI : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
      (coefficientMap (k := k) (C := C)).toAlgebra
    a i ⊗ₜ[MvPolynomial S k] (1 : MvPolynomial S C) =
      (1 : k) ⊗ₜ[MvPolynomial S k] MvPolynomial.X i := by
  let : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
  let : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
    (coefficientMap (k := k) (C := C)).toAlgebra
  have h := TensorProduct.smul_tmul (R := MvPolynomial S k) (MvPolynomial.X i : MvPolynomial S k)
    (1 : k) (1 : MvPolynomial S C)
  change (MvPolynomial.eval a (MvPolynomial.X i) * 1) ⊗ₜ[MvPolynomial S k] (1 : MvPolynomial S C) =
    (1 : k) ⊗ₜ[MvPolynomial S k] (coefficientMap (MvPolynomial.X i) * 1) at h
  simpa only [MvPolynomial.eval_X, coefficientMap, MvPolynomial.map_X, mul_one] using h

/-- The same original balancing relation retains each actual original base scalar. -/
theorem constantMap_algebraMap (a : S → k) (r : k) :
    letI : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
    letI : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
      (coefficientMap (k := k) (C := C)).toAlgebra
    constantMap a (algebraMap k C r) = r ⊗ₜ[MvPolynomial S k] (1 : MvPolynomial S C) := by
  let : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
  let : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
    (coefficientMap (k := k) (C := C)).toAlgebra
  have h := TensorProduct.smul_tmul (R := MvPolynomial S k) (MvPolynomial.C r : MvPolynomial S k)
    (1 : k) (1 : MvPolynomial S C)
  change (MvPolynomial.eval a (MvPolynomial.C r) * 1) ⊗ₜ[MvPolynomial S k] (1 : MvPolynomial S C) =
    (1 : k) ⊗ₜ[MvPolynomial S k] (coefficientMap (MvPolynomial.C r) * 1) at h
  change (1 : k) ⊗ₜ[MvPolynomial S k] MvPolynomial.C (algebraMap k C r) = _
  simpa only [coefficientMap, MvPolynomial.eval_C, MvPolynomial.map_C, mul_one] using h.symm

/-- The actual inverse retains EVERY original chart polynomial, not just support. -/
theorem constantMap_chartEvaluation (a : S → k) (F : MvPolynomial S C) :
    letI : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
    letI : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
      (coefficientMap (k := k) (C := C)).toAlgebra
    constantMap a (chartEvaluation a F) = (1 : k) ⊗ₜ[MvPolynomial S k] F := by
  let : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
  let : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
    (coefficientMap (k := k) (C := C)).toAlgebra
  induction F using MvPolynomial.induction_on with
  | C c => simp [chartEvaluation, constantMap]
  | add F G hF hG => simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (· + ·) hF hG
  | mul_X F i hF =>
    have hi : constantMap (C := C) a (chartEvaluation a (MvPolynomial.X i)) =
        (1 : k) ⊗ₜ[MvPolynomial S k] MvPolynomial.X i := by
      rw [chartEvaluation, MvPolynomial.eval₂Hom_X', constantMap_algebraMap, tensor_variable]
    rw [map_mul, map_mul, hF, hi, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- The original polynomial parameter fibre is the SAME original chart ring,
with all ORIGINAL scalar actions internally fixed by the original maps. -/
def fibreEvaluationIso (a : S → k) :
    letI : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
    letI : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
      (coefficientMap (k := k) (C := C)).toAlgebra
    k ⊗[MvPolynomial S k] MvPolynomial S C ≃+* C := by
  letI : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
  letI : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
    (coefficientMap (k := k) (C := C)).toAlgebra
  apply RingEquiv.ofRingHom (evaluationMap a) (constantMap a)
  · ext c
    rw [RingHom.comp_apply]
    change evaluationMap a ((1 : k) ⊗ₜ[MvPolynomial S k] MvPolynomial.C c) = c
    rw [evaluationMap_tmul]
    simp [chartEvaluation]
  · apply RingHom.ext
    intro z
    change constantMap a (evaluationMap a z) = z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z t hz ht => simpa only [map_add] using congrArg₂ (· + ·) hz ht
    | tmul r F =>
      rw [evaluationMap_tmul, map_mul, constantMap_algebraMap, constantMap_chartEvaluation,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The WHOLE original linear equation becomes the SAME original selected linear
combination in the original chart ring. -/
theorem chartEvaluation_linearForm [Fintype S] (a : S → k) (c : S → C) :
    chartEvaluation a (linearForm c) = ∑ i, algebraMap k C (a i) * c i := by
  simp only [linearForm, map_sum, map_mul, chartEvaluation, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', RingHom.id_apply]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The actual whole fibre isomorphism retains the SAME selected equation. -/
theorem fibreEvaluationIso_linearForm [Fintype S] (a : S → k) (c : S → C) :
    letI : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
    letI : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
      (coefficientMap (k := k) (C := C)).toAlgebra
    fibreEvaluationIso a ((1 : k) ⊗ₜ[MvPolynomial S k] linearForm c) =
      ∑ i, algebraMap k C (a i) * c i := by
  let : Algebra (MvPolynomial S k) k := (MvPolynomial.eval a).toAlgebra
  let : Algebra (MvPolynomial S k) (MvPolynomial S C) :=
    (coefficientMap (k := k) (C := C)).toAlgebra
  change evaluationMap a ((1 : k) ⊗ₜ[MvPolynomial S k] linearForm c) = _
  rw [evaluationMap_tmul, map_one, one_mul, chartEvaluation_linearForm]

end EnvelopeProperty.Vanishing.NadelBertiniSncFlatPolynomial
