/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.PolynomialGaussInflation
import Mathlib.Topology.Homotopy.Contractible

open scoped Polynomial NNReal Topology ContinuousMap
open Polynomial Topology unitInterval
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {v : Valuation R ℝ≥0}

/-- The actual coefficient projection on whole original polynomial points. -/
def polynomialProjection : C(RelativeSpectrum v A[X], RelativeSpectrum v A) :=
  ⟨proj, continuous_proj⟩

/-- The actual zero-radius original Gauss section, with every coefficient retained. -/
def zeroGaussSection : C(RelativeSpectrum v A, RelativeSpectrum v A[X]) :=
  ⟨fun y => gauss y 0,
    continuous_gauss_prod.comp (continuous_id.prodMk continuous_const)⟩

/-- The actual Gauss point at each original point's own radius and whole coefficient restriction. -/
def polynomialRadialGaussMap : C(RelativeSpectrum v A[X], RelativeSpectrum v A[X]) where
  toFun x := gauss (v := v) (A := A) (proj (v := v) (A := A) x) (val x (X : A[X]))
  continuous_toFun := by
    rw [continuous_iff]
    intro F
    simp only [gauss_val_apply, proj_val_apply]
    exact Continuous.finset_sup_apply fun i _ =>
      (continuous_val_apply (C (F.coeff i))).mul ((continuous_val_apply X).pow i)

/-- Whole polynomial inflation gives a jointly continuous deformation to the actual radial Gauss map. -/
def polynomialGaussDeformation : (ContinuousMap.id (RelativeSpectrum v A[X])).Homotopy
    (polynomialRadialGaussMap (v := v) (A := A)) where
  toFun p := polynomialGaussInflation (v := v) (A := A) p.2
    (Real.toNNReal (p.1 : ℝ) * val p.2 (X : A[X]))
  continuous_toFun := by
    have hx : Continuous (Prod.snd : I × RelativeSpectrum v A[X] → RelativeSpectrum v A[X]) :=
      continuous_snd
    have ht : Continuous fun p : I × RelativeSpectrum v A[X] =>
        Real.toNNReal (p.1 : ℝ) * val p.2 (X : A[X]) :=
      (continuous_real_toNNReal.comp (continuous_subtype_val.comp continuous_fst)).mul
        ((continuous_val_apply (X : A[X])).comp hx)
    rw [continuous_iff]
    intro F
    simp only [polynomialGaussInflation_val_apply, gauss_val_apply]
    exact Continuous.finset_sup_apply fun i _ =>
      ((continuous_val_apply _).comp hx).mul (ht.pow i)
  map_zero_left x := by
    change polynomialGaussInflation x (Real.toNNReal (0 : ℝ) * val x X) = x
    rw [Real.toNNReal_zero, zero_mul, polynomialGaussInflation_zero]
  map_one_left x := by
    change polynomialGaussInflation x (Real.toNNReal (1 : ℝ) * val x X) =
      gauss (proj x) (val x X)
    rw [Real.toNNReal_one, one_mul, polynomialGaussInflation_eq_gauss x _ le_rfl]

/-- The original radial Gauss map contracts through genuine varying Gauss points to the zero section. -/
def polynomialGaussContraction : (polynomialRadialGaussMap (v := v) (A := A)).Homotopy
    ((zeroGaussSection (v := v)).comp polynomialProjection) where
  toFun p := gauss (proj p.2) ((1 - Real.toNNReal (p.1 : ℝ)) * val p.2 X)
  continuous_toFun := by
    have ht : Continuous fun p : I × RelativeSpectrum v A[X] =>
        (1 - Real.toNNReal (p.1 : ℝ)) * val p.2 (X : A[X]) :=
      (continuous_const.sub
        (continuous_real_toNNReal.comp (continuous_subtype_val.comp continuous_fst))).mul
          ((continuous_val_apply X).comp continuous_snd)
    rw [continuous_iff]
    intro F
    simp only [gauss_val_apply, proj_val_apply]
    exact Continuous.finset_sup_apply fun i _ =>
      ((continuous_val_apply _).comp continuous_snd).mul (ht.pow i)
  map_zero_left x := by
    change gauss (proj x) ((1 - Real.toNNReal (0 : ℝ)) * val x X) = gauss (proj x) (val x X)
    rw [Real.toNNReal_zero, tsub_zero, one_mul]
  map_one_left x := by
    change gauss (proj x) ((1 - Real.toNNReal (1 : ℝ)) * val x X) = gauss (proj x) 0
    rw [Real.toNNReal_one, tsub_self, zero_mul]

/-- An explicit whole-point retraction homotopy retaining the original coefficient projection. -/
def polynomialRetraction : (ContinuousMap.id (RelativeSpectrum v A[X])).Homotopy
    ((zeroGaussSection (v := v)).comp polynomialProjection) :=
  polynomialGaussDeformation.trans polynomialGaussContraction

/-- The actual polynomial retraction is fixed on the entire original zero Gauss section image. -/
def polynomialRetractionRel : (ContinuousMap.id (RelativeSpectrum v A[X])).HomotopyRel
    ((zeroGaussSection (v := v)).comp polynomialProjection) (Set.range zeroGaussSection) := by
  let F : (ContinuousMap.id (RelativeSpectrum v A[X])).HomotopyRel
      polynomialRadialGaussMap (Set.range zeroGaussSection) :=
    { toHomotopy := polynomialGaussDeformation
      prop' := by
        intro θ x hx
        obtain ⟨y, rfl⟩ := hx
        change polynomialGaussInflation (gauss y 0)
          (Real.toNNReal (θ : ℝ) * val (gauss y 0) X) = gauss y 0
        rw [gauss_val_X, mul_zero]
        exact polynomialGaussInflation_zero _ }
  let G : (polynomialRadialGaussMap (v := v) (A := A)).HomotopyRel
      ((zeroGaussSection (v := v)).comp polynomialProjection) (Set.range zeroGaussSection) :=
    { toHomotopy := polynomialGaussContraction
      prop' := by
        intro θ x hx
        obtain ⟨y, rfl⟩ := hx
        change gauss (proj (gauss y 0))
          ((1 - Real.toNNReal (θ : ℝ)) * val (gauss y 0) X) =
            gauss (proj (gauss y 0)) (val (gauss y 0) X)
        rw [gauss_val_X, mul_zero] }
  exact F.trans G

/-- The original polynomial coefficient projection and zero Gauss section are genuine homotopy inverses. -/
def polynomialHomotopyEquiv : RelativeSpectrum v A[X] ≃ₕ RelativeSpectrum v A where
  toFun := polynomialProjection
  invFun := zeroGaussSection
  left_inv := ⟨polynomialRetraction.symm⟩
  right_inv := by
    have h : (polynomialProjection (v := v) (A := A)).comp zeroGaussSection =
        ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro y
      exact proj_gauss y 0
    rw [h]

/-- Adjoining an original polynomial variable preserves and reflects contractibility. -/
theorem contractibleSpace_polynomial_iff :
    ContractibleSpace (RelativeSpectrum v A[X]) ↔ ContractibleSpace (RelativeSpectrum v A) :=
  polynomialHomotopyEquiv.contractibleSpace_iff

/-- The original relative spectrum over the prescribed base itself is an actual single point. -/
theorem contractibleSpace_self (v : Valuation R ℝ≥0) : ContractibleSpace (RelativeSpectrum v R) := by
  let : Nonempty (RelativeSpectrum v R) := ⟨self v⟩
  let : Subsingleton (RelativeSpectrum v R) := ⟨by
    intro x y
    apply ext_val
    intro a
    have hx : val x a = v a := by simpa using val_algebraMap x a
    have hy : val y a = v a := by simpa using val_algebraMap y a
    exact hx.trans hy.symm⟩
  infer_instance

/-- The actual whole affine line over any valued commutative ring is contractible. -/
theorem contractibleSpace_affineLine (v : Valuation R ℝ≥0) :
    ContractibleSpace (RelativeSpectrum v R[X]) := by
  let := contractibleSpace_self v
  exact polynomialHomotopyEquiv.contractibleSpace

end EnvelopeProperty.Berkovich.RelativeSpectrum
