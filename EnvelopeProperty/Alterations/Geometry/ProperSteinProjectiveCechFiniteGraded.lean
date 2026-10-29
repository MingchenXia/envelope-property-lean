import EnvelopeProperty.Alterations.Geometry.ProperSteinProjectiveCechDimensionShift
import EnvelopeProperty.Alterations.Geometry.ProperSteinProjectiveCechFiniteProducts

/-! # Finite cohomology of actual finite graded polynomial modules

The cohomology of free modules is computed by the polynomial
localization–Laurent comparison. Actual successive homogeneous kernels and
the native connecting homomorphism prove finiteness without a finiteness
certificate for the module's cohomology.
-/

/-!
Only Mathlib and modules of `Alterations` are imported.
The polynomial finiteness theorem is stated over Noetherian commutative coefficient rings,
not only over fields.
-/

universe u

open CategoryTheory DirectSum

namespace Alterations.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section ZeroCocycles

variable {K : Type u} [CommRing K]

/-- Native degree-zero cohomology is canonically the actual kernel of the first differential. -/
def nativeCochainZeroCocyclesIso (C : CochainComplex (ModuleCat.{u} K) ℕ) :
    ModuleCat.of K (LinearMap.ker (C.d 0 1).hom) ≅ C.homology 0 :=
  (C.sc' 0 0 1).moduleCatCyclesIso.symm ≪≫
    (C.cyclesIsoSc' 0 0 1 (by simp) (by simp)).symm ≪≫ C.isoHomologyπ₀

/-- Finite native degree-zero cohomology makes the actual first-differential kernel finite. -/
theorem nativeCochainZeroCocycles_finite (C : CochainComplex (ModuleCat.{u} K) ℕ)
    [Module.Finite K (C.homology 0)] :
    Module.Finite K (LinearMap.ker (C.d 0 1).hom) :=
  Module.Finite.equiv (nativeCochainZeroCocyclesIso C).toLinearEquiv.symm

variable {I : Type u} [LinearOrder I] (F : Finset I ⥤ ModuleCat.{u} K)

/-- Actual singleton-coordinate Čech cocycles are the native degree-zero cohomology. -/
def actualSubsetCechZeroCocyclesIso :
    ModuleCat.of K (LinearMap.ker (subsetCechCardDifferential F 1)) ≅
      (subsetCechComplex F).homology 0 := by
  have hd : (subsetCechComplex F).d 0 1 =
      ModuleCat.ofHom (subsetCechCardDifferential F 1) := by
    exact CochainComplex.of_d
      (fun p => ModuleCat.of K (subsetCechCardPiece F (p + 1)))
      (fun p => ModuleCat.ofHom (subsetCechCardDifferential F (p + 1))) 0
  have hker : LinearMap.ker ((subsetCechComplex F).d 0 1).hom =
      LinearMap.ker (subsetCechCardDifferential F 1) := by
    rw [hd]
    rfl
  exact eqToIso (by rw [hker]; rfl) ≪≫
    nativeCochainZeroCocyclesIso (subsetCechComplex F)

/-- Finite native Čech degree-zero cohomology makes the actual cocycle module finite. -/
theorem actualSubsetCechZeroCocycles_finite
    [Module.Finite K ((subsetCechComplex F).homology 0)] :
    Module.Finite K (LinearMap.ker (subsetCechCardDifferential F 1)) :=
  Module.Finite.equiv (actualSubsetCechZeroCocyclesIso F).toLinearEquiv.symm

end ZeroCocycles

variable {K I M : Type u} [CommRing K] [IsNoetherianRing K] [LinearOrder I] [Fintype I]
  [AddCommGroup M] [Module K M] [Module (MvPolynomial I K) M]
  [IsScalarTower K (MvPolynomial I K) M]
  (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I)) ℳ]
  [Module.Finite (MvPolynomial I K) M]

/-- Every true finite internally graded polynomial module has finite native
coordinate-cover cohomology in every true integral twisting degree. -/
theorem finiteGradedPolynomialCoordinateCech_homology_finite (k : ℤ) (p : ℕ) :
    Module.Finite K
      ((homogeneousCoordinateCechComplex (polynomialIntegralGrading (K := K) (I := I))
        ℳ (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree k).homology p) := by
  apply homogeneousCoordinateCech_homology_finite_of_shiftedFree
    (polynomialIntegralGrading (K := K) (I := I))
    (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree
  intro J _ _ δ m q
  exact finiteShiftedPolynomialCoordinateCech_homology_finite (K := K) (I := I) δ m q

/-- The actual coordinate cocycle module of every finite graded polynomial module is finite. -/
theorem finiteGradedPolynomialCoordinateCech_zeroCocycles_finite (k : ℤ) :
    Module.Finite K (LinearMap.ker (subsetCechCardDifferential
      (homogeneousCoordinateSubsetDiagram (polynomialIntegralGrading (K := K) (I := I))
        ℳ (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree k) 1)) := by
  have : Module.Finite K
      ((subsetCechComplex (homogeneousCoordinateSubsetDiagram
        (polynomialIntegralGrading (K := K) (I := I)) ℳ
        (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree k)).homology 0) :=
    finiteGradedPolynomialCoordinateCech_homology_finite ℳ k 0
  exact actualSubsetCechZeroCocycles_finite _

end

end Alterations.Geometry.ProperSteinProjectiveCech
