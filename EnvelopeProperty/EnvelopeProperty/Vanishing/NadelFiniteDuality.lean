import EnvelopeProperty.AlgGeom.CyclicSectionPowerBasis
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.Dual.Basis

/-! # The actual dual module of the original monic cyclic root algebra

The top-coefficient pairing is perfect even at ramification or nilpotent
section coefficients.  The dual module uses native coextension of scalars,
with its original coefficient action and restriction/coextension adjunction.
No canonical sheaf on a singular normalization or vanishing is asserted.
-/

noncomputable section

namespace EnvelopeProperty.Vanishing.NadelFiniteDuality

open Module CategoryTheory
open CyclicSectionAlgebra CyclicSectionPowerBasis

universe u
variable {R : Type u} [CommRing R] [Nontrivial R]

/-- The original monic quotient, in positive degree `n + 1`. -/
abbrev Root (n : ℕ) (a : R) := RootRing (n + 1) a

/-- The actual coefficient of the last vector in the original root power basis. -/
def topCoefficient (n : ℕ) (a : R) : Root n a →ₗ[R] R :=
  (basis (n + 1) a (Nat.succ_pos n)).coord (Fin.last n)

/-- The original top coefficient evaluated on every original basis monomial. -/
theorem topCoefficient_pow_lt (n : ℕ) (a : R) (i : ℕ) (hi : i < n + 1) :
    topCoefficient n a (root (n + 1) a ^ i) = if i = n then 1 else 0 := by
  classical
  rw [← basis_apply (n + 1) a (Nat.succ_pos n) ⟨i, hi⟩]
  simp only [topCoefficient, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  simp only [Fin.ext_iff, Fin.val_last]

/-- Reduction by the original monic equation has zero last coefficient in this range. -/
theorem topCoefficient_pow_reduced (n : ℕ) (a : R) (i : ℕ)
    (hi : n + 1 ≤ i) (hi' : i < n + 1 + n) :
    topCoefficient n a (root (n + 1) a ^ i) = 0 := by
  have hpow : root (n + 1) a ^ i = a • root (n + 1) a ^ (i - (n + 1)) := by
    calc
      _ = root (n + 1) a ^ ((n + 1) + (i - (n + 1))) := by congr 1; omega
      _ = _ := by rw [pow_add, root_pow, Algebra.smul_def]
  rw [hpow, map_smul, topCoefficient_pow_lt n a _ (by omega), if_neg (by omega), smul_zero]

/-- The original reversed powers are the actual dual frame for top-coefficient multiplication. -/
theorem topCoefficient_mul_reverse (n : ℕ) (a : R) (i j : Fin (n + 1)) :
    topCoefficient n a (root (n + 1) a ^ (i : ℕ) *
      root (n + 1) a ^ (j.rev : ℕ)) = if i = j then 1 else 0 := by
  classical
  rw [← pow_add]
  have hi := i.isLt
  have hj := j.isLt
  have hrev := j.add_rev_cast
  by_cases h : (i : ℕ) + (j.rev : ℕ) < n + 1
  · rw [topCoefficient_pow_lt n a _ h]
    congr 1
    simp only [Fin.ext_iff]
    apply propext
    omega
  · rw [topCoefficient_pow_reduced n a _ (by omega) (by omega)]
    rw [if_neg]
    intro hij
    subst j
    omega

/-- The whole actual multiplication pairing, with the original top-coefficient functional. -/
def multiplicationPairing (n : ℕ) (a : R) : Root n a →ₗ[R] Module.Dual R (Root n a) :=
  (LinearMap.mul R (Root n a)).compr₂ (topCoefficient n a)

@[simp]
theorem multiplicationPairing_apply (n : ℕ) (a : R) (x y : Root n a) :
    multiplicationPairing n a x y = topCoefficient n a (x * y) := rfl

/-- Multiplication by each original reversed power gives its same actual dual basis functional. -/
theorem multiplicationPairing_reverse_basis (n : ℕ) (a : R) (i : Fin (n + 1)) :
    multiplicationPairing n a (basis (n + 1) a (Nat.succ_pos n) i.rev) =
      (basis (n + 1) a (Nat.succ_pos n)).dualBasis i := by
  classical
  apply (basis (n + 1) a (Nat.succ_pos n)).ext
  intro j
  rw [Basis.dualBasis_apply_self, multiplicationPairing_apply, basis_apply, basis_apply,
    mul_comm, topCoefficient_mul_reverse]

/-- The actual whole monic root algebra is linearly equivalent to its original linear dual. -/
def multiplicationEquiv (n : ℕ) (a : R) :
    Root n a ≃ₗ[R] Module.Dual R (Root n a) :=
  (basis (n + 1) a (Nat.succ_pos n)).equiv
    (basis (n + 1) a (Nat.succ_pos n)).dualBasis Fin.revPerm

/-- The constructed equivalence is the original multiplication pairing, on every element. -/
theorem multiplicationEquiv_toLinearMap (n : ℕ) (a : R) :
    (multiplicationEquiv n a).toLinearMap = multiplicationPairing n a := by
  apply (basis (n + 1) a (Nat.succ_pos n)).ext
  intro i
  rw [LinearEquiv.coe_toLinearMap, multiplicationEquiv, Basis.equiv_apply]
  simpa only [Fin.revPerm_apply, Fin.rev_rev] using
    (multiplicationPairing_reverse_basis n a i.rev).symm

/-- Every original linear functional is uniquely top-coefficient multiplication by an element. -/
theorem multiplicationPairing_bijective (n : ℕ) (a : R) :
    Function.Bijective (multiplicationPairing n a) := by
  rw [← multiplicationEquiv_toLinearMap]
  exact (multiplicationEquiv n a).bijective

/-- The literal native right-adjoint object, with its actual original root-algebra action. -/
abbrev dualizingModule (n : ℕ) (a : R) : ModuleCat (Root n a) :=
  (ModuleCat.coextendScalars (algebraMap R (Root n a))).obj (ModuleCat.of R R)

/-- Restriction along the actual coefficient map retains the original quotient's coefficient action. -/
def restrictedRootEquiv (n : ℕ) (a : R) :
    (ModuleCat.restrictScalars (algebraMap R (Root n a))).obj
      (ModuleCat.of (Root n a) (Root n a)) ≃ₗ[R] Root n a where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change algebraMap R (Root n a) r * (show Root n a from x) =
      r • (show Root n a from x)
    exact (Algebra.smul_def r (show Root n a from x)).symm

/-- Multiplication against the original top coefficient as a map into native coextension. -/
def dualizingMap (n : ℕ) (a : R) : Root n a →ₗ[Root n a] dualizingModule n a where
  toFun x := (ModuleCat.CoextendScalars.equiv _ _).symm
    ((multiplicationPairing n a x).comp (restrictedRootEquiv n a).toLinearMap)
  map_add' x y := by
    apply ModuleCat.CoextendScalars.ext
    ext (z : Root n a)
    change topCoefficient n a ((x + y) * z) =
      topCoefficient n a (x * z) + topCoefficient n a (y * z)
    rw [add_mul, map_add]
  map_smul' b x := by
    apply ModuleCat.CoextendScalars.ext
    ext (y : Root n a)
    change topCoefficient n a ((b * x) * y) = topCoefficient n a (x * (y * b))
    rw [mul_comm b x, mul_assoc, mul_comm b y]

/-- The constructed native coextension map retains the original multiplication formula everywhere. -/
@[simp]
theorem dualizingMap_apply (n : ℕ) (a : R) (x y : Root n a) :
    dualizingMap n a x y = topCoefficient n a (y * x) := by
  change topCoefficient n a (x * y) = topCoefficient n a (y * x)
  rw [mul_comm]

/-- Perfectness is proved for the literal native coextension carrier, with no supplied comparison. -/
theorem dualizingMap_bijective (n : ℕ) (a : R) :
    Function.Bijective (dualizingMap n a) := by
  constructor
  · intro x y h
    apply (multiplicationPairing_bijective n a).1
    ext z
    have hz := congrArg (fun φ : dualizingModule n a => φ z) h
    change topCoefficient n a (x * z) = topCoefficient n a (y * z) at hz
    exact hz
  · intro φ
    let f := ModuleCat.CoextendScalars.equiv (algebraMap R (Root n a))
      (ModuleCat.of R R) φ
    let ψ : Module.Dual R (Root n a) := f.comp (restrictedRootEquiv n a).symm.toLinearMap
    obtain ⟨x, hx⟩ := (multiplicationPairing_bijective n a).2 ψ
    refine ⟨x, ?_⟩
    apply ModuleCat.CoextendScalars.ext
    ext (y : Root n a)
    have hy := LinearMap.congr_fun hx y
    exact hy

/-- The actual coextension dual module is a free rank-one module over the original root algebra. -/
def dualizingEquiv (n : ℕ) (a : R) : Root n a ≃ₗ[Root n a] dualizingModule n a :=
  LinearEquiv.ofBijective (dualizingMap n a) (dualizingMap_bijective n a)

/-- The actual root-algebra-linear equivalence is the original top-coefficient multiplication. -/
@[simp]
theorem dualizingEquiv_apply (n : ℕ) (a : R) (x y : Root n a) :
    dualizingEquiv n a x y = topCoefficient n a (y * x) := dualizingMap_apply n a x y

/-- The same proved equivalence as an actual isomorphism in the original root-module category. -/
def dualizingIso (n : ℕ) (a : R) :
    ModuleCat.of (Root n a) (Root n a) ≅ dualizingModule n a :=
  LinearEquiv.toModuleIso (X₁ := ModuleCat.of (Root n a) (Root n a))
    (X₂ := dualizingModule n a) (dualizingEquiv n a)

/-- The literal native restriction/coextension adjunction counit on the original dual module. -/
def dualizingCounit (n : ℕ) (a : R) :
    (ModuleCat.restrictScalars (algebraMap R (Root n a))).obj (dualizingModule n a) ⟶
      ModuleCat.of R R :=
  (ModuleCat.restrictCoextendScalarsAdj (algebraMap R (Root n a))).counit.app
    (ModuleCat.of R R)

omit [Nontrivial R] in
/-- The actual duality counit evaluates the original functional at one. -/
@[simp]
theorem dualizingCounit_apply (n : ℕ) (a : R) (φ : dualizingModule n a) :
    dualizingCounit n a φ = φ (1 : Root n a) := rfl

/-- Under the proved original dual frame, the native counit is the original top coefficient. -/
theorem dualizingCounit_equiv (n : ℕ) (a : R) (x : Root n a) :
    dualizingCounit n a (dualizingEquiv n a x) = topCoefficient n a x := by
  rw [dualizingCounit_apply, dualizingEquiv_apply, one_mul]

/-- The actual top functional under the original whole root-frame rescaling. -/
theorem topCoefficient_rescale (n : ℕ) (a b : R) (v : Rˣ)
    (h : b = (v : R) ^ (n + 1) * a) (x : Root n b) :
    topCoefficient n a (rescaleEquiv (n + 1) a b v h x) =
      (v : R) ^ n * topCoefficient n b x :=
  repr_rescaleEquiv (n + 1) a b (Nat.succ_pos n) v h x (Fin.last n)

/-- Whole multiplication pairings have their actual original rescaling weight. -/
theorem multiplicationPairing_rescale (n : ℕ) (a b : R) (v : Rˣ)
    (h : b = (v : R) ^ (n + 1) * a) (x y : Root n b) :
    multiplicationPairing n a (rescaleEquiv (n + 1) a b v h x)
      (rescaleEquiv (n + 1) a b v h y) =
        (v : R) ^ n * multiplicationPairing n b x y := by
  simp only [multiplicationPairing_apply, ← map_mul, topCoefficient_rescale]

/-- Every original native dualizing functional has its actual root-frame transition weight. -/
theorem dualizingEquiv_rescale (n : ℕ) (a b : R) (v : Rˣ)
    (h : b = (v : R) ^ (n + 1) * a) (x y : Root n b) :
    dualizingEquiv n a (rescaleEquiv (n + 1) a b v h x)
      (rescaleEquiv (n + 1) a b v h y) =
        (v : R) ^ n * dualizingEquiv n b x y := by
  change topCoefficient n a (rescaleEquiv (n + 1) a b v h x *
      rescaleEquiv (n + 1) a b v h y) =
    (v : R) ^ n * topCoefficient n b (x * y)
  exact multiplicationPairing_rescale n a b v h x y

end EnvelopeProperty.Vanishing.NadelFiniteDuality
