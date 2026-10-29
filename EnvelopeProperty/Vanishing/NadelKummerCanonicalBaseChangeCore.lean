import EnvelopeProperty.Vanishing.NadelKummerCanonicalTraceDual
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Actual multiplication and evaluation under finite-free dual base change

Native dual base change is reused.  The new diagrams concern the original
tensor algebra multiplication, native coextension action, and unit counit.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChange

open CategoryTheory ModuleCat TensorProduct
open scoped TensorProduct
open NadelKummerCanonicalTrace

universe u
variable {A B S : Type u} [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S]

/-- Restriction through the actual algebra map has the original coefficient action. -/
def algebraRestrictionEquiv :
    (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) ≃ₗ[A] B where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change algebraMap A B r * (show B from x) = r • (show B from x)
    exact (Algebra.smul_def r (show B from x)).symm

/-- The whole native dual carrier is its actual original coefficient-module dual. -/
def nativeFunctionalEquiv :
    (coextendScalars (algebraMap A B)).obj (ModuleCat.of A A) ≃ Module.Dual A B :=
  (CoextendScalars.equiv (algebraMap A B) (ModuleCat.of A A)).toEquiv |>.trans
    ((algebraRestrictionEquiv (A := A) (B := B)).arrowCongr (LinearEquiv.refl A A)).toEquiv

/-- The original native dual carrier comparison fixes every actual functional value. -/
theorem nativeFunctionalEquiv_apply
    (φ : (coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)) (b : B) :
    nativeFunctionalEquiv φ b = φ b := rfl

/-- Multiplication against the original actual coefficient functional. -/
def coefficientPairing (ℓ : B →ₗ[A] A) : B →ₗ[A] Module.Dual A B :=
  (LinearMap.mul A B).compr₂ ℓ

/-- Native finite-free dual base change on the actual original tensor module. -/
def dualBaseChangeEquiv [Module.Free A B] [Module.Finite A B] :
    S ⊗[A] Module.Dual A B ≃ₗ[S] Module.Dual S (S ⊗[A] B) :=
  (TensorProduct.isBaseChange A B S).toDualBaseChange

/-- The full pure-tensor evaluation formula retains the actual original coefficient map. -/
theorem dualBaseChangeEquiv_tmul [Module.Free A B] [Module.Finite A B]
    (s t : S) (ℓ : Module.Dual A B) (b : B) :
    dualBaseChangeEquiv (s ⊗ₜ[A] ℓ) (t ⊗ₜ[A] b) =
      s * t * algebraMap A S (ℓ b) := by
  have h := (TensorProduct.isBaseChange A B S).toDualBaseChange_tmul s ℓ b
  change (TensorProduct.isBaseChange A B S).toDualBaseChange
    (s ⊗ₜ[A] ℓ) (1 ⊗ₜ[A] b) = s * algebraMap A S (ℓ b) at h
  have ht : t ⊗ₜ[A] b = t • (1 ⊗ₜ[A] b : S ⊗[A] B) := TensorProduct.tmul_eq_smul_one_tmul t b
  rw [ht, map_smul, smul_eq_mul]
  change t * ((TensorProduct.isBaseChange A B S).toDualBaseChange
    (s ⊗ₜ[A] ℓ) (1 ⊗ₜ[A] b)) = _
  rw [h]
  ring

/-- Base change of the old multiplication pairing is the actual new tensor-algebra pairing. -/
theorem coefficientPairing_baseChange [Module.Free A B] [Module.Finite A B]
    (ℓ : B →ₗ[A] A) :
    (dualBaseChangeEquiv (A := A) (B := B) (S := S)).toLinearMap.comp
        ((coefficientPairing ℓ).baseChange S) =
      coefficientPairing (Module.Dual.baseChange S ℓ) := by
  apply AlgebraTensorModule.ext
  intro s b
  apply AlgebraTensorModule.ext
  intro t c
  change dualBaseChangeEquiv (s ⊗ₜ[A] coefficientPairing ℓ b) (t ⊗ₜ[A] c) =
    Module.Dual.baseChange S ℓ ((s ⊗ₜ[A] b) * (t ⊗ₜ[A] c))
  rw [dualBaseChangeEquiv_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Module.Dual.baseChange_apply_tmul, Algebra.smul_def]
  change s * t * algebraMap A S (ℓ (b * c)) = algebraMap A S (ℓ (b * c)) * (s * t)
  ring

/-- The native tensor-algebra-linear dual frame from the actual extended coefficient. -/
def baseChangedFrame (ℓ : B →ₗ[A] A) :
    (S ⊗[A] B) →ₗ[S ⊗[A] B]
      (coextendScalars (algebraMap S (S ⊗[A] B))).obj (ModuleCat.of S S) :=
  coextensionFrame (algebraMap S (S ⊗[A] B))
    ((Module.Dual.baseChange S ℓ).comp (algebraRestrictionEquiv (A := S) (B := S ⊗[A] B)).toLinearMap)

/-- The whole actual tensor-algebra dual frame has the original multiplication evaluation. -/
theorem baseChangedFrame_apply (ℓ : B →ₗ[A] A) (x y : S ⊗[A] B) :
    baseChangedFrame (S := S) ℓ x y = Module.Dual.baseChange S ℓ (y * x) := by
  rw [baseChangedFrame, coextensionFrame_apply]
  rfl

/-- The actual native frame counit retains its original pure-tensor coefficient formula. -/
theorem baseChangedFrame_counit_tmul (ℓ : B →ₗ[A] A) (s : S) (b : B) :
    (restrictCoextendScalarsAdj (algebraMap S (S ⊗[A] B))).counit.app (ModuleCat.of S S)
        (baseChangedFrame (S := S) ℓ (s ⊗ₜ[A] b)) =
      s * algebraMap A S (ℓ b) := by
  change baseChangedFrame (S := S) ℓ (s ⊗ₜ[A] b) (1 : S ⊗[A] B) = _
  rw [baseChangedFrame_apply, one_mul, Module.Dual.baseChange_apply_tmul, Algebra.smul_def,
    mul_comm]

end EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChange
