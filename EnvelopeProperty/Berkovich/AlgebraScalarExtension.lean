/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.NormFormGeneral

/-!
# Scalar extension of an affine algebra morphism

Over arbitrary commutative coefficient rings, the scalar-extended structural
map gives the actual extended-base algebra action. Explicit balanced tensor
maps produce the cancellation equivalence and preserve every original element.
Finite freeness, module finiteness and etaleness follow from this equivalence;
entire determinant norm forms and scalar norms commute with the comparison.

The algebra actions are named producers. Auxiliary instance registrations are
local, so the API does not select a right tensor action globally.
-/
open scoped TensorProduct
noncomputable section
namespace EnvelopeProperty
namespace ScalarExtension
variable (R S A B : Type*) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
 [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
local instance : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra

def ringMap : S ⊗[R] A →ₐ[S] S ⊗[R] B :=
  Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom R A B)

@[instance_reducible]
def algebra : Algebra (S ⊗[R] A) (S ⊗[R] B) := (ringMap R S A B).toRingHom.toAlgebra
local instance (priority := low) : Algebra (S ⊗[R] A) (S ⊗[R] B) := algebra R S A B
local instance (priority := low) : Algebra A (S ⊗[R] B) :=
  ((algebraMap (S ⊗[R] A) (S ⊗[R] B)).comp (algebraMap A (S ⊗[R] A))).toAlgebra
local instance (priority := low) : IsScalarTower A (S ⊗[R] A) (S ⊗[R] B) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance (priority := low) : IsScalarTower R (S ⊗[R] A) (S ⊗[R] B) :=
  IsScalarTower.of_algebraMap_eq fun r => ((ringMap R S A B).restrictScalars R).commutes r |>.symm

local instance (priority := low) : IsScalarTower R A (S ⊗[R] B) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R (S ⊗[R] A) (S ⊗[R] B),
      IsScalarTower.algebraMap_apply R A (S ⊗[R] A),
      ← IsScalarTower.algebraMap_apply A (S ⊗[R] A) (S ⊗[R] B)]

def leftMap : S ⊗[R] A →ₐ[A] S ⊗[R] B where
  __ := (ringMap R S A B).toRingHom
  commutes' _a := rfl

def rightMap : B →ₐ[A] S ⊗[R] B where
  __ := (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom
  commutes' a := by
    change (1 : S) ⊗ₜ[R] (algebraMap A B a) =
      ringMap R S A B ((1 : S) ⊗ₜ[R] a)
    rfl

def forward : (S ⊗[R] A) ⊗[A] B →ₐ[A] S ⊗[R] B :=
  Algebra.TensorProduct.lift (leftMap R S A B) (rightMap R S A B) (fun _ _ => .all _ _)

def inverse : S ⊗[R] B →ₐ[R] (S ⊗[R] A) ⊗[A] B :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : S ⊗[R] A →ₐ[S ⊗[R] A]
      (S ⊗[R] A) ⊗[A] B).restrictScalars R).comp Algebra.TensorProduct.includeLeft)
    ((Algebra.TensorProduct.includeRight : B →ₐ[A] (S ⊗[R] A) ⊗[A] B).restrictScalars R)
    (fun _ _ => .all _ _)

theorem forward_tmul (s : S) (a : A) (b : B) :
    forward R S A B ((s ⊗ₜ[R] a) ⊗ₜ[A] b) = s ⊗ₜ[R] (algebraMap A B a * b) := by
  simp [forward, leftMap, rightMap, ringMap,
    Algebra.TensorProduct.tmul_mul_tmul]

theorem inverse_tmul (s : S) (b : B) :
    inverse R S A B (s ⊗ₜ[R] b) = (s ⊗ₜ[R] (1 : A)) ⊗ₜ[A] b := by
  simp [inverse, Algebra.TensorProduct.tmul_mul_tmul]


theorem inverse_forward (q : (S ⊗[R] A) ⊗[A] B) :
    inverse R S A B (forward R S A B q) = q := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | add q q' hq hq' => simp [hq, hq']
  | tmul c b =>
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add c c' hc hc' => simp [TensorProduct.add_tmul, hc, hc']
    | tmul s a =>
      rw [forward_tmul, inverse_tmul]
      rw [← Algebra.smul_def, TensorProduct.tmul_smul]
      apply congrArg (fun c : S ⊗[R] A => c ⊗ₜ[A] b)
      rw [Algebra.smul_def]
      change ((1 : S) ⊗ₜ[R] a) * (s ⊗ₜ[R] (1 : A)) = s ⊗ₜ[R] a
      simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem forward_inverse (q : S ⊗[R] B) :
    forward R S A B (inverse R S A B q) = q := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | add q q' hq hq' => simp [hq, hq']
  | tmul s b => rw [inverse_tmul, forward_tmul]; simp

/-- The same genuine map preserves the entire scalar-extended base ring. -/
def forwardBase : (S ⊗[R] A) ⊗[A] B →ₐ[S ⊗[R] A] S ⊗[R] B where
  __ := (forward R S A B).toRingHom
  commutes' c := by
    change forward R S A B (c ⊗ₜ[A] (1 : B)) = ringMap R S A B c
    simp [forward, leftMap, rightMap, ← Algebra.TensorProduct.one_def]

/-- Actual scalar tensor cancellation, preserving the extended base-ring action. -/
def equiv : (S ⊗[R] A) ⊗[A] B ≃ₐ[S ⊗[R] A] S ⊗[R] B :=
  { forwardBase R S A B with
    invFun := inverse R S A B
    left_inv := inverse_forward R S A B
    right_inv := forward_inverse R S A B }

@[simp]
theorem equiv_tmul (s : S) (a : A) (b : B) :
    equiv R S A B ((s ⊗ₜ[R] a) ⊗ₜ[A] b) = s ⊗ₜ[R] (algebraMap A B a * b) :=
  forward_tmul R S A B s a b

@[simp]
theorem equiv_one_tmul (b : B) :
    equiv R S A B ((1 : S ⊗[R] A) ⊗ₜ[A] b) = (1 : S) ⊗ₜ[R] b := by
  change equiv R S A B (((1 : S) ⊗ₜ[R] (1 : A)) ⊗ₜ[A] b) = _
  simp

@[simp]
theorem equiv_symm_tmul (s : S) (b : B) :
    (equiv R S A B).symm (s ⊗ₜ[R] b) = (s ⊗ₜ[R] (1 : A)) ⊗ₜ[A] b :=
  inverse_tmul R S A B s b


/-- Finite freeness follows through actual scalar tensor cancellation. -/
theorem moduleFree [Module.Free A B] : Module.Free (S ⊗[R] A) (S ⊗[R] B) :=
  Module.Free.of_equiv (equiv R S A B).toLinearEquiv

/-- Module finiteness follows through actual scalar tensor cancellation. -/
theorem moduleFinite [Module.Finite A B] : Module.Finite (S ⊗[R] A) (S ⊗[R] B) :=
  Module.Finite.equiv (equiv R S A B).toLinearEquiv

/-- Etaleness follows through actual scalar tensor cancellation. -/
theorem etale [Algebra.Etale A B] : Algebra.Etale (S ⊗[R] A) (S ⊗[R] B) :=
  Algebra.Etale.of_equiv (equiv R S A B)

local instance (priority := low) [Module.Free A B] : Module.Free (S ⊗[R] A) (S ⊗[R] B) :=
  moduleFree R S A B
local instance (priority := low) [Module.Finite A B] : Module.Finite (S ⊗[R] A) (S ⊗[R] B) :=
  moduleFinite R S A B
local instance (priority := low) [Algebra.Etale A B] : Algebra.Etale (S ⊗[R] A) (S ⊗[R] B) :=
  etale R S A B

/-- Entire determinant norm forms agree after actual scalar tensor cancellation. -/
theorem map_normForm [Module.Free A B] [Module.Finite A B] {σ : Type*} [Fintype σ]
    (b : σ → B) :
    MvPolynomial.map (algebraMap A (S ⊗[R] A)) (normForm A b) =
      normForm (S ⊗[R] A) (fun j => (1 : S) ⊗ₜ[R] b j) := by
  rw [map_normForm_baseChange]
  simpa only [equiv_one_tmul] using (normForm_algEquiv (equiv R S A B)
    (fun j => (1 : S ⊗[R] A) ⊗ₜ[A] b j)).symm

/-- Scalar determinant norms agree after actual scalar tensor cancellation. -/
theorem map_algebraNorm [Module.Free A B] [Module.Finite A B] (b : B) :
    algebraMap A (S ⊗[R] A) (Algebra.norm A b) =
      Algebra.norm (S ⊗[R] A) ((1 : S) ⊗ₜ[R] b) := by
  rw [algebraNorm_baseChange_tmul, ← equiv_one_tmul R S A B b,
    Algebra.norm_eq_of_algEquiv (equiv R S A B)]

end ScalarExtension
end EnvelopeProperty
