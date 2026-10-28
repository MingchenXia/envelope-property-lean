import EnvelopeProperty.Vanishing.NadelCanonicalEtaleBaseChange
import EnvelopeProperty.Vanishing.NadelCanonicalPushoutCore

/-! # Actual mixed tensor/Omega comparison on an étale coefficient pushout -/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelCanonicalBaseChange

open CategoryTheory ModuleCat CanonicalGeometry
open scoped TensorProduct

variable {R A S B C : Type u}
    [CommRing R] [CommRing A] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    [Algebra A S] [Algebra A B] [Algebra A C] [Algebra S C] [Algebra B C]
    [IsScalarTower R A B] [IsScalarTower R B C]
    [IsScalarTower A S C] [IsScalarTower A B C]
    [Algebra.IsPushout A S B C] [Algebra.FormallyEtale B C]

/-- The actual original top differential module with its original A-coefficients restricted along A to B. -/
abbrev originalTopModule (n : ℕ) : ModuleCat A :=
  (restrictScalars (algebraMap A B)).obj (ModuleCat.of B (affineCanonicalModule R B n))

/-- The actual pushout top differential module with its original S-coefficients. -/
abbrev pushoutTopModule (n : ℕ) : ModuleCat S :=
  (restrictScalars (algebraMap S C)).obj (ModuleCat.of C (affineCanonicalModule R C n))

/-- Native pushout tensor cancellation followed by actual étale Kähler and exterior base change gives the true mixed comparison. -/
def pushoutTopEquiv {n : ℕ} (b : Module.Basis (Fin n) B (KaehlerDifferential R B)) :
    S ⊗[A] originalTopModule (R := R) (A := A) (B := B) n ≃ₗ[S]
      pushoutTopModule (R := R) (S := S) (C := C) n := by
  let M := originalTopModule (R := R) (A := A) (B := B) n
  let : Module B M := inferInstanceAs (Module B (affineCanonicalModule R B n))
  let : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let N := pushoutTopModule (R := R) (S := S) (C := C) n
  let : Module C N := inferInstanceAs (Module C (affineCanonicalModule R C n))
  let : IsScalarTower S C N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : C ⊗[B] M ≃ₗ[C] N := etaleTopEquiv (B := C) b
  exact mixedTensorEquiv e

omit [Algebra R A] [IsScalarTower R A B] in
/-- On every original differential wedge the mixed comparison is the genuine differential pullback. -/
theorem pushoutTopEquiv_wedge {n : ℕ}
    (b : Module.Basis (Fin n) B (KaehlerDifferential R B))
    (w : Fin n → KaehlerDifferential R B) :
    pushoutTopEquiv (A := A) (S := S) (C := C) b
        (1 ⊗ₜ[A] exteriorPower.ιMulti B n w) =
      exteriorPower.ιMulti C n (fun j => KaehlerDifferential.map R R B C (w j)) := by
  let M := originalTopModule (R := R) (A := A) (B := B) n
  let : Module B M := inferInstanceAs (Module B (affineCanonicalModule R B n))
  let : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let N := pushoutTopModule (R := R) (S := S) (C := C) n
  let : Module C N := inferInstanceAs (Module C (affineCanonicalModule R C n))
  let : IsScalarTower S C N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : C ⊗[B] M ≃ₗ[C] N := etaleTopEquiv (B := C) b
  have h := mixedTensorEquiv_tmul (A := A) e (1 : S) (exteriorPower.ιMulti B n w)
  simp only [map_one] at h
  exact h.trans (etaleTopEquiv_wedge b w)

omit [Algebra.FormallyEtale B C] in
/-- Actual formally étale coefficient change gives formal étaleness of the other pushout projection. -/
theorem pushoutRight_formallyEtale [Algebra.FormallyEtale A S] :
    Algebra.FormallyEtale B C := by
  let : Algebra.IsPushout A B S C := Algebra.IsPushout.symm inferInstance
  exact Algebra.FormallyEtale.of_equiv (Algebra.IsPushout.equiv A B S C)

omit [Algebra.FormallyEtale B C] in
/-- The mixed comparison is internally produced from the original coefficient etaleness and actual ring pushout. -/
def coefficientPushoutTopEquiv [Algebra.FormallyEtale A S] {n : ℕ}
    (b : Module.Basis (Fin n) B (KaehlerDifferential R B)) :
    S ⊗[A] originalTopModule (R := R) (A := A) (B := B) n ≃ₗ[S]
      pushoutTopModule (R := R) (S := S) (C := C) n := by
  let : Algebra.FormallyEtale B C := pushoutRight_formallyEtale (A := A) (S := S)
  exact pushoutTopEquiv b

end EnvelopeProperty.Vanishing.NadelCanonicalBaseChange
