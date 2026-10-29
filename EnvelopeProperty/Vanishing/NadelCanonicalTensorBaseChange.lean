import EnvelopeProperty.Vanishing.NadelCanonicalPushoutBaseChange

/-! # Actual literal coefficient tensor products and their original top differentials -/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelCanonicalBaseChange

open CategoryTheory ModuleCat CanonicalGeometry
open scoped TensorProduct

variable {R A S B : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
    [Algebra R A] [Algebra R S] [Algebra R B] [Algebra A S] [Algebra A B]
    [IsScalarTower R A S] [IsScalarTower R A B]

/-- The native original small-ring action agrees with both actual tensor coefficient paths. -/
theorem tensorRight_scalarTower :
    letI : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    IsScalarTower R B (S ⊗[A] B) := by
  let : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change (algebraMap R S r) ⊗ₜ[A] (1 : B) = (1 : S) ⊗ₜ[A] (algebraMap R B r)
  rw [IsScalarTower.algebraMap_apply R A S, IsScalarTower.algebraMap_apply R A B]
  exact DFunLike.congr_fun
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := A) (A := S) (B := B))
      (algebraMap R A r)

/-- The actual literal mixed tensor/Omega comparison is produced without an Omega-model or pushout certificate. -/
def tensorTopEquiv [Algebra.FormallyEtale A S] {n : ℕ}
    (b : Module.Basis (Fin n) B (KaehlerDifferential R B)) :
    S ⊗[A] originalTopModule (R := R) (A := A) (B := B) n ≃ₗ[S]
      pushoutTopModule (R := R) (S := S) (C := S ⊗[A] B) n := by
  let : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R B (S ⊗[A] B) := tensorRight_scalarTower
  exact coefficientPushoutTopEquiv b

/-- Every original genuine wedge has its native differential images under the literal tensor/Omega equivalence. -/
theorem tensorTopEquiv_wedge [Algebra.FormallyEtale A S] {n : ℕ}
    (b : Module.Basis (Fin n) B (KaehlerDifferential R B))
    (w : Fin n → KaehlerDifferential R B) :
    tensorTopEquiv (A := A) (S := S) b (1 ⊗ₜ[A] exteriorPower.ιMulti B n w) =
      letI : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
      letI : IsScalarTower R B (S ⊗[A] B) := tensorRight_scalarTower
      exteriorPower.ιMulti (S ⊗[A] B) n
        (fun j => KaehlerDifferential.map R R B (S ⊗[A] B) (w j)) := by
  let : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R B (S ⊗[A] B) := tensorRight_scalarTower
  let : Algebra.FormallyEtale B (S ⊗[A] B) :=
    pushoutRight_formallyEtale (A := A) (S := S)
  exact pushoutTopEquiv_wedge b w

end EnvelopeProperty.Vanishing.NadelCanonicalBaseChange
