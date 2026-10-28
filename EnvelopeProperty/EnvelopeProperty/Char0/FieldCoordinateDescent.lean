import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import EnvelopeProperty.Char0.CountableSmallCoefficientModel

/-! # Faithfully flat descent of the actual selected coordinate tuple -/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0.FieldCoordinateDescent

open scoped TensorProduct

universe u v w

variable {k : Type u} {L : Type v} {A : Type w}
  [Field k] [Field L] [CommRing A] [Algebra k L] [Algebra k A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra MvPolynomial.algebraMvPolynomial

/-- Faithfully flat reflection for the literal original coordinate tuple,
with independent coefficient and model universes. -/
theorem etale_of_tensorCoordinates {n : ℕ} (z : Fin n → A)
    (hz : (MvPolynomial.aeval (R := L) (fun i => (1 ⊗ₜ[k] z i : L ⊗[k] A))).toRingHom.Etale) :
    (MvPolynomial.aeval (R := k) z).toRingHom.Etale := by
  let : Algebra (MvPolynomial (Fin n) k) A := (MvPolynomial.aeval (R := k) z).toAlgebra
  let : IsScalarTower k (MvPolynomial (Fin n) k) A :=
    IsScalarTower.of_algebraMap_eq fun r => ((MvPolynomial.aeval (R := k) z).commutes r).symm
  let : Algebra (MvPolynomial (Fin n) L) (L ⊗[k] A) :=
    (MvPolynomial.aeval (R := L) (fun i => (1 ⊗ₜ[k] z i : L ⊗[k] A))).toAlgebra
  let : IsScalarTower L (MvPolynomial (Fin n) L) (L ⊗[k] A) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      ((MvPolynomial.aeval (R := L) (fun i => (1 ⊗ₜ[k] z i : L ⊗[k] A))).commutes r).symm
  let : Algebra (MvPolynomial (Fin n) k) (L ⊗[k] A) :=
    ((algebraMap A (L ⊗[k] A)).comp (algebraMap (MvPolynomial (Fin n) k) A)).toAlgebra
  let : IsScalarTower (MvPolynomial (Fin n) k) A (L ⊗[k] A) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k (MvPolynomial (Fin n) k) (L ⊗[k] A) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap k (L ⊗[k] A) r = algebraMap A (L ⊗[k] A)
        (algebraMap (MvPolynomial (Fin n) k) A (algebraMap k (MvPolynomial (Fin n) k) r))
      rw [← IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n) k) A,
        ← IsScalarTower.algebraMap_apply k A (L ⊗[k] A)]
  let : IsScalarTower k (MvPolynomial (Fin n) L) (L ⊗[k] A) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply k L (MvPolynomial (Fin n) L),
        ← IsScalarTower.algebraMap_apply L (MvPolynomial (Fin n) L) (L ⊗[k] A),
        ← IsScalarTower.algebraMap_apply k L (L ⊗[k] A)]
  let : IsScalarTower (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) L) (L ⊗[k] A) :=
    IsScalarTower.of_algebraMap_eq fun P => by
      change (1 ⊗ₜ[k] MvPolynomial.aeval (R := k) z P : L ⊗[k] A) =
        MvPolynomial.aeval (R := L) (fun i => (1 ⊗ₜ[k] z i : L ⊗[k] A))
          (MvPolynomial.map (algebraMap k L) P)
      rw [MvPolynomial.aeval_map_algebraMap]
      exact (MvPolynomial.aeval_one_tmul (N := L) k z P).symm
  let : Algebra.IsPushout (MvPolynomial (Fin n) k) A (MvPolynomial (Fin n) L)
      (L ⊗[k] A) :=
    (Algebra.IsPushout.comp_iff k (MvPolynomial (Fin n) k) L
      (MvPolynomial (Fin n) L) (T := A) (T' := L ⊗[k] A)).mp
      TensorProduct.isPushout'
  let : Module.FaithfullyFlat (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) L) :=
    Module.FaithfullyFlat.of_linearEquiv (MvPolynomial (Fin n) k) _
      (Algebra.IsPushout.equiv k (MvPolynomial (Fin n) k) L
        (MvPolynomial (Fin n) L)).symm.toLinearEquiv
  let : Algebra.Etale (MvPolynomial (Fin n) L) (L ⊗[k] A) := hz
  let : Algebra.IsPushout (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) L) A
      (L ⊗[k] A) := Algebra.IsPushout.symm inferInstance
  let e := Algebra.IsPushout.equiv (MvPolynomial (Fin n) k)
    (MvPolynomial (Fin n) L) A (L ⊗[k] A)
  let : Algebra.Etale (MvPolynomial (Fin n) L)
      ((MvPolynomial (Fin n) L) ⊗[MvPolynomial (Fin n) k] A) :=
    Algebra.Etale.of_equiv e.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat (MvPolynomial (Fin n) L)

private theorem etale_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hf : f.Etale) (hg : g.Etale) :
    (g.comp f).Etale := by
  let : Algebra R S := f.toAlgebra
  let : Algebra S T := g.toAlgebra
  let : Algebra R T := (g.comp f).toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.Etale R S := hf
  let : Algebra.Etale S T := hg
  exact Algebra.Etale.comp R S T

/-- The actual tensor-equivalence readback of the selected tuple descends
its etaleness to the same original model. -/
theorem etale_of_tensorEquiv_coordinates {B : Type*} [CommRing B] [Algebra L B]
    (E : (L ⊗[k] A) ≃ₐ[L] B) {n : ℕ} (z : Fin n → A)
    (hz : (MvPolynomial.aeval (R := L) (fun i => E (1 ⊗ₜ[k] z i))).toRingHom.Etale) :
    (MvPolynomial.aeval (R := k) z).toRingHom.Etale := by
  let a := MvPolynomial.aeval (R := L) (fun i => (1 ⊗ₜ[k] z i : L ⊗[k] A))
  let b := MvPolynomial.aeval (R := L) (fun i => E (1 ⊗ₜ[k] z i))
  let : Algebra (MvPolynomial (Fin n) L) (L ⊗[k] A) := a.toAlgebra
  let : Algebra (MvPolynomial (Fin n) L) B := b.toAlgebra
  have he : E.toAlgHom.comp a = b := by
    ext i
    simp [a, b]
  let eP : (L ⊗[k] A) ≃ₐ[MvPolynomial (Fin n) L] B :=
    { E.toRingEquiv with commutes' := fun P => DFunLike.congr_fun he P }
  let : Algebra.Etale (MvPolynomial (Fin n) L) B := hz
  have hten : Algebra.Etale (MvPolynomial (Fin n) L) (L ⊗[k] A) :=
    Algebra.Etale.of_equiv eP.symm
  exact etale_of_tensorCoordinates z hten

/-- The canonical small FIELD and model equivalences retain the SAME selected
actual etale tuple, with no selected-coordinate comparison premise. -/
theorem etale_smallModelCoordinates
    (F : Type*) [Field F] [Countable F] (A₀ : Type*) [CommRing A₀]
    [Algebra F A₀] [Countable A₀] {n : ℕ} (z : Fin n → A₀)
    (hz : (MvPolynomial.aeval (R := F) z).toRingHom.Etale) :
    (MvPolynomial.aeval (R := CountableSmallCoefficientModel.Field0 F)
      (fun i => (CountableSmallCoefficientModel.modelEquiv F A₀).symm (z i))).toRingHom.Etale := by
  let E := CountableSmallCoefficientModel.modelEquiv F A₀
  let eF := MvPolynomial.mapEquiv (Fin n) (CountableSmallCoefficientModel.fieldEquiv F)
  have hcomp :
      (MvPolynomial.aeval (R := CountableSmallCoefficientModel.Field0 F)
        (fun i => E.symm (z i))).toRingHom =
      E.symm.toRingHom.comp ((MvPolynomial.aeval (R := F) z).toRingHom.comp eF.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change MvPolynomial.aeval (R := CountableSmallCoefficientModel.Field0 F)
        (fun i => E.symm (z i)) (MvPolynomial.C c) =
          E.symm (MvPolynomial.aeval (R := F) z (eF (MvPolynomial.C c)))
      simp only [eF, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C,
        MvPolynomial.aeval_C]
      exact (E.symm.commutes (CountableSmallCoefficientModel.fieldEquiv F c)).symm
    · intro i
      simp [eF]
  rw [hcomp]
  exact etale_comp _ _
    (etale_comp _ _ (RingHom.Etale.of_bijective eF.bijective) hz)
    (RingHom.Etale.of_bijective E.symm.bijective)

end EnvelopeProperty.Char0.FieldCoordinateDescent
