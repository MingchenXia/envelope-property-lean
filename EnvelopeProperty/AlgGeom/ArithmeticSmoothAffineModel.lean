import EnvelopeProperty.AlgGeom.ArithmeticSmoothCoefficientBase
import Mathlib.RingTheory.Smooth.NoetherianDescent

/-!
# A genuinely smooth affine arithmetic family with the same original algebra

The native smooth Noetherian-descent producer constructs a genuinely smooth
coefficient model from the original smooth algebra. We enlarge its actual
integer coefficient subalgebra by all specified original coefficients, and use
the preceding actual smooth arithmetic-base producer. Extending that SAME
native smooth model gives a genuinely smooth model over the produced smooth
integer base, with the entire original tensor equivalence retained.
-/

noncomputable section
open scoped TensorProduct Classical

namespace EnvelopeProperty.ArithmeticSmoothAffineModel

open ArithmeticCoefficientModel ArithmeticSmoothCoefficientBase

universe u v w z
variable {k : Type u} [Field k] {σ : Type w} {ι : Type z}

/-- The actual joined integer coefficient subalgebra inside the same original field. -/
def coefficientEnlargement (R₀ : Subalgebra ℤ k) (fs : ι → MvPolynomial σ k)
    (extra : Finset k) : Subalgebra ℤ k :=
  R₀ ⊔ coefficientRing fs extra

/-- Finite original coefficients can be adjoined to the actual finitely generated smooth core. -/
theorem coefficientEnlargement_finiteType [Finite ι] (R₀ : Subalgebra ℤ k) (hR₀ : R₀.FG)
    (fs : ι → MvPolynomial σ k) (extra : Finset k) :
    Algebra.FiniteType ℤ (coefficientEnlargement R₀ fs extra) :=
  (Subalgebra.fg_iff_finiteType _).mp
    (hR₀.sup ((Subalgebra.fg_iff_finiteType _).mpr (coefficientRing_finiteType fs extra)))

/-- Actual enlargement and the produced smooth principal open retain all original coefficients. -/
theorem exists_smooth_coefficientEnlargement [CharZero k] [Finite ι]
    (R₀ : Subalgebra ℤ k) (hR₀ : R₀.FG) (fs : ι → MvPolynomial σ k) (extra : Finset k) :
    ∃ S : Subalgebra ℤ k, R₀ ≤ S ∧ coefficientRing fs extra ≤ S ∧
      Algebra.Smooth ℤ S ∧ Algebra.FiniteType ℤ S ∧ IsDomain S ∧ CharZero S := by
  let R₁ := coefficientEnlargement R₀ fs extra
  let : Algebra.FiniteType ℤ R₁ := coefficientEnlargement_finiteType R₀ hR₀ fs extra
  obtain ⟨r, hr, -, hs, hFT, hD, hC, -, hle⟩ := exists_smooth_localizedCoefficientRing R₁
  exact ⟨localizedCoefficientRing R₁ r hr, le_sup_left.trans hle, le_sup_right.trans hle,
    hs, hFT, hD, hC⟩

variable {A : Type v} [CommRing A] [Algebra k A]

/-- Original smoothness produces an ACTUAL smooth affine model over an ACTUAL smooth integer
subalgebra of the same field. The native coefficient model and its whole original equivalence
are internally produced; specified original coefficients/extras are retained literally. -/
theorem exists_smooth_affine_arithmetic_model [CharZero k] [Algebra.Smooth k A] [Finite ι]
    (fs : ι → MvPolynomial σ k) (extra : Finset k) :
    ∃ (R₀ : Subalgebra ℤ k) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra R₀ B₀),
      R₀.FG ∧ Algebra.Smooth R₀ B₀ ∧
      ∃ E₀ : (k ⊗[R₀] B₀) ≃ₐ[k] A,
      ∃ (S : Subalgebra ℤ k) (h₀ : R₀ ≤ S),
        letI : Algebra R₀ S := (Subalgebra.inclusion h₀).toRingHom.toAlgebra
        letI : @IsScalarTower R₀ S k (inferInstance : Algebra R₀ S).toSMul
            (inferInstance : Algebra S k).toSMul (inferInstance : Algebra R₀ k).toSMul :=
          IsScalarTower.of_algebraMap_eq' (R := R₀) (S := S) (A := k) (by ext x; rfl)
        Algebra.Smooth ℤ S ∧ Algebra.FiniteType ℤ S ∧ IsDomain S ∧ CharZero S ∧
        coefficientRing fs extra ≤ S ∧
        Algebra.Smooth S (S ⊗[R₀] B₀) ∧ Algebra.FinitePresentation S (S ⊗[R₀] B₀) ∧
        ∃ E : (k ⊗[S] (S ⊗[R₀] B₀)) ≃ₐ[k] A,
          E.toAlgHom.comp (Algebra.TensorProduct.cancelBaseChange R₀ S k k B₀).symm.toAlgHom =
              E₀.toAlgHom ∧
          (∀ (c : k) (s : S) (b : B₀), E (c ⊗ₜ (s ⊗ₜ b)) = E₀ (((s : k) * c) ⊗ₜ b)) ∧
          E.toRingHom.comp (algebraMap k (k ⊗[S] (S ⊗[R₀] B₀))) = algebraMap k A := by
  obtain ⟨R₀, B₀, _, _, hR₀, hB₀, ⟨Eback⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ k A
  let E₀ : (k ⊗[R₀] B₀) ≃ₐ[k] A := Eback.symm
  obtain ⟨S, h₀, hcoeff, hS, hFT, hD, hC⟩ := exists_smooth_coefficientEnlargement R₀ hR₀ fs extra
  let : Algebra R₀ S := (Subalgebra.inclusion h₀).toRingHom.toAlgebra
  let : @IsScalarTower R₀ S k (inferInstance : Algebra R₀ S).toSMul
      (inferInstance : Algebra S k).toSMul (inferInstance : Algebra R₀ k).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := R₀) (S := S) (A := k) (by ext x; rfl)
  let : Algebra.Smooth R₀ B₀ := hB₀
  let : Algebra.Smooth S (S ⊗[R₀] B₀) := Algebra.Smooth.baseChange R₀ B₀ S
  let E : (k ⊗[S] (S ⊗[R₀] B₀)) ≃ₐ[k] A :=
    (Algebra.TensorProduct.cancelBaseChange R₀ S k k B₀).trans E₀
  refine ⟨R₀, B₀, inferInstance, inferInstance, hR₀, hB₀, E₀, S, h₀, hS, hFT, hD, hC,
    hcoeff, inferInstance, inferInstance, E, ?_, ?_, ?_⟩
  · apply AlgHom.ext
    intro x
    exact congrArg E₀ ((Algebra.TensorProduct.cancelBaseChange R₀ S k k B₀).apply_symm_apply x)
  · intro c s b
    change E₀ ((Algebra.TensorProduct.cancelBaseChange R₀ S k k B₀) (c ⊗ₜ (s ⊗ₜ b))) = _
    rw [Algebra.TensorProduct.cancelBaseChange_tmul]
    rfl
  · ext c
    exact E.commutes c

end EnvelopeProperty.ArithmeticSmoothAffineModel
