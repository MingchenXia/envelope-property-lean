import EnvelopeProperty.AlgGeom.FormalFunctionsReesMultiplication
import Mathlib.RingTheory.Filtration

/-! # Genuine Rees linearity and finite associated filtration images -/

open scoped Polynomial DirectSum
noncomputable section
universe u
namespace EnvelopeProperty.FormalFunctionsReesLinear

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Additive induction in the actual Rees algebra by its original genuine
homogeneous monomials, retaining actual membership in every original ideal power. -/
theorem rees_induction_on {P : reesAlgebra I → Prop} (p : reesAlgebra I)
    (hzero : P 0) (hadd : ∀ p q, P p → P q → P (p + q))
    (hmonomial : ∀ d (a : ↥(I ^ d)), P (FormalFunctionsReesMultiplication.monomial I d a)) :
    P p := by
  have h (q : ⨁ d : ℕ, ↥(I ^ d)) : P ((FcReesPowerDecomposition.powerEquiv I).symm q) := by
    induction q using DirectSum.induction_on with
    | zero => simpa only [map_zero] using hzero
    | of d a =>
      have he : (FcReesPowerDecomposition.powerEquiv I).symm
          (DirectSum.of (fun d => ↥(I ^ d)) d a) =
        FormalFunctionsReesMultiplication.monomial I d a := by
        apply (FcReesPowerDecomposition.powerEquiv I).injective
        rw [LinearEquiv.apply_symm_apply]
        exact (FcReesPowerDecomposition.coefficients_monomial I d a).symm
      rw [he]
      exact hmonomial d a
    | add q q' hq hq' =>
      simpa only [map_add] using hadd _ _ hq hq'
  simpa only [LinearEquiv.symm_apply_apply] using h (FcReesPowerDecomposition.powerEquiv I p)

section Linear

variable {D : ℕ → Type u} [∀ d, AddCommGroup (D d)] [∀ d, Module R (D d)]
variable [Module (reesAlgebra I) (⨁ d : ℕ, D d)]
variable {N : Type u} [AddCommGroup N] [Module R N] [Module (reesAlgebra I) N]

/-- A genuine original coefficient-linear map is Rees-linear once its actual
homogeneous scalar square is proved on every actual original summand. -/
def linearMapOfMonomialSmul (L : (⨁ d : ℕ, D d) →ₗ[R] N)
    (hL : ∀ e (a : ↥(I ^ e)) d (x : D d),
      L (FormalFunctionsReesMultiplication.monomial I e a • DirectSum.lof R ℕ D d x) =
        FormalFunctionsReesMultiplication.monomial I e a • L (DirectSum.lof R ℕ D d x)) :
    (⨁ d : ℕ, D d) →ₗ[reesAlgebra I] N where
  toFun := L
  map_add' := L.map_add
  map_smul' p x := by
    change L (p • x) = p • L x
    induction p using rees_induction_on I with
    | hzero => simp only [zero_smul, map_zero]
    | hadd p q hp hq =>
      rw [add_smul, L.map_add, hp, hq, add_smul]
    | hmonomial e a =>
      induction x using DirectSum.induction_on with
      | zero => simp only [smul_zero, map_zero]
      | of d x => exact hL e a d x
      | add x y hx hy =>
        rw [smul_add, L.map_add, hx, hy, L.map_add, smul_add]

end Linear

variable {N : Type u} [AddCommGroup N] [Module R N]

/-- An ACTUAL surjection from a finite Rees module proves stability of the
SAME original filtration; no stability or associated-finiteness certificate is assumed. -/
theorem filtration_stable_of_surjective [IsNoetherianRing R] [Module.Finite R N]
    (F : I.Filtration N) {M : Type u} [AddCommGroup M] [Module (reesAlgebra I) M]
    [Module.Finite (reesAlgebra I) M] (L : M →ₗ[reesAlgebra I] F.submodule)
    (hL : Function.Surjective L) : F.Stable := by
  let : Module.Finite (reesAlgebra I) F.submodule := Module.Finite.of_surjective L hL
  apply (F.submodule_fg_iff_stable (fun n => IsNoetherian.noetherian (F.N n))).mp
  exact Module.Finite.iff_fg.mp inferInstance

end EnvelopeProperty.FormalFunctionsReesLinear
