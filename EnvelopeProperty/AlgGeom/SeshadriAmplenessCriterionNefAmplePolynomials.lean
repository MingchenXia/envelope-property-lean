import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionIntersectionPositivity
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # The intersection polynomial of a line pencil

Let `p : X ⟶ Spec k` be projective and let `N, A` be invertible modules on `X`.
For a list `λ` of invertible modules and a coherent module `F`, the mixed Euler
difference `I(λ; F) = Δ_λ χ(X, F)` (`SeshadriAmplenessCriterion.mixedEulerDifference`) is the
intersection number `λ · F` when `|λ| = dim X`. This file defines the polynomial
`P_n(λ; F)(t)`, the full multilinear expansion of `(N + t A)^n · λ · F`, by the recursion
`P_0(λ; F) = I(λ; F)` and `P_{n+1}(λ; F) = P_n(N, λ; F) + t P_n(A, λ; F)`, and proves:

* permutation invariance in `λ`, the degree bound and the top coefficient
  `I(A^n, λ; F)`;
* the derivative formula `P_{n+1}'(λ; F) = (n + 1) P_n(A, λ; F)`;
* exact denominator clearing in top degree (`n + |λ| = D ≥ dim X`):
  `b^n P_n(λ; F)(a / b) = I((N^b ⊗ A^a)^n, λ; F)`.

These are the intersection polynomials of the proof of Kleiman's theorem that nef plus
ample is ample (Lazarsfeld, *Positivity I*, Theorem 1.4.9 and Corollary 1.4.10), in the form
used by the numerical criterion of `SeshadriAmplenessCriterionNefAmple.isAmple_tensor_nef`.

Blueprint: `seshadri-ampleness-criterion-nef-ample-polynomials.tex`.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace Polynomial
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterionNefAmple
open SeshadriAmplenessCriterion
section Algebra
variable {α : Type*} (I : List α → ℝ) (N A : α)
private def pencilAux : ℕ → List α → Polynomial ℝ
  | 0, ls => C (I ls)
  | n + 1, ls => pencilAux n (N :: ls) + X * pencilAux n (A :: ls)

private theorem move_cons (L B : α) (n : ℕ) (ls : List α) :
    (L :: List.replicate n B ++ ls).Perm (List.replicate n B ++ L :: ls) := by
  induction n with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    simpa only [List.replicate_succ, List.cons_append] using
      (List.Perm.swap B L (List.replicate n B ++ ls)).trans (List.Perm.cons B ih)

private theorem pencilAux_perm (hI : ∀ {ls ms : List α}, ls.Perm ms → I ls = I ms)
    (n : ℕ) {ls ms : List α} (hp : ls.Perm ms) :
    pencilAux I N A n ls = pencilAux I N A n ms := by
  induction n generalizing ls ms with
  | zero => exact congrArg C (hI hp)
  | succ n ih =>
    simp only [pencilAux]
    rw [ih (List.Perm.cons N hp), ih (List.Perm.cons A hp)]

private theorem pencilAux_natDegree_le (n : ℕ) (ls : List α) :
    (pencilAux I N A n ls).natDegree ≤ n := by
  induction n generalizing ls with
  | zero => simp [pencilAux]
  | succ n ih =>
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact (ih (N :: ls)).trans (Nat.le_succ n)
    · exact (Polynomial.natDegree_mul_le.trans
        (add_le_add (show (X : Polynomial ℝ).natDegree ≤ 1 by simp) (ih (A :: ls)))).trans
        (by omega)

private theorem pencilAux_coeff_top (hI : ∀ {ls ms : List α}, ls.Perm ms → I ls = I ms)
    (n : ℕ) (ls : List α) :
    (pencilAux I N A n ls).coeff n = I (List.replicate n A ++ ls) := by
  induction n generalizing ls with
  | zero => simp [pencilAux]
  | succ n ih =>
    rw [pencilAux, Polynomial.coeff_add, Polynomial.coeff_X_mul,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        ((pencilAux_natDegree_le I N A n (N :: ls)).trans_lt (Nat.lt_succ_self n)),
      zero_add, ih (A :: ls)]
    simp only [List.replicate_succ, List.cons_append]
    exact (hI (move_cons A A n ls)).symm

private theorem pencilAux_derivative_succ (hI : ∀ {ls ms : List α}, ls.Perm ms → I ls = I ms)
    (n : ℕ) (ls : List α) :
    derivative (pencilAux I N A (n + 1) ls) = C ((n + 1 : ℕ) : ℝ) *
        pencilAux I N A n (A :: ls) := by
  induction n generalizing ls with
  | zero => simp [pencilAux]
  | succ n ih =>
    have hs := pencilAux_perm I N A hI n (List.Perm.swap N A ls)
    calc
      derivative (pencilAux I N A (n + 1 + 1) ls) =
          derivative (pencilAux I N A (n + 1) (N :: ls)) + pencilAux I N A (n + 1) (A :: ls) +
            X * derivative (pencilAux I N A (n + 1) (A :: ls)) := by
        rw [pencilAux, derivative_add, derivative_mul, derivative_X, one_mul]
        ring
      _ = C ((n + 1 : ℕ) : ℝ) * pencilAux I N A n (A :: N :: ls) +
          pencilAux I N A (n + 1) (A :: ls) +
          X * (C ((n + 1 : ℕ) : ℝ) * pencilAux I N A n (A :: A :: ls)) := by rw [ih, ih]
      _ = C ((n + 1 + 1 : ℕ) : ℝ) * pencilAux I N A (n + 1) (A :: ls) := by
        rw [hs]
        simp only [pencilAux, Nat.cast_add, Nat.cast_one, Polynomial.C_add, Polynomial.C_1]
        ring
private theorem pencilAux_eval_scale
    (hI : ∀ {ls ms : List α}, ls.Perm ms → I ls = I ms)
    (valid : α → Prop) (hN : valid N) (hA : valid A)
    (a b : ℝ) (hb : b ≠ 0) (B : α) (hB : valid B) (D : ℕ)
    (hcombine : ∀ ls : List α, ls.length + 1 = D →
      (∀ L ∈ ls, valid L) → I (B :: ls) = b * I (N :: ls) + a * I (A :: ls))
    (n : ℕ) (ls : List α) (hlen : n + ls.length = D)
    (hls : ∀ L ∈ ls, valid L) :
    b ^ n * (pencilAux I N A n ls).eval (a / b) = I (List.replicate n B ++ ls) := by
  induction n generalizing ls with
  | zero => simp [pencilAux]
  | succ n ih =>
    let R := List.replicate n B ++ ls
    have hlenR : R.length + 1 = D := by
      simp only [R, List.length_append, List.length_replicate]
      omega
    have hR : ∀ L ∈ R, valid L := by
      intro L hL
      rcases List.mem_append.mp hL with hL | hL
      · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hL
        exact hB
      · exact hls L hL
    have hlenN : n + (N :: ls).length = D := by simp only [List.length_cons]; omega
    have hlenA : n + (A :: ls).length = D := by simp only [List.length_cons]; omega
    have hlsN : ∀ L ∈ N :: ls, valid L := by
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hN
      · exact hls L hL
    have hlsA : ∀ L ∈ A :: ls, valid L := by
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hA
      · exact hls L hL
    have hNm : I (N :: R) = I (List.replicate n B ++ N :: ls) := hI (move_cons N B n ls)
    have hAm : I (A :: R) = I (List.replicate n B ++ A :: ls) := hI (move_cons A B n ls)
    have hC := hcombine R hlenR hR
    have hquot : b * (a / b) = a := by
      simpa only [mul_comm] using div_mul_cancel₀ a hb
    change b ^ (n + 1) * (pencilAux I N A (n + 1) ls).eval (a / b) = I (B :: R)
    calc
      b ^ (n + 1) * (pencilAux I N A (n + 1) ls).eval (a / b) =
          b * (b ^ n * (pencilAux I N A n (N :: ls)).eval (a / b)) +
            a * (b ^ n * (pencilAux I N A n (A :: ls)).eval (a / b)) := by
        simp only [pencilAux, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, pow_succ]
        calc
          _ = b * (b ^ n * (pencilAux I N A n (N :: ls)).eval (a / b)) +
              (b * (a / b)) * (b ^ n * (pencilAux I N A n (A :: ls)).eval (a / b)) := by ring
          _ = _ := by rw [hquot]
      _ = b * I (List.replicate n B ++ N :: ls) +
            a * I (List.replicate n B ++ A :: ls) := by rw [ih _ hlenN hlsN, ih _ hlenA hlsA]
      _ = I (B :: R) := by rw [← hNm, ← hAm]; exact hC.symm

end Algebra
section Geometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
variable {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X]
variable (f : X ⟶ Spec (.of k))

/-- The pencil polynomial `P_n(λ; F)(t)`: the full multilinear expansion of
`(N + t A)^n · λ · F`, whose coefficients are mixed Euler differences. -/
def mixedPencilPolynomial (N A : X.Modules) (n : ℕ) (ls : List X.Modules)
    (F : X.Modules) : Polynomial ℝ :=
  pencilAux (fun ms => (mixedEulerDifference f ms F : ℝ)) N A n ls

/-- With no variable slots, the pencil polynomial is the constant `I(λ; F)`. -/
theorem mixedPencilPolynomial_zero (N A : X.Modules) (ls : List X.Modules)
    (F : X.Modules) :
    mixedPencilPolynomial f N A 0 ls F =
      Polynomial.C (mixedEulerDifference f ls F : ℝ) := rfl

/-- The defining recursion `P_{n+1}(λ; F) = P_n(N, λ; F) + t P_n(A, λ; F)`. -/
theorem mixedPencilPolynomial_succ (N A : X.Modules) (n : ℕ)
    (ls : List X.Modules) (F : X.Modules) :
    mixedPencilPolynomial f N A (n + 1) ls F =
      mixedPencilPolynomial f N A n (N :: ls) F +
        Polynomial.X * mixedPencilPolynomial f N A n (A :: ls) F := rfl

/-- Permuting the fixed list `λ` does not change the pencil polynomial. -/
theorem mixedPencilPolynomial_perm (N A : X.Modules) (n : ℕ)
    {ls ms : List X.Modules} (hp : ls.Perm ms) (F : X.Modules) :
    mixedPencilPolynomial f N A n ls F = mixedPencilPolynomial f N A n ms F :=
  pencilAux_perm _ N A
    (fun h => congrArg (fun z : ℤ => (z : ℝ)) (mixedEulerDifference_perm f h F)) n hp

/-- The pencil polynomial `P_n(λ; F)` has degree at most `n`. -/
theorem mixedPencilPolynomial_natDegree_le (N A : X.Modules) (n : ℕ)
    (ls : List X.Modules) (F : X.Modules) :
    (mixedPencilPolynomial f N A n ls F).natDegree ≤ n :=
  pencilAux_natDegree_le _ N A n ls

/-- The coefficient of `t^n` in `P_n(λ; F)` is `I(A^n, λ; F)`. -/
theorem mixedPencilPolynomial_coeff_top (N A : X.Modules) (n : ℕ)
    (ls : List X.Modules) (F : X.Modules) :
    (mixedPencilPolynomial f N A n ls F).coeff n =
      (mixedEulerDifference f (List.replicate n A ++ ls) F : ℝ) :=
  pencilAux_coeff_top _ N A
    (fun h => congrArg (fun z : ℤ => (z : ℝ)) (mixedEulerDifference_perm f h F)) n ls

/-- Formal differentiation inserts the direction `A`:
`P_{n+1}(λ; F)' = (n + 1) P_n(A, λ; F)`. -/
theorem mixedPencilPolynomial_derivative_succ (N A : X.Modules) (n : ℕ)
    (ls : List X.Modules) (F : X.Modules) :
    Polynomial.derivative (mixedPencilPolynomial f N A (n + 1) ls F) =
      Polynomial.C ((n + 1 : ℕ) : ℝ) * mixedPencilPolynomial f N A n (A :: ls) F :=
  pencilAux_derivative_succ _ N A
    (fun h => congrArg (fun z : ℤ => (z : ℝ)) (mixedEulerDifference_perm f h F)) n ls

/-- At every real parameter, the derivative of the top pencil polynomial with one fixed
slot `A` is nonnegative as soon as the polynomial with the two fixed slots `A, A` is
nonnegative there (for `n = 0` the derivative vanishes). -/
theorem mixedPencilPolynomial_derivative_eval_nonneg (N A : X.Modules) (n : ℕ)
    (ls : List X.Modules) (F : X.Modules) (t : ℝ)
    (h : ∀ m : ℕ, n = m + 1 → 0 ≤ (mixedPencilPolynomial f N A m (A :: ls) F).eval t) :
    0 ≤ (Polynomial.derivative (mixedPencilPolynomial f N A n ls F)).eval t := by
  cases n with
  | zero =>
    rw [mixedPencilPolynomial_zero, Polynomial.derivative_C, Polynomial.eval_zero]
  | succ m =>
    rw [mixedPencilPolynomial_derivative_succ, Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_nonneg (Nat.cast_nonneg _) (h m rfl)

variable [X.IsSeparated] [IsProjective f]

/-- Clearing a positive denominator in top degree gives exactly the mixed intersection
of the tensor-power line `N^b ⊗ A^a`: if `dim X ≤ D = n + |λ|`, then
`b^n P_n(λ; F)(a / b) = I((N^b ⊗ A^a)^n, λ; F)`. The required multilinearity is the
top-degree tensor additivity of mixed Euler differences. -/
theorem mixedPencilPolynomial_eval_scale (N A : X.Modules)
    (hN : IsInvertible N) (hA : IsInvertible A)
    (n : ℕ) (ls : List X.Modules) (D : ℕ)
    (hdim : topologicalKrullDim X ≤ D) (hlen : n + ls.length = D)
    (hls : ∀ L ∈ ls, IsInvertible L)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (a b : ℕ) (hb : 0 < b) :
    (b : ℝ) ^ n * (mixedPencilPolynomial f N A n ls F).eval ((a : ℝ) / (b : ℝ)) =
      (mixedEulerDifference f
        (List.replicate n (CanonicalGeometry.bundleTensorPower N b ⊗
          CanonicalGeometry.bundleTensorPower A a) ++ ls) F : ℝ) := by
  have hPN : IsInvertible (CanonicalGeometry.bundleTensorPower N b) :=
    TensorPowerBaseIdealGrading.tensorPower_isInvertible hN b
  have hPA : IsInvertible (CanonicalGeometry.bundleTensorPower A a) :=
    TensorPowerBaseIdealGrading.tensorPower_isInvertible hA a
  have hB : IsInvertible (CanonicalGeometry.bundleTensorPower N b ⊗
      CanonicalGeometry.bundleTensorPower A a) :=
    (hPN.tensorObj hPA).of_iso (ModularCurves.monoidalTensorObjIso _ _)
  refine pencilAux_eval_scale _ N A
    (fun h => congrArg (fun z : ℤ => (z : ℝ)) (mixedEulerDifference_perm f h F))
    IsInvertible hN hA (a : ℝ) (b : ℝ) (by exact_mod_cast hb.ne')
    _ hB D ?_ n ls hlen hls
  intro tail htail hInv
  have hline : mixedEulerDifference f
      ((CanonicalGeometry.bundleTensorPower N b ⊗ CanonicalGeometry.bundleTensorPower A a) ::
        tail) F =
      (b : ℤ) * mixedEulerDifference f (N :: tail) F +
        (a : ℤ) * mixedEulerDifference f (A :: tail) F := by
    rw [mixedEulerDifference_tensor_add f D hdim _ _ hPN hPA tail htail hInv F,
      mixedEulerDifference_tensorPower_cons f D hdim N hN tail htail hInv F b,
      mixedEulerDifference_tensorPower_cons f D hdim A hA tail htail hInv F a]
  exact_mod_cast hline
end Geometry
end EnvelopeProperty.SeshadriAmplenessCriterionNefAmple
