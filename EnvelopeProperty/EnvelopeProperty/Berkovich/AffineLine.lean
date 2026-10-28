/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual affine lines through rational points

The genuine linear polynomial substitution preserves every coefficient and the
entire rational point at parameter zero. A nonzero direction makes its polynomial
homomorphism surjective, hence gives an actual closed scheme immersion of the line.
Over any infinite field and nonempty coordinate set, it constructs a real direction
and parameter meeting any given nonzero polynomial principal open, with only
finitely many bad rational parameters.

This pure algebra and scheme module is independent of all analytic point spaces,
field norms and paper interfaces. Open-subset curves, dimension, reduction,
normalization and subharmonicity are separate producers.
-/

open scoped Polynomial
noncomputable section
namespace EnvelopeProperty.AffineLine
variable {F σ : Type*} [Field F]

/-- The actual affine line substitution sends every coordinate to a_i+t b_i. -/
def subst (a b : σ → F) : MvPolynomial σ F →ₐ[F] F[X] :=
  MvPolynomial.aeval fun i => Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X

/-- The actual rational point at parameter t. -/
def point (a b : σ → F) (t : F) : σ → F := fun i => a i + t * b i

/-- Entire polynomial evaluation agrees with the actual affine parameter point. -/
theorem aeval_comp_subst (a b : σ → F) (t : F) :
    (Polynomial.aeval t).comp (subst a b) = MvPolynomial.aeval (point a b t) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, subst, MvPolynomial.aeval_X, map_add, map_mul,
    Polynomial.aeval_C, Polynomial.aeval_X, point, Algebra.algebraMap_self, RingHom.id_apply]
  rw [mul_comm]

/-- The whole original polynomial has the same value after actual parameter evaluation. -/
theorem eval_subst (a b : σ → F) (t : F) (p : MvPolynomial σ F) :
    Polynomial.eval t (subst a b p) = MvPolynomial.eval (point a b t) p :=
  congrArg (fun f : MvPolynomial σ F →ₐ[F] F => f p) (aeval_comp_subst a b t)

/-- Parameter zero returns the entire original polynomial value. -/
theorem eval_subst_zero (a b : σ → F) (p : MvPolynomial σ F) :
    Polynomial.eval 0 (subst a b p) = MvPolynomial.eval a p := by
  have h : point a b 0 = a := by
    funext i
    simp only [point, zero_mul, add_zero]
  simpa only [h] using eval_subst a b 0 p

/-- The actual linear-polynomial coordinate map is onto when its direction is nonzero. -/
theorem subst_surjective (a b : σ → F) (hb : b ≠ 0) : Function.Surjective (subst a b) := by
  classical
  have hi : ∃ i, b i ≠ 0 := by
    by_contra! h
    exact hb (funext h)
  obtain ⟨i, hi⟩ := hi
  let q : MvPolynomial σ F := MvPolynomial.C (b i)⁻¹ * (MvPolynomial.X i - MvPolynomial.C (a i))
  have hq : subst a b q = Polynomial.X := by
    simp only [q, map_mul, map_sub, subst, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Polynomial.algebraMap_eq, add_sub_cancel_left]
    rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hi, map_one, one_mul]
  intro p
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' =>
    obtain ⟨q, hq⟩ := hp
    obtain ⟨q', hq'⟩ := hp'
    exact ⟨q + q', by simp only [map_add, hq, hq']⟩
  | monomial n c =>
    refine ⟨MvPolynomial.C c * q ^ n, ?_⟩
    simp only [map_mul, map_pow, hq]
    rw [show subst a b (MvPolynomial.C c) = Polynomial.C c from by simp only [subst, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]]
    exact Polynomial.C_mul_X_pow_eq_monomial

/-- A nonzero polynomial has an actual rational point outside its vanishing locus. -/
theorem exists_eval_ne_zero [Infinite F] {p : MvPolynomial σ F} (hp : p ≠ 0) :
    ∃ a : σ → F, MvPolynomial.eval a p ≠ 0 := by
  by_contra! h
  apply hp
  exact MvPolynomial.funext fun a => by simpa only [map_zero] using h a

/-- A genuine nonconstant affine line through any rational point meets a given principal open. -/
theorem exists_direction_subst_ne_zero [Infinite F] [Nonempty σ]
    (a : σ → F) {p : MvPolynomial σ F} (hp : p ≠ 0) :
    ∃ b : σ → F, b ≠ 0 ∧ subst a b p ≠ 0 := by
  classical
  by_cases ha : MvPolynomial.eval a p = 0
  · obtain ⟨z, hz⟩ := exists_eval_ne_zero hp
    let b : σ → F := fun i => z i - a i
    have hb : b ≠ 0 := by
      intro hb
      have hza : z = a := by
        funext i
        have hi := congrFun hb i
        change z i - a i = 0 at hi
        exact sub_eq_zero.mp hi
      exact hz (hza ▸ ha)
    refine ⟨b, hb, ?_⟩
    intro hzero
    have ht : point a b 1 = z := by
      funext i
      simp [point, b]
    have he := eval_subst a b 1 p
    rw [hzero, Polynomial.eval_zero, ht] at he
    exact hz he.symm
  · let i : σ := Classical.choice inferInstance
    let b : σ → F := fun j => if j = i then 1 else 0
    have hb : b ≠ 0 := by
      intro hb
      have h := congrFun hb i
      simp [b] at h
    refine ⟨b, hb, ?_⟩
    intro hzero
    have he := eval_subst_zero a b p
    rw [hzero, Polynomial.eval_zero] at he
    exact ha he.symm


/-- The actual line has a genuine rational parameter in the prescribed principal open. -/
theorem exists_direction_parameter_ne_zero [Infinite F] [Nonempty σ]
    (a : σ → F) {p : MvPolynomial σ F} (hp : p ≠ 0) :
    ∃ b : σ → F, b ≠ 0 ∧ ∃ t : F, MvPolynomial.eval (point a b t) p ≠ 0 := by
  obtain ⟨b, hb, hline⟩ := exists_direction_subst_ne_zero a hp
  have ht : ∃ t : F, Polynomial.eval t (subst a b p) ≠ 0 := by
    by_contra! h
    exact hline (Polynomial.zero_of_eval_zero _ h)
  obtain ⟨t, ht⟩ := ht
  exact ⟨b, hb, t, by simpa only [eval_subst] using ht⟩

/-- The line passes through the entire given F-rational algebra homomorphism at zero. -/
theorem aeval_zero_comp_subst (φ : MvPolynomial σ F →ₐ[F] F) (b : σ → F) :
    (Polynomial.aeval 0).comp (subst (fun i => φ (MvPolynomial.X i)) b) = φ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, subst, MvPolynomial.aeval_X, map_add, map_mul,
    Polynomial.aeval_C, Polynomial.aeval_X, mul_zero, add_zero,
    Algebra.algebraMap_self, RingHom.id_apply]

/-- A nonzero restricted polynomial excludes only finitely many actual rational parameters. -/
theorem finite_bad_parameters (a b : σ → F) {p : MvPolynomial σ F}
    (hp : subst a b p ≠ 0) : {t : F | MvPolynomial.eval (point a b t) p = 0}.Finite := by
  simpa only [Polynomial.IsRoot, eval_subst] using Polynomial.finite_setOfPred_isRoot hp

section Schemes
open AlgebraicGeometry CategoryTheory
universe u
variable {F σ : Type u} [Field F]

/-- The actual affine line scheme morphism induced by the whole coordinate substitution. -/
def schemeMap (a b : σ → F) :
    Spec (CommRingCat.of F[X]) ⟶ Spec (CommRingCat.of (MvPolynomial σ F)) :=
  Spec.map (CommRingCat.ofHom (subst a b).toRingHom)

/-- A nonzero direction gives a genuine closed line immersion. -/
theorem schemeMap_isClosedImmersion (a b : σ → F) (hb : b ≠ 0) :
    IsClosedImmersion (schemeMap a b) :=
  IsClosedImmersion.spec_of_surjective _ (subst_surjective a b hb)

/-- The actual scheme point at zero is the original whole rational point, not just its coordinate values. -/
theorem schemeMap_zero (a b : σ → F) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0 : F[X] →+* F)) ≫ schemeMap a b =
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval a)) := by
  rw [schemeMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact eval_subst_zero a b p

end Schemes
end EnvelopeProperty.AffineLine
