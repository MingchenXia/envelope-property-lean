import Mathlib.RingTheory.AdjoinRoot

/-! # Actual affine cyclic section algebras and their root transition cocycle

The section coefficient may vanish. These are genuine native quotient algebras;
global cyclic-cover gluing and vanishing are separate constructions.
-/

open Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.CyclicSectionAlgebra
variable {R : Type u} [CommRing R]

/-- The native cyclic quotient for an arbitrary original section coefficient. -/
abbrev RootRing (n : ℕ) (a : R) := AdjoinRoot (X ^ n - C a)

/-- The original polynomial coordinate in the actual cyclic quotient. -/
def root (n : ℕ) (a : R) : RootRing n a := AdjoinRoot.root (X ^ n - C a)

/-- The original root satisfies the actual section equation, even at its zeros. -/
theorem root_pow (n : ℕ) (a : R) : root n a ^ n = algebraMap R (RootRing n a) a := by
  have h := AdjoinRoot.mk_self (f := X ^ n - C a)
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  exact sub_eq_zero.mp h

private def rootHom (n : ℕ) (a b v : R) (h : v ^ n * a = b) :
    RootRing n b →ₐ[R] RootRing n a :=
  AdjoinRoot.liftAlgHom (X ^ n - C b) (Algebra.ofId R (RootRing n a))
    (algebraMap R (RootRing n a) v * root n a) (by
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      change (algebraMap R (RootRing n a) v * root n a) ^ n -
        algebraMap R (RootRing n a) b = 0
      rw [mul_pow, root_pow, ← map_pow, ← map_mul, h, sub_self])

private theorem rootHom_root (n : ℕ) (a b v : R) (h : v ^ n * a = b) :
    rootHom n a b v h (root n b) = algebraMap R (RootRing n a) v * root n a := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The actual original root rescaling, including ramified section coefficients. -/
def rescaleEquiv (n : ℕ) (a b : R) (v : Rˣ) (h : b = (v : R) ^ n * a) :
    RootRing n b ≃ₐ[R] RootRing n a := by
  have hi : ((v⁻¹ : Rˣ) : R) ^ n * b = a := by
    rw [h, ← mul_assoc, ← mul_pow]
    simp
  let f := rootHom n a b (v : R) h.symm
  let g := rootHom n b a ((v⁻¹ : Rˣ) : R) hi
  have hgf : g.comp f = AlgHom.id R (RootRing n b) := by
    apply AdjoinRoot.algHom_ext
    change g (f (root n b)) = root n b
    dsimp only [f, g]
    rw [rootHom_root, map_mul, AlgHom.commutes, rootHom_root, ← mul_assoc, ← map_mul]
    simp
  have hfg : f.comp g = AlgHom.id R (RootRing n a) := by
    apply AdjoinRoot.algHom_ext
    change f (g (root n a)) = root n a
    dsimp only [f, g]
    rw [rootHom_root, map_mul, AlgHom.commutes, rootHom_root, ← mul_assoc, ← map_mul]
    simp
  exact AlgEquiv.ofAlgHom f g hfg hgf

/-- The rescaling acts on the SAME original quotient coordinate. -/
theorem rescaleEquiv_root (n : ℕ) (a b : R) (v : Rˣ) (h : b = (v : R) ^ n * a) :
    rescaleEquiv n a b v h (root n b) = algebraMap R (RootRing n a) (v : R) * root n a := by
  exact rootHom_root n a b (v : R) h.symm

/-- Identity change of line frame fixes the ENTIRE original cyclic algebra. -/
theorem rescaleEquiv_one (n : ℕ) (a : R) :
    rescaleEquiv n a a 1 (by simp) = AlgEquiv.refl := by
  have h : (rescaleEquiv n a a 1 (by simp)).toAlgHom = AlgHom.id R (RootRing n a) := by
    apply AdjoinRoot.algHom_ext
    change rescaleEquiv n a a 1 (by simp) (root n a) = root n a
    rw [rescaleEquiv_root]
    simp
  exact AlgEquiv.ext (fun x => DFunLike.congr_fun h x)

/-- The genuine transition maps satisfy the whole original cyclic-cover cocycle. -/
theorem rescaleEquiv_trans (n : ℕ) (a b c : R) (v w : Rˣ)
    (hb : b = (v : R) ^ n * a) (hc : c = (w : R) ^ n * b) :
    (rescaleEquiv n b c w hc).trans (rescaleEquiv n a b v hb) =
      rescaleEquiv n a c (w * v) (by rw [hc, hb]; simp only [Units.val_mul, mul_pow, mul_assoc]) := by
  have h : ((rescaleEquiv n b c w hc).trans (rescaleEquiv n a b v hb)).toAlgHom =
      (rescaleEquiv n a c (w * v) (by rw [hc, hb]; simp only [Units.val_mul, mul_pow, mul_assoc])).toAlgHom := by
    apply AdjoinRoot.algHom_ext
    change rescaleEquiv n a b v hb (rescaleEquiv n b c w hc (root n c)) =
      rescaleEquiv n a c (w * v) (by rw [hc, hb]; simp only [Units.val_mul, mul_pow, mul_assoc]) (root n c)
    rw [rescaleEquiv_root, map_mul, AlgEquiv.commutes, rescaleEquiv_root, rescaleEquiv_root]
    simp only [Units.val_mul, map_mul, mul_assoc]
  exact AlgEquiv.ext (fun x => DFunLike.congr_fun h x)

end EnvelopeProperty.CyclicSectionAlgebra
