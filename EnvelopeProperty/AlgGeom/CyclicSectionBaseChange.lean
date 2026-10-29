import EnvelopeProperty.AlgGeom.CyclicSectionAlgebra

/-! # Actual cyclic coefficient base change and the whole frame square

The tensor equivalence specializes native `AdjoinRoot.tensorAlgEquiv` and
`TensorProduct.rid`, the same composition used by the existing general
`Alterations.Algebra.ResidueExtensionLift.baseChangeEquiv`.
No dependency source is modified or copied.
-/

open Polynomial Algebra.TensorProduct
open scoped TensorProduct
noncomputable section
universe u v w
namespace EnvelopeProperty.CyclicSectionBaseChange
open CyclicSectionAlgebra
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]

/-- Actual tensor base change keeps the prescribed original cyclic coefficient. -/
def baseChangeEquiv (n : ℕ) (a : R) (b : S) (h : b = algebraMap R S a) :
    S ⊗[R] RootRing n a ≃ₐ[S] RootRing n b := by
  let q : (S ⊗[R] R)[X] := X ^ n - C (1 ⊗ₜ[R] a)
  let e := Algebra.TensorProduct.rid R S S
  have hq : (X ^ n - C a).map (includeRight : R →ₐ[R] S ⊗[R] R).toRingHom = q := by
    simp [q]
  have he : q.map e.toRingHom = (X ^ n - C b : S[X]) := by
    simp [q, e, h, Algebra.smul_def]
  refine (AdjoinRoot.tensorAlgEquiv (X ^ n - C a) q hq).trans
    (AdjoinRoot.mapAlgEquiv e q (X ^ n - C b) ?_)
  change Associated (q.map e.toRingHom) (X ^ n - C b)
  rw [he]

/-- The actual tensor equivalence preserves the SAME original root. -/
theorem baseChangeEquiv_root (n : ℕ) (a : R) (b : S) (h : b = algebraMap R S a) :
    baseChangeEquiv n a b h (1 ⊗ₜ[R] root n a) = root n b := by
  simp [baseChangeEquiv, root]

/-- The actual original cyclic coefficient-extension algebra morphism. -/
def coefficientMap (n : ℕ) (a : R) (b : S) (h : b = algebraMap R S a) :
    RootRing n a →ₐ[R] RootRing n b :=
  AdjoinRoot.mapAlgHom (Algebra.ofId R S) (X ^ n - C a) (X ^ n - C b) (by
    change (X ^ n - C b) ∣ (X ^ n - C a).map (algebraMap R S)
    simp [h])

/-- Coefficient extension sends the original root to the actual original target root. -/
theorem coefficientMap_root (n : ℕ) (a : R) (b : S) (h : b = algebraMap R S a) :
    coefficientMap n a b h (root n a) = root n b := by
  simp [coefficientMap, root]

/-- The WHOLE original tensor comparison induces the SAME coefficient-extension map. -/
theorem baseChangeEquiv_includeRight (n : ℕ) (a : R) (b : S) (h : b = algebraMap R S a) :
    ((baseChangeEquiv n a b h).toAlgHom.restrictScalars R).comp
      (includeRight : RootRing n a →ₐ[R] S ⊗[R] RootRing n a) = coefficientMap n a b h := by
  apply AdjoinRoot.algHom_ext
  change baseChangeEquiv n a b h (1 ⊗ₜ[R] root n a) = coefficientMap n a b h (root n a)
  rw [baseChangeEquiv_root, coefficientMap_root]

/-- The original identity coefficient map fixes the ENTIRE original cyclic quotient. -/
theorem coefficientMap_id (n : ℕ) (a : R) :
    coefficientMap n a a (by simp) = AlgHom.id R (RootRing n a) := by
  apply AdjoinRoot.algHom_ext
  change coefficientMap n a a (by simp) (root n a) = root n a
  exact coefficientMap_root n a a _

variable {T : Type w} [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Every actual tower preserves the WHOLE original coefficient-map composition. -/
theorem coefficientMap_comp (n : ℕ) (a : R) (b : S) (c : T)
    (hb : b = algebraMap R S a) (hc : c = algebraMap S T b) :
    ((coefficientMap n b c hc).restrictScalars R).comp (coefficientMap n a b hb) =
      coefficientMap n a c (by rw [hc, hb, ← IsScalarTower.algebraMap_apply R S T]) := by
  apply AdjoinRoot.algHom_ext
  change coefficientMap n b c hc (coefficientMap n a b hb (root n a)) =
    coefficientMap n a c (by rw [hc, hb, ← IsScalarTower.algebraMap_apply R S T]) (root n a)
  rw [coefficientMap_root, coefficientMap_root, coefficientMap_root]

omit [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T] in
/-- Actual affine coefficient extension commutes with the SAME original frame rescaling
on the ENTIRE original cyclic quotient. -/
theorem coefficientMap_rescale (n : ℕ) (a b : R) (c d : S) (u : Rˣ)
    (h : b = (u : R) ^ n * a) (hc : c = algebraMap R S a) (hd : d = algebraMap R S b) :
    (coefficientMap n a c hc).comp (rescaleEquiv n a b u h).toAlgHom =
      ((rescaleEquiv n c d (Units.map (algebraMap R S).toMonoidHom u) (by
        change d = (algebraMap R S (u : R)) ^ n * c
        rw [hd, h, map_mul, map_pow, ← hc])).toAlgHom.restrictScalars R).comp
        (coefficientMap n b d hd) := by
  apply AdjoinRoot.algHom_ext
  change coefficientMap n a c hc (rescaleEquiv n a b u h (root n b)) =
    rescaleEquiv n c d (Units.map (algebraMap R S).toMonoidHom u) (by
      change d = (algebraMap R S (u : R)) ^ n * c
      rw [hd, h, map_mul, map_pow, ← hc]) (coefficientMap n b d hd (root n b))
  rw [rescaleEquiv_root, map_mul, AlgHom.commutes, coefficientMap_root,
    coefficientMap_root, rescaleEquiv_root]
  rw [IsScalarTower.algebraMap_apply R S (RootRing n c)]
  rfl

end EnvelopeProperty.CyclicSectionBaseChange
