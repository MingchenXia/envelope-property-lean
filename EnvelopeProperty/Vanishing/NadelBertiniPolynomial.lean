import EnvelopeProperty.AffineGlobalSections
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # The actual affine coefficient-product ring retains both original projections -/
noncomputable section
open AlgebraicGeometry CategoryTheory TensorProduct
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniPolynomial
open FlatGlobalSections
variable {R : Type u} [CommRing R] {S : Type} {X : Scheme.{u}} [IsAffine X]
  (p : X ⟶ Spec (.of R))

/-- The whole actual original affine coefficient-product ring is the original
polynomial algebra on the original section ring, without a flatness certificate. -/
def sectionsEquiv : MvPolynomial S Γ(X, ⊤) ≃+*
    Γ(baseChange (S := MvPolynomial S R) p, ⊤) := by
  let : Algebra R Γ(X, ⊤) := sectionsAlgebra p
  let : Algebra (MvPolynomial S R) Γ(baseChange (S := MvPolynomial S R) p, ⊤) :=
    sectionsAlgebra (structureMap (S := MvPolynomial S R) p)
  exact (MvPolynomial.algebraTensorAlgEquiv R Γ(X, ⊤)).symm.toRingEquiv.trans
    ((Algebra.TensorProduct.comm R Γ(X, ⊤) (MvPolynomial S R)).toRingEquiv.trans
      (AffineGlobalSections.tensorEquiv (S := MvPolynomial S R) p).toRingEquiv)

/-- Every original coefficient variable is the actual parameter projection's coordinate. -/
theorem sectionsEquiv_X (a : S) :
    sectionsEquiv (S := S) p (MvPolynomial.X a) =
      ProperBirationalSections.coefficientMap (structureMap (S := MvPolynomial S R) p)
        (MvPolynomial.X a) := by
  let : Algebra R Γ(X, ⊤) := sectionsAlgebra p
  let : Algebra (MvPolynomial S R) Γ(baseChange (S := MvPolynomial S R) p, ⊤) :=
    sectionsAlgebra (structureMap (S := MvPolynomial S R) p)
  change AffineGlobalSections.tensorEquiv (S := MvPolynomial S R) p
    (Algebra.TensorProduct.comm R Γ(X, ⊤) (MvPolynomial S R)
      ((MvPolynomial.algebraTensorAlgEquiv R Γ(X, ⊤)).symm (MvPolynomial.X a))) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_symm_X, Algebra.TensorProduct.comm_tmul,
    AffineGlobalSections.tensorEquiv_tmul]
  simp only [map_one, mul_one]

/-- Every original section is retained by the same actual original source projection. -/
theorem sectionsEquiv_C (b : Γ(X, ⊤)) :
    sectionsEquiv (S := S) p (MvPolynomial.C b) =
      (firstProjection (S := MvPolynomial S R) p).appTop b := by
  let : Algebra R Γ(X, ⊤) := sectionsAlgebra p
  let : Algebra (MvPolynomial S R) Γ(baseChange (S := MvPolynomial S R) p, ⊤) :=
    sectionsAlgebra (structureMap (S := MvPolynomial S R) p)
  have h : (MvPolynomial.algebraTensorAlgEquiv (σ := S) R Γ(X, ⊤)).symm
      (MvPolynomial.C b) = b ⊗ₜ[R] (1 : MvPolynomial S R) := by
    simpa only [MvPolynomial.algebraMap_eq, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply] using
      (MvPolynomial.algebraTensorAlgEquiv (σ := S) R Γ(X, ⊤)).symm.commutes b
  change AffineGlobalSections.tensorEquiv (S := MvPolynomial S R) p
    (Algebra.TensorProduct.comm R Γ(X, ⊤) (MvPolynomial S R)
      ((MvPolynomial.algebraTensorAlgEquiv R Γ(X, ⊤)).symm (MvPolynomial.C b))) = _
  rw [h, Algebra.TensorProduct.comm_tmul, AffineGlobalSections.tensorEquiv_tmul]
  simp only [map_one, one_mul]

private theorem ringHom_eq_eval {A B : Type*} [CommRing A] [CommRing B] {T : Type*}
    (e : MvPolynomial T A →+* B) (φ : A →+* B) (x : T → B)
    (hC : ∀ a, e (MvPolynomial.C a) = φ a)
    (hX : ∀ a, e (MvPolynomial.X a) = x a) : e = MvPolynomial.eval₂Hom φ x := by
  apply MvPolynomial.ringHom_ext
  · intro a
    exact (hC a).trans (MvPolynomial.eval₂_C φ x a).symm
  · intro a
    exact (hX a).trans (MvPolynomial.eval₂_X φ x a).symm

/-- The whole original polynomial maps by its actual original coefficient and variable maps. -/
theorem sectionsEquiv_eval (F : MvPolynomial S Γ(X, ⊤)) :
    sectionsEquiv (S := S) p F =
      MvPolynomial.eval₂ (firstProjection (S := MvPolynomial S R) p).appTop.hom
        (fun a => ProperBirationalSections.coefficientMap
          (structureMap (S := MvPolynomial S R) p) (MvPolynomial.X a)) F := by
  have h := ringHom_eq_eval (sectionsEquiv (S := S) p).toRingHom
    (firstProjection (S := MvPolynomial S R) p).appTop.hom
    (fun a => ProperBirationalSections.coefficientMap
      (structureMap (S := MvPolynomial S R) p) (MvPolynomial.X a))
    (sectionsEquiv_C p) (sectionsEquiv_X p)
  exact DFunLike.congr_fun h F

/-- The actual entire original universal linear polynomial retains all original terms. -/
theorem sectionsEquiv_linearForm [Fintype S] (c : S → Γ(X, ⊤)) :
    sectionsEquiv (S := S) p (∑ a, MvPolynomial.C (c a) * MvPolynomial.X a) =
      ∑ a, (firstProjection (S := MvPolynomial S R) p).appTop (c a) *
        ProperBirationalSections.coefficientMap (structureMap (S := MvPolynomial S R) p)
          (MvPolynomial.X a) := by
  simp only [map_sum, map_mul, sectionsEquiv_C, sectionsEquiv_X]

end EnvelopeProperty.Vanishing.NadelBertiniPolynomial
