import EnvelopeProperty.Cartier.EtaleDeRham
import EnvelopeProperty.AlgGeom.Canonical.ExteriorSheaf

/-! # Every actual exterior wedge under genuine basis scalar extension -/
noncomputable section
namespace EnvelopeProperty.Cartier.ExteriorBasisScalarExtension
open scoped TensorProduct Classical
universe u v

section Semilinear
variable {A B M N : Type u} [CommRing A] [CommRing B]
variable [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]

/-- The actual original left product is exactly the original decomposable cons wedge. -/
theorem leftWedge_ιMulti (m : M) (q : ℕ) (w : Fin q → M) :
    PolynomialDeRham.leftWedge m q (exteriorPower.ιMulti A q w) =
      exteriorPower.ιMulti A (q+1) (Fin.cons m w) := by
  apply Subtype.ext
  change ExteriorAlgebra.ι A m * ExteriorAlgebra.ιMulti A q w =
    ExteriorAlgebra.ιMulti A (q+1) (Fin.cons m w)
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  rfl

/-- The actual universal exterior semilinear map commutes with original left exterior
multiplication on EVERY original homogeneous form. -/
theorem exteriorSemilinearMap_leftWedge (f : A →+* B) (φ : M →ₛₗ[f] N)
    (m : M) (q : ℕ) (w : ⋀[A]^q M) :
    CanonicalGeometry.exteriorSemilinearMap f φ (q+1) (PolynomialDeRham.leftWedge m q w) =
      PolynomialDeRham.leftWedge (φ m) q (CanonicalGeometry.exteriorSemilinearMap f φ q w) := by
  have hw : w ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A q (M := M))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    rw [leftWedge_ιMulti, CanonicalGeometry.exteriorSemilinearMap_ιMulti,
      CanonicalGeometry.exteriorSemilinearMap_ιMulti, leftWedge_ιMulti]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, map_smulₛₗ, hx]

end Semilinear

section Linear
variable {A M N : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable [AddCommGroup N] [Module A N] {I : Type v} [LinearOrder I]

/-- The genuine original basis isomorphism induces the SAME original exterior basis map. -/
theorem exteriorLinearEquiv_basis (b : Module.Basis I A M) (c : Module.Basis I A N)
    (q : ℕ) (s : Set.powersetCard I q) :
    CanonicalGeometry.exteriorLinearEquiv (b.equiv c (Equiv.refl _)) q
      (b.exteriorPower q s) = c.exteriorPower q s := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    CanonicalGeometry.exteriorLinearEquiv_ιMulti, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family]
  congr 1
  funext j
  exact Module.Basis.equiv_apply _ _ _ _

end Linear

section Scalar
variable {A B M N : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
variable {I : Type v} [LinearOrder I]

/-- The genuine coefficient-one tensor map followed by an actual scalar-extended linear map
is an actual semilinear map, with the SAME original coefficient ring map. -/
def tensorOneSemilinear (e : (B ⊗[A] M) →ₗ[B] N) : M →ₛₗ[algebraMap A B] N where
  toFun m := e (1 ⊗ₜ[A] m)
  map_add' x y := by rw [TensorProduct.tmul_add, map_add]
  map_smul' a m := by
    change e ((1 : B) ⊗ₜ[A] (a • m)) = (algebraMap A B a) • e (1 ⊗ₜ[A] m)
    calc
      _ = e ((algebraMap A B a) ⊗ₜ[A] m) := by
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      _ = _ := by
        rw [← e.map_smul]
        congr 1
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The SAME actual basis scalar-extension map on EVERY original vector. -/
def basisSemilinearMap (b : Module.Basis I A M) (c : Module.Basis I B N) :
    M →ₛₗ[algebraMap A B] N :=
  tensorOneSemilinear ((b.baseChange B).equiv c (Equiv.refl _)).toLinearMap

omit [LinearOrder I] in
/-- The original vector basis is retained by the actual semilinear comparison. -/
theorem basisSemilinearMap_basis (b : Module.Basis I A M) (c : Module.Basis I B N) (i : I) :
    basisSemilinearMap b c (b i) = c i := by
  change ((b.baseChange B).equiv c (Equiv.refl _)) (1 ⊗ₜ[A] b i) = _
  rw [← Module.Basis.baseChange_apply, Module.Basis.equiv_apply]
  rfl

/-- The actual original basis scalar-extension comparison factors through the genuine
exterior scalar-extension map and the SAME actual degree-one basis isomorphism. -/
theorem exteriorEquiv_eq (b : Module.Basis I A M) (c : Module.Basis I B N) (q : ℕ) :
    ((b.exteriorPower q).baseChange B).equiv (c.exteriorPower q) (Equiv.refl _) =
      (CanonicalGeometry.exteriorBasisBaseChangeEquiv (B := B) b q).trans
        (CanonicalGeometry.exteriorLinearEquiv ((b.baseChange B).equiv c (Equiv.refl _)) q) := by
  apply LinearEquiv.toLinearMap_injective
  apply ((b.exteriorPower q).baseChange B).ext
  intro s
  change (((b.exteriorPower q).baseChange B).equiv (c.exteriorPower q) (Equiv.refl _))
      (((b.exteriorPower q).baseChange B) s) = _
  rw [Module.Basis.equiv_apply]
  change c.exteriorPower q s =
    CanonicalGeometry.exteriorLinearEquiv ((b.baseChange B).equiv c (Equiv.refl _)) q
      (CanonicalGeometry.exteriorBasisBaseChangeEquiv (B := B) b q
        (((b.exteriorPower q).baseChange B) s))
  rw [Module.Basis.baseChange_apply, CanonicalGeometry.exteriorBasisBaseChangeEquiv_basis,
    exteriorLinearEquiv_basis]

/-- EVERY actual decomposable original wedge is carried to the wedge of its SAME actual
scalar-extended original vectors; this is not only a chosen-basis assertion. -/
theorem exteriorEquiv_wedge (b : Module.Basis I A M) (c : Module.Basis I B N)
    (q : ℕ) (m : Fin q → M) :
    (((b.exteriorPower q).baseChange B).equiv (c.exteriorPower q) (Equiv.refl _))
      (1 ⊗ₜ[A] exteriorPower.ιMulti A q m) =
    exteriorPower.ιMulti B q (fun j => ((b.baseChange B).equiv c (Equiv.refl _)) (1 ⊗ₜ[A] m j)) := by
  rw [exteriorEquiv_eq, LinearEquiv.trans_apply,
    CanonicalGeometry.exteriorBasisBaseChangeEquiv_wedge,
    CanonicalGeometry.exteriorLinearEquiv_ιMulti]
  rfl
/-- The ENTIRE genuine exterior basis comparison equals the actual universal semilinear
exterior map of its SAME original vector comparison. -/
theorem exteriorEquiv_eq_semilinear (b : Module.Basis I A M) (c : Module.Basis I B N) (q : ℕ) :
    tensorOneSemilinear
      (((b.exteriorPower q).baseChange B).equiv (c.exteriorPower q) (Equiv.refl _)).toLinearMap =
      CanonicalGeometry.exteriorSemilinearMap (algebraMap A B) (basisSemilinearMap b c) q := by
  apply DFunLike.ext
  intro w
  have hw : w ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A q (M := M))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    change (((b.exteriorPower q).baseChange B).equiv (c.exteriorPower q) (Equiv.refl _))
      (1 ⊗ₜ[A] exteriorPower.ιMulti A q z) = _
    rw [exteriorEquiv_wedge, CanonicalGeometry.exteriorSemilinearMap_ιMulti]
    rfl
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => simp only [map_smulₛₗ, hx]

/-- Actual whole exterior scalar extension commutes with SAME original left multiplication
on EVERY original homogeneous form. -/
theorem exteriorEquiv_leftWedge (b : Module.Basis I A M) (c : Module.Basis I B N)
    (m : M) (q : ℕ) (w : ⋀[A]^q M) :
    (((b.exteriorPower (q+1)).baseChange B).equiv (c.exteriorPower (q+1)) (Equiv.refl _))
      (1 ⊗ₜ[A] PolynomialDeRham.leftWedge m q w) =
    PolynomialDeRham.leftWedge (basisSemilinearMap b c m) q
      ((((b.exteriorPower q).baseChange B).equiv (c.exteriorPower q) (Equiv.refl _))
        (1 ⊗ₜ[A] w)) := by
  change tensorOneSemilinear
      (((b.exteriorPower (q+1)).baseChange B).equiv (c.exteriorPower (q+1)) (Equiv.refl _)).toLinearMap
        (PolynomialDeRham.leftWedge m q w) =
    PolynomialDeRham.leftWedge (basisSemilinearMap b c m) q
      (tensorOneSemilinear
        (((b.exteriorPower q).baseChange B).equiv (c.exteriorPower q) (Equiv.refl _)).toLinearMap w)
  rw [exteriorEquiv_eq_semilinear, exteriorEquiv_eq_semilinear]
  exact exteriorSemilinearMap_leftWedge _ _ m q w


end Scalar
end EnvelopeProperty.Cartier.ExteriorBasisScalarExtension
