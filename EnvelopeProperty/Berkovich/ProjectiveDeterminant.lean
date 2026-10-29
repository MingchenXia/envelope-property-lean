/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.LinearAlgebra.FreeModule.Determinant
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Intrinsic determinants of finite projective modules

Actual finite projectivity produces a finite free splitting. Stabilizing an
endomorphism by the identity on its complement gives a determinant proved
independent of that splitting by rectangular Sylvester. The construction is
multiplicative, invariant under genuine linear equivalences and compatible
with tensor coefficient base change over arbitrary commutative rings.

The splitting's rank is the ambient free-module rank. The module itself may
have varying local ranks; no global constant-rank hypothesis is used. On a
finite free module the intrinsic determinant equals `LinearMap.det`.
-/

open scoped Classical TensorProduct
noncomputable section
namespace EnvelopeProperty

/-- An actual finite free retract, with its full splitting law. -/
structure FiniteFreeSplitting (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] where
  /-- Rank of the ambient free module, not an asserted constant rank of `M`. -/
  rank : ℕ
  i : M →ₗ[R] Fin rank → R
  p : (Fin rank → R) →ₗ[R] M
  pi : p.comp i = LinearMap.id

namespace FiniteFreeSplitting
variable {R M : Type*}

section Splitting
variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- Actual finite free splitting, produced by genuine projectivity. -/
def ofFiniteProjective [Module.Finite R M] [Module.Projective R M] : FiniteFreeSplitting R M :=
  Classical.choice (by
    obtain ⟨n, p, i, hp, hi, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
    exact ⟨⟨n, i, p, hpi⟩⟩)

@[simp]
theorem p_i (s : FiniteFreeSplitting R M) (x : M) : s.p (s.i x) = x :=
  congrArg (fun f : M →ₗ[R] M => f x) s.pi

/-- Transport of an actual splitting along a genuine linear equivalence. -/
def ofEquiv {N : Type*} [AddCommMonoid N] [Module R N]
    (s : FiniteFreeSplitting R M) (e : M ≃ₗ[R] N) : FiniteFreeSplitting R N where
  rank := s.rank
  i := s.i.comp e.symm.toLinearMap
  p := e.toLinearMap.comp s.p
  pi := by
    apply LinearMap.ext
    intro x
    simp

end Splitting

section Determinant
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- Stabilization acts by f on the direct summand and the identity on its complement. -/
def stabilized (s : FiniteFreeSplitting R M) (f : Module.End R M) :
    Module.End R (Fin s.rank → R) := 1 + s.i.comp ((f - 1).comp s.p)

def det (s : FiniteFreeSplitting R M) (f : Module.End R M) : R :=
  LinearMap.det (s.stabilized f)

/-- Actual finite free basis comparison form of the rectangular Sylvester identity. -/
theorem det_one_add_comp_comm {P Q : Type*} [AddCommGroup P] [AddCommGroup Q]
    [Module R P] [Module R Q] {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι R P) (c : Module.Basis κ R Q)
    (u : Q →ₗ[R] P) (v : P →ₗ[R] Q) :
    LinearMap.det (1 + u.comp v) = LinearMap.det (1 + v.comp u) := by
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix c]
  simp only [map_add, LinearMap.toMatrix_one]
  rw [LinearMap.toMatrix_comp b c b, LinearMap.toMatrix_comp c b c]
  exact Matrix.det_one_add_mul_comm _ _

/-- Genuine split-independence compares the entire stabilized operators. -/
theorem det_eq (s t : FiniteFreeSplitting R M) (f : Module.End R M) : s.det f = t.det f := by
  let u := s.i.comp ((f - 1).comp t.p)
  let v := t.i.comp s.p
  have hs : s.stabilized f = 1 + u.comp v := by
    ext x
    simp [stabilized, u, v]
  have ht : t.stabilized f = 1 + v.comp u := by
    ext x
    simp [stabilized, u, v]
  rw [det, det, hs, ht]
  exact det_one_add_comp_comm (Pi.basisFun R (Fin s.rank)) (Pi.basisFun R (Fin t.rank)) u v


@[simp]
theorem stabilized_one (s : FiniteFreeSplitting R M) : s.stabilized 1 = 1 := by
  simp [stabilized]

/-- The actual projector makes stabilization multiplicative on entire operators. -/
theorem stabilized_mul (s : FiniteFreeSplitting R M) (f g : Module.End R M) :
    s.stabilized (f * g) = s.stabilized f * s.stabilized g := by
  ext x
  simp [stabilized, Module.End.mul_apply]
  abel

def stabilizedHom (s : FiniteFreeSplitting R M) :
    Module.End R M →* Module.End R (Fin s.rank → R) where
  toFun := s.stabilized
  map_one' := s.stabilized_one
  map_mul' := s.stabilized_mul

def detHom (s : FiniteFreeSplitting R M) : Module.End R M →* R :=
  LinearMap.det.comp s.stabilizedHom

/-- The intrinsic splitting determinant agrees with the ordinary determinant on finite free modules. -/
theorem det_eq_det_of_free [Module.Free R M] [Module.Finite R M]
    (s : FiniteFreeSplitting R M) (f : Module.End R M) : s.det f = LinearMap.det f := by
  nontriviality R
  let b := Module.Free.chooseBasis R M
  let : Fintype (Module.Free.ChooseBasisIndex R M) := Fintype.ofFinite _
  have hs := det_one_add_comp_comm (Pi.basisFun R (Fin s.rank)) b (s.i.comp (f - 1)) s.p
  have hp : s.p.comp (s.i.comp (f - 1)) = f - 1 := by
    ext x
    simp
  have hOne : (1 : Module.End R M) + (f - 1) = f := by abel
  rw [hp, hOne] at hs
  simpa only [det, stabilized, LinearMap.comp_assoc] using hs

/-- Genuine conjugacy preserves the stabilized operator on the same finite free module. -/
theorem stabilized_ofEquiv {N : Type*} [AddCommGroup N] [Module R N]
    (s : FiniteFreeSplitting R M) (e : M ≃ₗ[R] N) (f : Module.End R M) :
    (s.ofEquiv e).stabilized (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) =
      s.stabilized f := by
  change (1 + (s.i.comp e.symm.toLinearMap).comp
    ((e.toLinearMap.comp (f.comp e.symm.toLinearMap) - 1).comp
      (e.toLinearMap.comp s.p))) = s.stabilized f
  apply LinearMap.ext
  intro x
  simp [stabilized]

end Determinant

section BaseChangeConstruction
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable (S : Type*) [CommSemiring S] [Algebra R S]

/-- The actual standard finite free tensor comparison. -/
def standardBaseChangeEquiv (n : ℕ) :
    S ⊗[R] (Fin n → R) ≃ₗ[S] Fin n → S :=
  TensorProduct.piScalarRight R S S (Fin n)

/-- Tensor extension of the genuine splitting, with the actual standard finite free comparison. -/
def baseChange (s : FiniteFreeSplitting R M) : FiniteFreeSplitting S (S ⊗[R] M) where
  rank := s.rank
  i := (standardBaseChangeEquiv (R := R) S s.rank).toLinearMap.comp (s.i.baseChange S)
  p := (s.p.baseChange S).comp (standardBaseChangeEquiv (R := R) S s.rank).symm.toLinearMap
  pi := by
    apply LinearMap.ext
    intro z
    change (s.p.baseChange S) ((standardBaseChangeEquiv (R := R) S s.rank).symm
      ((standardBaseChangeEquiv (R := R) S s.rank) ((s.i.baseChange S) z))) = z
    rw [LinearEquiv.symm_apply_apply]
    change ((s.p.baseChange S).comp (s.i.baseChange S)) z = z
    rw [← LinearMap.baseChange_comp, s.pi, LinearMap.baseChange_id, LinearMap.id_apply]

end BaseChangeConstruction

section BaseChangeDeterminant
variable [CommRing R] [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S]

/-- Actual coefficient base change of the entire endomorphism matrix in an extended basis. -/
theorem det_baseChange_of_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (f : Module.End R M) :
    LinearMap.det (f.baseChange S) = algebraMap R S (LinearMap.det f) := by
  rw [← LinearMap.det_toMatrix (b.baseChange S), ← LinearMap.det_toMatrix b, RingHom.map_det]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, Algebra.smul_def]

/-- The constructed target stabilized operator is the genuine conjugate of tensor base change. -/
theorem stabilized_baseChange (s : FiniteFreeSplitting R M) (f : Module.End R M) :
    (s.baseChange S).stabilized (f.baseChange S) =
      (standardBaseChangeEquiv (R := R) S s.rank).toLinearMap.comp
        (((s.stabilized f).baseChange S).comp
          (standardBaseChangeEquiv (R := R) S s.rank).symm.toLinearMap) := by
  let e := standardBaseChangeEquiv (R := R) S s.rank
  change (1 + (e.toLinearMap.comp (s.i.baseChange S)).comp
    (((f.baseChange S) - 1).comp ((s.p.baseChange S).comp e.symm.toLinearMap))) =
      e.toLinearMap.comp (((s.stabilized f).baseChange S).comp e.symm.toLinearMap)
  apply LinearMap.ext
  intro x
  simp only [stabilized, LinearMap.baseChange_add, LinearMap.baseChange_one,
    LinearMap.baseChange_comp, LinearMap.baseChange_sub, LinearMap.add_apply,
    Module.End.one_apply, LinearMap.comp_apply, map_add]
  exact congrArg (fun z => z + e ((s.i.baseChange S)
    ((f.baseChange S - 1) ((s.p.baseChange S) (e.symm x))))) (e.apply_symm_apply x).symm


/-- Genuine coefficient base change of the splitting determinant. -/
theorem det_baseChange (s : FiniteFreeSplitting R M) (f : Module.End R M) :
    (s.baseChange S).det (f.baseChange S) = algebraMap R S (s.det f) := by
  change LinearMap.det ((s.baseChange S).stabilized (f.baseChange S)) = _
  rw [stabilized_baseChange]
  change LinearMap.det ((standardBaseChangeEquiv (R := R) S s.rank).toLinearMap.comp
    (((s.stabilized f).baseChange S).comp
      (standardBaseChangeEquiv (R := R) S s.rank).symm.toLinearMap)) = _
  rw [LinearMap.det_conj]
  exact det_baseChange_of_basis S (Pi.basisFun R (Fin s.rank)) (s.stabilized f)

end BaseChangeDeterminant

end FiniteFreeSplitting

/-- The genuine intrinsic determinant of a finite projective module, produced
from a finite free splitting and proved independent of that choice. -/
def projectiveDet (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] : Module.End R M →* R :=
  (FiniteFreeSplitting.ofFiniteProjective (R := R) (M := M)).detHom

theorem projectiveDet_eq_split {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (s : FiniteFreeSplitting R M)
    (f : Module.End R M) : projectiveDet R M f = s.det f :=
  FiniteFreeSplitting.det_eq (FiniteFreeSplitting.ofFiniteProjective (R := R) (M := M)) s f

@[simp]
theorem projectiveDet_one (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] : projectiveDet R M 1 = 1 :=
  (projectiveDet R M).map_one

theorem projectiveDet_mul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (f g : Module.End R M) :
    projectiveDet R M (f * g) = projectiveDet R M f * projectiveDet R M g :=
  (projectiveDet R M).map_mul f g

theorem projectiveDet_eq_det_of_free {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Free R M] (f : Module.End R M) :
    projectiveDet R M f = LinearMap.det f :=
  FiniteFreeSplitting.det_eq_det_of_free (FiniteFreeSplitting.ofFiniteProjective (R := R) (M := M)) f


/-- Intrinsic determinant is preserved by a genuine linear equivalence. -/
theorem projectiveDet_conj {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (e : M ≃ₗ[R] N) (f : Module.End R M) :
    projectiveDet R N (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) = projectiveDet R M f := by
  let s := FiniteFreeSplitting.ofFiniteProjective (R := R) (M := M)
  rw [projectiveDet_eq_split (s.ofEquiv e), projectiveDet_eq_split s,
    FiniteFreeSplitting.det, FiniteFreeSplitting.stabilized_ofEquiv]
  rfl

/-- Intrinsic finite-projective determinant commutes with genuine tensor coefficient base change. -/
theorem projectiveDet_baseChange {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (S : Type*) [CommRing S] [Algebra R S] (f : Module.End R M) :
    projectiveDet S (S ⊗[R] M) (f.baseChange S) = algebraMap R S (projectiveDet R M f) := by
  let s := FiniteFreeSplitting.ofFiniteProjective (R := R) (M := M)
  rw [projectiveDet_eq_split (s.baseChange S), projectiveDet_eq_split s,
    FiniteFreeSplitting.det_baseChange]


end EnvelopeProperty
