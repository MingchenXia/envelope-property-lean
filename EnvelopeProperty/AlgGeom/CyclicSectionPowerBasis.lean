import EnvelopeProperty.AlgGeom.CyclicSectionAlgebra

/-! # Original finite cyclic power bases and entire coefficient transitions -/

open Polynomial Module
noncomputable section
universe u
namespace EnvelopeProperty.CyclicSectionPowerBasis
open CyclicSectionAlgebra
variable {R : Type u} [CommRing R]

/-- Every positive-degree original cyclic section quotient is finite. -/
theorem finite (n : ℕ) (a : R) (hn : 0 < n) : Module.Finite R (RootRing n a) :=
  (monic_X_pow_sub_C a hn.ne').finite_adjoinRoot

/-- Every positive-degree original cyclic section quotient is free over its base. -/
theorem free (n : ℕ) (a : R) (hn : 0 < n) : Module.Free R (RootRing n a) :=
  (monic_X_pow_sub_C a hn.ne').free_adjoinRoot

variable [Nontrivial R]

/-- The native monic power basis indexed by the actual original degree. -/
def basis (n : ℕ) (a : R) (hn : 0 < n) : Basis (Fin n) R (RootRing n a) :=
  (AdjoinRoot.powerBasis' (monic_X_pow_sub_C a hn.ne')).basis.reindex
    (finCongr (show (X ^ n - C a).natDegree = n from natDegree_X_pow_sub_C))

/-- Every vector of the native degree-indexed basis is the SAME original root power. -/
theorem basis_apply (n : ℕ) (a : R) (hn : 0 < n) (i : Fin n) :
    basis n a hn i = root n a ^ (i : ℕ) := by
  rw [basis, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- Genuine frame rescaling has the expected action on each original power vector. -/
theorem rescaleEquiv_basis (n : ℕ) (a b : R) (hn : 0 < n) (v : Rˣ)
    (h : b = (v : R) ^ n * a) (i : Fin n) :
    rescaleEquiv n a b v h (basis n b hn i) = (v : R) ^ (i : ℕ) • basis n a hn i := by
  simp only [basis_apply, map_pow, rescaleEquiv_root, mul_pow, Algebra.smul_def]

/-- The coefficient formula holds on the ENTIRE actual original cyclic algebra. -/
theorem repr_rescaleEquiv (n : ℕ) (a b : R) (hn : 0 < n) (v : Rˣ)
    (h : b = (v : R) ^ n * a) (x : RootRing n b) (i : Fin n) :
    (basis n a hn).repr (rescaleEquiv n a b v h x) i =
      (v : R) ^ (i : ℕ) * (basis n b hn).repr x i := by
  have hl : ((basis n a hn).coord i).comp (rescaleEquiv n a b v h).toLinearMap =
      (v : R) ^ (i : ℕ) • (basis n b hn).coord i := by
    apply (basis n b hn).ext
    intro j
    change (basis n a hn).repr (rescaleEquiv n a b v h (basis n b hn j)) i =
      (v : R) ^ (i : ℕ) * (basis n b hn).repr (basis n b hn j) i
    rw [rescaleEquiv_basis, LinearEquiv.map_smul]
    by_cases hji : j = i
    · subst j
      simp
    · simp [Basis.repr_self, hji]
  exact DFunLike.congr_fun hl x

end EnvelopeProperty.CyclicSectionPowerBasis
