import EnvelopeProperty.AlgGeom.CyclicSectionBaseChange
import EnvelopeProperty.AlgGeom.CyclicSectionPowerBasis

/-! # Original cyclic coefficients under scalar extension and the constant summand -/

noncomputable section
universe u v
namespace EnvelopeProperty.CyclicSectionCoefficientNaturality
open Module CyclicSectionAlgebra CyclicSectionPowerBasis CyclicSectionBaseChange
variable {R : Type u} [CommRing R] [Nontrivial R]
variable {S : Type v} [CommRing S] [Nontrivial S] [Algebra R S]

/-- The original coefficient-extension map preserves every actual power-basis vector. -/
theorem coefficientMap_basis (n : ℕ) (a : R) (b : S) (h : b = algebraMap R S a)
    (hn : 0 < n) (i : Fin n) :
    coefficientMap n a b h (basis n a hn i) = basis n b hn i := by
  simp only [basis_apply, map_pow, coefficientMap_root]

/-- Every coefficient of the SAME arbitrary original quotient element commutes
with the actual original extension of coefficients. -/
theorem repr_coefficientMap (n : ℕ) (a : R) (b : S) (h : b = algebraMap R S a)
    (hn : 0 < n) (x : RootRing n a) (i : Fin n) :
    (basis n b hn).repr (coefficientMap n a b h x) i =
      algebraMap R S ((basis n a hn).repr x i) := by
  have hl : (((basis n b hn).coord i).restrictScalars R).comp
      (coefficientMap n a b h).toLinearMap =
      (Algebra.ofId R S).toLinearMap.comp ((basis n a hn).coord i) := by
    apply (basis n a hn).ext
    intro j
    change (basis n b hn).repr (coefficientMap n a b h (basis n a hn j)) i =
      algebraMap R S ((basis n a hn).repr (basis n a hn j) i)
    rw [coefficientMap_basis]
    by_cases hj : j = i
    · subst j
      simp
    · simp [Basis.repr_self, hj]
  exact DFunLike.congr_fun hl x

/-- The constant coordinate of the original native cyclic quotient. -/
def constantCoefficient (n : ℕ) (a : R) (hn : 0 < n) : RootRing n a →ₗ[R] R :=
  (basis n a hn).coord ⟨0, hn⟩

/-- The actual constant coordinate retracts the SAME original scalar inclusion. -/
theorem constantCoefficient_algebraMap (n : ℕ) (a : R) (hn : 0 < n) (r : R) :
    constantCoefficient n a hn (algebraMap R (RootRing n a) r) = r := by
  have h0 : basis n a hn ⟨0, hn⟩ = 1 := by
    rw [basis_apply]
    simp
  have hr : algebraMap R (RootRing n a) r = r • basis n a hn ⟨0, hn⟩ := by
    rw [h0, Algebra.smul_def, mul_one]
  rw [hr, map_smul]
  simp [constantCoefficient]

/-- The constant-summand retraction is an equality of WHOLE original linear maps. -/
theorem constantCoefficient_comp_algebraMap (n : ℕ) (a : R) (hn : 0 < n) :
    (constantCoefficient n a hn).comp (Algebra.ofId R (RootRing n a)).toLinearMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro r
  exact constantCoefficient_algebraMap n a hn r

/-- The WHOLE constant projection is invariant under the original line-frame change. -/
theorem constantCoefficient_rescale (n : ℕ) (a b : R) (hn : 0 < n) (v : Rˣ)
    (h : b = (v : R) ^ n * a) :
    (constantCoefficient n a hn).comp (rescaleEquiv n a b v h).toLinearMap =
      constantCoefficient n b hn := by
  ext x
  simpa [constantCoefficient] using repr_rescaleEquiv n a b hn v h x ⟨0, hn⟩

/-- The WHOLE constant projection commutes with the SAME original coefficient extension. -/
theorem constantCoefficient_baseChange (n : ℕ) (a : R) (b : S)
    (h : b = algebraMap R S a) (hn : 0 < n) :
    ((constantCoefficient n b hn).restrictScalars R).comp (coefficientMap n a b h).toLinearMap =
      (Algebra.ofId R S).toLinearMap.comp (constantCoefficient n a hn) := by
  ext x
  exact repr_coefficientMap n a b h hn x ⟨0, hn⟩

end EnvelopeProperty.CyclicSectionCoefficientNaturality
