import EnvelopeProperty.AlgGeom.CyclicSectionCoefficientNaturality

/-! # Original cyclic constant projections over all commutative rings

The nontrivial-ring projection is the SAME native power-basis coefficient.
The zero-ring case is handled by its unique linear map, so actual empty opens
need no additional hypothesis when the projections are glued.
-/

noncomputable section
universe u v
namespace EnvelopeProperty.CyclicSectionGlobalCoverConstantTerm
open CyclicSectionAlgebra CyclicSectionBaseChange CyclicSectionCoefficientNaturality
variable {R : Type u} [CommRing R]

/-- The actual original cyclic constant projection, including zero base rings. -/
def constantTerm (n : ℕ) (a : R) (hn : 0 < n) : RootRing n a →ₗ[R] R := by
  classical
  by_cases h : Nontrivial R
  · letI := h
    exact constantCoefficient n a hn
  · exact 0

/-- Over a nontrivial base this is the SAME original power-basis coordinate. -/
theorem constantTerm_eq [Nontrivial R] (n : ℕ) (a : R) (hn : 0 < n) :
    constantTerm n a hn = constantCoefficient n a hn := by
  classical
  simp [constantTerm, show Nontrivial R from inferInstance]

/-- The actual scalar inclusion is retracted, over every original commutative ring. -/
theorem constantTerm_algebraMap (n : ℕ) (a : R) (hn : 0 < n) (r : R) :
    constantTerm n a hn (algebraMap R (RootRing n a) r) = r := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact Subsingleton.elim _ _
  · rw [constantTerm_eq]
    exact constantCoefficient_algebraMap n a hn r

/-- The WHOLE original scalar inclusion has its actual all-ring linear retraction. -/
theorem constantTerm_comp_algebraMap (n : ℕ) (a : R) (hn : 0 < n) :
    (constantTerm n a hn).comp (Algebra.ofId R (RootRing n a)).toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro r
  exact constantTerm_algebraMap n a hn r

/-- The WHOLE original constant projection is invariant under actual frame rescaling. -/
theorem constantTerm_rescale (n : ℕ) (a b : R) (hn : 0 < n) (v : Rˣ)
    (h : b = (v : R) ^ n * a) :
    (constantTerm n a hn).comp (rescaleEquiv n a b v h).toLinearMap = constantTerm n b hn := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · ext x
    exact Subsingleton.elim _ _
  · rw [constantTerm_eq, constantTerm_eq]
    exact constantCoefficient_rescale n a b hn v h

variable {S : Type v} [CommRing S] [Algebra R S]

/-- The WHOLE constant projection commutes with actual base change, including zero rings. -/
theorem constantTerm_baseChange (n : ℕ) (a : R) (b : S)
    (h : b = algebraMap R S a) (hn : 0 < n) :
    ((constantTerm n b hn).restrictScalars R).comp (coefficientMap n a b h).toLinearMap =
      (Algebra.ofId R S).toLinearMap.comp (constantTerm n a hn) := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · ext x
    exact Subsingleton.elim _ _
  · have : Nontrivial R := (algebraMap R S).domain_nontrivial
    rw [constantTerm_eq, constantTerm_eq]
    exact constantCoefficient_baseChange n a b h hn

end EnvelopeProperty.CyclicSectionGlobalCoverConstantTerm
