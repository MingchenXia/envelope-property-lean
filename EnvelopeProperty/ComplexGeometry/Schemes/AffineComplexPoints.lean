import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual complex affine points

The point set is the algebra hom set, with the initial topology for all
evaluations. Polynomial quotient points will be identified with their literal
complex zero locus in its product topology. This constructs the affine analytic
carrier; smooth charts and global analytic gluing are separate obligations.
-/

namespace ComplexSchemes

noncomputable section

universe u v

/-- Actual complex points of a complex algebra. -/
abbrev ComplexAlgebraPoint (A : Type u) [CommRing A] [Algebra ℂ A] := A →ₐ[ℂ] ℂ

/-- The initial topology for evaluation of every algebra element. -/
instance complexAlgebraPointTopology (A : Type u) [CommRing A] [Algebra ℂ A] :
    TopologicalSpace (ComplexAlgebraPoint A) :=
  TopologicalSpace.induced (fun p : ComplexAlgebraPoint A => (fun a : A => p a))
    inferInstance

variable {A : Type u} [CommRing A] [Algebra ℂ A]
  {B : Type v} [CommRing B] [Algebra ℂ B]

/-- Every algebra evaluation is continuous in the actual point topology. -/
theorem complexPoint_evaluation_continuous (a : A) :
    Continuous (fun p : ComplexAlgebraPoint A => p a) :=
  (continuous_apply a).comp continuous_induced_dom

/-- The universal continuity criterion for the evaluation topology. -/
theorem continuous_complexPoint_iff {Y : Type*} [TopologicalSpace Y]
    (g : Y → ComplexAlgebraPoint A) :
    Continuous g ↔ ∀ a : A, Continuous (fun y => g y a) := by
  rw [continuous_induced_rng, continuous_pi_iff]
  rfl

/-- Pullback by an actual algebra map is continuous on complex points. -/
theorem complexPoint_pullback_continuous (h : A →ₐ[ℂ] B) :
    Continuous (fun p : ComplexAlgebraPoint B => p.comp h) := by
  apply (continuous_complexPoint_iff _).2
  intro a
  exact complexPoint_evaluation_continuous (h a)

variable {σ : Type*}

/-- The literal polynomial zero locus in complex coordinate space. -/
def complexPolynomialZeroLocus (I : Ideal (MvPolynomial σ ℂ)) : Set (σ → ℂ) :=
  {z | ∀ q ∈ I, MvPolynomial.eval z q = 0}

/-- Each polynomial function is continuous in the coordinate product topology. -/
theorem complexPolynomial_continuous (q : MvPolynomial σ ℂ) :
    Continuous (fun z : σ → ℂ => MvPolynomial.eval z q) :=
  q.continuous_eval

/-- A polynomial zero locus is a closed subset of complex coordinate space. -/
theorem complexPolynomialZeroLocus_isClosed (I : Ideal (MvPolynomial σ ℂ)) :
    IsClosed (complexPolynomialZeroLocus I) := by
  have h := isClosed_iInter (fun q : I =>
    isClosed_eq (complexPolynomial_continuous (q : MvPolynomial σ ℂ))
      (continuous_const (y := (0 : ℂ))))
  convert h using 1
  ext z
  simp [complexPolynomialZeroLocus]

/-- Quotient-point evaluation is the actual polynomial evaluation at its coordinates. -/
theorem quotientComplexPoint_eval (I : Ideal (MvPolynomial σ ℂ))
    (p : ComplexAlgebraPoint (MvPolynomial σ ℂ ⧸ I)) (q : MvPolynomial σ ℂ) :
    p (Ideal.Quotient.mk I q) =
      MvPolynomial.eval (fun i => p (Ideal.Quotient.mk I (MvPolynomial.X i))) q := by
  have h : p.comp (Ideal.Quotient.mkₐ ℂ I) =
      MvPolynomial.aeval (fun i => p (Ideal.Quotient.mk I (MvPolynomial.X i))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    MvPolynomial.aeval_eq_eval] using congrArg (fun f => f q) h

/-- An actual quotient point gives coordinates in the literal zero locus. -/
def quotientComplexPoint_coordinates (I : Ideal (MvPolynomial σ ℂ))
    (p : ComplexAlgebraPoint (MvPolynomial σ ℂ ⧸ I)) : complexPolynomialZeroLocus I :=
  ⟨fun i => p (Ideal.Quotient.mk I (MvPolynomial.X i)), by
    intro q hq
    rw [← quotientComplexPoint_eval I p q,
      Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero]⟩

/-- The quotient universal property constructs a point from its zero-locus coordinates. -/
def quotientComplexPoint_ofCoordinates (I : Ideal (MvPolynomial σ ℂ))
    (z : complexPolynomialZeroLocus I) : ComplexAlgebraPoint (MvPolynomial σ ℂ ⧸ I) :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval z.val) (by
    intro q hq
    simpa only [MvPolynomial.aeval_eq_eval] using z.property q hq)

/-- The actual affine quotient point set is equivalent to its polynomial zero locus. -/
def quotientComplexPointEquiv (I : Ideal (MvPolynomial σ ℂ)) :
    ComplexAlgebraPoint (MvPolynomial σ ℂ ⧸ I) ≃ complexPolynomialZeroLocus I where
  toFun := quotientComplexPoint_coordinates I
  invFun := quotientComplexPoint_ofCoordinates I
  left_inv p := by
    apply AlgHom.ext
    intro a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I a
    change MvPolynomial.aeval _ q = p (Ideal.Quotient.mk I q)
    exact (quotientComplexPoint_eval I p q).symm
  right_inv z := by
    apply Subtype.ext
    funext i
    change MvPolynomial.aeval z.val (MvPolynomial.X i) = z.val i
    exact MvPolynomial.aeval_X z.val i

/-- Forward affine coordinates are continuous evaluations. -/
theorem quotientComplexPoint_coordinates_continuous (I : Ideal (MvPolynomial σ ℂ)) :
    Continuous (quotientComplexPoint_coordinates I) := by
  apply Continuous.subtype_mk
  apply continuous_pi_iff.mpr
  intro i
  exact complexPoint_evaluation_continuous (Ideal.Quotient.mk I (MvPolynomial.X i))

/-- Every quotient-element evaluation of the inverse is polynomial, hence continuous. -/
theorem quotientComplexPoint_ofCoordinates_continuous (I : Ideal (MvPolynomial σ ℂ)) :
    Continuous (quotientComplexPoint_ofCoordinates I) := by
  apply (continuous_complexPoint_iff _).2
  intro a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I a
  change Continuous (fun z : complexPolynomialZeroLocus I => MvPolynomial.aeval z.val q)
  exact (complexPolynomial_continuous q).comp continuous_subtype_val

/-- The quotient point topology is the usual subspace topology of its complex zero locus. -/
def quotientComplexPointHomeomorph (I : Ideal (MvPolynomial σ ℂ)) :
    ComplexAlgebraPoint (MvPolynomial σ ℂ ⧸ I) ≃ₜ complexPolynomialZeroLocus I where
  toEquiv := quotientComplexPointEquiv I
  continuous_toFun := quotientComplexPoint_coordinates_continuous I
  continuous_invFun := quotientComplexPoint_ofCoordinates_continuous I

end

end ComplexSchemes
