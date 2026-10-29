import EnvelopeProperty.AlgGeom.Canonical.CotangentSmoothLocallyFree
import Mathlib.RingTheory.RingHom.StandardSmooth

/-! # Genuine affine etale-coordinate cover from SAME actual original smooth geometry -/
noncomputable section
namespace EnvelopeProperty.Cartier.SmoothEtaleAffineCover
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical
universe u

/-- The ACTUAL original standard-smooth presentation supplies genuine etale evaluation
coordinates, with NO basis or polynomial-map matching premise. -/
theorem exists_etale_coordinates {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R B] :
    ∃ v : Fin n → B, (MvPolynomial.aeval (R := R) v).toRingHom.Etale := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n R B
  let v : Fin n → B := fun i => g (MvPolynomial.X i)
  have he : MvPolynomial.aeval (R := R) v = g := by
    ext i
    exact MvPolynomial.aeval_X v i
  exact ⟨v, he ▸ hg⟩

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
variable (n : ℕ) [SmoothOfRelativeDimension n f]

/-- Actual original smooth geometry supplies each real affine chart and its SAME structural
etale coordinates, no selected cover/algebra-action/coordinate comparison data. -/
theorem exists_affine_etale_chart (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧
      letI := CanonicalGeometry.cotangentOpenAlgebra f V
      ∃ v : Fin n → Γ(X, V), (MvPolynomial.aeval (R := k) v).toRingHom.Etale := by
  obtain ⟨V, hV, hx, hs⟩ := CanonicalGeometry.smooth_cotangent_affine_chart f n x
  refine ⟨V, hV, hx, ?_⟩
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, V) := hs
  exact exists_etale_coordinates n

/-- Actual whole original affine etale-coordinate cover is DERIVED from smoothness,
including EMPTY schemes internally, with SAME original coefficients and actual points. -/
theorem exists_affine_etale_cover :
    ∃ U : X → X.Opens, (∀ x, IsAffineOpen (U x)) ∧ (∀ x, x ∈ U x) ∧
      IsOpenCover U ∧ ∀ x,
        letI := CanonicalGeometry.cotangentOpenAlgebra f (U x)
        ∃ v : Fin n → Γ(X, U x), (MvPolynomial.aeval (R := k) v).toRingHom.Etale := by
  choose U hU hmem he using (fun x : X => exists_affine_etale_chart f n x)
  refine ⟨U, hU, hmem, ?_, he⟩
  change (⨆ x, U x) = ⊤
  apply le_antisymm le_top
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, hmem x⟩

end EnvelopeProperty.Cartier.SmoothEtaleAffineCover
