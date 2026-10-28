import EnvelopeProperty.Projective.HomogeneousSectionModelNorms
import EnvelopeProperty.Projective.FS

/-! # Original Fubini–Study functions from actual original line-section model norms -/
open scoped Classical NNReal ENNReal Topology
open CategoryTheory AlgebraicGeometry MvPolynomial
open EnvelopeProperty.Berkovich
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ProjBerk
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {n : ℕ}
private local instance originalHomogeneousSectionProper :
    IsProper (nativeStructureMap (R := k) (n := n)) := nativeStructureMap_isProper

/-- The ACTUAL original O(d) global-section model norm on the ORIGINAL paper
analytic projective space, using its actual original residue-field fibre. -/
def homogeneousSectionNorm (j : Fin (n + 1)) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) (x : ProjBerk k n) : ℝ≥0 :=
  RelativeSchemeValuedPoint.modelLineNorm Valuation.one_apply_le_one (nativeHomeomorph x)
    (coordinateHyperplanePoleSheafPower_isInvertible (R := k) j d)
    (RelativeSchemeValuedPoint.fibreSection (nativeHomeomorph x)
      (ProjectiveHomogeneousSections.sectionHom j d F hF))

/-- EVERY original homogeneous form has exactly its original polynomial norm,
with no new section, model, norm or comparison assumption. -/
theorem homogeneousSectionNorm_eq_val (j : Fin (n + 1)) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) (x : ProjBerk k n) :
    homogeneousSectionNorm j d F hF x = x.1.val F :=
  RelativeNormalizedProjectiveSpectrum.homogeneousSection_modelLineNorm
    (1 : Valuation k ℝ≥0) Valuation.one_apply_le_one (normalizedSpectrumHomeomorph x) j d F hF

/-- The ORIGINAL logAbs is precisely the logarithm of the ACTUAL original
whole line-section model norm, including zero sections and negative infinity. -/
theorem homogeneousSectionNorm_log (j : Fin (n + 1)) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) (x : ProjBerk k n) :
    ENNReal.log (homogeneousSectionNorm j d F hF x : ℝ≥0∞) = logAbs F x := by
  rw [homogeneousSectionNorm_eq_val]
  rfl

namespace FSData
variable {a : ℚ}

/-- The finite original section family and its ORIGINAL weights, evaluated
using only norms of ACTUAL original whole O(d) global line sections. -/
def modelNormEval (D : FSData k n a) (j : Fin (n + 1)) (x : ProjBerk k n) : EReal :=
  (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.attach.sup fun t =>
    ENNReal.log (homogeneousSectionNorm j D.deg t.1.1 (D.isHomogeneous t.1 t.2) x : ℝ≥0∞) +
      (t.1.2 : EReal)

/-- The WHOLE original Fubini–Study function is EXACTLY its genuine
finite weighted maximum of ACTUAL original line-section logarithmic norms. -/
theorem modelNormEval_eq_eval (D : FSData k n a) (j : Fin (n + 1)) :
    D.modelNormEval j = D.eval := by
  funext x
  simp only [modelNormEval, homogeneousSectionNorm_log, eval]
  exact congrArg (fun z : EReal => (((D.m : ℝ)⁻¹ : ℝ) : EReal) * z)
    (Finset.sup_attach D.terms (fun t => logAbs t.1 x + (t.2 : EReal)))
end FSData
end EnvelopeProperty.ProjBerk
