import EnvelopeProperty.Global.NativeRankOneAnalyticComparison
import EnvelopeProperty.Global.NativeRankOneProperModel
import EnvelopeProperty.Global.Veronese

/-! # Actual native positive diagonal projective models of the ORIGINAL multicone

The native ring is the SAME original positive diagonal Veronese, not the
dimensionally different total-degree Proj of a higher-rank multicone.
-/
open scoped Classical NNReal Topology
open Topology MvPolynomial AlgebraicGeometry CategoryTheory
open EnvelopeProperty.Berkovich
noncomputable section
universe u
namespace EnvelopeProperty.MultiModel
variable {k K : Type u} [Field k] [Field K] [Algebra k K] {r : ℕ} [NeZero r]
  (X : MultiModel k K r) {a : Fin r →₀ ℕ} (ha : ∀ c, 0 < a c)

/-- The actual native scheme of the SAME original strictly positive diagonal Veronese. -/
def nativeVeroneseScheme : Scheme.{u} := (X.veronese ha).nativeRankOneScheme

/-- The actual positive diagonal model retains its SAME original coefficient structure. -/
def nativeVeroneseStructure : X.nativeVeroneseScheme ha ⟶ Spec (.of k) :=
  (X.veronese ha).nativeRankOneStructure

/-- The actual SAME original diagonal model is integral. -/
instance nativeVeroneseScheme_isIntegral : IsIntegral (X.nativeVeroneseScheme ha) :=
  (X.veronese ha).nativeRankOneScheme_isIntegral

/-- The actual original diagonal structure is proper over the original algebraically closed field. -/
instance nativeVeroneseStructure_isProper [IsAlgClosed k] :
    IsProper (X.nativeVeroneseStructure ha) :=
  (X.veronese ha).nativeRankOneStructure_isProper

/-- The WHOLE original multicone analytic space is the true valued-point space of its actual positive diagonal model. -/
def nativeVeroneseAnalyticHomeomorph : X.an ≃ₜ
    RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) (X.nativeVeroneseStructure ha) :=
  (X.veroneseHomeomorph ha).trans (X.veronese ha).nativeRankOneAnalyticHomeomorph

/-- The comparison retains the SAME original diagonal restriction's true projective-stalk residue point. -/
theorem nativeVeroneseAnalyticHomeomorph_val (x : X.an) :
    (X.nativeVeroneseAnalyticHomeomorph ha x).1 =
      (X.veronese ha).nativeRankOnePoint (X.veroneseAnMap ha x) := rfl

/-- The ENTIRE actual native prime is the SAME original diagonal restriction's valuation kernel. -/
theorem nativeVeroneseAnalyticHomeomorph_support (x : X.an) :
    (X.nativeVeroneseAnalyticHomeomorph ha x).1.point.asHomogeneousIdeal.toIdeal =
      (X.veroneseAnMap ha x).1.val.supp := rfl

/-- EVERY native diagonal homogeneous fraction has its exact SAME original multicone numerator/coordinate values. -/
theorem nativeVeroneseAnalyticHomeomorph_eval_mk (x : X.an)
    (i : Fin ((X.veronese ha).M 0 + 1))
    (hx : (X.veronese ha).nativeRankOneSupport (X.veroneseAnMap ha x) ∈
      (X.veronese ha).nativeRankOneCoordinateOpen i)
    (d : ℕ) (p : (X.veronese ha).S)
    (hp : p ∈ (X.veronese ha).nativeTotalGrading (d • (1 : ℕ))) :
    SchemeValuedPoint.eval (X.nativeVeroneseAnalyticHomeomorph ha x).1
      ((X.veronese ha).nativeRankOneCoordinateOpen i) hx
      (Proj.awayToSection (X.veronese ha).nativeTotalGrading ((X.veronese ha).coordElem ⟨0, i⟩)
        (HomogeneousLocalization.Away.mk (X.veronese ha).nativeTotalGrading
          ((X.veronese ha).nativeRankOneCoordinate_mem i) d p hp)) =
      x.1.val (X.veroneseAlgHom ha p) /
        x.1.val (X.veroneseAlgHom ha ((X.veronese ha).coordElem ⟨0, i⟩)) ^ d := by
  exact (X.veronese ha).nativeRankOnePoint_eval_mk (X.veroneseAnMap ha x) i hx d p hp

end EnvelopeProperty.MultiModel
