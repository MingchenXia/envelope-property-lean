import EnvelopeProperty.Global.NativeRankOneChartComparison
import EnvelopeProperty.Berkovich.GradedNativeValuedPoints
import EnvelopeProperty.Berkovich.SpectrumBridge

/-! # The SAME original rank-one analytic point as a genuine native Proj valued point -/
open scoped Classical NNReal Topology
open Topology MvPolynomial AlgebraicGeometry CategoryTheory
open EnvelopeProperty.Berkovich
noncomputable section
universe u
namespace EnvelopeProperty.MultiModel
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

/-- Every true native projection is the SAME original multihomogeneous component. -/
theorem nativeRankOne_proj_eq_homComp (d : ℕ) (p : X.S) :
    GradedRing.proj X.nativeTotalGrading d p = X.homComp (Finsupp.single 0 d) p := by
  apply Subtype.ext
  change (((DirectSum.decompose X.nativeTotalGrading) p d : X.S) : MvPolynomial (Fin 1) K) = _
  rw [X.nativeTotalGrading_decompose_val]
  have h := rankOne_homogeneous_eq_monomial d
    (MvPolynomial.homogeneousComponent d (p : MvPolynomial (Fin 1) K))
    (MvPolynomial.homogeneousComponent_isHomogeneous d _)
  simpa only [MvPolynomial.coeff_homogeneousComponent, Finsupp.degree_single, ite_true,
    homComp, coe_ofPiece] using h

/-- The ORIGINAL analytic point is an actual relevant graded seminorm on the SAME original algebra. -/
def nativeRankOneRelevantPoint (x : X.an) : RelevantGradedSpectrum X.nativeTotalGrading :=
  ⟨x.1.toSpectrum, by
    constructor
    · intro p d
      rw [X.nativeRankOne_proj_eq_homComp]
      exact x.property.1 p (Finsupp.single 0 d)
    · intro h
      obtain ⟨i, hi⟩ := x.property.2.exists_val_coordElem_eq_one 0
      have hc := h (HomogeneousIdeal.mem_irrelevant_of_mem X.nativeTotalGrading
        (by decide : 0 < (1 : ℕ)) (X.nativeRankOneCoordinate_mem i))
      change x.1.val (X.coordElem ⟨0, i⟩) = 0 at hc
      exact one_ne_zero (hi.symm.trans hc)⟩

/-- The true relevant graded point retains continuity from the original seminorm topology. -/
@[fun_prop]
theorem continuous_nativeRankOneRelevantPoint : Continuous X.nativeRankOneRelevantPoint :=
  (Berk.continuous_toSpectrum.comp continuous_subtype_val).subtype_mk _

/-- The genuine native support is the SAME original homogeneous valuation kernel. -/
def nativeRankOneSupport (x : X.an) : X.nativeRankOneScheme :=
  RelevantGradedSpectrum.support (X.nativeRankOneRelevantPoint x)

/-- The original native projective support varies continuously. -/
@[fun_prop]
theorem continuous_nativeRankOneSupport : Continuous X.nativeRankOneSupport :=
  RelevantGradedSpectrum.continuous_support.comp X.continuous_nativeRankOneRelevantPoint

/-- The ENTIRE actual native projective ideal is the SAME original valuation kernel. -/
theorem nativeRankOneSupport_toIdeal (x : X.an) :
    (X.nativeRankOneSupport x).asHomogeneousIdeal.toIdeal = x.1.val.supp := rfl

/-- Every original coordinate open retains its literal nonvanishing condition. -/
theorem nativeRankOneSupport_mem_coordinateOpen (x : X.an) (i : Fin (X.M 0 + 1)) :
    X.nativeRankOneSupport x ∈ X.nativeRankOneCoordinateOpen i ↔
      x.1.val (X.coordElem ⟨0, i⟩) ≠ 0 := Iff.rfl

/-- The actual ORIGINAL rank-one analytic point has a true projective stalk-residue native point. -/
def nativeRankOnePoint (x : X.an) : SchemeValuedPoint X.nativeRankOneScheme :=
  RelevantGradedSpectrum.nativePoint (X.nativeRankOneRelevantPoint x)

/-- The native whole point retains the original projective support. -/
theorem nativeRankOnePoint_point (x : X.an) :
    (X.nativeRankOnePoint x).point = X.nativeRankOneSupport x := rfl

/-- EVERY original homogeneous numerator and coordinate power has its original exact chart value. -/
theorem nativeRankOnePoint_eval_mk (x : X.an) (i : Fin (X.M 0 + 1))
    (hx : X.nativeRankOneSupport x ∈ X.nativeRankOneCoordinateOpen i)
    (d : ℕ) (p : X.S) (hp : p ∈ X.nativeTotalGrading (d • (1 : ℕ))) :
    SchemeValuedPoint.eval (X.nativeRankOnePoint x) (X.nativeRankOneCoordinateOpen i) hx
      (Proj.awayToSection X.nativeTotalGrading (X.coordElem ⟨0, i⟩)
        (HomogeneousLocalization.Away.mk X.nativeTotalGrading
          (X.nativeRankOneCoordinate_mem i) d p hp)) =
      x.1.val p / x.1.val (X.coordElem ⟨0, i⟩) ^ d :=
  RelevantGradedSpectrum.nativePoint_eval_mk (X.nativeRankOneRelevantPoint x)
    (X.coordElem ⟨0, i⟩) (X.nativeRankOneCoordinate_mem i) hx d p hp

end EnvelopeProperty.MultiModel
