import EnvelopeProperty.Global.GeneralPSH2ContinuationSupportTrivial
import EnvelopeProperty.Global.NativeRankOneAnalyticComparison
import EnvelopeProperty.Global.Veronese

/-!
# Actual native Proj residue semantics of original support-trivial points

The entire true projective stalk residue valuation is identified, through its
actual ordinary localization and degree-zero stalk construction. The canonical
whole original analytic homeomorphism then intertwines support trivialization.
No affine-cone/projective residue field identification is made. Intrinsic
numerical cones and the BJ PSH comparison remain separate consumers.

Complete mathematical route: owned audit `native-support-trivial-route.tex`.
-/

open scoped Classical NNReal Topology
open AlgebraicGeometry CategoryTheory
open EnvelopeProperty.Berkovich

noncomputable section

universe u

namespace EnvelopeProperty.Berkovich.SchemeValuedPoint

/-- The trivial valuation on the ACTUAL original scheme stalk residue field. -/
def trivialAt {Y : Scheme.{u}} (p : Y) : SchemeValuedPoint Y := ⟨p, 1⟩

end EnvelopeProperty.Berkovich.SchemeValuedPoint

namespace EnvelopeProperty.Berkovich.RelevantGradedSpectrum

variable {A : Type u} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

private theorem localValuation_binary (x : RelevantGradedSpectrum 𝒜)
    (hbin : ∀ p : A, x.1.val p = 0 ∨ x.1.val p = 1)
    (z : Localization.AtPrime x.1.val.supp) :
    localValuation x z = 0 ∨ localValuation x z = 1 := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq x.1.val.supp.primeCompl z
  rw [localValuation, Valuation.extendToLocalization_mk']
  have hs : x.1.val s.1 = 1 := (hbin s.1).resolve_left s.2
  rw [hs, inv_one, mul_one]
  exact hbin a

/-- All original ring values zero or one force the ENTIRE actual projective
stalk residue valuation to be the true trivial field valuation. -/
theorem nativePoint_residueVal_eq_one_of_binary (x : RelevantGradedSpectrum 𝒜)
    (hbin : ∀ p : A, x.1.val p = 0 ∨ x.1.val p = 1) :
    (nativePoint x).residueVal = 1 := by
  apply Valuation.ext
  intro z
  by_cases hz : z = 0
  · simp only [hz, map_zero]
  · rw [Valuation.one_apply_of_ne_zero hz]
    have hv : (nativePoint x).residueVal z = 0 ∨ (nativePoint x).residueVal z = 1 := by
      obtain ⟨a, rfl⟩ := (Proj 𝒜).residue_surjective (support x) z
      rw [nativePoint_residue]
      exact localValuation_binary x hbin _
    exact hv.resolve_left ((nativePoint x).residueVal.ne_zero_iff.mpr hz)

/-- The SAME canonical native point of a binary graded seminorm is the
trivial valuation on its true projective residue field at its original support. -/
theorem nativePoint_eq_trivialAt_of_binary (x : RelevantGradedSpectrum 𝒜)
    (hbin : ∀ p : A, x.1.val p = 0 ∨ x.1.val p = 1) :
    nativePoint x = SchemeValuedPoint.trivialAt (support x) := by
  exact congrArg (SchemeValuedPoint.mk (X := Proj 𝒜) (support x))
    (nativePoint_residueVal_eq_one_of_binary x hbin)

end EnvelopeProperty.Berkovich.RelevantGradedSpectrum

namespace EnvelopeProperty.MultiModel

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

/-- The genuine ORIGINAL native Proj support is retained by original support
trivialization, through equality of the entire original valuation kernel. -/
theorem nativeRankOneSupport_supportTrivialPoint (x : X.an) :
    X.nativeRankOneSupport (X.supportTrivialPoint x) = X.nativeRankOneSupport x := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  exact X.supportTrivialPoint_supp x

/-- The WHOLE actual original native point is the trivial valuation on the
true projective stalk residue field at the SAME original native support. -/
theorem nativeRankOnePoint_supportTrivialPoint (x : X.an) :
    X.nativeRankOnePoint (X.supportTrivialPoint x) =
      SchemeValuedPoint.trivialAt (X.nativeRankOneSupport x) := by
  have hbin : ∀ p : X.S,
      (X.nativeRankOneRelevantPoint (X.supportTrivialPoint x)).1.val p = 0 ∨
        (X.nativeRankOneRelevantPoint (X.supportTrivialPoint x)).1.val p = 1 := by
    intro p
    change (Berk.zeroScale x.1).val p = 0 ∨ (Berk.zeroScale x.1).val p = 1
    by_cases hp : x.1.val p = 0
    · exact Or.inl (Berk.zeroScale_val_of_eq_zero hp)
    · exact Or.inr (Berk.zeroScale_val_of_ne_zero hp)
  calc
    X.nativeRankOnePoint (X.supportTrivialPoint x) =
        SchemeValuedPoint.trivialAt (X.nativeRankOneSupport (X.supportTrivialPoint x)) :=
      RelevantGradedSpectrum.nativePoint_eq_trivialAt_of_binary
        (X.nativeRankOneRelevantPoint (X.supportTrivialPoint x)) hbin
    _ = SchemeValuedPoint.trivialAt (X.nativeRankOneSupport x) :=
      congrArg SchemeValuedPoint.trivialAt (X.nativeRankOneSupport_supportTrivialPoint x)

/-- The ACTUAL native trivial residue point lies over the exact SAME original
trivial base-field point, derived from the original analytic comparison. -/
theorem nativeRankOne_trivialAt_mem_relativeLocus (x : X.an) :
    SchemeValuedPoint.trivialAt (X.nativeRankOneSupport x) ∈
      SchemeValuedPoint.relativeLocus (1 : Valuation k ℝ≥0) X.nativeRankOneStructure := by
  rw [← X.nativeRankOnePoint_supportTrivialPoint x]
  exact X.nativeRankOnePoint_mem_relativeLocus (X.supportTrivialPoint x)

/-- The true native trivial residue valuation as a point of the SAME original
prescribed-base locus; no relative-membership certificate is assumed. -/
def nativeRankOneSupportTrivialRelativePoint (x : X.an) :
    RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.nativeRankOneStructure :=
  ⟨SchemeValuedPoint.trivialAt (X.nativeRankOneSupport x),
    X.nativeRankOne_trivialAt_mem_relativeLocus x⟩

/-- The WHOLE original analytic homeomorphism intertwines original support
trivialization with the actual native projective residue valuation. -/
theorem nativeRankOneAnalyticHomeomorph_supportTrivialPoint (x : X.an) :
    X.nativeRankOneAnalyticHomeomorph (X.supportTrivialPoint x) =
      X.nativeRankOneSupportTrivialRelativePoint x := by
  apply Subtype.ext
  exact X.nativeRankOnePoint_supportTrivialPoint x

section PositiveDiagonal

variable {r : ℕ} [NeZero r] (Y : MultiModel k K r) {a : Fin r →₀ ℕ}
  (ha : ∀ c, 0 < a c)

/-- Support trivialization commutes with restriction to the SAME original
positive diagonal ring, as equality of ENTIRE original seminorms. -/
theorem veroneseAnMap_supportTrivialPoint (x : Y.an) :
    Y.veroneseAnMap ha (Y.supportTrivialPoint x) =
      (Y.veronese ha).supportTrivialPoint (Y.veroneseAnMap ha x) := by
  refine Subtype.ext (Berk.ext_val fun p => ?_)
  change (Berk.zeroScale x.1).val (Y.veroneseAlgHom ha p) =
    (Berk.zeroScale (Y.veroneseAnMap ha x).1).val p
  rw [Berk.zeroScale_val_apply, Berk.zeroScale_val_apply]
  rfl

/-- The actual native positive diagonal Proj support is the SAME original
support after trivialization, at every original positive model rank. -/
theorem nativeDiagonalSupport_supportTrivialPoint (x : Y.an) :
    (Y.veronese ha).nativeRankOneSupport (Y.veroneseAnMap ha (Y.supportTrivialPoint x)) =
      (Y.veronese ha).nativeRankOneSupport (Y.veroneseAnMap ha x) := by
  rw [Y.veroneseAnMap_supportTrivialPoint ha]
  exact (Y.veronese ha).nativeRankOneSupport_supportTrivialPoint _

/-- The WHOLE actual native diagonal point is the genuine trivial valuation
of its original projective residue field, at every positive model rank. -/
theorem nativeDiagonalPoint_supportTrivialPoint (x : Y.an) :
    (Y.veronese ha).nativeRankOnePoint (Y.veroneseAnMap ha (Y.supportTrivialPoint x)) =
      SchemeValuedPoint.trivialAt
        ((Y.veronese ha).nativeRankOneSupport (Y.veroneseAnMap ha x)) := by
  rw [Y.veroneseAnMap_supportTrivialPoint ha]
  exact (Y.veronese ha).nativeRankOnePoint_supportTrivialPoint _

/-- The actual composite WHOLE original positive-diagonal analytic
homeomorphism intertwines original and genuine native support trivialization. -/
theorem nativeDiagonalAnalyticHomeomorph_supportTrivialPoint (x : Y.an) :
    ((Y.veroneseHomeomorph ha).trans
      (Y.veronese ha).nativeRankOneAnalyticHomeomorph) (Y.supportTrivialPoint x) =
        (Y.veronese ha).nativeRankOneSupportTrivialRelativePoint (Y.veroneseAnMap ha x) := by
  change (Y.veronese ha).nativeRankOneAnalyticHomeomorph
      (Y.veroneseAnMap ha (Y.supportTrivialPoint x)) = _
  rw [Y.veroneseAnMap_supportTrivialPoint ha]
  exact (Y.veronese ha).nativeRankOneAnalyticHomeomorph_supportTrivialPoint _

end PositiveDiagonal

end EnvelopeProperty.MultiModel

#check @EnvelopeProperty.Berkovich.SchemeValuedPoint.trivialAt
#check @EnvelopeProperty.Berkovich.RelevantGradedSpectrum.nativePoint_residueVal_eq_one_of_binary
#check @EnvelopeProperty.Berkovich.RelevantGradedSpectrum.nativePoint_eq_trivialAt_of_binary
#check @EnvelopeProperty.MultiModel.nativeRankOneSupport_supportTrivialPoint
#check @EnvelopeProperty.MultiModel.nativeRankOnePoint_supportTrivialPoint
#check @EnvelopeProperty.MultiModel.nativeRankOne_trivialAt_mem_relativeLocus
#check @EnvelopeProperty.MultiModel.nativeRankOneSupportTrivialRelativePoint
#check @EnvelopeProperty.MultiModel.nativeRankOneAnalyticHomeomorph_supportTrivialPoint
#check @EnvelopeProperty.MultiModel.veroneseAnMap_supportTrivialPoint
#check @EnvelopeProperty.MultiModel.nativeDiagonalSupport_supportTrivialPoint
#check @EnvelopeProperty.MultiModel.nativeDiagonalPoint_supportTrivialPoint
#check @EnvelopeProperty.MultiModel.nativeDiagonalAnalyticHomeomorph_supportTrivialPoint
#print axioms EnvelopeProperty.Berkovich.SchemeValuedPoint.trivialAt
#print axioms EnvelopeProperty.Berkovich.RelevantGradedSpectrum.nativePoint_residueVal_eq_one_of_binary
#print axioms EnvelopeProperty.Berkovich.RelevantGradedSpectrum.nativePoint_eq_trivialAt_of_binary
#print axioms EnvelopeProperty.MultiModel.nativeRankOneSupport_supportTrivialPoint
#print axioms EnvelopeProperty.MultiModel.nativeRankOnePoint_supportTrivialPoint
#print axioms EnvelopeProperty.MultiModel.nativeRankOne_trivialAt_mem_relativeLocus
#print axioms EnvelopeProperty.MultiModel.nativeRankOneSupportTrivialRelativePoint
#print axioms EnvelopeProperty.MultiModel.nativeRankOneAnalyticHomeomorph_supportTrivialPoint
#print axioms EnvelopeProperty.MultiModel.veroneseAnMap_supportTrivialPoint
#print axioms EnvelopeProperty.MultiModel.nativeDiagonalSupport_supportTrivialPoint
#print axioms EnvelopeProperty.MultiModel.nativeDiagonalPoint_supportTrivialPoint
#print axioms EnvelopeProperty.MultiModel.nativeDiagonalAnalyticHomeomorph_supportTrivialPoint
