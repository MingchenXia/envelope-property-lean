import EnvelopeProperty.Local.PLIdealTwistedModelSheaves
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateEmbedding
import EnvelopeProperty.AlgGeom.AmpleLinePositivePowers
import EnvelopeProperty.AlgGeom.AmpleLineTwistGeneration
import EnvelopeProperty.AlgGeom.NativeProjectiveVarietyComparison
import EnvelopeProperty.AlgGeom.PLModelAuxiliaryPolarizationBaseChange

/-! # Ampleness of the projective twists `O(n)|_X` of a projective subvariety

Let `X ⊆ ℙᴹ_k` be a projective subvariety with closed immersion `ι : X ⟶ ℙᴹ_k`. For every
coordinate `j` and every `n > 0` the restricted twist `X.nativeTwistLineSheaf j n = ι^* O_j(n)` is
very ample over `k`, hence ample, and so are all its positive tensor powers. Indeed `O_j(d+1)` is
very ample on `ℙᴹ_k` (Veronese embedding, production `mixedTwist_isVeryAmple`) and very
ampleness restricts along closed immersions; for powers we use that positive powers of ample lines
on integral schemes are ample.

These are the original-polarization inputs `IsAmple X.hom (L^b)` of the nef-to-FS chain, for the
fibre-one lines `O(n)|_X` of the twisted ratio line and of the tautological twist of the
normalized simultaneous PL model (blueprint `thm:pl-native-twist-line-ample`).
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk CanonicalGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- Every positive twist `ι^* O_j(d+1)` of a projective subvariety is very ample over `k`. -/
theorem nativeTwistLineSheaf_succ_isVeryAmple (j : Fin (M + 1)) (d : ℕ) :
    SchemeLineAmpleness.IsVeryAmple X.nativeStructure (X.nativeTwistLineSheaf j (d + 1)) := by
  have h := SchemeAmpleClosedRestriction.veryAmple_pullback
    (ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateEmbedding.mixedTwist_isVeryAmple
      (R := k) (m := M) j d) X.nativeInclusion
  rw [PLModelAuxiliaryPolarization.projectiveSpaceStructure_eq_nativeStructureMap] at h
  exact h

/-- Every positive twist `ι^* O_j(n)`, `n > 0`, of a projective subvariety is ample over `k`. -/
theorem nativeTwistLineSheaf_isAmple (j : Fin (M + 1)) (n : ℕ) (hn : 0 < n) :
    SchemeLineAmpleness.IsAmple X.nativeStructure (X.nativeTwistLineSheaf j n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact AmpleLineTwistGeneration.isAmple_of_isVeryAmple
      (X.nativeTwistLineSheaf_succ_isVeryAmple j d)

/-- Every positive tensor power of a positive twist `ι^* O_j(n)` is ample over `k`. -/
theorem nativeTwistLineSheaf_tensorPower_isAmple (j : Fin (M + 1)) (n : ℕ) (hn : 0 < n)
    (b : ℕ) (hb : 0 < b) :
    SchemeLineAmpleness.IsAmple X.nativeStructure
      (bundleTensorPower (X.nativeTwistLineSheaf j n) b) := by
  let : IsIntegral X.NativeScheme := X.originalNativeScheme_isIntegral
  exact AmpleLinePositivePowers.isAmple_tensorPower X.nativeStructure _
    (X.nativeTwistLineSheaf_isAmple j n hn) b hb

end EnvelopeProperty.ProjSubvariety
