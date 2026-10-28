import EnvelopeProperty.Vanishing.NadelBertiniSncStrata
import EnvelopeProperty.Vanishing.NadelBertiniGlobalSmooth
import EnvelopeProperty.Vanishing.NadelBertiniRationalParameterIncidence

/-! # The SAME actual rational parameter for ALL original closed SNC strata

Original source smoothness and the original family's SNC coordinates internally
produce every original stratum's source smoothness and every original incidence's
total smoothness. The actual finite all-strata family then internally produces
one original rational evaluation tuple; none of these smoothness or tuple
certificates is supplied as input.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniSncParameters
open NadelBertiniUniversal NadelBertiniGenericIncidence NadelBertiniRationalParameter
  NadelBertiniRationalParameterIncidence NadelBertiniSncStrata
variable {k : Type u} [Field k] [CharZero k] {m : ℕ} {X : Scheme.{u}}

/-- Every SAME original closed SNC stratum's actual universal incidence total
space is smooth, internally from ORIGINAL X/k smoothness and ORIGINAL E.IsSnc. -/
theorem stratum_totalIncidence_smooth
    (j : X ⟶ DeJongAlterations.projectiveSpace k m) [IsClosedImmersion j]
    [Smooth (j ≫ DeJongAlterations.projectiveSpaceStructure k m)]
    (E : X.DivisorFamily) (hE : E.IsSnc) (s : Finset E.ι) :
    Smooth (projectiveToSource ((stratum E s).subschemeι ≫ j) ≫
      ((stratum E s).subschemeι ≫ j) ≫ DeJongAlterations.projectiveSpaceStructure k m) := by
  let : Smooth (((stratum E s).subschemeι ≫ j) ≫
      DeJongAlterations.projectiveSpaceStructure k m) := by
    rw [Category.assoc]
    exact stratum_smooth (j ≫ DeJongAlterations.projectiveSpaceStructure k m) E hE s
  exact NadelBertiniGlobalSmooth.projectiveTotal_smooth ((stratum E s).subschemeι ≫ j)

/-- Internally choose SAME actual nonzero original rational hyperplane coefficients
in the genuine good open for EVERY original closed SNC stratum. No parameter,
stratum smoothness, total-incidence smoothness, or good-open certificate is input. -/
theorem exists_good_parameter_for_all_strata
    (j : X ⟶ DeJongAlterations.projectiveSpace k m) [IsClosedImmersion j]
    [Smooth (j ≫ DeJongAlterations.projectiveSpaceStructure k m)]
    (E : X.DivisorFamily) (hE : E.IsSnc) :
    ∃ a : Fin (m + 1) → k, a 0 ≠ 0 ∧
      (parameterMap a ≫ Spec.map (CommRingCat.ofHom
        (algebraMap k (parameterRing k m))) = 𝟙 _) ∧
      ∀ s : Finset E.ι, ∀ t : Spec (.of k), parameterMap a t ∈
        projectiveGoodOpen ((stratum E s).subschemeι ≫ j) := by
  exact exists_simultaneous_projective_good_parameter
    (fun s : Finset E.ι => (stratum E s).subscheme)
    (fun s => (stratum E s).subschemeι ≫ j)
    (fun s => stratum_embedding_closed j E s)
    (fun s => stratum_totalIncidence_smooth j E hE s)

end EnvelopeProperty.Vanishing.NadelBertiniSncParameters
