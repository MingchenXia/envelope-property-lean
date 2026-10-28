import EnvelopeProperty.Vanishing.NadelBertiniSncFlatCartier
import EnvelopeProperty.Vanishing.NadelBertiniSncParameters
import EnvelopeProperty.Vanishing.NadelBertiniSncCriterion

/-! # An internally chosen SAME original hyperplane preserves the whole SNC family

Every original all-stratum good parameter, whole-ideal restriction, actual local
Cartier equation and common original SNC parameter system is produced internally.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniSncFlatBertini
open NadelBertiniUniversal NadelBertiniGenericIncidence NadelBertiniRationalParameter
  NadelBertiniRationalParameterIncidence NadelBertiniSncStrata NadelBertiniFibreSmooth
variable {k : Type u} [Field k] [CharZero k] {m : ℕ} {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- SAME original rational coefficients in the actual ambient good open and
EVERY actual closed-stratum good open, internally from original smoothness/SNC. -/
theorem exists_ambient_and_strata_good_parameter
    (j : X ⟶ DeJongAlterations.projectiveSpace k m) [IsClosedImmersion j]
    [Smooth (j ≫ DeJongAlterations.projectiveSpaceStructure k m)]
    (E : X.DivisorFamily) (hE : E.IsSnc) :
    ∃ a : Fin (m + 1) → k, a 0 ≠ 0 ∧
      (parameterMap a ≫ Spec.map (CommRingCat.ofHom
        (algebraMap k (parameterRing k m))) = 𝟙 _) ∧
      (∀ t : Spec (.of k), parameterMap a t ∈ projectiveGoodOpen j) ∧
      ∀ s : Finset E.ι, ∀ t : Spec (.of k), parameterMap a t ∈
        projectiveGoodOpen ((stratum E s).subschemeι ≫ j) := by
  let U : Option (Finset E.ι) → (Spec (.of (parameterRing k m))).Opens :=
    fun s => s.elim (projectiveGoodOpen j)
      (fun s => projectiveGoodOpen ((stratum E s).subschemeι ≫ j))
  have hU : ∀ s, genericPoint (Spec (.of (parameterRing k m))) ∈ U s := by
    intro s
    cases s with
    | none =>
      let := NadelBertiniGlobalSmooth.projectiveTotal_smooth j
      exact (projectiveGoodOpen_specification j).1
    | some s =>
      let := NadelBertiniSncParameters.stratum_totalIncidence_smooth j E hE s
      exact (projectiveGoodOpen_specification ((stratum E s).subschemeι ≫ j)).1
  obtain ⟨a, ha0, ha⟩ := exists_nonzero_parameter_mem_finite_opens U hU
  exact ⟨a, ha0, parameterMap_structure a, ha none, fun s => ha (some s)⟩

/-- Genuine one-step projective Bertini for the SAME original SNC family: the
actual rational tuple and original selected Cartier hypersurface are produced
internally; no desired auxiliary divisor, tuple, Cartier or SNC certificate is input. -/
theorem exists_projective_snc_selected
    (j : X ⟶ DeJongAlterations.projectiveSpace k m) [IsClosedImmersion j]
    [Smooth (j ≫ DeJongAlterations.projectiveSpaceStructure k m)]
    (E : X.DivisorFamily) (hE : E.IsSnc) :
    ∃ a : Fin (m + 1) → k, a 0 ≠ 0 ∧
      (projectiveSelectedIdeal j a).IsInvertible ∧
      Smooth ((projectiveSelectedIdeal j a).subschemeι ≫ j ≫
        DeJongAlterations.projectiveSpaceStructure k m) ∧
      (E.append (projectiveSelectedIdeal j a)).IsSnc ∧
      E.HasSncWith (projectiveSelectedIdeal j a) := by
  obtain ⟨a, ha0, _, ha, has⟩ := exists_ambient_and_strata_good_parameter j E hE
  have hH := NadelBertiniSncFlatCartier.projective_selected_isInvertible j a ha
  let hHS := projective_selected_smooth j a ha
  have hcartier : ∀ s : Finset E.ι,
      ((projectiveSelectedIdeal j a).comap (stratum E s).subschemeι).IsInvertible := by
    intro s
    rw [NadelBertiniSelectedBaseChange.projectiveSelectedIdeal_comap]
    exact NadelBertiniSncFlatCartier.projective_selected_isInvertible
      ((stratum E s).subschemeι ≫ j) a (has s)
  have hsmooth : ∀ s : Finset E.ι, Smooth
      (((projectiveSelectedIdeal j a).comap (stratum E s).subschemeι).subschemeι ≫
        (stratum E s).subschemeι ≫ (j ≫ DeJongAlterations.projectiveSpaceStructure k m)) := by
    intro s
    rw [NadelBertiniSelectedBaseChange.projectiveSelectedIdeal_comap]
    let : Smooth (((stratum E s).subschemeι ≫ j) ≫
        DeJongAlterations.projectiveSpaceStructure k m) := by
      rw [Category.assoc]
      exact stratum_smooth (j ≫ DeJongAlterations.projectiveSpaceStructure k m) E hE s
    simpa only [Category.assoc] using
      (projective_selected_smooth ((stratum E s).subschemeι ≫ j) a (has s))
  obtain ⟨hSnc, hWith⟩ := NadelBertiniSncCriterion.append_isSnc_of_strata_cartier_smooth
    (j ≫ DeJongAlterations.projectiveSpaceStructure k m) E hE
    (projectiveSelectedIdeal j a) hH hcartier hsmooth
  exact ⟨a, ha0, hH, hHS, hSnc, hWith⟩

end EnvelopeProperty.Vanishing.NadelBertiniSncFlatBertini
