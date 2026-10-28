import EnvelopeProperty.Vanishing.RelativeNadelBertiniProjective
import EnvelopeProperty.Vanishing.NadelBertiniSncCriterion

/-! # Actual relative projective Bertini preserves the original SNC family

All closed SNC strata use the same original R-projective coordinate sections
and one original rational k-coefficient tuple.  Their genuine nonproper
parameter good opens internally produce that tuple, Cartier restrictions,
and common regular parameters for the whole appended family.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.RelativeNadelBertiniSnc
open NadelBertiniUniversal NadelBertiniSncStrata NadelBertiniRationalParameter
  NadelBertiniRestrictionCover SchemeLineSectionEvaluation
open RelativeNadelBertiniProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k R : Type u} [Field k] [CommRing R]
  {m : ℕ} {X Y : Scheme.{u}}

/-- Every original R-projective coordinate section retains its whole native
pullback along any original source morphism. -/
theorem projectiveSections_pullback (f : Y ⟶ X)
    (j : X ⟶ DeJongAlterations.projectiveSpace R m) (i : Fin (m + 1)) :
    ((pullbackComp f j).hom.app
      (MvPolynomial.coordinateHyperplaneTwist (R := R) (0 : Fin (m + 1)) 1)).app ⊤
      (affinePullbackUnitTop f (projectiveLine j) (projectiveSections j i)) =
      projectiveSections (f ≫ j) i := by
  change ((pullbackComp f j).hom.app
      (MvPolynomial.coordinateHyperplaneTwist (R := R) (0 : Fin (m + 1)) 1)).app ⊤
      (affinePullbackUnitTop f (projectiveLine j)
        (sectionAtOne (pullbackSectionHom j
          (ProjectiveTwistGlobalGeneration.coordinateSectionHom
            (R := R) (0 : Fin (m + 1)) i 1)))) = _
  rw [pullback_sectionAtOne]
  exact congrArg sectionAtOne (pullbackSectionHom_comp f j
    (ProjectiveTwistGlobalGeneration.coordinateSectionHom (R := R) (0 : Fin (m + 1)) i 1))

/-- The entire original relative selected ideal, including all nilpotent
structure, commutes with arbitrary original source base change. -/
theorem selectedIdeal_comap (p : X ⟶ Spec (.of k)) (f : Y ⟶ X)
    (j : X ⟶ DeJongAlterations.projectiveSpace R m) (a : Fin (m + 1) → k) :
    (selectedIdeal p j a).comap f = selectedIdeal (f ≫ p) (f ≫ j) a := by
  let L' := (pullback f).obj (projectiveLine j)
  let s' := fun i => affinePullbackUnitTop f (projectiveLine j) (projectiveSections j i)
  let e : L' ≅ projectiveLine (f ≫ j) :=
    (pullbackComp f j).app
      (MvPolynomial.coordinateHyperplaneTwist (R := R) (0 : Fin (m + 1)) 1)
  have hi := NadelBertiniSelectedBaseChange.selectedIdeal_iso (f ≫ p) a L' s'
    ((lineInvertible j).pullback f) (projectiveLine (f ≫ j)) (lineInvertible (f ≫ j)) e
  have hs : (fun i => e.hom.app ⊤ (s' i)) = projectiveSections (f ≫ j) := by
    funext i
    exact projectiveSections_pullback f j i
  rw [hs] at hi
  exact (NadelBertiniSelectedBaseChange.selectedIdeal_comap p f a
    (projectiveLine j) (projectiveSections j) (lineInvertible j)).trans hi

/-- One actual original rational tuple lies in the actual ambient good open
and every whole closed-stratum good open; all opens are produced internally. -/
theorem exists_ambient_and_strata_good_parameter [CharZero k]
    (p : X ⟶ Spec (.of k)) [Smooth p] [FiniteType p]
    (j : X ⟶ DeJongAlterations.projectiveSpace R m) [IsClosedImmersion j]
    (E : X.DivisorFamily) (hE : E.IsSnc) :
    ∃ a : Fin (m + 1) → k, a 0 ≠ 0 ∧
      (∀ t : Spec (.of k), parameterMap a t ∈ goodOpen p j) ∧
      ∀ s : Finset E.ι, ∀ t : Spec (.of k), parameterMap a t ∈
        goodOpen ((stratum E s).subschemeι ≫ p) ((stratum E s).subschemeι ≫ j) := by
  let U : Option (Finset E.ι) → (Spec (.of (parameterRing k m))).Opens :=
    fun s => s.elim (goodOpen p j) (fun s =>
      goodOpen ((stratum E s).subschemeι ≫ p) ((stratum E s).subschemeι ≫ j))
  have hU : ∀ s, genericPoint (Spec (.of (parameterRing k m))) ∈ U s := by
    intro s
    cases s with
    | none => exact genericPoint_mem_goodOpen p j
    | some s =>
      let : Smooth ((stratum E s).subschemeι ≫ p) := stratum_smooth p E hE s
      exact genericPoint_mem_goodOpen ((stratum E s).subschemeι ≫ p)
        ((stratum E s).subschemeι ≫ j)
  obtain ⟨a, ha0, ha⟩ :=
    NadelBertiniRationalParameterIncidence.exists_nonzero_parameter_mem_finite_opens U hU
  exact ⟨a, ha0, ha none, fun s => ha (some s)⟩

/-- Genuine relative projective Bertini for the original SNC family.  The
original arbitrary R is retained, and X need not be proper over k.  The
actual rational parameter, Cartier zero ideal, smoothness and whole SNC
enlargement are all outputs of the original geometry. -/
theorem exists_relative_projective_snc_selected [CharZero k]
    (p : X ⟶ Spec (.of k)) [Smooth p] [FiniteType p]
    (j : X ⟶ DeJongAlterations.projectiveSpace R m) [IsClosedImmersion j]
    (E : X.DivisorFamily) (hE : E.IsSnc) :
    ∃ a : Fin (m + 1) → k, a 0 ≠ 0 ∧
      (selectedIdeal p j a).IsInvertible ∧
      Smooth ((selectedIdeal p j a).subschemeι ≫ p) ∧
      (E.append (selectedIdeal p j a)).IsSnc ∧ E.HasSncWith (selectedIdeal p j a) := by
  obtain ⟨a, ha0, ha, has⟩ := exists_ambient_and_strata_good_parameter p j E hE
  have hH := selected_isInvertible p j a ha
  let hHS := selected_smooth p j a ha
  have hcartier : ∀ s : Finset E.ι,
      ((selectedIdeal p j a).comap (stratum E s).subschemeι).IsInvertible := by
    intro s
    rw [selectedIdeal_comap]
    exact selected_isInvertible ((stratum E s).subschemeι ≫ p)
      ((stratum E s).subschemeι ≫ j) a (has s)
  have hsmooth : ∀ s : Finset E.ι, Smooth
      (((selectedIdeal p j a).comap (stratum E s).subschemeι).subschemeι ≫
        (stratum E s).subschemeι ≫ p) := by
    intro s
    rw [selectedIdeal_comap]
    exact selected_smooth ((stratum E s).subschemeι ≫ p)
      ((stratum E s).subschemeι ≫ j) a (has s)
  obtain ⟨hSnc, hWith⟩ := NadelBertiniSncCriterion.append_isSnc_of_strata_cartier_smooth
    p E hE (selectedIdeal p j a) hH hcartier hsmooth
  exact ⟨a, ha0, hH, hHS, hSnc, hWith⟩

end EnvelopeProperty.Vanishing.RelativeNadelBertiniSnc
