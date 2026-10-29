import EnvelopeProperty.AlgGeom.AffinePushforwardCohomology

/-! # Actual cohomology comparison from acyclic inverse-image intersections

This general Leray comparison proves the cohomological mechanism.  Its local
acyclicity premise remains a separate theorem to prove for principalization;
it is neither a DI assumption nor an original Nadel completion claim.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelLerayCech

/-- Native Cech and ordered homology compare to the actual positive group
when the actual source intersections are acyclic, without affine hypotheses. -/
theorem subsingleton_H_iff_ordered_zero {X S : Scheme.{u}}
    (p : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hlocal : ∀ (a : ℕ) (i : Fin (a + 1) → ι) (j : ℕ),
      Subsingleton (CategoryTheory.Sheaf.H
        ((TopCat.Sheaf.restrict AddCommGrpCat
          (∏ᶜ fun k : Fin (a + 1) => U (i k)).isOpenEmbedding).obj M.sheaf) (j + 1)))
    (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1)) ↔
      IsZero ((orderedBaseCechComplex p M U).homology (q + 1)) := by
  have hcech := TopCat.Sheaf.cechComplex_exactAt_succ_iff_subsingleton_H_of_subsingleton_restrict_H
    U M.sheaf hU hlocal q
  constructor
  · intro h
    have hb := (baseCechComplex_exactAt_iff p M U (q + 1)).mpr (hcech.mpr h)
    have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hb
    exact IsZero.of_iso hz (baseCechOrderedHomologyIso p M U (q + 1)).symm
  · intro h
    have hb : IsZero ((baseCechComplex p M U).homology (q + 1)) :=
      IsZero.of_iso h (baseCechOrderedHomologyIso p M U (q + 1))
    exact hcech.mp ((baseCechComplex_exactAt_iff p M U (q + 1)).mp
      ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr hb))

/-- The whole positive cohomology comparison for an arbitrary original map.
The true local-vanishing groups must be proved before using this theorem. -/
theorem subsingleton_H_iff_pushforward {X Y : Scheme.{u}}
    (f : Y ⟶ X) [X.IsSeparated] (M : Y.Modules)
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i))
    (hlocal : ∀ (a : ℕ) (i : Fin (a + 1) → ι) (j : ℕ),
      Subsingleton (CategoryTheory.Sheaf.H
        ((TopCat.Sheaf.restrict AddCommGrpCat
          (∏ᶜ fun k : Fin (a + 1) => f ⁻¹ᵁ U (i k)).isOpenEmbedding).obj M.sheaf) (j + 1)))
    (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H
        ((Scheme.Modules.pushforward f).obj M).sheaf (q + 1)) := by
  have hs := subsingleton_H_iff_ordered_zero (f ≫ 𝟙 X) M (fun i => f ⁻¹ᵁ U i)
    (f.iSup_preimage_eq_top hU) hlocal q
  have ht := AffinePushforwardCohomology.subsingleton_H_iff_ordered_zero (𝟙 X)
    ((Scheme.Modules.pushforward f).obj M) U hU hUa q
  let e := HomologicalComplex.homologyMapIso
    (orderedBaseCechComplexPushforwardIso f (𝟙 X) M U) (q + 1)
  exact hs.trans ⟨fun h => ht.mpr (IsZero.of_iso h e.symm),
    fun h => IsZero.of_iso (ht.mp h) e⟩

end EnvelopeProperty.Vanishing.NadelLerayCech
