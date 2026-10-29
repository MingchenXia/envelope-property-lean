import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationVanishing

/-! # Actual inverse-image vanishing for every positive original power section

The SAME original global twist hypothesis internally transports through
native pullback/power multiplication isomorphisms, at original exponents
d*m. The actual original section-open pullback then gives literal original
inverse-image higher cohomology vanishing, with no local acyclicity input.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeLineSectionPowerInverseVanishing
open CanonicalGeometry SchemeLineSectionEvaluation SchemeModuleCechLineSectionLocalization
attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Eventual global positive H of SAME original F twisted by powers of f*H
proves actual ordinary positive H vanishing on the literal inverse image
of the nonzero open of EVERY positive-power original H section. Native
power bounds and all whole original line comparisons are internal. -/
theorem inverseImage_powerSection_H_succ_subsingleton {X Y : Scheme.{u}}
    [CompactSpace Y] [Y.IsSeparated] (f : Y ⟶ X) (H : X.Modules) (hH : IsInvertible H)
    (F : Y.Modules) [F.IsQuasicoherent] (d : ℕ) (hd : 0 < d)
    (s : unitObj X ⟶ bundleTensorPower H d) (q : ℕ)
    (hGlobal : ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      Subsingleton (CategoryTheory.Sheaf.H
        (F ⊗ bundleTensorPower ((pullback f).obj H) m).sheaf (q + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H
      (F.restrict (f ⁻¹ᵁ sectionOpen (bundleTensorPower H d)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH d) s).ι).sheaf (q + 1)) := by
  obtain ⟨N, hN⟩ := hGlobal
  let B := (pullback f).obj H
  let T := (pullback f).obj (bundleTensorPower H d)
  let hT := (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH d).pullback f
  have hTwists : ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      Subsingleton (CategoryTheory.Sheaf.H (F ⊗ bundleTensorPower T m).sheaf (q + 1)) := by
    refine ⟨N, fun m hm => ?_⟩
    let E : bundleTensorPower T m ≅ bundleTensorPower B (d * m) :=
      BundleTensorPowerPullback.powerIso (BundleTensorPowerPullback.pullbackIso f H d) m ≪≫
        BundleTensorPowerPullback.powerMulIso B d m
    let EF : F ⊗ bundleTensorPower T m ≅ F ⊗ bundleTensorPower B (d * m) := Iso.refl F ⊗ᵢ E
    exact AffinePushforwardCohomology.subsingleton_H_of_retract EF.hom EF.inv EF.hom_inv_id
      (q + 1) (hN (d * m) (hm.trans (Nat.le_mul_of_pos_left m hd)))
  have h := sectionOpen_restrict_H_succ_subsingleton T hT (pullbackSectionHom f s) F q hTwists
  have hV : sectionOpen T hT (pullbackSectionHom f s) =
      f ⁻¹ᵁ sectionOpen (bundleTensorPower H d)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH d) s :=
    sectionOpen_pullback (bundleTensorPower H d)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH d) s f
  rw [hV] at h
  exact h

end EnvelopeProperty.SchemeLineSectionPowerInverseVanishing
