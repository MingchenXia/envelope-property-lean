import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationStepPullback
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorQuasicoherent

/-! # Actual eventual local lifts and zero-clearing in the original twist system

Every sufficiently large original twist lifts a given actual local section.
An actual normalized-zero section is killed by every sufficiently long
actual original section transition. The QC denominator arguments are
internal and concern the SAME original modules and SAME original section.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Opposite AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.SchemeModuleCechLineSectionLocalization

open CanonicalGeometry SchemeLineSectionEvaluation
open SchemeOpenPullbackSectionEquiv SchemeOpenPullbackWholeUnits

attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME actual finite transition preserves the normalized value of
EVERY original whole section, using the native pullback unit. -/
theorem normalizedTopValue_transition {X : Scheme.{u}} (L : X.Modules)
    (hL : IsInvertible L) (s : unitObj X ⟶ L) (F : X.Modules) (m a : ℕ)
    (y : Γ(F ⊗ bundleTensorPower L m, ⊤)) :
    normalizedTopValue L hL s F (m + a)
        ((twistIterate F L s m a).app ⊤ y) = normalizedTopValue L hL s F m y := by
  unfold normalizedTopValue
  rw [Berkovich.SchemeFramedSectionPullback.affinePullbackUnitTop_naturality]
  have h := congrArg (fun φ => φ.app ⊤
      (affinePullbackUnitTop (sectionOpen L hL s).ι (F ⊗ bundleTensorPower L m) y))
    (twistIterate_normalized L hL s F m a)
  exact h

/-- Every sufficiently large ACTUAL original twist lifts a given section
of the literal nonzero open, in a genuine original affine line frame. -/
theorem affine_eventual_normalized_lift {X : Scheme.{u}} [IsAffine X]
    (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L)
    (F : X.Modules) [F.IsQuasicoherent] (e : L ≅ unitObj X)
    (x : Γ((pullback (sectionOpen L hL s).ι).obj F, ⊤)) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∃ y : Γ(F ⊗ bundleTensorPower L m, ⊤), normalizedTopValue L hL s F m y = x := by
  obtain ⟨N, y, hy⟩ := affine_normalized_lift L hL s F e x
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact ⟨(twistIterate F L s N a).app ⊤ y,
    (normalizedTopValue_transition L hL s F N a y).trans hy⟩

private theorem twistIterate_zero_of_scalar_zero {X : Scheme.{u}} (F L : X.Modules)
    (s : unitObj X ⟶ L) (e : L ≅ unitObj X) (m a : ℕ)
    (y : Γ(F ⊗ bundleTensorPower L m, ⊤))
    (hy : SchemeLineSectionUnitFrames.frameScalar e s ^ a • y = 0) :
    (twistIterate F L s m a).app ⊤ y = 0 := by
  let E₀ := tensorFrameIso F (SchemeTensorPowerFrames.powerFrame e m)
  let E₁ := tensorFrameIso F (SchemeTensorPowerFrames.powerFrame e (m + a))
  apply (ConcreteCategory.bijective_of_isIso (E₁.hom.app ⊤)).1
  rw [map_zero]
  have h := congrArg (fun φ => φ.app ⊤ y) (twistIterate_frame F L s e m a)
  change E₁.hom.app ⊤ ((twistIterate F L s m a).app ⊤ y) =
    (SchemeUnitScalarAction.unitAction F (ModularCurves.unitEndomorphismOfTopSection
      (SchemeLineSectionUnitFrames.frameScalar e s ^ a))).val.app (op ⊤)
        (E₀.hom.app ⊤ y) at h
  rw [SchemeUnitScalarAction.unitAction_apply] at h
  have hs : (ModularCurves.unitEndomorphismOfTopSection
      (SchemeLineSectionUnitFrames.frameScalar e s ^ a)).val.app (op ⊤)
        (1 : Γ(X, ⊤)) = SchemeLineSectionUnitFrames.frameScalar e s ^ a := by
    change (1 : Γ(X, ⊤)) * X.presheaf.map
      (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op
        (SchemeLineSectionUnitFrames.frameScalar e s ^ a) = _
    simp
  rw [hs] at h
  calc
    E₁.hom.app ⊤ ((twistIterate F L s m a).app ⊤ y) =
        SchemeLineSectionUnitFrames.frameScalar e s ^ a • E₀.hom.app ⊤ y := h
    _ = E₀.hom.app ⊤ (SchemeLineSectionUnitFrames.frameScalar e s ^ a • y) :=
      ((E₀.hom.val.app (op ⊤)).hom.map_smul _ _).symm
    _ = 0 := by rw [hy, map_zero]

/-- Actual quasicoherence internally clears every normalized-zero section
by EVERY sufficiently long actual original section transition, on an
original affine frame. No annihilator or differential certificate is input. -/
theorem affine_eventual_zero_clearing {X : Scheme.{u}} [IsAffine X]
    (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L)
    (F : X.Modules) [F.IsQuasicoherent] (e : L ≅ unitObj X)
    (m : ℕ) (y : Γ(F ⊗ bundleTensorPower L m, ⊤))
    (hy : normalizedTopValue L hL s F m y = 0) :
    ∃ A : ℕ, ∀ a : ℕ, A ≤ a → (twistIterate F L s m a).app ⊤ y = 0 := by
  classical
  let V := sectionOpen L hL s
  let M := F ⊗ bundleTensorPower L m
  let r := SchemeLineSectionUnitFrames.frameScalar e s
  let : M.IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight F _
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m)
  have hu : affinePullbackUnitTop V.ι M y = 0 := by
    have h := congrArg ((normalizedTwistIso L hL s F m).inv.app ⊤) hy
    change (normalizedTwistIso L hL s F m).inv.val.app (op ⊤)
        ((normalizedTwistIso L hL s F m).hom.val.app (op ⊤) (affinePullbackUnitTop V.ι M y)) =
      (normalizedTwistIso L hL s F m).inv.val.app (op ⊤) 0 at h
    rw [iso_hom_inv_app_applyT, map_zero] at h
    exact h
  have hr : M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op y = 0 := by
    apply (openSectionsEquiv M V).injective
    rw [openSectionsEquiv_global, hu, map_zero]
  have hb : M.presheaf.map (homOfLE (X.basicOpen_le r)).op y = 0 := by
    have hc : ∀ W : X.Opens, V = W →
        M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op y = 0 := by
      rintro W rfl
      exact hr
    exact hc _ (sectionOpen_eq_basicOpen_of_frame L hL s e)
  obtain ⟨A, hA⟩ :=
    exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isQuasicoherent_of_isAffineOpen
      M ⟨⊤, isAffineOpen_top X⟩ r y hb
  refine ⟨A, fun a ha => ?_⟩
  have hz : r ^ a • y = 0 := by
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
    rw [pow_add, mul_comm, mul_smul, hA, smul_zero]
  exact twistIterate_zero_of_scalar_zero F L s e m a y hz

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
