import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationSections
import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationTransitions

/-! # Eventual zero-clearing for original affine-open twisted sections

A normalized-zero original section is killed by every sufficiently long
actual original s-transition. The normalized map, original section groups,
ordinary affine frame and actual transitions are retained throughout.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleCechLineSectionLocalization
open CanonicalGeometry SchemeLineSectionEvaluation SchemeOpenPullbackSectionEquiv
attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal inverse image of an ORIGINAL affine frame open in the
original section-open is affine. The actual pulled section's zero-open
equality identifies its original affine principal chart internally. -/
theorem sectionOpen_preimage_affine_of_frame {X : Scheme.{u}}
    (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L)
    (U : X.affineOpens) (e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme) :
    IsAffineOpen ((sectionOpen L hL s).ι ⁻¹ᵁ U.1) := by
  let V := sectionOpen L hL s
  let g := U.1.ι
  let W := sectionOpen ((pullback g).obj L) (hL.pullback g) (pullbackSectionHom g s)
  let : IsAffine U.1.toScheme := U.2
  have hW : IsAffineOpen W := by
    change IsAffineOpen (sectionOpen ((pullback U.1.ι).obj L)
      (hL.pullback U.1.ι) (pullbackSectionHom U.1.ι s))
    rw [sectionOpen_eq_basicOpen_of_frame _ _ _ e]
    exact (isAffineOpen_top U.1.toScheme).basicOpen _
  have hImage : IsAffineOpen (g ''ᵁ W) := hW.image_of_isOpenImmersion g
  have hEq : g ''ᵁ W = U.1 ⊓ V := by
    change U.1.ι ''ᵁ sectionOpen ((pullback U.1.ι).obj L)
      (hL.pullback U.1.ι) (pullbackSectionHom U.1.ι s) = U.1 ⊓ V
    rw [sectionOpen_pullback, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
  have hInf : IsAffineOpen (V ⊓ U.1) := by
    rw [inf_comm, ← hEq]
    exact hImage
  apply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion V.ι).mp
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact hInf

private theorem zeroSectionEquiv_naturality {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (U : X.Opens) (x : Γ(M, U)) :
    openSectionsEquiv N U (φ.app U x) =
      ((pullback U.ι).map φ).app ⊤ (openSectionsEquiv M U x) := by
  rw [openSectionsEquiv_apply, openSectionsEquiv_apply]
  unfold SchemePullbackLocalSections.openPullbackSection
  let k := (eqToHom U.ι_preimage_self.symm).op
  have hu := congrArg (fun a => a.app U x)
    ((pullbackPushforwardAdjunction U.ι).unit.naturality φ)
  change ((pullbackPushforwardAdjunction U.ι).unit.app N).app U (φ.app U x) =
    ((pullback U.ι).map φ).app (U.ι ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction U.ι).unit.app M).app U x) at hu
  have hn := PresheafOfModules.naturality_apply ((pullback U.ι).map φ).val k
    (((pullbackPushforwardAdjunction U.ι).unit.app M).app U x)
  exact (congrArg (((pullback U.ι).obj N).presheaf.map k) hu).trans hn.symm

private theorem normalizedTopValue_zero_of_native_zero {X : Scheme.{u}} (L : X.Modules)
    (hL : IsInvertible L) (s : unitObj X ⟶ L) (F : X.Modules) (m : ℕ)
    (y : Γ(F ⊗ bundleTensorPower L m, ⊤))
    (hy : (normalizedPushforwardMap L hL s F m).app ⊤ y = 0) :
    normalizedTopValue L hL s F m y = 0 := by
  let V := sectionOpen L hL s
  let P := (pullback V.ι).obj (F ⊗ bundleTensorPower L m)
  let Q := (pullback V.ι).obj F
  let ν := (normalizedTwistIso L hL s F m).hom
  let k := (eqToHom (Scheme.Hom.preimage_top V.ι).symm).op
  let z := ((pullbackPushforwardAdjunction V.ι).unit.app (F ⊗ bundleTensorPower L m)).app ⊤ y
  have hn := PresheafOfModules.naturality_apply ν.val k z
  have hh := congrArg (Q.presheaf.map k) hy
  change Q.presheaf.map k (ν.app (V.ι ⁻¹ᵁ ⊤) z) = Q.presheaf.map k 0 at hh
  rw [map_zero] at hh
  exact hn.trans hh

/-- Actual normalized-zero sections over an ORIGINAL affine open are killed
by EVERY sufficiently long SAME original finite section transition. Ordinary
geometric line frames suffice; all normalized maps/transition comparisons,
quasicoherence and actual annihilator bounds are derived internally. -/
theorem affineOpen_eventual_zero_clearing {X : Scheme.{u}}
    (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L)
    (F : X.Modules) [F.IsQuasicoherent] (U : X.affineOpens)
    (e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme)
    (m : ℕ) (y : Γ(F ⊗ bundleTensorPower L m, U.1))
    (hy : (normalizedPushforwardMap L hL s F m).app U.1 y = 0) :
    ∃ A : ℕ, ∀ a : ℕ, A ≤ a → (twistIterate F L s m a).app U.1 y = 0 := by
  let g := U.1.ι
  let Fg := (pullback g).obj F
  let Lg := (pullback g).obj L
  let sg := pullbackSectionHom g s
  let W := sectionOpen Lg (hL.pullback g) sg
  let G := (pushforward (sectionOpen L hL s).ι).obj
    ((pullback (sectionOpen L hL s).ι).obj F)
  let M := F ⊗ bundleTensorPower L m
  let T := twistPullbackIso g F L m
  let y₀ := openSectionsEquiv M U.1 y
  let t := T.hom.app ⊤ y₀
  let : IsAffine U.1.toScheme := U.2
  let : Fg.IsQuasicoherent := (isQuasicoherent U.1.toScheme).prop_of_iso
    ((restrictFunctorIsoPullback g).app F) inferInstance
  have hz : ((pullback g).map (normalizedPushforwardMap L hL s F m)).app ⊤ y₀ = 0 := by
    rw [← zeroSectionEquiv_naturality, hy, map_zero]
  have hb := congrArg (fun φ => φ.app ⊤ y₀)
    (normalizedPushforwardMap_pullback g L hL s F m)
  change (sectionOpenPushforwardIso g L hL s F).hom.app ⊤
      (((pullback g).map (normalizedPushforwardMap L hL s F m)).app ⊤ y₀) =
    (normalizedPushforwardMap Lg (hL.pullback g) sg Fg m).app ⊤ t at hb
  rw [hz, map_zero] at hb
  have ht : normalizedTopValue Lg (hL.pullback g) sg Fg m t = 0 :=
    normalizedTopValue_zero_of_native_zero Lg (hL.pullback g) sg Fg m t hb.symm
  obtain ⟨A, hA⟩ := affine_eventual_zero_clearing Lg (hL.pullback g) sg Fg e m t ht
  refine ⟨A, fun a ha => ?_⟩
  apply (openSectionsEquiv (F ⊗ bundleTensorPower L (m + a)) U.1).injective
  rw [map_zero, zeroSectionEquiv_naturality]
  apply (ConcreteCategory.bijective_of_isIso ((twistPullbackIso g F L (m + a)).hom.app ⊤)).1
  rw [map_zero]
  have hc := congrArg (fun φ => φ.app ⊤ y₀)
    (twistIterate_pullback_of_frame g F L s e m a)
  change (twistPullbackIso g F L (m + a)).hom.app ⊤
      (((pullback g).map (twistIterate F L s m a)).app ⊤ y₀) =
    (twistIterate Fg Lg sg m a).app ⊤ t at hc
  exact hc.trans (hA a ha)

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
