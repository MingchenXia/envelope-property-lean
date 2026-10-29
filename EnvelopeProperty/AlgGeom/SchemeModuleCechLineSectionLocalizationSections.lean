import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationNatural

/-! # Actual local denominators in original affine-open section groups

The affine-frame denominator theorem is transported internally to the
SAME original sheaf sections on an original affine open. The actual native
normalized restriction map is the map being lifted; no matching equation,
localization datum or caller-provided lift is input.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleCechLineSectionLocalization
open CanonicalGeometry SchemeLineSectionEvaluation
open SchemeOpenPullbackSectionEquiv
attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def pushTopEquiv {A B : Scheme.{u}} (j : A ⟶ B) (M : A.Modules) :
    Γ(M, ⊤) ≃+ Γ((pushforward j).obj M, ⊤) :=
  (M.presheaf.mapIso (eqToIso (Scheme.Hom.preimage_top j)).op).addCommGroupIsoToAddEquiv

private theorem pushTopEquiv_apply {A B : Scheme.{u}} (j : A ⟶ B) (M : A.Modules)
    (x : Γ(M, ⊤)) : pushTopEquiv j M x = pushforwardTopSection j M x := rfl

private theorem unitTop_push {A B : Scheme.{u}} (j : A ⟶ B) (M : B.Modules)
    (x : Γ(M, ⊤)) :
    pushforwardTopSection j ((pullback j).obj M) (affinePullbackUnitTop j M x) =
      ((pullbackPushforwardAdjunction j).unit.app M).app ⊤ x := by
  let P := (pullback j).obj M
  let y := ((pullbackPushforwardAdjunction j).unit.app M).app ⊤ x
  change P.presheaf.map (eqToHom (Scheme.Hom.preimage_top j)).op
    (P.presheaf.map (eqToHom (Scheme.Hom.preimage_top j).symm).op y) = y
  have hh : P.presheaf.map (eqToHom (Scheme.Hom.preimage_top j).symm).op ≫
      P.presheaf.map (eqToHom (Scheme.Hom.preimage_top j)).op = 𝟙 _ := by
    rw [← P.presheaf.map_comp, ← P.presheaf.map_id]
    exact P.presheaf.congr_map (Subsingleton.elim _ _)
  exact ConcreteCategory.congr_hom hh y

private theorem normalizedPushforwardMap_top {X : Scheme.{u}} (L : X.Modules)
    (hL : IsInvertible L) (s : unitObj X ⟶ L) (F : X.Modules) (m : ℕ)
    (y : Γ(F ⊗ bundleTensorPower L m, ⊤)) :
    (normalizedPushforwardMap L hL s F m).app ⊤ y =
      pushTopEquiv (sectionOpen L hL s).ι ((pullback (sectionOpen L hL s).ι).obj F)
        (normalizedTopValue L hL s F m y) := by
  rw [pushTopEquiv_apply]
  unfold normalizedTopValue
  rw [← pushforwardMap_app_top_pushforwardTopSection, unitTop_push]
  rfl

private theorem sectionEquiv_naturality {X : Scheme.{u}} {M N : X.Modules}
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

/-- Every sufficiently large SAME original twist lifts an actual original
normalized target section over an original affine open. All open-square,
native section, tensor, power and normalization comparisons are internal.
The ordinary original geometric affine frame will be selected internally
from invertibility by the finite-cover cochain consumer. -/
theorem affineOpen_eventual_normalized_lift {X : Scheme.{u}}
    (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L)
    (F : X.Modules) [F.IsQuasicoherent] (U : X.affineOpens)
    (e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme)
    (x : Γ((pushforward (sectionOpen L hL s).ι).obj
      ((pullback (sectionOpen L hL s).ι).obj F), U.1)) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∃ y : Γ(F ⊗ bundleTensorPower L m, U.1),
        (normalizedPushforwardMap L hL s F m).app U.1 y = x := by
  classical
  let g := U.1.ι
  let Fg := (pullback g).obj F
  let Lg := (pullback g).obj L
  let sg := pullbackSectionHom g s
  let W := sectionOpen Lg (hL.pullback g) sg
  let G := (pushforward (sectionOpen L hL s).ι).obj
    ((pullback (sectionOpen L hL s).ι).obj F)
  let B := sectionOpenPushforwardIso g L hL s F
  let E := pushTopEquiv W.ι ((pullback W.ι).obj Fg)
  let z := E.symm (B.hom.app ⊤ (openSectionsEquiv G U.1 x))
  let : IsAffine U.1.toScheme := U.2
  let : Fg.IsQuasicoherent := (isQuasicoherent U.1.toScheme).prop_of_iso
    ((restrictFunctorIsoPullback g).app F) inferInstance
  obtain ⟨N, hN⟩ := affine_eventual_normalized_lift Lg (hL.pullback g) sg Fg e z
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨t, ht⟩ := hN m hm
  let M := F ⊗ bundleTensorPower L m
  let T := twistPullbackIso g F L m
  let y₀ := T.inv.app ⊤ t
  let y := (openSectionsEquiv M U.1).symm y₀
  refine ⟨y, ?_⟩
  apply (openSectionsEquiv G U.1).injective
  apply (ConcreteCategory.bijective_of_isIso (B.hom.app ⊤)).1
  rw [sectionEquiv_naturality]
  have hy : openSectionsEquiv M U.1 y = y₀ := (openSectionsEquiv M U.1).apply_symm_apply y₀
  rw [hy]
  have hb := congrArg (fun φ => φ.app ⊤ y₀)
    (normalizedPushforwardMap_pullback g L hL s F m)
  change B.hom.app ⊤ (((pullback g).map (normalizedPushforwardMap L hL s F m)).app ⊤ y₀) =
    (normalizedPushforwardMap Lg (hL.pullback g) sg Fg m).app ⊤ (T.hom.app ⊤ y₀) at hb
  have hT : T.hom.app ⊤ y₀ = t := iso_inv_hom_app_applyT T (op ⊤) t
  rw [hT] at hb
  calc
    B.hom.app ⊤ (((pullback g).map (normalizedPushforwardMap L hL s F m)).app ⊤ y₀) =
        (normalizedPushforwardMap Lg (hL.pullback g) sg Fg m).app ⊤ t := hb
    _ = E (normalizedTopValue Lg (hL.pullback g) sg Fg m t) :=
      normalizedPushforwardMap_top Lg (hL.pullback g) sg Fg m t
    _ = E z := by rw [ht]
    _ = B.hom.app ⊤ (openSectionsEquiv G U.1 x) := E.apply_symm_apply _

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
