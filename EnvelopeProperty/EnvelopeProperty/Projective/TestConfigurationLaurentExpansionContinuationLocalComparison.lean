import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationOpenRestriction

/-! # The original canonical local pullback iso and its adjunction unit

The actual inverse-image-open scheme square constructs every comparison.
Mates of the five canonical factors derive unit compatibility; no local
section comparison or local bijectivity is a supplied datum.
-/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules

/-- The canonical comparison on the SAME original inverse-image open,
constructed from its genuine scheme square and native pullback composition. -/
def originalOpenPullbackIso {X Y : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens) :
    pullback g ⋙ restrictFunctor (g ⁻¹ᵁ U).ι ≅
      restrictFunctor U.ι ⋙ pullback (g ∣_ U) :=
  Functor.isoWhiskerLeft (pullback g) (restrictFunctorIsoPullback (g ⁻¹ᵁ U).ι) ≪≫
    pullbackComp (g ⁻¹ᵁ U).ι g ≪≫
    pullbackCongr (morphismRestrict_ι g U).symm ≪≫
    (pullbackComp (g ∣_ U) U.ι).symm ≪≫
    Functor.isoWhiskerRight (restrictFunctorIsoPullback U.ι).symm (pullback (g ∣_ U))

/-- The original right-adjoint comparison uses only the SAME actual
open-inclusion scheme square, with BOTH original pushforward maps. -/
def originalOpenPushforwardIso {X Y : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens) :
    pushforward (g ⁻¹ᵁ U).ι ⋙ pushforward g ≅
      pushforward (g ∣_ U) ⋙ pushforward U.ι :=
  pushforwardComp (g ⁻¹ᵁ U).ι g ≪≫
    pushforwardCongr (morphismRestrict_ι g U).symm ≪≫
    (pushforwardComp (g ∣_ U) U.ι).symm

private theorem conjugate_pullbackCongr_inv {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) :
    conjugateEquiv (pullbackPushforwardAdjunction f) (pullbackPushforwardAdjunction g)
      (pullbackCongr h).inv = (pushforwardCongr h).hom := by
  subst g
  rw [show (pullbackCongr (rfl : f = f)).inv = 𝟙 _ from rfl, conjugateEquiv_id]
  ext M U s
  simp

private theorem conjugate_pullbackComp_hom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (pullbackPushforwardAdjunction (f ≫ g))
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (pullbackComp f g).hom = (pushforwardComp f g).inv := by
  have h := conjugateEquiv_comm
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g))
    (α := (pullbackComp f g).inv) (β := (pullbackComp f g).hom)
    (pullbackComp f g).hom_inv_id
  rw [conjugateEquiv_pullbackComp_inv] at h
  apply (cancel_epi (pushforwardComp f g).hom).1
  exact h.trans (pushforwardComp f g).hom_inv_id.symm

private theorem conjugate_five {C D : Type*} [Category* C] [Category* D]
    {F₀ F₁ F₂ F₃ F₄ F₅ : C ⥤ D} {R₀ R₁ R₂ R₃ R₄ R₅ : D ⥤ C}
    (a₀ : F₀ ⊣ R₀) (a₁ : F₁ ⊣ R₁) (a₂ : F₂ ⊣ R₂)
    (a₃ : F₃ ⊣ R₃) (a₄ : F₄ ⊣ R₄) (a₅ : F₅ ⊣ R₅)
    (t₁ : F₀ ⟶ F₁) (t₂ : F₁ ⟶ F₂) (t₃ : F₂ ⟶ F₃)
    (t₄ : F₃ ⟶ F₄) (t₅ : F₄ ⟶ F₅) :
    conjugateEquiv a₅ a₀ (t₁ ≫ t₂ ≫ t₃ ≫ t₄ ≫ t₅) =
      conjugateEquiv a₅ a₄ t₅ ≫ conjugateEquiv a₄ a₃ t₄ ≫
        conjugateEquiv a₃ a₂ t₃ ≫ conjugateEquiv a₂ a₁ t₂ ≫
          conjugateEquiv a₁ a₀ t₁ := by
  rw [← conjugateEquiv_comp a₅ a₁ a₀,
    ← conjugateEquiv_comp a₅ a₂ a₁,
    ← conjugateEquiv_comp a₅ a₃ a₂,
    ← conjugateEquiv_comp a₅ a₄ a₃]
  simp only [Category.assoc]

/-- The mate of THIS actual canonical local pullback iso is the actual
original pushforward comparison, DERIVED from its five native factors. -/
theorem originalOpenPullbackIso_conjugate {X Y : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens) :
    conjugateEquiv
      ((pullbackPushforwardAdjunction g).comp (restrictAdjunction (g ⁻¹ᵁ U).ι))
      ((restrictAdjunction U.ι).comp (pullbackPushforwardAdjunction (g ∣_ U)))
      (originalOpenPullbackIso g U).inv = (originalOpenPushforwardIso g U).hom := by
  let a₀ := (pullbackPushforwardAdjunction g).comp (restrictAdjunction (g ⁻¹ᵁ U).ι)
  let a₁ := (pullbackPushforwardAdjunction g).comp
    (pullbackPushforwardAdjunction (g ⁻¹ᵁ U).ι)
  let a₂ := pullbackPushforwardAdjunction ((g ⁻¹ᵁ U).ι ≫ g)
  let a₃ := pullbackPushforwardAdjunction ((g ∣_ U) ≫ U.ι)
  let a₄ := (pullbackPushforwardAdjunction U.ι).comp
    (pullbackPushforwardAdjunction (g ∣_ U))
  let a₅ := (restrictAdjunction U.ι).comp (pullbackPushforwardAdjunction (g ∣_ U))
  change conjugateEquiv a₀ a₅ _ = _
  simp only [originalOpenPullbackIso, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc]
  rw [conjugate_five a₅ a₄ a₃ a₂ a₁ a₀]
  dsimp only [a₀, a₁, a₂, a₃, a₄, a₅]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_pullbackComp_inv,
    conjugate_pullbackCongr_inv, conjugate_pullbackComp_hom,
    conjugateEquiv_whiskerRight]
  simp [restrictFunctorIsoPullback, Adjunction.leftAdjointUniq, originalOpenPushforwardIso]

/-- Compatibility of the ORIGINAL composite adjunction units through THIS
actual canonical local iso, as an equality of ENTIRE module-sheaf morphisms. -/
theorem originalOpenPullbackIso_unit {X Y : Scheme.{u}} (g : Y ⟶ X)
    (U : X.Opens) (M : X.Modules) :
    (((pullbackPushforwardAdjunction g).comp
        (restrictAdjunction (g ⁻¹ᵁ U).ι)).unit.app M) ≫
      (originalOpenPushforwardIso g U).hom.app
        ((restrictFunctor (g ⁻¹ᵁ U).ι).obj ((pullback g).obj M)) ≫
      (pushforward (g ∣_ U) ⋙ pushforward U.ι).map
        ((originalOpenPullbackIso g U).hom.app M) =
      (((restrictAdjunction U.ι).comp
        (pullbackPushforwardAdjunction (g ∣_ U))).unit.app M) := by
  have h := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (restrictAdjunction (g ⁻¹ᵁ U).ι))
    ((restrictAdjunction U.ι).comp (pullbackPushforwardAdjunction (g ∣_ U)))
    (originalOpenPullbackIso g U).inv M
  rw [originalOpenPullbackIso_conjugate] at h
  calc
    _ = ((((restrictAdjunction U.ι).comp
        (pullbackPushforwardAdjunction (g ∣_ U))).unit.app M) ≫
      (pushforward (g ∣_ U) ⋙ pushforward U.ι).map
        ((originalOpenPullbackIso g U).inv.app M)) ≫
      (pushforward (g ∣_ U) ⋙ pushforward U.ι).map
        ((originalOpenPullbackIso g U).hom.app M) := by
      simpa only [Category.assoc, Functor.comp_obj] using congrArg
        (fun k => k ≫ (pushforward (g ∣_ U) ⋙ pushforward U.ι).map
          ((originalOpenPullbackIso g U).hom.app M)) h
    _ = _ := by simp [Category.assoc, ← Functor.map_comp]

/-- Actual sections of the original restricted sheaf are the SAME
original open sections, using only the native restriction section iso. -/
def originalOpenSectionsIso {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Γ(M.restrict U.ι, ⊤) ≅ Γ(M, U) :=
  M.restrictAppIso U.ι ⊤ ≪≫ (M.presheaf.mapIso (eqToIso U.ι_image_top).op).symm

private theorem modulePushforwardMap_app {X Y : Scheme.{u}} (g : Y ⟶ X)
    {M N : Y.Modules} (a : M ⟶ N) (U : X.Opens) :
    ((pushforward g).map a).app U = a.app (g ⁻¹ᵁ U) := rfl

private theorem originalOpenSectionsIso_inv_restrictUnit {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    (M.restrict U.ι).presheaf.map
        (homOfLE (show (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U from by simp)).op
          (((restrictAdjunction U.ι).unit.app M).app U s) =
      (originalOpenSectionsIso M U).inv s := by
  simp only [Scheme.Modules.restrict_map, restrictAdjunction_unit_app_app,
    originalOpenSectionsIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom,
    restrictAppIso, Iso.refl_inv]
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Category.comp_id]
  exact congrArg (fun k => M.presheaf.map k s) (Subsingleton.elim _ _)

/-- The canonical original local iso preserves EVERY original open section
under the SAME original adjunction-unit maps, not just globally extendible sections. -/
theorem originalOpenPullbackIso_unit_section {X Y : Scheme.{u}} (g : Y ⟶ X)
    (U : X.Opens) (M : X.Modules) (s : Γ(M, U)) :
    ((originalOpenPullbackIso g U).hom.app M).app ⊤
        ((originalOpenSectionsIso ((pullback g).obj M) (g ⁻¹ᵁ U)).inv
          (pullbackOpenRestrictMap g M U s)) =
      affinePullbackUnitTop (g ∣_ U) (M.restrict U.ι)
        ((originalOpenSectionsIso M U).inv s) := by
  rw [← pullbackTopRestrictMap_apply]
  have h := originalOpenPullbackIso_unit g U M
  have hv := congrArg
    (fun a : M ⟶ (pushforward (g ∣_ U) ⋙ pushforward U.ι).obj
        ((pullback (g ∣_ U)).obj (M.restrict U.ι)) =>
      a.app U s) h
  simp only [Adjunction.comp_unit_app, originalOpenPushforwardIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.comp_map, Functor.comp_obj,
    Scheme.Modules.Hom.comp_app, modulePushforwardMap_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app, restrictAdjunction_unit_app_app] at hv
  let W := g ⁻¹ᵁ U
  let N := (pullback g).obj M
  let A := N.restrict W.ι
  let B := (pullback (g ∣_ U)).obj (M.restrict U.ι)
  let V₀ := U.ι ⁻¹ᵁ U
  let V := (g ∣_ U) ⁻¹ᵁ V₀
  let T := W.ι ⁻¹ᵁ W
  let e : A ⟶ B := (originalOpenPullbackIso g U).hom.app M
  let x : Γ(A, T) := ((restrictAdjunction W.ι).unit.app N).app W
    (pullbackOpenRestrictMap g M U s)
  let y : Γ(M.restrict U.ι, V₀) := ((restrictAdjunction U.ι).unit.app M).app U s
  have hVT : V = T :=
    congrArg (fun k : W.toScheme ⟶ X => k ⁻¹ᵁ U) (morphismRestrict_ι g U)
  have hT : T = ⊤ := by dsimp [T, W]; simp
  have hU : V₀ = ⊤ := by dsimp [V₀]; simp
  have hV : V = ⊤ := hVT.trans hT
  let i : (⊤ : W.toScheme.Opens) ⟶ V := homOfLE hV.ge
  change e.app V (A.presheaf.map (eqToHom hVT).op x) =
    pullbackOpenRestrictMap (g ∣_ U) (M.restrict U.ι) V₀ y at hv
  have ht := congrArg (fun z : Γ(B, V) => B.presheaf.map i.op z) hv
  have he := PresheafOfModules.naturality_apply e.val i.op
    (A.presheaf.map (eqToHom hVT).op x)
  change e.app ⊤ (A.presheaf.map i.op (A.presheaf.map (eqToHom hVT).op x)) =
    B.presheaf.map i.op (e.app V (A.presheaf.map (eqToHom hVT).op x)) at he
  rw [← he] at ht
  have hc : A.presheaf.map i.op (A.presheaf.map (eqToHom hVT).op x) =
      A.presheaf.map (homOfLE hT.ge).op x := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact congrArg (fun k => A.presheaf.map k x) (Subsingleton.elim _ _)
  rw [hc] at ht
  have hu := (pullbackOpenRestrictMap_restrict (g ∣_ U) (M.restrict U.ι)
    (show (⊤ : U.toScheme.Opens) ≤ V₀ from hU.ge) y).symm
  change B.presheaf.map i.op (pullbackOpenRestrictMap (g ∣_ U) (M.restrict U.ι) V₀ y) =
    pullbackOpenRestrictMap (g ∣_ U) (M.restrict U.ι) ⊤
      ((M.restrict U.ι).presheaf.map (homOfLE hU.ge).op y) at hu
  rw [hu] at ht
  have hx : A.presheaf.map (homOfLE hT.ge).op x =
      (originalOpenSectionsIso N W).inv (pullbackOpenRestrictMap g M U s) :=
    originalOpenSectionsIso_inv_restrictUnit N W (pullbackOpenRestrictMap g M U s)
  have hy : (M.restrict U.ι).presheaf.map (homOfLE hU.ge).op y =
      (originalOpenSectionsIso M U).inv s :=
    originalOpenSectionsIso_inv_restrictUnit M U s
  rw [hx, hy] at ht
  exact ht

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
