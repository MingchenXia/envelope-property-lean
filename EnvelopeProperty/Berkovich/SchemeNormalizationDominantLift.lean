/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Algebra.InjectiveNormalizationExtension
import EnvelopeProperty.Berkovich.SchemeNormalStalks
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.IntegralSchemeNormalization
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

private theorem affine_app_injective (h : Y ⟶ X) [IsDominant h]
    (U : X.affineOpens) (V : Y.affineOpens) [hVne : Nonempty V.1]
    (hVU : V.1 ≤ h ⁻¹ᵁ U.1) : Function.Injective (h.appLE U.1 V.1 hVU) := by
  let : IsAffine U.1 := U.2
  let : IsAffine V.1 := V.2
  have hVset : (V.1 : Set Y).Nonempty := by
    rcases hVne with ⟨v⟩
    exact ⟨v.1, v.2⟩
  let : IsDominant V.1.ι := Opens.isDominant_ι (V.1.isOpen.dense hVset)
  let r := h.resLE U.1 V.1 hVU
  have : IsDominant (r ≫ U.1.ι) := by
    rw [show r ≫ U.1.ι = V.1.ι ≫ h from h.resLE_comp_ι hVU]
    infer_instance
  let : IsDominant r := IsDominant.of_comp_of_isOpenImmersion r U.1.ι
  let : IsSchemeTheoreticallyDominant r := IsSchemeTheoreticallyDominant.of_isDominant r
  have hr := r.app_injective (⊤ : U.1.toScheme.Opens)
  change Function.Injective ((h.resLE U.1 V.1 hVU).app ⊤) at hr
  rw [Scheme.Hom.resLE_app_top] at hr
  have hh : Function.Injective
      (U.1.topIso.inv ≫ (U.1.topIso.hom ≫ h.appLE U.1 V.1 hVU ≫ V.1.topIso.inv)) :=
    hr.comp (ConcreteCategory.bijective_of_isIso U.1.topIso.inv).injective
  have he : U.1.topIso.inv ≫
      (U.1.topIso.hom ≫ h.appLE U.1 V.1 hVU ≫ V.1.topIso.inv) =
      h.appLE U.1 V.1 hVU ≫ V.1.topIso.inv := by simp
  rw [he] at hh
  intro a b hab
  exact hh (congrArg V.1.topIso.inv hab)

private theorem local_lift_exists (h : Y ⟶ X) [IsDominant h]
    (hN : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : X.affineOpens) (V : Y.affineOpens) [Nonempty U.1] [Nonempty V.1]
    (hVU : V.1 ≤ h ⁻¹ᵁ U.1) :
    ∃ a : V.1.toScheme ⟶ normalization X, a ≫ projection X = V.1.ι ≫ h := by
  let : IsIntegrallyClosed Γ(Y, V.1) := affine_sections_isIntegrallyClosed Y hN V.1 V.2
  obtain ⟨ψ, hψ, _⟩ := existsUnique_integralClosure_extension
    (h.appLE U.1 V.1 hVU).hom (affine_app_injective h U V hVU)
  refine ⟨V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ) ≫ chartMap X U.1 U.2, ?_⟩
  rw [Category.assoc, Category.assoc, chartMap_comp_projection,
    ← Category.assoc (Spec.map _)]
  change V.2.isoSpec.hom ≫
    (Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U.1) (integralClosure Γ(X, U.1) (FractionRing Γ(X, U.1)))))) ≫
      U.2.fromSpec = _
  rw [← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap Γ(X, U.1)
      (integralClosure Γ(X, U.1) (FractionRing Γ(X, U.1)))) ≫
      CommRingCat.ofHom ψ = h.appLE U.1 V.1 hVU := by
    exact CommRingCat.hom_ext hψ
  rw [he, IsAffineOpen.SpecMap_appLE_fromSpec h U.2 V.2 hVU]
  simp only [IsAffineOpen.fromSpec, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

private theorem local_lift_unique (h : Y ⟶ X) [IsDominant h]
    (hN : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : X.affineOpens) (V : Y.affineOpens) [Nonempty U.1] [Nonempty V.1]
    (hVU : V.1 ≤ h ⁻¹ᵁ U.1)
    (a b : V.1.toScheme ⟶ normalization X)
    (ha : a ≫ projection X = V.1.ι ≫ h)
    (hb : b ≫ projection X = V.1.ι ≫ h) : a = b := by
  let : IsOpenImmersion (chartMap X U.1 U.2) := chartMap_isOpenImmersion X U.1 U.2
  have hr (a : V.1.toScheme ⟶ normalization X)
      (ha : a ≫ projection X = V.1.ι ≫ h) :
      Set.range a ⊆ Set.range (chartMap X U.1 U.2) := by
    rintro _ ⟨q, rfl⟩
    change a q ∈ (chartMap X U.1 U.2).opensRange
    rw [chartMap_opensRange]
    change projection X (a q) ∈ U.1
    have he := congrArg (fun g : V.1.toScheme ⟶ X => g q) ha
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at he
    rw [he]
    exact hVU q.2
  let c (a : V.1.toScheme ⟶ normalization X) (ha : a ≫ projection X = V.1.ι ≫ h) :=
    IsOpenImmersion.lift (chartMap X U.1 U.2) a (hr a ha)
  have hc (a : V.1.toScheme ⟶ normalization X) (ha : a ≫ projection X = V.1.ι ≫ h) :
      c a ha ≫ chartMap X U.1 U.2 = a := IsOpenImmersion.lift_fac _ _ _
  let χ (a : V.1.toScheme ⟶ normalization X) (ha : a ≫ projection X = V.1.ι ≫ h) :=
    (Spec.preimage (V.2.isoSpec.inv ≫ c a ha)).hom
  have hχ (a : V.1.toScheme ⟶ normalization X) (ha : a ≫ projection X = V.1.ι ≫ h) :
      (χ a ha).comp (algebraMap Γ(X, U.1)
        (integralClosure Γ(X, U.1) (FractionRing Γ(X, U.1)))) =
      (h.appLE U.1 V.1 hVU).hom := by
    apply CommRingCat.hom_ext_iff.mp
    apply Spec.map_injective
    apply (cancel_mono U.2.fromSpec).mp
    change Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1)
      (integralClosure Γ(X, U.1) (FractionRing Γ(X, U.1)))) ≫
      Spec.preimage (V.2.isoSpec.inv ≫ c a ha)) ≫ U.2.fromSpec = _
    rw [Spec.map_comp]
    rw [Spec.map_preimage, Category.assoc]
    change V.2.isoSpec.inv ≫ c a ha ≫
      (DomainNormalization.projection Γ(X, U.1) ≫ U.2.fromSpec) = _
    rw [← chartMap_comp_projection, ← Category.assoc (c a ha), hc a ha, ha,
      IsAffineOpen.SpecMap_appLE_fromSpec h U.2 V.2 hVU]
    simp only [IsAffineOpen.fromSpec, Category.assoc]
  let : IsIntegrallyClosed Γ(Y, V.1) := affine_sections_isIntegrallyClosed Y hN V.1 V.2
  obtain ⟨_, _, hu⟩ := existsUnique_integralClosure_extension
    (h.appLE U.1 V.1 hVU).hom (affine_app_injective h U V hVU)
  have he : χ a ha = χ b hb := (hu _ (hχ a ha)).trans (hu _ (hχ b hb)).symm
  have hec : c a ha = c b hb := by
    apply (cancel_epi V.2.isoSpec.inv).mp
    rw [← Spec.map_preimage (V.2.isoSpec.inv ≫ c a ha),
      ← Spec.map_preimage (V.2.isoSpec.inv ≫ c b hb)]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) he
  rw [← hc a ha, ← hc b hb, hec]

private theorem lift_unique (h : Y ⟶ X) [IsDominant h]
    (hN : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (a b : Y ⟶ normalization X) (ha : a ≫ projection X = h)
    (hb : b ≫ projection X = h) : a = b := by
  apply Scheme.hom_ext_of_forall
  intro y
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show h y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ h ⁻¹ᵁ U from hyU)
  let : Nonempty U := ⟨⟨h y, hyU⟩⟩
  let : Nonempty V := ⟨⟨y, hyV⟩⟩
  refine ⟨V, hyV, local_lift_unique h hN ⟨U, hU⟩ ⟨V, hV⟩ hVU
    (V.ι ≫ a) (V.ι ≫ b) ?_ ?_⟩
  · simpa only [Category.assoc] using congrArg (fun g => V.ι ≫ g) ha
  · simpa only [Category.assoc] using congrArg (fun g => V.ι ≫ g) hb

/-- Every actual dominant map from an integral scheme with normal original stalks
uniquely lifts to the SAME original generic-field normalization. -/
theorem existsUnique_dominant_normalization_lift (h : Y ⟶ X) [IsDominant h]
    (hN : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    ∃! a : Y ⟶ normalization X, a ≫ projection X = h := by
  classical
  have hp (y : Y) : ∃ (U : X.affineOpens) (V : Y.affineOpens),
      y ∈ V.1 ∧ V.1 ≤ h ⁻¹ᵁ U.1 := by
    obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
      (show h y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ h ⁻¹ᵁ U from hyU)
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hyV, hVU⟩
  choose U V hyV hVU using hp
  have hcover : TopologicalSpace.IsOpenCover (fun y => (V y).1) := by
    apply eq_top_iff.mpr
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyV y⟩
  let cov := Y.openCoverOfIsOpenCover (fun y => (V y).1) hcover
  have hlocal (y : Y) : ∃ a : cov.X y ⟶ normalization X,
      a ≫ projection X = cov.f y ≫ h := by
    let : Nonempty (V y).1 := ⟨⟨y, hyV y⟩⟩
    let : Nonempty (U y).1 := ⟨⟨h y, hVU y (hyV y)⟩⟩
    exact local_lift_exists h hN (U y) (V y) (hVU y)
  choose a ha using hlocal
  have hcompat (i j : Y) :
      pullback.fst (cov.f i) (cov.f j) ≫ a i = pullback.snd _ _ ≫ a j := by
    apply Scheme.hom_ext_of_forall
    intro q
    let T := pullback (cov.f i) (cov.f j)
    let e : T ⟶ Y := pullback.fst (cov.f i) (cov.f j) ≫ cov.f i
    let : Nonempty T := ⟨q⟩
    have : IsOpenImmersion e := by dsimp [e]; infer_instance
    let : IsIntegral T := isIntegral_of_isOpenImmersion e
    let : IsDominant e := ⟨by
      change Dense (Set.range e)
      exact e.opensRange.isOpen.dense ⟨e q, q, rfl⟩⟩
    have hNT (t : T) : IsIntegrallyClosed (T.presheaf.stalk t) := by
      let : IsIntegrallyClosed (Y.presheaf.stalk (e t)) := hN (e t)
      exact IsIntegrallyClosed.of_equiv (asIso (e.stalkMap t)).commRingCatIsoToRingEquiv
    have hleft : (pullback.fst (cov.f i) (cov.f j) ≫ a i) ≫ projection X = e ≫ h := by
      dsimp only [e]
      rw [Category.assoc, ha i, Category.assoc]
    have hright : (pullback.snd (cov.f i) (cov.f j) ≫ a j) ≫ projection X = e ≫ h := by
      rw [Category.assoc, ha j]
      exact (congrArg (fun g => g ≫ h) (pullback.condition (f := cov.f i) (g := cov.f j)).symm)
    have heq := lift_unique (e ≫ h) hNT
      (pullback.fst (cov.f i) (cov.f j) ≫ a i)
      (pullback.snd (cov.f i) (cov.f j) ≫ a j) hleft hright
    exact ⟨⊤, trivial, congrArg (fun g => (⊤ : T.Opens).ι ≫ g) heq⟩
  let F : Y ⟶ normalization X := cov.glueMorphisms a hcompat
  have hF : F ≫ projection X = h := by
    apply cov.hom_ext
    intro i
    dsimp only [F]
    rw [← Category.assoc, cov.ι_glueMorphisms, ha i]
  exact ⟨F, hF, fun b hb => lift_unique h hN b F hb hF⟩

end EnvelopeProperty.IntegralSchemeNormalization
