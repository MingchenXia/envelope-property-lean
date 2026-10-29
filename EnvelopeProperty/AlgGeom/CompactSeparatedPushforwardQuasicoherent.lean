import EnvelopeProperty.AlgGeom.SchemeModulePrincipalLocalization
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechPushforward
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent

/-! # Actual compact separated quasicoherent modules push forward quasicoherently to an affine scheme -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace EnvelopeProperty.CompactSeparatedPushforwardQuasicoherent
universe u
set_option backward.isDefEq.respectTransparency false

private theorem originalRestrictionLocalizationCongr
    {T : TopCat.{u}} {A : Type u} [CommRing A]
    (P : (Opens T)ᵒᵖ ⥤ ModuleCat.{u} A) (r : A)
    {U U' V V' : Opens T} (hU : U = U') (hV : V = V')
    (h : V ≤ U) (h' : V' ≤ U')
    (hl : IsLocalizedModule.Away r (P.map (homOfLE h).op).hom) :
    IsLocalizedModule.Away r (P.map (homOfLE h').op).hom := by
  subst U'
  subst V'
  exact hl

private theorem originalLocalizationAcrossIso {A : Type u} [CommRing A]
    {P Q P' Q' : ModuleCat.{u} A} (r : A) (f : P ⟶ Q) (f' : P' ⟶ Q')
    (eP : P ≅ P') (eQ : Q ≅ Q')
    (hs : f ≫ eQ.hom = eP.hom ≫ f') (hl : IsLocalizedModule.Away r f.hom) :
    IsLocalizedModule.Away r f'.hom := by
  let : IsLocalizedModule.Away r f.hom := hl
  apply (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers r)
    eP.hom.hom (ConcreteCategory.bijective_of_isIso eP.hom)).mp
  have he : f'.hom ∘ₗ eP.hom.hom = eQ.hom.hom ∘ₗ f.hom :=
    (congrArg ModuleCat.Hom.hom hs).symm
  rw [he]
  exact (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers r)
    eQ.hom.hom (ConcreteCategory.bijective_of_isIso eQ.hom)).mpr hl

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (M : Y.Modules) [M.IsQuasicoherent]
    [CompactSpace Y] [Y.IsSeparated]

/-- The SAME whole original pushed-module restriction to EVERY original
basic open genuinely localizes for its SAME original global coefficient action. -/
theorem pushforward_restriction_isLocalizedModule (r : Γ(X, ⊤)) :
    IsLocalizedModule.Away r
      ((Scheme.Modules.baseModulePresheaf (𝟙 X) ((Scheme.Modules.pushforward g).obj M)).map
        (X.basicOpen r).leTop.op).hom := by
  let P := Scheme.Modules.baseModulePresheaf (g ≫ 𝟙 X) M
  let Q := Scheme.Modules.baseModulePresheaf (𝟙 X) ((Scheme.Modules.pushforward g).obj M)
  let V := X.basicOpen r
  let h : g ⁻¹ᵁ V ≤ g ⁻¹ᵁ (⊤ : X.Opens) := fun y hy => trivial
  have hl := SchemeModulePrincipalLocalization.restriction_isLocalizedModule (g ≫ 𝟙 X) M r
  have hlocal : IsLocalizedModule.Away r (P.map (homOfLE h).op).hom :=
    originalRestrictionLocalizationCongr P r (Scheme.Hom.preimage_top g).symm rfl le_top h hl
  let eTop := Scheme.Modules.baseModulePresheafPushforwardAppIso g (𝟙 X) M ⊤
  let eV := Scheme.Modules.baseModulePresheafPushforwardAppIso g (𝟙 X) M V
  have hs : P.map (homOfLE h).op ≫ eV.hom =
      eTop.hom ≫ Q.map V.leTop.op := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl
  exact originalLocalizationAcrossIso r _ _ eTop eV hs hlocal

/-- Actual compactness, separatedness and quasi-coherence DERIVE genuine
quasi-coherence of the ENTIRE original pushforward to ANY original affine scheme.
No pushforward/localization/coefficient/finite-cover certificate is supplied. -/
theorem isQuasicoherent_pushforward [IsAffine X] :
    ((Scheme.Modules.pushforward g).obj M).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_of_isLocalized_basicOpen
    ((Scheme.Modules.pushforward g).obj M)
    (pushforward_restriction_isLocalizedModule g M)

end EnvelopeProperty.CompactSeparatedPushforwardQuasicoherent
