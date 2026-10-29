import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineNaturality
import EnvelopeProperty.AlgGeom.Canonical.ModuleSpecGammaCarrier
import EnvelopeProperty.AlgGeom.SpecPushforwardTilde

/-! # Generic raw readbacks of the original native affine Gamma maps -/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules
universe u

/-- Restriction of scalars retains the same original module element. -/
def restrictedNativeSection {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (M : ModuleCat B)
    (s : (ModuleCat.restrictScalars φ).obj M) : M := s

run_cmd
  for (short, original) in [
      (`originalRawAffineGammaTransportEq,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.affineCanonicalΓTransport_eq),
      (`originalRawAffineGammaTransport,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.affineCanonicalΓTransport)] do
    let name := Lean.mkPrivateNameCore
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineNaturality original
    unless (← Lean.getEnv).contains name do
      throwError "missing original affine transport helper {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

/-- The same native affine Gamma map reads as its actual original top component. -/
theorem moduleSpecGamma_map_toRaw (A : CommRingCat.{u}) (M N : (Spec A).Modules)
    (f : M ⟶ N) (s : (moduleSpecΓFunctor (R := A)).obj M) :
    ModuleSpecGammaCarrier.toRaw A N ((moduleSpecΓFunctor (R := A)).map f s) =
      f.app ⊤ (ModuleSpecGammaCarrier.toRaw A M s) := rfl

/-- Original-ring scalar multiplication reads as its original section coefficient. -/
theorem moduleSpecGamma_smul_toRaw (A : CommRingCat.{u}) (M : (Spec A).Modules)
    (a : A) (s : (moduleSpecΓFunctor (R := A)).obj M) :
    ModuleSpecGammaCarrier.toRaw A M (a • s) =
      (· • · : Γ(Spec A, ⊤) → Γ(M, ⊤) → Γ(M, ⊤))
        ((Scheme.ΓSpecIso A).inv a)
        (show Γ(M, ⊤) from ModuleSpecGammaCarrier.toRaw A M s) := rfl

/-- The actual affine pushforward retains the same raw top section. -/
def affinePushforwardRawSection {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (N : (Spec B).Modules) (s : Γ(N, ⊤)) :
    Γ((pushforward (Spec.map φ)).obj N, ⊤) := s

/-- The original pushforward morphism retains its original raw component. -/
theorem affinePushforwardRawSection_map {A B : CommRingCat.{u}} (φ : A ⟶ B)
    {M N : (Spec B).Modules} (f : M ⟶ N) (s : Γ(M, ⊤)) :
    ((pushforward (Spec.map φ)).map f).app ⊤ (affinePushforwardRawSection φ M s) =
      affinePushforwardRawSection φ N (f.app ⊤ s) := rfl

/-- The native pushforward comparison reads the same original raw section. -/
theorem specPushforwardSectionsIso_hom_raw {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (N : (Spec B).Modules) (s : (moduleSpecΓFunctor (R := B)).obj N) :
    (SpecPushforwardTilde.sectionsIso φ N).hom
      (ModuleSpecGammaCarrier.toNative A ((pushforward (Spec.map φ)).obj N)
        (affinePushforwardRawSection φ N (ModuleSpecGammaCarrier.toRaw B N s))) = s := by
  exact SpecPushforwardTilde.sectionsIso_hom_apply φ N
    (ModuleSpecGammaCarrier.toNative A ((pushforward (Spec.map φ)).obj N)
      (affinePushforwardRawSection φ N (ModuleSpecGammaCarrier.toRaw B N s)))

/-- The actual affine pullback top section is the original adjunction unit. -/
theorem affinePullbackUnitTop_eq_unit {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (L : (Spec A).Modules) (w : Γ(L, ⊤)) :
    affinePullbackUnitTop (Spec.map φ) L w =
      ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app L).app ⊤ w := by
  change ((pullback (Spec.map φ)).obj L).presheaf.map (𝟙 (.op ⊤)) _ = _
  exact congr($(((pullback (Spec.map φ)).obj L).presheaf.map_id (.op ⊤)).hom
    (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app L).app ⊤ w))

/-- The original field transport has its actual raw equality-transport value. -/
theorem affineCanonicalGammaTransport_toRaw {K : Type u} [Field K]
    (B : CommRingCat.{u}) {f₁ f₂ : Spec B ⟶ Spec (.of K)} (h : f₁ = f₂) (n : ℕ)
    (s : (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f₁ n)) :
    ModuleSpecGammaCarrier.toRaw B (exteriorCotangentSheaf f₂ n)
        (originalRawAffineGammaTransport B h n s) =
      (eqToHom (congrArg (fun f => exteriorCotangentSheaf f n) h)).app ⊤
        (ModuleSpecGammaCarrier.toRaw B (exteriorCotangentSheaf f₁ n) s) := by
  rw [originalRawAffineGammaTransportEq]
  cases h
  rfl

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
