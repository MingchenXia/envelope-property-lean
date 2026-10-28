import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationGamma

/-! # Explicit raw readback of the original affine pushforward and unit -/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules Opposite
universe u

/-- Read an actual top pushforward section in its same original source carrier. -/
def affinePushforwardRawRead {A B : CommRingCat.{u}} (φ : CommRingCat.Hom A B)
    (M : (Spec B).Modules) (s : ((pushforward (Spec.map φ)).obj M).val.obj (op ⊤)) : M.val.obj (op ⊤) := s

theorem affinePushforwardRawRead_section {A B : CommRingCat.{u}} (φ : CommRingCat.Hom A B)
    (M : (Spec B).Modules) (s : M.val.obj (op ⊤)) :
    affinePushforwardRawRead φ M (affinePushforwardRawSection φ M s) = s := rfl

theorem affinePushforwardRawSection_read {A B : CommRingCat.{u}} (φ : CommRingCat.Hom A B)
    (M : (Spec B).Modules) (s : ((pushforward (Spec.map φ)).obj M).val.obj (op ⊤)) :
    affinePushforwardRawSection φ M (affinePushforwardRawRead φ M s) = s := rfl

/-- The actual pushforward morphism reads as its original source top component. -/
theorem affinePushforwardRawRead_map {A B : CommRingCat.{u}} (φ : CommRingCat.Hom A B)
    {M N : (Spec B).Modules} (f : M ⟶ N)
    (s : ((pushforward (Spec.map φ)).obj M).val.obj (op ⊤)) :
    affinePushforwardRawRead φ N (((pushforward (Spec.map φ)).map f).app ⊤ s) =
      f.app ⊤ (affinePushforwardRawRead φ M s) := rfl

/-- The original affine unit read in the original source carrier. -/
theorem affinePullbackUnitTop_eq_read_unit {A B : CommRingCat.{u}} (φ : CommRingCat.Hom A B)
    (L : (Spec A).Modules) (w : Γ(L, ⊤)) :
    affinePullbackUnitTop (Spec.map φ) L w =
      affinePushforwardRawRead φ ((pullback (Spec.map φ)).obj L)
        (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app L).app ⊤ w) := by
  exact affinePullbackUnitTop_eq_unit φ L w

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
