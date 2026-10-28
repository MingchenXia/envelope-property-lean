import EnvelopeProperty.Vanishing.NadelBertiniSelectedBaseChange
import EnvelopeProperty.AlgGeom.SchemeLineZeroIdealNativeFrameOrders

/-! # The entire original selected section and zero ideal in their actual frame -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniSncFlatFrame
open NadelBertiniFibreSection NadelBertiniFibreGeometry NadelBertiniSelectedBaseChange
  SchemeLineSectionEvaluation
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}}

/-- The SAME whole original selected section retains its exact original local
linear coefficient in the actual original pulled line frame. -/
theorem selected_frame_coefficient (p : X ⟶ Spec (.of k)) (a : Fin (m + 1) → k)
    (L : X.Modules) (s : Fin (m + 1) → Γ(L, ⊤)) (W : X.affineOpens)
    (e : (pullback W.1.ι).obj L ≅ unitObj W.1.toScheme) :
    (show Γ(W.1.toScheme, ⊤) from e.hom.app ⊤
      (affinePullbackUnitTop W.1.ι L (selectedSection p a L s))) =
    ∑ i, ProperBirationalSections.coefficientMap (W.1.ι ≫ p) (a i) *
      (show Γ(W.1.toScheme, ⊤) from e.hom.app ⊤ (affinePullbackUnitTop W.1.ι L (s i))) := by
  rw [selectedSection_pullback]
  change e.hom.app ⊤ (∑ i, ProperBirationalSections.coefficientMap (W.1.ι ≫ p) (a i) •
    affinePullbackUnitTop W.1.ι L (s i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Hom.app_smul e.hom _ _

/-- The whole ideal of the SAME actual original selected zero scheme is generated
by the SAME original selected chart coefficient, with the actual top restriction. -/
theorem selectedIdeal_ideal_of_frame (p : X ⟶ Spec (.of k)) (a : Fin (m + 1) → k)
    (L : X.Modules) (hL : IsInvertible L) (s : Fin (m + 1) → Γ(L, ⊤)) (W : X.affineOpens)
    (e : (pullback W.1.ι).obj L ≅ unitObj W.1.toScheme) :
    (selectedIdeal p a L hL s).ideal W = Ideal.span
      ({W.1.topIso.hom (∑ i, ProperBirationalSections.coefficientMap (W.1.ι ≫ p) (a i) *
        (show Γ(W.1.toScheme, ⊤) from e.hom.app ⊤
          (affinePullbackUnitTop W.1.ι L (s i))))} : Set Γ(X, W.1)) := by
  let α := SchemeModuleGlobalSections.sectionHom L (selectedSection p a L s)
  have h := SchemeLineZeroIdealNativeFrameOrders.zeroIdeal_ideal_of_pullback_frame L hL α W e
  have hc : (show Γ(W.1.toScheme, ⊤) from sectionAtOne
      (pullbackSectionHom W.1.ι α ≫ e.hom)) =
      (show Γ(W.1.toScheme, ⊤) from e.hom.app ⊤
        (affinePullbackUnitTop W.1.ι L (selectedSection p a L s))) := by
    change e.hom.app ⊤ (sectionAtOne (pullbackSectionHom W.1.ι
      (topSectionHom L (selectedSection p a L s)))) = _
    exact congrArg (e.hom.app ⊤)
      (Berkovich.SchemeFramedSectionPullback.affinePullbackUnitTop_eq_sectionAtOne
        W.1.ι L (selectedSection p a L s)).symm
  exact h.trans (congrArg (fun r : Γ(W.1.toScheme, ⊤) =>
    Ideal.span ({W.1.topIso.hom r} : Set Γ(X, W.1)))
    (hc.trans (selected_frame_coefficient p a L s W e)))

end EnvelopeProperty.Vanishing.NadelBertiniSncFlatFrame
