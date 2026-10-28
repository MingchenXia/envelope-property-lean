import EnvelopeProperty.Vanishing.NadelPrincipalizationOpenKernel

/-! # Whole original geometric pushed kernels through genuine section isomorphisms -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationSectionKernelIso
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem iso_section_zero_iff {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (W : X.Opens) (s : Γ(M, W)) : e.hom.app W s = 0 ↔ s = 0 := by
  constructor
  · intro hs
    have hi := ConcreteCategory.congr_hom
      (congrArg (fun φ => φ.app W) e.hom_inv_id) s
    change e.inv.app W (e.hom.app W s) = s at hi
    exact hi.symm.trans ((congrArg (e.inv.app W) hs).trans (map_zero _))
  · rintro rfl
    exact map_zero _

/-- A PROVED original whole section triangle through an actual original
module isomorphism identifies the ENTIRE original geometric pushed kernels.
Geometric consumers must construct the isomorphism and prove its triangle. -/
theorem kernel_eq {Y X : Scheme.{u}} (p : Y ⟶ X) [QuasiCompact p]
    (M N : Y.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] (e : M ≅ N)
    (δ : unitObj Y ⟶ M) (ε : unitObj Y ⟶ N) (hδ : δ ≫ e.hom = ε) :
    unitMapPushforwardKernelIdealSheaf p M
      ((pullbackPushforwardAdjunction p).homEquiv _ _ ((pullbackUnitIso p).hom ≫ δ)) =
    unitMapPushforwardKernelIdealSheaf p N
      ((pullbackPushforwardAdjunction p).homEquiv _ _ ((pullbackUnitIso p).hom ≫ ε)) := by
  let α := (pullbackPushforwardAdjunction p).homEquiv _ _ ((pullbackUnitIso p).hom ≫ δ)
  let β := (pullbackPushforwardAdjunction p).homEquiv _ _ ((pullbackUnitIso p).hom ≫ ε)
  have hα : α ≫ (pushforward p).map e.hom = β := by
    dsimp only [α, β]
    rw [pushforwardUnitSection_homEquiv, pushforwardUnitSection_homEquiv]
    rw [Category.assoc, ← (pushforward p).map_comp, hδ]
  apply Scheme.IdealSheafData.ext
  funext U
  ext a
  change α.app U.1 a = 0 ↔ β.app U.1 a = 0
  have hv := congrArg (fun φ => φ.app U.1 a) hα
  change ((pushforward p).map e.hom).app U.1 (α.app U.1 a) = β.app U.1 a at hv
  rw [← hv]
  exact (iso_section_zero_iff ((pushforward p).mapIso e) U.1 _).symm

end EnvelopeProperty.Vanishing.NadelPrincipalizationSectionKernelIso
