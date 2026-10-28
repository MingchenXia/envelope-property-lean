import EnvelopeProperty.AlgGeom.AffineModuleFlatBaseChange

/-! # Entire original global-section equivalences from actual scheme/module isomorphisms -/
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleIsoGlobalSections

variable {X Y : Scheme.{u}}

private def moduleIsoApp {M N : X.Modules} (α : M ≅ N) (U : X.Opens) :
    M.val.obj (op U) ≅ N.val.obj (op U) where
  hom := α.hom.val.app (op U)
  inv := α.inv.val.app (op U)
  hom_inv_id := congrArg (fun f : M ⟶ M => f.val.app (op U)) α.hom_inv_id
  inv_hom_id := congrArg (fun f : N ⟶ N => f.val.app (op U)) α.inv_hom_id

/-- The ACTUAL original module isomorphism acts on the ENTIRE original global module. -/
def moduleIsoTopEquiv {M N : X.Modules} (α : M ≅ N) :
    Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(N, ⊤) :=
  (moduleIsoApp α ⊤).toLinearEquiv

@[simp] theorem moduleIsoTopEquiv_apply {M N : X.Modules} (α : M ≅ N) (s : Γ(M, ⊤)) :
    moduleIsoTopEquiv α s = α.hom.app ⊤ s := rfl

/-- The SAME entire original module comparison retains the actual original base action. -/
def moduleIsoTopOverBase {R : Type u} [CommRing R] (p : X ⟶ Spec (.of R))
    {M N : X.Modules} (α : M ≅ N) :
    AffineModuleFlatBaseChange.sections p M ≃ₗ[R] AffineModuleFlatBaseChange.sections p N :=
  ((ModuleCat.restrictScalars (ProperBirationalSections.coefficientMap p)).mapIso
    (moduleIsoApp α ⊤)).toLinearEquiv

@[simp] theorem moduleIsoTopOverBase_apply {R : Type u} [CommRing R]
    (p : X ⟶ Spec (.of R)) {M N : X.Modules} (α : M ≅ N) (s : Γ(M, ⊤)) :
    moduleIsoTopOverBase p α s = α.hom.app ⊤ s := rfl

/-- The ACTUAL whole pullback unit is bijective for a genuinely given original
scheme isomorphism; no global-section lifting or matching certificate is supplied. -/
theorem pullbackUnitTop_bijective (e : Y ≅ X) (M : X.Modules) :
    Function.Bijective (affinePullbackUnitTop e.hom M) := by
  let : (pullback e.hom).IsEquivalence := pullback_isEquivalence_of_iso e
  let : (pushforward e.hom).IsEquivalence :=
    (pullbackPushforwardAdjunction e.hom).isEquivalence_right_of_isEquivalence_left
  let : IsIso (pullbackPushforwardAdjunction e.hom).unit := by infer_instance
  let u := (pullbackPushforwardAdjunction e.hom).unit.app M
  have : IsIso u := by dsimp only [u]; infer_instance
  have hu : Function.Bijective (u.app ⊤) :=
    (ConcreteCategory.isIso_iff_bijective (u.app ⊤)).mp inferInstance
  have he : affinePullbackUnitTop e.hom M = (u.app ⊤) := by
    funext m
    let N := (pullback e.hom).obj M
    let a : Γ(N, ⊤) := u.app ⊤ m
    change N.presheaf.map (𝟙 (op (⊤ : Y.Opens))) a = a
    exact ConcreteCategory.congr_hom (N.presheaf.map_id (op ⊤)) a
  rw [he]
  exact hu

/-- The entire original global-section equivalence uses the actual original unit map. -/
def pullbackUnitTopEquiv (e : Y ≅ X) (M : X.Modules) :
    Γ(M, ⊤) ≃ Γ((pullback e.hom).obj M, ⊤) :=
  Equiv.ofBijective (affinePullbackUnitTop e.hom M) (pullbackUnitTop_bijective e M)

@[simp] theorem pullbackUnitTopEquiv_apply (e : Y ≅ X) (M : X.Modules) (s : Γ(M, ⊤)) :
    pullbackUnitTopEquiv e M s = affinePullbackUnitTop e.hom M s := rfl

/-- Genuinely given original scheme and module isomorphisms derive the ENTIRE
global-section correspondence, not only chosen finite section families. -/
def schemeModuleIsoTopEquiv (e : Y ≅ X) (M : X.Modules) {N : Y.Modules}
    (α : (pullback e.hom).obj M ≅ N) : Γ(M, ⊤) ≃ Γ(N, ⊤) :=
  (pullbackUnitTopEquiv e M).trans (moduleIsoTopEquiv α).toEquiv

@[simp] theorem schemeModuleIsoTopEquiv_apply (e : Y ≅ X) (M : X.Modules) {N : Y.Modules}
    (α : (pullback e.hom).obj M ≅ N) (s : Γ(M, ⊤)) :
    schemeModuleIsoTopEquiv e M α s = α.hom.app ⊤ (affinePullbackUnitTop e.hom M s) := rfl

end EnvelopeProperty.SchemeModuleIsoGlobalSections
