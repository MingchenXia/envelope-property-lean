import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationGamma
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationRawModuleMap

/-!
# Section presentations of the affine pullback unit

For a scheme `X` and an `𝒪_X`-module `N`, a global section of `N` can be presented either
as an element of the abelian group `Γ(N, ⊤)` or as an element of the module
`N.val.obj (op ⊤)` over `Γ(X, ⊤)`; the two carriers are the same.  For a ring
homomorphism `φ : A ⟶ B` and an `𝒪_{Spec A}`-module `M`, the top section of `β^* M`
(`β = Spec φ`) obtained from the pullback-pushforward adjunction unit is
`affinePullbackUnitTop β M m`.

This file records the identity bridges between these presentations, and the fact that a
morphism `D : β^* M ⟶ N` evaluated on the pulled-back section `β^* m` is the raw top
component of `D` applied to the raw unit section.  These are the bookkeeping steps used when
the affine canonical trace of a finite free cover is normalized on the generators
`r • β^* m` of `Γ(Spec B, β^* M)` (Esnault–Viehweg, *Lectures on vanishing theorems*, §3,
the trace of a finite cyclic cover).

## Main declarations

* `affineRawSection`, `affineSectionOfRaw`: the two identity bridges between the carriers.
* `affineRawPullbackUnit`: the unit section `β^* m` in the raw carrier.
* `affineRawUnit_map_toSection`: evaluation of `D : β^* M ⟶ N` on `β^* m`.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules Opposite
universe u
set_option autoImplicit false

/-- A top section of `N`, presented in the raw top-section module `N.val.obj (op ⊤)`. -/
def affineRawSection {X : Scheme.{u}} (N : X.Modules) (s : Γ(N, ⊤)) : N.val.obj (op ⊤) := s

/-- A raw top section of `N`, presented as an element of `Γ(N, ⊤)`. -/
def affineSectionOfRaw {X : Scheme.{u}} (N : X.Modules) (s : N.val.obj (op ⊤)) : Γ(N, ⊤) := s

/-- Presenting a section in the raw carrier and back does not change it. -/
theorem affineSectionOfRaw_rawSection {X : Scheme.{u}} (N : X.Modules) (s : Γ(N, ⊤)) :
    affineSectionOfRaw N (affineRawSection N s) = s := rfl

/-- Presenting a raw section as a section and back does not change it. -/
theorem affineRawSection_sectionOfRaw {X : Scheme.{u}} (N : X.Modules)
    (s : N.val.obj (op ⊤)) :
    affineRawSection N (affineSectionOfRaw N s) = s := rfl

/-- The pulled-back top section `β^* m` of `β^* M`, for `β = Spec φ`, in the raw carrier. -/
def affineRawPullbackUnit {A B : CommRingCat.{u}} (φ : A ⟶ B) (M : (Spec A).Modules)
    (m : M.val.obj (op ⊤)) : ((Scheme.Modules.pullback (Spec.map φ)).obj M).val.obj (op ⊤) :=
  affinePullbackUnitTop (Spec.map φ) M m

/-- The raw pulled-back section is the value of the adjunction unit `M ⟶ β_* β^* M`. -/
theorem affineRawPullbackUnit_eq_unit {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (M : (Spec A).Modules) (m : Γ(M, ⊤)) :
    affineRawPullbackUnit φ M m =
      affineRawSection ((Scheme.Modules.pullback (Spec.map φ)).obj M)
        (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m) :=
  affinePullbackUnitTop_eq_unit φ M m

/-- A morphism `D : β^* M ⟶ N` evaluated on the pulled-back section `β^* m` is the raw top
component of `D` applied to the raw unit section. -/
theorem affineRawUnit_map_toSection {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (M : (Spec A).Modules) (N : (Spec B).Modules)
    (D : (Scheme.Modules.pullback (Spec.map φ)).obj M ⟶ N) (m : M.val.obj (op ⊤)) :
    D.app ⊤ (affinePullbackUnitTop (Spec.map φ) M m) =
      affineSectionOfRaw N (affineRawModuleMap D (affineRawPullbackUnit φ M m)) := rfl

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
