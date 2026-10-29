import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceCandidate
import EnvelopeProperty.AlgGeom.SpecPushforwardTilde
import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverStructuralUnit
import EnvelopeProperty.AlgGeom.Canonical.NativeInvertibility

/-! # The SAME original mixed candidate is an actual regular sheaf morphism

The original A-linear mixed candidate is lifted through the existing
affine quasicoherent equivalence. Its source is the actual whole native
pushforward of the original mixed canonical sheaf. The native affine
pushforward section comparison and the original mixed map are kept.
This constructor does not assert differential normalization or that this
regular candidate is a factor of the original rational canonical trace.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules
open NadelCanonicalMixed
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Exact existing affine-QC lift and its checked native section readback.
-- Only elaborator scope is extended; no environment declaration is added.
run_cmd
  for (short, original) in [
      (`frozenAffineLift,
        `EnvelopeProperty.CyclicSectionGlobalCoverStructuralUnit.affineLift),
      (`frozenAffineLiftSections,
        `EnvelopeProperty.CyclicSectionGlobalCoverStructuralUnit.affineLift_sections)] do
    let name := Lean.mkPrivateNameCore
      `EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverStructuralUnit original
    unless (← Lean.getEnv).contains name do
      throwError "missing existing native affine-QC lift helper {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

variable {k A : Type u} [Field k] [CharZero k] [CommRing A] [Algebra k A] [Nontrivial A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

local notation "Bₘ" => mixedRing x N I σ u
local notation "β" => Spec.map (CommRingCat.ofHom (algebraMap A Bₘ))
local notation "ωA" => exteriorCotangentSheaf (affineStructuralMap k (CommRingCat.of A)) n
local notation "ωB" => exteriorCotangentSheaf (mixedStructure (k := k) x N I σ u) n

/-- The SAME original mixed A-linear candidate lifts to a regular
morphism on the SAME entire native affine canonical pushforward.
Smoothness and quasicoherence are produced internally from the original
etale coordinates and positive tame degrees. -/
def mixedCanonicalSheafCandidate
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    (pushforward β).obj ωB ⟶ ωA := by
  let : SmoothOfRelativeDimension n (affineStructuralMap k (.of A)) :=
    coordinateStructure_smooth x hx
  let : SmoothOfRelativeDimension n (mixedStructure (k := k) x N I σ u) :=
    mixedStructure_smooth x N I σ u hx hN htame
  let : (ωA).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible (affineStructuralMap k (.of A)) n).isQuasicoherent
  let : (ωB).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible (mixedStructure (k := k) x N I σ u) n).isQuasicoherent
  let : ((pushforward β).obj ωB).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom β
  exact frozenAffineLift (.of A) _ _
    ((SpecPushforwardTilde.sectionsIso
      (CommRingCat.ofHom (algebraMap A Bₘ)) ωB).hom ≫
      mixedCanonicalCandidate x N I σ u hx hN htame)

/-- The ENTIRE affine-section map of the SAME regular mixed sheaf
candidate is the existing original mixed candidate after the existing
native pushforward section comparison. No value or matching equation
is supplied by the caller. -/
theorem mixedCanonicalSheafCandidate_sections
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    (moduleSpecΓFunctor (R := .of A)).map
        (mixedCanonicalSheafCandidate x N I σ u hx hN htame) =
      (SpecPushforwardTilde.sectionsIso
        (CommRingCat.ofHom (algebraMap A Bₘ)) ωB).hom ≫
        mixedCanonicalCandidate x N I σ u hx hN htame := by
  let : SmoothOfRelativeDimension n (affineStructuralMap k (.of A)) :=
    coordinateStructure_smooth x hx
  let : SmoothOfRelativeDimension n (mixedStructure (k := k) x N I σ u) :=
    mixedStructure_smooth x N I σ u hx hN htame
  let : (ωA).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible (affineStructuralMap k (.of A)) n).isQuasicoherent
  let : (ωB).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible (mixedStructure (k := k) x N I σ u) n).isQuasicoherent
  let : ((pushforward β).obj ωB).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom β
  exact frozenAffineLiftSections (.of A) _ _
    ((SpecPushforwardTilde.sectionsIso
      (CommRingCat.ofHom (algebraMap A Bₘ)) ωB).hom ≫
      mixedCanonicalCandidate x N I σ u hx hN htame)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
