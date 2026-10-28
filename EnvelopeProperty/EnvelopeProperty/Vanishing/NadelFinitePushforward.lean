import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite type of the whole original finite pushforward

No source integrality, connectedness or chosen-component hypothesis is used.
-/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelFinitePushforward

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual sections of a finite pushforward are finite over the same original
affine base ring, by transitivity of module finiteness. -/
theorem sections_finite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (U : Y.affineOpens) :
    Module.Finite Γ(Y, U.1) Γ((pushforward f).obj M, U.1) := by
  let V : X.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  let : Module.Finite Γ(X, V.1) Γ(M, V.1) :=
    sections_module_finite_of_isFiniteType_of_isAffineOpen M V
  let : Algebra Γ(Y, U.1) Γ(X, V.1) := (f.app U.1).hom.toAlgebra
  let : Module.Finite Γ(Y, U.1) Γ(X, V.1) := f.finite_app U.1 U.2
  let : Module Γ(Y, U.1) Γ(M, V.1) :=
    Module.compHom Γ(M, V.1) (f.app U.1).hom
  let : IsScalarTower Γ(Y, U.1) Γ(X, V.1) Γ(M, V.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  change Module.Finite Γ(Y, U.1) Γ(M, V.1)
  exact Module.Finite.trans Γ(X, V.1) Γ(M, V.1)

/-- The whole original pushforward along any finite scheme morphism preserves
finite-type quasicoherent modules. -/
theorem isFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((pushforward f).obj M).IsFiniteType := by
  let N := (pushforward f).obj M
  let : N.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom f
  exact isFiniteType_of_sections_module_finite N (sections_finite f M)

end EnvelopeProperty.Vanishing.NadelFinitePushforward
