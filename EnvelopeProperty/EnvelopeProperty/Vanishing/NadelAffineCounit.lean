import EnvelopeProperty.Vanishing.NadelAffineCounitDetection

/-! # The whole original affine adjunction counit is epic on coherent modules -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelAffineCounit

/-- The actual original affine pullback-pushforward counit is an epimorphism
on every finite-type quasicoherent source module.  The triangle identity and
proved whole-map detection supply the result internally. -/
theorem counit_epi {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Epi ((pullbackPushforwardAdjunction f).counit.app M) := by
  constructor
  intro N a b hab
  apply NadelAffineCounitDetection.hom_ext (M := M) f
  have h := congrArg
    ((pullbackPushforwardAdjunction f).homEquiv ((pushforward f).obj M) N) hab
  simpa only [Adjunction.homEquiv_apply, Functor.map_comp, ← Category.assoc,
    Adjunction.right_triangle_components, Category.id_comp] using h

end EnvelopeProperty.Vanishing.NadelAffineCounit
