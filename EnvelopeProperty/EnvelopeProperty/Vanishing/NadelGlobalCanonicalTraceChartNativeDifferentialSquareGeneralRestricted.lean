import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceChartNativeDifferentialSquareWordRestriction

/-! # The original restricted differential square before chart specialization

Naturality of the fixed restriction--pullback comparison transports the
original native pullback square for arbitrary scheme arrows. Only the
source restriction map must be an open immersion.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart.NativeDifferentialSquareData
open AlgebraicGeometry CategoryTheory Scheme.Modules CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation:10 A " ⟶ₙ " B =>
  @Quiver.Hom _ (@CategoryStruct.toQuiver _ (@Category.toCategoryStruct _ inferInstance)) A B

/-- The fixed original native square after source restriction, for
arbitrary scheme arrows before their actual chart values are supplied. -/
theorem general_restricted_differential_square
    {k : Type u} [Field k] {X Y A B : Scheme.{u}}
    (f : X ⟶ₙ Spec (.of k)) (g : A ⟶ₙ X) (π : Y ⟶ₙ X)
    (p : B ⟶ₙ A) (v : B ⟶ₙ Y)
    [IsOpenImmersion v] (w : p ≫ g = v ≫ π) (n : ℕ) :
    nativeDifferentialType%(
  let hraw := fixed_pullback_differential_square f g π p v w n
  restriction_square_original_word_indices
    (pullback g) (pullback p) (pullback π) (pullback v)
    (restrictFunctorIsoPullback v) (exteriorCotangentSheaf f n)
    (exteriorCotangentSheafPullbackMap f π n)
    ((pullbackComp v π).hom.app (exteriorCotangentSheaf f n))
    ((pullbackCongr w).inv.app (exteriorCotangentSheaf f n))
    ((pullbackComp p g).inv.app (exteriorCotangentSheaf f n))
    ((pullback p).map (exteriorCotangentSheafPullbackMap f g n))
    (exteriorCotangentSheafPullbackMap (g ≫ f) p n)
    (exteriorCotangentSheafPullbackMap (π ≫ f) v n) _ hraw
    ) :=
  let hraw := fixed_pullback_differential_square f g π p v w n
  restriction_square_original_word_indices
    (pullback g) (pullback p) (pullback π) (pullback v)
    (restrictFunctorIsoPullback v) (exteriorCotangentSheaf f n)
    (exteriorCotangentSheafPullbackMap f π n)
    ((pullbackComp v π).hom.app (exteriorCotangentSheaf f n))
    ((pullbackCongr w).inv.app (exteriorCotangentSheaf f n))
    ((pullbackComp p g).inv.app (exteriorCotangentSheaf f n))
    ((pullback p).map (exteriorCotangentSheafPullbackMap f g n))
    (exteriorCotangentSheafPullbackMap (g ≫ f) p n)
    (exteriorCotangentSheafPullbackMap (π ≫ f) v n) _ hraw

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart.NativeDifferentialSquareData
