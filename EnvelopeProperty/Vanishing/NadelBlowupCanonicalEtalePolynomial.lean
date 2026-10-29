import EnvelopeProperty.Vanishing.NadelBlowupCanonicalGluingWhole
import EnvelopeProperty.AlgGeom.Canonical.AffineFormallyEtaleDifferential

/-! # The actual whole etale canonical differential over original polynomial space -/

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalEtalePolynomial
open CoordinateSubspace CanonicalGeometry NadelBlowupCanonicalGluingDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual open target restriction detects the original pulled whole
canonical differential from its actual composite differential. -/
theorem pullback_differential_isIso_of_open_composite
    {k : Type u} [Field k] {X Y V : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (q : V ⟶ Y) [IsOpenImmersion q]
    (n : ℕ) (hc : IsIso (exteriorCotangentSheafPullbackMap f (q ≫ g) n)) :
    IsIso ((pullback q).map (exteriorCotangentSheafPullbackMap f g n)) := by
  let a := (pullback q).map (exteriorCotangentSheafPullbackMap f g n)
  let b := exteriorCotangentSheafPullbackMap (g ≫ f) q n ≫
    eqToHom (congrArg (fun z => exteriorCotangentSheaf z n) (Category.assoc q g f).symm)
  let := hc
  let : IsIso (exteriorCotangentSheafPullbackMap (g ≫ f) q n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion (g ≫ f) q n
  have he : (pullbackComp q g).inv.app (exteriorCotangentSheaf f n) ≫ (a ≫ b) =
      exteriorCotangentSheafPullbackMap f (q ≫ g) n := by
    simpa only [a, b, Category.assoc] using
      (exteriorCotangentSheafPullbackMap_comp f g q n).symm
  let : IsIso (a ≫ b) := IsIso.of_isIso_fac_left he
  exact IsIso.of_isIso_comp_right a b

variable (k : Type u) [Field k] (n : ℕ)

/-- Genuine etaleness and the internally produced original polynomial
coordinate basis derive the ENTIRE actual affine canonical differential iso. -/
theorem affine_polynomial_etale_isIso {Y : Scheme.{u}} [IsAffine Y]
    (g : Y ⟶ Spec (.of (MvPolynomial (Fin n) k))) [Etale g] :
    IsIso (exteriorCotangentSheafPullbackMap
      (affineStructuralMap k (.of (MvPolynomial (Fin n) k))) g n) := by
  let f := affineStructuralMap k (.of (MvPolynomial (Fin n) k))
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_Spec_map_algebraMap_mvPolynomial k n
  have he : g.appTop.hom.Etale := HasRingHomProperty.appTop (@Etale) g inferInstance
  let : Algebra Γ(Spec (.of (MvPolynomial (Fin n) k)), ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra.Etale Γ(Spec (.of (MvPolynomial (Fin n) k)), ⊤) Γ(Y, ⊤) := he
  exact exteriorCotangentSheafPullbackMap_isIso_of_formallyEtale f g n
    (affineGammaSpecEtaleBasis k (.of (MvPolynomial (Fin n) k)) X
      (NadelBlowupCanonicalSheafCoordinates.coordinates_etale k n)) (by
        change Algebra.FormallyEtale Γ(Spec (.of (MvPolynomial (Fin n) k)), ⊤) Γ(Y, ⊤)
        infer_instance)

/-- For an arbitrary original etale source, the SAME original whole
native polynomial-space canonical differential is an actual isomorphism.
The actual native affine point-cover and all bases are internally produced. -/
theorem polynomial_etale_isIso {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of (MvPolynomial (Fin n) k))) [Etale g] :
    IsIso (exteriorCotangentSheafPullbackMap
      (affineStructuralMap k (.of (MvPolynomial (Fin n) k))) g n) := by
  apply isIso_of_open_cover Y.affineCover.X Y.affineCover.f Y.affineCover.exists_eq
  intro i
  apply pullback_differential_isIso_of_open_composite
  exact affine_polynomial_etale_isIso k n (Y.affineCover.f i ≫ g)

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalEtalePolynomial
