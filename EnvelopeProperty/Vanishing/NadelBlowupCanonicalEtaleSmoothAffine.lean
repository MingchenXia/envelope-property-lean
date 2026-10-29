import EnvelopeProperty.Vanishing.NadelBlowupCanonicalEtaleModel

/-! # Whole native etale canonical differentials over actual standard-smooth charts -/

open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalEtaleSmoothAffine
open CanonicalGeometry CoordinateSubspace NadelBlowupCanonicalGluingDescent
open NadelBlowupCanonicalEtalePolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (A : CommRingCat.{u}) [Algebra k A]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n k A]

theorem structural_smooth : SmoothOfRelativeDimension n (affineStructuralMap k A) := by
  rw [affineStructuralMap, affineBaseRingMap, HasRingHomProperty.Spec_iff
    (P := @SmoothOfRelativeDimension.{u} n), CommRingCat.hom_ofHom]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := n)).mpr inferInstance)

/-- The local native spectrum section basis is PRODUCED from actual
standard smoothness through the genuine original GammaSpec algebra iso. -/
def spectrumSectionBasis :
    letI := affineChartAlgebra (affineStructuralMap k A) ⊤
    Module.Basis (Fin n) Γ(Spec A, ⊤) (KaehlerDifferential k Γ(Spec A, ⊤)) := by
  letI := affineChartAlgebra (affineStructuralMap k A) ⊤
  have h : RingHom.IsStandardSmoothOfRelativeDimension n (algebraMap k Γ(Spec A, ⊤)) :=
    isStandardSmoothOfRelativeDimension_algebraMap_of_algEquiv (affineGammaSpecAlgEquiv k A)
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := n)).mpr inferInstance)
  let : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(Spec A, ⊤) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := n)).mp h
  exact standardSmoothDifferentialBasis k Γ(Spec A, ⊤) n

/-- The genuine affine native differential is an iso; its original source
basis is constructed internally, with no target basis assumption. -/
theorem affine_etale_isIso {Y : Scheme.{u}} [IsAffine Y] (g : Y ⟶ Spec A) [Etale g] :
    IsIso (exteriorCotangentSheafPullbackMap (affineStructuralMap k A) g n) := by
  let := structural_smooth k A n
  have he : g.appTop.hom.Etale := HasRingHomProperty.appTop (@Etale) g inferInstance
  let : Algebra Γ(Spec A, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra.Etale Γ(Spec A, ⊤) Γ(Y, ⊤) := he
  exact exteriorCotangentSheafPullbackMap_isIso_of_formallyEtale _ g n
    (spectrumSectionBasis k A n) (by
      change Algebra.FormallyEtale Γ(Spec A, ⊤) Γ(Y, ⊤)
      infer_instance)

/-- Any actual etale source over the SAME original standard-smooth affine
scheme has its SAME ENTIRE native canonical differential an isomorphism. -/
theorem etale_isIso {Y : Scheme.{u}} (g : Y ⟶ Spec A) [Etale g] :
    IsIso (exteriorCotangentSheafPullbackMap (affineStructuralMap k A) g n) := by
  apply isIso_of_open_cover Y.affineCover.X Y.affineCover.f Y.affineCover.exists_eq
  intro i
  apply pullback_differential_isIso_of_open_composite
  exact affine_etale_isIso k A n (Y.affineCover.f i ≫ g)

/-- Genuine whole native differential composition preserves isomorphisms. -/
theorem differential_composite_isIso {K : Type u} [Field K] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ X) (h : Z ⟶ Y) (q : ℕ)
    (hg : IsIso (exteriorCotangentSheafPullbackMap f g q))
    (hh : IsIso (exteriorCotangentSheafPullbackMap (g ≫ f) h q)) :
    IsIso (exteriorCotangentSheafPullbackMap f (h ≫ g) q) := by
  let := hg
  let := hh
  rw [exteriorCotangentSheafPullbackMap_comp]
  infer_instance

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalEtaleSmoothAffine
