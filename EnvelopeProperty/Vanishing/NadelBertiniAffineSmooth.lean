import EnvelopeProperty.Vanishing.NadelBertiniAffineIncidence
import EnvelopeProperty.Vanishing.NadelBertiniLinearSmooth
import EnvelopeProperty.Vanishing.NadelBertiniSubschemeSections
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
/-! # The actual entire affine universal incidence is smooth over its same original source -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniAffineSmooth
open EnvelopeProperty.Vanishing NadelBertiniUniversal NadelBertiniPolynomial NadelBertiniLinearSmooth
variable {R : Type u} [CommRing R] {m : ℕ} {X : Scheme.{u}} [IsAffine X]

def sourceSectionsAlgEquiv (p : X ⟶ Spec (.of R)) :
    let : Algebra Γ(X, ⊤) Γ(product (m := m) p, ⊤) :=
      (FlatGlobalSections.firstProjection (S := parameterRing R m) p).appTop.hom.toAlgebra
    MvPolynomial (Fin (m + 1)) Γ(X, ⊤) ≃ₐ[Γ(X, ⊤)] Γ(product (m := m) p, ⊤) := by
  let : Algebra Γ(X, ⊤) Γ(product (m := m) p, ⊤) :=
    (FlatGlobalSections.firstProjection (S := parameterRing R m) p).appTop.hom.toAlgebra
  refine { toRingEquiv := sectionsEquiv (S := Fin (m + 1)) p, commutes' := ?_ }
  exact sectionsEquiv_C p

theorem affine_toSource_smooth (p : X ⟶ Spec (.of R)) (L : X.Modules) (hL : IsInvertible L)
    (e : L ≅ unitObj X) (s : Fin (m + 1) → Γ(L, ⊤)) (j : Fin (m + 1))
    (hj : (show Γ(X, ⊤) from e.hom.app ⊤ (s j)) = 1) :
    Smooth (toSource p L hL s) := by
  let Y := product (m := m) p
  let f := FlatGlobalSections.firstProjection (S := parameterRing R m) p
  let I := incidenceIdeal p L hL s
  let c : Fin (m + 1) → Γ(X, ⊤) := fun a => e.hom.app ⊤ (s a)
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(X, ⊤) Γ(I.subscheme, ⊤) := (I.subschemeι ≫ f).appTop.hom.toAlgebra
  let E := sourceSectionsAlgEquiv (m := m) p
  have hI : I.ideal ⟨⊤, isAffineOpen_top Y⟩ = Ideal.map E.toRingHom (linearIdeal c) :=
    NadelBertiniAffineIncidence.incidenceIdeal_top p L hL e s
  let eQ := Ideal.quotientEquivAlg (linearIdeal c) (I.ideal ⟨⊤, isAffineOpen_top Y⟩) E hI
  have := linear_smooth c j hj
  have : Algebra.Smooth Γ(X, ⊤) (Γ(Y, ⊤) ⧸ I.ideal ⟨⊤, isAffineOpen_top Y⟩) :=
    Algebra.Smooth.of_equiv eQ
  have : Algebra.Smooth Γ(X, ⊤) Γ(I.subscheme, ⊤) :=
    Algebra.Smooth.of_equiv (NadelBertiniSubschemeSections.quotientAlgEquivSections I f)
  have : IsAffine I.subscheme := (IsClosedImmersion.isAffine_surjective_of_isAffine I.subschemeι).1
  change Smooth (I.subschemeι ≫ f)
  rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
  exact (RingHom.smooth_algebraMap).mpr inferInstance
end EnvelopeProperty.Vanishing.NadelBertiniAffineSmooth
