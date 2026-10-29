import EnvelopeProperty.Vanishing.NadelBlowupCanonicalSheafImage
import EnvelopeProperty.Vanishing.NadelBlowupCanonicalJacobian
import EnvelopeProperty.AlgGeom.Canonical.SpecGlobalCoordinateNaturality
import Hironaka.Scheme.BlowUp.CoordinateSubspace.Smooth

/-! # The actual original coordinate blowup Jacobian in the native canonical image -/

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalSheafCoordinates
open CoordinateSubspace affineBlowUpAlgebra CanonicalGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem coordinates_etale (k : Type u) [CommRing k] (n : ℕ) :
    (MvPolynomial.aeval (R := k) (X : Fin n → MvPolynomial (Fin n) k)).toRingHom.Etale := by
  rw [MvPolynomial.aeval_X_left]
  exact RingHom.Etale.of_bijective Function.bijective_id

theorem coordinate_partial (k : Type u) [CommRing k] (n : ℕ) (j : Fin n) :
    Char0.etalePartialDeriv X (coordinates_etale k n) j = pderiv (R := k) j := by
  apply MvPolynomial.derivation_ext
  intro i
  rw [Char0.etalePartialDeriv_apply]
  simp only [pderiv_X, Pi.single_apply, eq_comm]

/-- The temporary source copy has its actual native algebra equivalence;
its spectrum isomorphism retains the original chart's exact morphism. -/
def sourceAlgebraEquiv (k : Type u) [CommRing k] (n : ℕ) :
    ULift.{0} (MvPolynomial (Fin n) k) ≃ₐ[k] MvPolynomial (Fin n) k :=
  ULift.algEquiv

def chartAlgebraMap (k : Type u) [CommRing k] (n r : ℕ) (j : Fin n) :
    ULift.{0} (MvPolynomial (Fin n) k) →ₐ[k] MvPolynomial (Fin n) k :=
  (chartSubst k (center n r) j).comp (sourceAlgebraEquiv k n).toAlgHom

def sourceSpectrumIso (k : Type u) [CommRing k] (n : ℕ) :
    Spec (.of (ULift.{0} (MvPolynomial (Fin n) k))) ≅ Spec (.of (MvPolynomial (Fin n) k)) :=
  Scheme.Spec.mapIso (sourceAlgebraEquiv k n).symm.toRingEquiv.toCommRingCatIso.op

theorem chartAlgebraMap_original (k : Type u) [CommRing k] (n r : ℕ) (j : Fin n) :
    Spec.map (CommRingCat.ofHom (chartAlgebraMap k n r j).toRingHom) ≫
      (sourceSpectrumIso k n).hom =
        Spec.map (CommRingCat.ofHom (chartSubst k (center n r) j).toRingHom) := by
  change Spec.map (CommRingCat.ofHom (chartAlgebraMap k n r j).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (sourceAlgebraEquiv k n).symm.toRingHom) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  rfl

theorem source_coordinates_etale (k : Type u) [CommRing k] (n : ℕ) :
    (MvPolynomial.aeval (R := k)
      (fun i : Fin n => (sourceAlgebraEquiv k n).symm (X i))).toRingHom.Etale :=
  Char0.etaleCoordinates_map_algEquiv (sourceAlgebraEquiv k n).symm X (coordinates_etale k n)

attribute [-instance] ULift.smulLeft in
/-- The ALL-original-functions Jacobian, under an actual source ring
isomorphism preserving the original map, is precisely the original exceptional power. -/
theorem original_jacobianIdeal (k : Type u) [CommRing k] (n r : ℕ) (j : Fin n)
    (hj : j.val < r) (hrn : r ≤ n) :
    letI : Algebra (ULift.{0} (MvPolynomial (Fin n) k)) (MvPolynomial (Fin n) k) :=
      (chartAlgebraMap k n r j).toAlgebra
    letI : IsScalarTower k (ULift.{0} (MvPolynomial (Fin n) k)) (MvPolynomial (Fin n) k) :=
      IsScalarTower.of_algebraMap_eq fun c => ((chartAlgebraMap k n r j).commutes c).symm
    Char0.affineRelativeJacobianIdeal (R := ULift.{0} (MvPolynomial (Fin n) k))
      (Char0.etaleDifferentialBasis X (coordinates_etale k n)) =
        Ideal.span {X j ^ (r - 1)} := by
  let : Algebra (ULift.{0} (MvPolynomial (Fin n) k)) (MvPolynomial (Fin n) k) :=
    (chartAlgebraMap k n r j).toAlgebra
  let : IsScalarTower k (ULift.{0} (MvPolynomial (Fin n) k)) (MvPolynomial (Fin n) k) :=
    IsScalarTower.of_algebraMap_eq fun c => ((chartAlgebraMap k n r j).commutes c).symm
  rw [Char0.affineRelativeJacobianIdeal_eq_span
    (fun i => (sourceAlgebraEquiv k n).symm (X i)) (source_coordinates_etale k n),
    Char0.relativeDifferentialDet_eq_etaleJacobian
      (fun i => (sourceAlgebraEquiv k n).symm (X i)) (source_coordinates_etale k n)
      X (coordinates_etale k n)]
  apply congrArg (fun t : MvPolynomial (Fin n) k => Ideal.span {t})
  change (Matrix.of fun i l => Char0.etalePartialDeriv X (coordinates_etale k n) l
    (chartSubst k (center n r) j (X i))).det = _
  simp only [coordinate_partial]
  exact NadelBlowupCanonicalJacobian.determinant j hj hrn

/-- The genuine Spec/ΓSpec square transfers that computed original ideal
with its exact source ring isomorphism and actual original chart-map triangle. -/
theorem native_jacobianIdeal (k : Type u) [Field k] (n r : ℕ) (j : Fin n)
    (hj : j.val < r) (hrn : r ≤ n) :
    let C := CommRingCat.of (ULift.{0} (MvPolynomial (Fin n) k))
    let B := CommRingCat.of (MvPolynomial (Fin n) k)
    let φ := chartAlgebraMap k n r j
    let f := affineStructuralMap k C
    let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
    letI := affineChartAlgebra f ⊤
    letI := affineChartAlgebra (g ≫ f) ⊤
    let e := affineGammaSpecAlgEquivOfStructuralEq k B (g ≫ f)
      (affineAlgebraMap_structuralSquare k C B φ)
    letI : Algebra Γ(Spec C, ⊤) Γ(Spec B, ⊤) := g.appTop.hom.toAlgebra
    Char0.affineRelativeJacobianIdeal (R := Γ(Spec C, ⊤))
      (Char0.etaleDifferentialBasis (fun i => e (X i))
        (Char0.etaleCoordinates_map_algEquiv e X (coordinates_etale k n))) =
      Ideal.span {(Scheme.ΓSpecIso B).inv.hom (X j ^ (r - 1))} := by
  let C := CommRingCat.of (ULift.{0} (MvPolynomial (Fin n) k))
  let B := CommRingCat.of (MvPolynomial (Fin n) k)
  let φ := chartAlgebraMap k n r j
  let f := affineStructuralMap k C
  let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let := affineChartAlgebra f ⊤
  let := affineChartAlgebra (g ≫ f) ⊤
  let : Algebra Γ(Spec C, ⊤) Γ(Spec B, ⊤) := g.appTop.hom.toAlgebra
  have h := affineSpecRelativeJacobianIdeal k C B φ
    (fun i => (sourceAlgebraEquiv k n).symm (X i)) (source_coordinates_etale k n)
    X (coordinates_etale k n)
  rw [original_jacobianIdeal k n r j hj hrn, Ideal.map_span, Set.image_singleton] at h
  exact h

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalSheafCoordinates
