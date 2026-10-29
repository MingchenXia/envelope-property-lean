import EnvelopeProperty.Char0.RelativeJacobianIdeal

/-! # Genuine original etale coordinates, partials and Jacobians under algebra isomorphisms -/

noncomputable section
namespace EnvelopeProperty.Char0
open CategoryTheory Module
open scoped Classical
universe u
variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)

/-- EVERY actual original algebra isomorphism preserves actual etaleness
of the SAME original coordinate tuple, with no etale comparison premise. -/
theorem etaleCoordinates_map_algEquiv {n : ℕ} (v : Fin n → A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    (MvPolynomial.aeval (R := k) (fun i => e (v i))).toRingHom.Etale := by
  have he : e.toRingHom.Etale := RingHom.Etale.of_bijective e.bijective
  have hcomp : (MvPolynomial.aeval (R := k) (fun i => e (v i))).toRingHom =
      e.toRingHom.comp (MvPolynomial.aeval (R := k) v).toRingHom :=
    congrArg AlgHom.toRingHom (MvPolynomial.comp_aeval v e.toAlgHom).symm
  rw [hcomp]
  exact RingHom.Etale.stableUnderComposition _ _ hv he

private def coordinateIsoConjugateDerivation (D : Derivation k B B) : Derivation k A A where
  toLinearMap := e.symm.toLinearMap.comp (D.toLinearMap.comp e.toLinearMap)
  map_one_eq_zero' := by
    change e.symm (D (e 1)) = 0
    rw [map_one, Derivation.map_one_eq_zero, map_zero]
  leibniz' a b := by
    change e.symm (D (e (a*b))) = a * e.symm (D (e b)) + b * e.symm (D (e a))
    rw [map_mul, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, AlgEquiv.symm_apply_apply]

/-- SAME original genuine coordinate partials commute with the ENTIRE
original algebra isomorphism on EVERY original function. -/
theorem etalePartialDeriv_map_algEquiv {n : ℕ} (v : Fin n → A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (j : Fin n) (a : A) :
    etalePartialDeriv (fun i => e (v i)) (etaleCoordinates_map_algEquiv e v hv) j (e a) =
      e (etalePartialDeriv v hv j a) := by
  let D := coordinateIsoConjugateDerivation e
    (etalePartialDeriv (fun i => e (v i)) (etaleCoordinates_map_algEquiv e v hv) j)
  have hD : D = etalePartialDeriv v hv j := by
    apply derivation_ext_etale v hv
    intro i
    change e.symm (etalePartialDeriv (fun l => e (v l))
      (etaleCoordinates_map_algEquiv e v hv) j (e (v i))) = etalePartialDeriv v hv j (v i)
    rw [etalePartialDeriv_apply, etalePartialDeriv_apply]
    split_ifs <;> simp only [map_one, map_zero]
  have h := congrArg (fun E : Derivation k A A => e (E a)) hD
  change e (e.symm (etalePartialDeriv (fun i => e (v i))
    (etaleCoordinates_map_algEquiv e v hv) j (e a))) = e (etalePartialDeriv v hv j a) at h
  simpa only [AlgEquiv.apply_symm_apply] using h

/-- The SAME original coordinate Jacobian determinant of EVERY original
function tuple is retained exactly under the SAME actual algebra isomorphism. -/
theorem etaleJacobian_map_algEquiv {n : ℕ} (v : Fin n → A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (z : Fin n → A) :
    etaleJacobian (fun i => e (v i)) (etaleCoordinates_map_algEquiv e v hv) (fun i => e (z i)) =
      e (etaleJacobian v hv z) := by
  unfold etaleJacobian
  rw [e.map_det]
  congr 1
  ext i j
  exact etalePartialDeriv_map_algEquiv e v hv j (z i)

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra k R] [Algebra k R']

/-- In an actual original coefficient-isomorphism square, the ENTIRE
ALL-original-source-functions Jacobian ideal transports along the SAME target
isomorphism. Actual source/target etale tuples DERIVE every basis and full image. -/
theorem affineRelativeJacobianIdeal_map_of_algEquivs
    (eR : R ≃ₐ[k] R') (φ : R →ₐ[k] A) (ψ : R' →ₐ[k] B)
    (hsq : ∀ r : R, ψ (eR r) = e (φ r))
    {n : ℕ} (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (v : Fin n → A) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    letI : Algebra R A := φ.toAlgebra
    letI : Algebra R' B := ψ.toAlgebra
    affineRelativeJacobianIdeal (R := R')
        (etaleDifferentialBasis (fun i => e (v i)) (etaleCoordinates_map_algEquiv e v hv)) =
      (affineRelativeJacobianIdeal (R := R) (etaleDifferentialBasis v hv)).map e.toRingHom := by
  let : Algebra R A := φ.toAlgebra
  let : Algebra R' B := ψ.toAlgebra
  let : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  let : IsScalarTower k R' B := IsScalarTower.of_algebraMap_eq fun a => (ψ.commutes a).symm
  have hz' := etaleCoordinates_map_algEquiv eR z hz
  have hv' := etaleCoordinates_map_algEquiv e v hv
  have hA := affineRelativeJacobianIdeal_eq_span z hz (etaleDifferentialBasis v hv)
  have hB := affineRelativeJacobianIdeal_eq_span (fun i => eR (z i)) hz'
    (etaleDifferentialBasis (fun i => e (v i)) hv')
  rw [hA, hB, relativeDifferentialDet_eq_etaleJacobian z hz v hv,
    relativeDifferentialDet_eq_etaleJacobian (fun i => eR (z i)) hz' (fun i => e (v i)) hv',
    Ideal.map_span, Set.image_singleton]
  change Ideal.span {etaleJacobian (fun i => e (v i)) hv' (fun i => ψ (eR (z i)))} =
    Ideal.span {e (etaleJacobian v hv (fun i => φ (z i)))}
  have hfun : (fun i => ψ (eR (z i))) = (fun i => e (φ (z i))) := funext fun i => hsq (z i)
  rw [hfun, etaleJacobian_map_algEquiv]

end EnvelopeProperty.Char0
