import EnvelopeProperty.Vanishing.NadelMixedKummerSmoothCore

/-! # Actual smoothness of the WHOLE mixed SNC Kummer source

The original etale coordinates, distinct active coordinate labels, original
unit coefficients and positive tame original degrees internally produce every
local cotangent splitting. No smooth source or normalization isomorphism is an input.
-/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelMixedKummer
namespace SmoothSource
open Algebra
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {n q : ℕ} (x : Fin n → R) (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
  (N : Fin q → ℕ) (c : Fin q → R) (p : Ideal (Ring N c)) [p.IsPrime]

/-- The ACTUAL localized relation Jacobian reduces to the transpose of the
ACTUAL full original residue Jacobian on any explicitly named columns. -/
theorem derivativeJacobian_residue (j : Fin q → (Fin n ⊕ Fin q)) :
    (derivativeJacobian x hx N c p j).map (IsLocalRing.residue (Localization.AtPrime p)) =
      ((residueJacobian x hx N c (residueMap N c p)).submatrix id j).transpose := by
  ext a b
  change IsLocalRing.residue (Localization.AtPrime p)
    (derivativeJacobian x hx N c p j a b) = _
  rw [derivativeJacobian_apply]
  change residueMap N c p
      (algebraMap (extension (k := k) N c).Ring (Ring N c)
        (extensionDerivative x hx N c (j a) (relation N c b))) =
    residueJacobian x hx N c (residueMap N c p) b (j a)
  cases j a <;> rfl

/-- An ACTUAL original residue minor that is a unit proves that the SAME
constructed local cotangent-Jacobian determinant is a unit. -/
theorem derivativeJacobian_det_isUnit (j : Fin q → (Fin n ⊕ Fin q))
    (hj : IsUnit ((residueJacobian x hx N c (residueMap N c p)).submatrix id j).det) :
    IsUnit (derivativeJacobian x hx N c p j).det := by
  have he : IsLocalRing.residue (Localization.AtPrime p)
      (derivativeJacobian x hx N c p j).det =
        ((residueJacobian x hx N c (residueMap N c p)).submatrix id j).det := by
    rw [RingHom.map_det]
    change ((derivativeJacobian x hx N c p j).map
      (IsLocalRing.residue (Localization.AtPrime p))).det = _
    rw [derivativeJacobian_residue, Matrix.det_transpose]
  have hn : IsLocalRing.residue (Localization.AtPrime p)
      (derivativeJacobian x hx N c p j).det ≠ 0 := by
    rw [he]
    exact hj.ne_zero
  exact (IsLocalRing.residue_ne_zero_iff_isUnit
    (R := Localization.AtPrime p) (derivativeJacobian x hx N c p j).det).mp hn

include hx in
/-- The actual original residue unit minor constructs a cotangent-complex
splitting for the SAME prime localization and proves its formal smoothness. -/
theorem formallySmoothAt_of_unit_minor (j : Fin q → (Fin n ⊕ Fin q))
    (hj : IsUnit ((residueJacobian x hx N c (residueMap N c p)).submatrix id j).det) :
    Algebra.FormallySmooth k (Localization.AtPrime p) := by
  have : Algebra.FormallySmooth k (extension (k := k) N c).Ring := ambient_formallySmooth x hx N c
  have : Algebra.FormallySmooth k (localExtension (k := k) N c p).Ring :=
    ExtensionLocalization.ambient_formallySmooth (extension (k := k) N c) p
  exact CotangentCriterion.formallySmooth (localExtension (k := k) N c p)
    (localRelation (k := k) N c p)
    (ExtensionLocalization.span_relation_eq_ker (extension (k := k) N c) p (relation N c)
      (span_relation_eq_ker N c))
    (fun i => localDerivative x hx N c p (j i))
    (derivativeJacobian_det_isUnit x hx N c p j hj)

variable (A : Set (Fin q)) (σ : A ↪ Fin n) (u : Fin q → Rˣ)
    (hc : ∀ i, c i = mixedCoefficient x A σ u i)

include hc in
/-- The ORIGINAL coefficient identities internally produce the whole original
residue unit minor; no column choice or Jacobian-unit certificate is input. -/
theorem exists_residue_unit_minor (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : R)) :
    ∃ j : Fin q ↪ (Fin n ⊕ Fin q),
      IsUnit ((residueJacobian x hx N c (residueMap N c p)).submatrix id j).det := by
  have he : c = mixedCoefficient x A σ u := funext hc
  subst c
  exact MixedJacobian.exists_unit_minor x hx A σ u N (residueMap N (mixedCoefficient x A σ u) p)
    hN htame

include hx hc in
/-- The SAME WHOLE original mixed quotient is formally smooth at EVERY actual
source prime, from the original coordinate, unit and degree geometric data. -/
theorem formallySmoothAt (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : R)) :
    Algebra.FormallySmooth k (Localization.AtPrime p) := by
  obtain ⟨j, hj⟩ := exists_residue_unit_minor x hx N c p A σ u hc hN htame
  exact formallySmoothAt_of_unit_minor x hx N c p j hj

include hx hc in
/-- The SAME WHOLE original mixed SNC root algebra is actually smooth over
its original base. Disconnected factors and zero bases are retained in full. -/
theorem smooth (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : R)) :
    Algebra.Smooth k (Ring N c) := by
  have : Algebra.FinitePresentation k (Ring N c) := finitePresentation x hx N c
  refine ⟨?_, inferInstance⟩
  apply (Algebra.smoothLocus_eq_univ_iff (R := k) (A := Ring N c)).mp
  apply Set.eq_univ_of_forall
  intro p
  exact formallySmoothAt x hx N c p.asIdeal A σ u hc hN htame

end SmoothSource
end EnvelopeProperty.Vanishing.NadelMixedKummer
