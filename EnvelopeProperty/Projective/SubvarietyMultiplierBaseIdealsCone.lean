import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsNonzero
import EnvelopeProperty.Projective.IdealRepresentation
import EnvelopeProperty.Berkovich.SchemeIdealExtension

/-! # Canonical actual cone ideals from SAME whole original scheme ideals -/

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
open ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual native representative is monotone on ENTIRE original ideals. -/
theorem nativeRepresentative_mono {R : Type u} [CommRing R] {n : ℕ}
    {I J : (NativeProjectiveScheme R n).IdealSheafData} (h : I ≤ J) :
    nativeHomogeneousRepresentative I ≤ nativeHomogeneousRepresentative J := by
  apply Ideal.homogeneousCore_mono
  apply iInf_mono
  intro j
  exact Ideal.comap_mono (Ideal.comap_mono (h ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩))

/-- The genuine homogeneous-core adjunction internally turns actual WHOLE
sheaf containment into containment in the canonical original representative. -/
theorem homogeneousIdeal_le_nativeRepresentative {R : Type u} [CommRing R] {n : ℕ}
    (H : HomogeneousIdeal (ProjectiveGrading R n))
    (I : (NativeProjectiveScheme R n).IdealSheafData)
    (h : GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) H ≤ I) :
    H ≤ nativeHomogeneousRepresentative I := by
  apply (Ideal.homogeneousCore.gc (ProjectiveGrading R n) H _).mp
  apply le_iInf
  intro j
  rw [← Ideal.map_le_iff_le_comap]
  have hh := Ideal.comap_mono (f := (nativeCoordinateSectionsIso (R := R) j).hom.hom)
    (h ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩)
  rw [homogeneousQuotient_coordinateSectionIdeal] at hh
  exact hh

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The actual original cone quotient after the SAME parameter exchange. -/
def parameterConeQuotient : MvPolynomial (Fin (M + 1)) k[X] →ₐ[k] X.ConeRing :=
  X.coneMk.comp (parameterEquiv (k := k) (M := M)).symm.toAlgHom

/-- Every original whole polynomial goes to its SAME original cone class. -/
theorem parameterConeQuotient_parameterEquiv
    (g : (MvPolynomial (Fin (M + 1)) k)[X]) :
    parameterConeQuotient X (parameterEquiv g) = X.coneMk g := by
  simp only [parameterConeQuotient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]

/-- No homogeneous representation is supplied: take the native representative
of the SAME original scheme ideal extended through the SAME original inclusion. -/
def homogeneousConeRepresentative (K : (familyScheme X).IdealSheafData) :
    HomogeneousIdeal (ProjectiveGrading k[X] M) :=
  nativeHomogeneousRepresentative (K.map (familyInclusion X))

/-- The canonical representative recovers the ENTIRE original ideal sheaf
on the SAME original family, with no support/radical replacement. -/
theorem homogeneousConeRepresentative_comap (K : (familyScheme X).IdealSheafData) :
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M)
      (homogeneousConeRepresentative X K)).comap (familyInclusion X) = K := by
  rw [homogeneousConeRepresentative, nativeHomogeneousRepresentative_quotientIdealSheaf,
    Scheme.IdealSheafData.comap_map_of_isClosedImmersion]

/-- The genuine cone ideal of the ENTIRE original scheme ideal. -/
def coneIdeal (K : (familyScheme X).IdealSheafData) : Ideal X.ConeRing :=
  (homogeneousConeRepresentative X K).toIdeal.map (parameterConeQuotient X).toRingHom

/-- Monotonicity retains every original object and the actual cone quotient. -/
theorem coneIdeal_mono {I J : (familyScheme X).IdealSheafData} (h : I ≤ J) :
    coneIdeal X I ≤ coneIdeal X J :=
  Ideal.map_mono (nativeRepresentative_mono (Scheme.IdealSheafData.map_mono _ h))

/-- Mapping the SAME parameter obstacle ideal gives EXACTLY the original cone ideal. -/
theorem parameterObstacleIdeal_map_cone (d : ℕ) (φ : X.an → ℝ) (m : ℕ) :
    (parameterObstacleIdeal X d φ m).map (parameterConeQuotient X).toRingHom =
      X.coneObstacleIdeal d φ m := by
  unfold parameterObstacleIdeal coneObstacleIdeal
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro g
  exact parameterConeQuotient_parameterEquiv X g

/-- Actual WHOLE original scheme containment yields containment of the SAME
original obstacle cone ideal. The final multiplier consumer supplies this
scheme containment by its actual proved theorem, not as a final certificate. -/
theorem coneObstacleIdeal_le_coneIdeal_of_schemeIdeal_le
    (d : ℕ) (φ : X.an → ℝ) (m : ℕ) (K : (familyScheme X).IdealSheafData)
    (h : schemeIdeal X d φ m ≤ K) : X.coneObstacleIdeal d φ m ≤ coneIdeal X K := by
  have hs : ambientSchemeIdeal X d φ m ≤ K.map (familyInclusion X) :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr h
  have hh := homogeneousIdeal_le_nativeRepresentative (homogeneousObstacleIdeal X d φ m)
    (K.map (familyInclusion X)) hs
  have hh' : parameterObstacleIdeal X d φ m ≤
      (homogeneousConeRepresentative X K).toIdeal := hh
  have hm : (parameterObstacleIdeal X d φ m).map (parameterConeQuotient X).toRingHom ≤
      coneIdeal X K := Ideal.map_mono hh'
  exact (parameterObstacleIdeal_map_cone X d φ m).symm ▸ hm

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
