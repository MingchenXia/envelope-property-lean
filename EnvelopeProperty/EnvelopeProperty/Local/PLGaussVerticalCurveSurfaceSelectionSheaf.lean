import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelection
import EnvelopeProperty.Projective.IdealRepresentation
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Actual original closed cuts through a prescribed closed subscheme

The literal ambient kernel internally supplies its canonical homogeneous
representative. Every sufficiently large degree gives an actual pulled
closed hypersurface through the original C, with its original whole map
triangle and avoidance of the prescribed actual points of Y.
-/
noncomputable section
open scoped Classical
open CategoryTheory AlgebraicGeometry MvPolynomial
open EnvelopeProperty.ProjBerk
universe u
namespace EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionSheaf
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {n : ℕ}

/-- The original principal ideal of the actual homogeneous equation, with its derived grading. -/
def homogeneousPrincipalIdeal {d : ℕ} (F : MvPolynomial (Fin (n + 1)) R)
    (hF : F.IsHomogeneous d) : HomogeneousIdeal (ProjectiveGrading R n) :=
  ⟨Ideal.span {F}, Ideal.homogeneous_span _ _ (by
    intro G hG
    have heq : G = F := Set.mem_singleton_iff.mp hG
    subst G
    exact ⟨d, hF⟩)⟩

/-- The actual original projective quotient kernel of the SAME principal homogeneous ideal. -/
def projectiveHypersurfaceIdeal {d : ℕ} (F : MvPolynomial (Fin (n + 1)) R)
    (hF : F.IsHomogeneous d) : (NativeProjectiveScheme R n).IdealSheafData :=
  EnvelopeProperty.GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n)
    (homogeneousPrincipalIdeal F hF)

/-- The SAME geometric ideal pullback defines the actual original closed cut of Y. -/
def originalHypersurfaceCut {Y : Scheme.{u}} (i : Y ⟶ NativeProjectiveScheme R n)
    {d : ℕ} (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d) : Y.IdealSheafData :=
  (projectiveHypersurfaceIdeal F hF).comap i

/-- The actual original quotient kernel support is the literal zero locus of its equation. -/
theorem projectiveHypersurfaceIdeal_support {d : ℕ}
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d) :
    ((projectiveHypersurfaceIdeal F hF).support : Set (NativeProjectiveScheme R n)) =
      ProjectiveSpectrum.zeroLocus (ProjectiveGrading R n) {F} := by
  exact (EnvelopeProperty.GradedQuotient.quotientIdealSheaf_support_eq_zeroLocus
    (ProjectiveGrading R n) (homogeneousPrincipalIdeal F hF)).trans
      (ProjectiveSpectrum.zeroLocus_span (ProjectiveGrading R n) {F})

/-- The WHOLE actual original quotient ideal sheaves preserve original homogeneous ideal inclusion. -/
theorem quotientIdealSheaf_mono (I J : HomogeneousIdeal (ProjectiveGrading R n)) (hIJ : I ≤ J) :
    EnvelopeProperty.GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) I ≤
      EnvelopeProperty.GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J := by
  apply Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun j : Fin (n + 1) => ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩)
    iSup_nativeCoordinateOpen_eq_top
  intro j
  apply (Ideal.comap_le_comap_iff_of_surjective
    (nativeCoordinateSectionsIso (R := R) j).hom.hom
    (nativeCoordinateSectionsIso (R := R) j).commRingCatIsoToRingEquiv.surjective _ _).mp
  exact (homogeneousQuotient_coordinateSectionIdeal I j).trans_le
    ((Ideal.map_mono (show I.toIdeal ≤ J.toIdeal from hIJ)).trans_eq
      (homogeneousQuotient_coordinateSectionIdeal J j).symm)

/-- The actual original closed immersion internally supplies the correct representative point exclusion. -/
theorem ambientKernelRepresentative_point_notMem {Y C : Scheme.{u}}
    (i : Y ⟶ NativeProjectiveScheme R n) [IsClosedImmersion i]
    (c : C ⟶ Y) [IsClosedImmersion c] (y : Y) (hy : y ∉ Set.range c) :
    i y ∉ ProjectiveSpectrum.zeroLocus (ProjectiveGrading R n)
      (nativeHomogeneousRepresentative (c ≫ i).ker : Set _) := by
  intro hz
  have hs : i y ∈ (EnvelopeProperty.GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n)
      (nativeHomogeneousRepresentative (c ≫ i).ker)).support :=
    (Set.ext_iff.mp (EnvelopeProperty.GradedQuotient.quotientIdealSheaf_support_eq_zeroLocus
      (ProjectiveGrading R n) (nativeHomogeneousRepresentative (c ≫ i).ker)) (i y)).mpr hz
  have hsupport := congrArg Scheme.IdealSheafData.support
    (nativeHomogeneousRepresentative_quotientIdealSheaf (c ≫ i).ker)
  have hs' : i y ∈ (c ≫ i).ker.support := hsupport ▸ hs
  have hclosure : i y ∈ closure (Set.range (c ≫ i)) :=
    (Set.ext_iff.mp (Scheme.Hom.support_ker (c ≫ i)) (i y)).mp hs'
  have hrange : i y ∈ Set.range (c ≫ i) :=
    (c ≫ i).isClosedEmbedding.isClosed_range.closure_eq ▸ hclosure
  obtain ⟨z, hz⟩ := hrange
  apply hy
  refine ⟨z, ?_⟩
  apply i.isClosedEmbedding.injective
  exact hz

/-- Every sufficiently large actual degree gives a genuine proper original closed cut through C. -/
theorem exists_eventually_original_closed_cut
    (k : Type u) [Field k] [Infinite k] [Algebra k R]
    {Y C : Scheme.{u}} (i : Y ⟶ NativeProjectiveScheme R n) [IsClosedImmersion i]
    (c : C ⟶ Y) [IsClosedImmersion c]
    {ι : Type*} [Finite ι] [Nonempty ι] (y : ι → Y) (hy : ∀ a, y a ∉ Set.range c) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∃ (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d),
      F ∈ nativeHomogeneousRepresentative (c ≫ i).ker ∧
      ∃ g : C ⟶ (originalHypersurfaceCut i F hF).subscheme,
        IsClosedImmersion g ∧ g ≫ (originalHypersurfaceCut i F hF).subschemeι = c ∧
        (∀ a, y a ∉ (originalHypersurfaceCut i F hF).support) ∧
        (originalHypersurfaceCut i F hF).support ≠ ⊤ := by
  let J := nativeHomogeneousRepresentative (c ≫ i).ker
  obtain ⟨N, hN⟩ := PLGaussVerticalCurveSurfaceSelection.exists_eventually_projective_hypersurface_avoiding
    (k := k) J (fun a => i (y a)) (fun a => ambientKernelRepresentative_point_notMem i c (y a) (hy a))
  refine ⟨N, ?_⟩
  intro d hd
  obtain ⟨F, hF, hFJ, _hcontain, havoid⟩ := hN d hd
  let K := originalHypersurfaceCut i F hF
  have hprincipal : homogeneousPrincipalIdeal F hF ≤ J :=
    (Ideal.span_singleton_le_iff_mem _).mpr hFJ
  have hsheaf : projectiveHypersurfaceIdeal F hF ≤ (c ≫ i).ker :=
    (quotientIdealSheaf_mono (homogeneousPrincipalIdeal F hF) J hprincipal).trans_eq
      (nativeHomogeneousRepresentative_quotientIdealSheaf (c ≫ i).ker)
  have hK : K ≤ c.ker := by
    have hmap : projectiveHypersurfaceIdeal F hF ≤ c.ker.map i := by
      rwa [Scheme.IdealSheafData.map_ker]
    exact Scheme.IdealSheafData.le_map_iff_comap_le.mp hmap
  let g := IsClosedImmersion.lift K.subschemeι c (by rw [K.ker_subschemeι]; exact hK)
  have hfac : g ≫ K.subschemeι = c := IsClosedImmersion.lift_fac _ _ _
  have hg : IsClosedImmersion g := by
    let : IsClosedImmersion (g ≫ K.subschemeι) := by rw [hfac]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion g K.subschemeι
  have havoidY : ∀ a, y a ∉ K.support := by
    intro a ha
    have hpoint : i (y a) ∈ ((projectiveHypersurfaceIdeal F hF).support : Set _) := by
      change y a ∈ ((projectiveHypersurfaceIdeal F hF).comap i).support at ha
      rw [Scheme.IdealSheafData.support_comap] at ha
      exact ha
    apply havoid a
    rwa [projectiveHypersurfaceIdeal_support] at hpoint
  have hproper : K.support ≠ ⊤ := by
    intro htop
    obtain ⟨a⟩ := (inferInstance : Nonempty ι)
    exact havoidY a (by rw [htop]; trivial)
  exact ⟨F, hF, hFJ, g, hg, hfac, havoidY, hproper⟩

end EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionSheaf
