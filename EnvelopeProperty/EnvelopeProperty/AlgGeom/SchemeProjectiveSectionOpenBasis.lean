import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationVanishing
import EnvelopeProperty.AlgGeom.ProjectiveHomogeneousSections
import EnvelopeProperty.Projective.NativeHomogeneousSectionValues
import EnvelopeProperty.Projective.IdealRepresentation
import EnvelopeProperty.AlgGeom.PositivePowerProjectiveGeneration

/-! # Actual homogeneous forms have their original projective section opens

The existing genuine homogeneous global section is transported to the
SAME actual O(1) tensor power. Its actual zero-ideal complement is exactly
the SAME original homogeneous basic open. Native projective stalk fractions
and actual original line frames prove the equality internally.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open MvPolynomial Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeProjectiveSectionOpenBasis
open CanonicalGeometry SchemeLineSectionEvaluation SchemeModuleCechLineSectionLocalization
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual original whole-line iso preserves the literal original section-open.
The ordinary geometric frames and whole section compatibility are internal. -/
theorem sectionOpen_postcompose_iso {X : Scheme.{u}} {M N : X.Modules}
    (hM : IsInvertible M) (hN : IsInvertible N) (s : unitObj X ⟶ M) (e : M ≅ N) :
    sectionOpen N hN (s ≫ e.hom) = sectionOpen M hM s := by
  ext x
  have hM₀ := hM
  obtain ⟨I, U, hU, eU⟩ := hM₀
  have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let a := (eU i).some
  let b := (pullback (U i).ι).mapIso e.symm ≪≫ a
  change (x ∉ (LineSectionZeroIdeal.zeroIdeal N hN (s ≫ e.hom)).support) ↔
    (x ∉ (LineSectionZeroIdeal.zeroIdeal M hM s).support)
  rw [SchemeLineZeroSupportPullback.mem_support_iff_pullback_frame_zero N hN (s ≫ e.hom)
      (U i) x hi b,
    SchemeLineZeroSupportPullback.mem_support_iff_pullback_frame_zero M hM s (U i) x hi a]
  have he : pullbackSectionHom (U i).ι (s ≫ e.hom) ≫ b.hom =
      pullbackSectionHom (U i).ι s ≫ a.hom := by
    simp only [pullbackSectionHom, b, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Functor.map_comp, Category.assoc]
    rw [← (pullback (U i).ι).map_comp_assoc e.hom e.inv a.hom, Iso.hom_inv_id,
      (pullback (U i).ι).map_id, Category.id_comp]
  rw [he]

variable {R : Type u} [CommRing R] {n : ℕ}
local notation "P" => Proj (homogeneousSubmodule (Fin (n + 1)) R)

private theorem native_form_germ_isUnit_iff (i : Fin (n + 1)) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d)
    (p : ProjBerk.NativeProjectiveScheme R n) (hp : p ∈ ProjBerk.nativeCoordinateOpen i) :
    IsUnit ((ProjBerk.NativeProjectiveScheme R n).presheaf.germ
      (ProjBerk.nativeCoordinateOpen i) p hp (ProjBerk.nativeFormSection i F)) ↔
      p ∈ Proj.basicOpen (ProjBerk.ProjectiveGrading R n) F := by
  rw [← MulEquiv.isUnit_map (Proj.stalkIso' (ProjBerk.ProjectiveGrading R n) p),
    ProjBerk.nativeFormSection_germ i p hp hF,
    ← HomogeneousLocalization.isUnit_iff_isUnit_val]
  change IsUnit (Localization.mk F
      (⟨(X i) ^ d, _⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl)) ↔
    F ∉ p.asHomogeneousIdeal
  rw [Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
  rfl

private theorem coefficient_germ_isUnit_iff (i : Fin (n + 1)) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d)
    (p : P) (hp : p ∈ coordinateOpen (R := R) i) :
    IsUnit ((P).presheaf.germ (coordinateOpen (R := R) i) p hp
      (ProjectiveHomogeneousSections.coefficient i d F hF)) ↔
      p ∈ Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) R) F := by
  rw [ProjBerk.homogeneousSection_coefficient_eq_coordinate]
  exact native_form_germ_isUnit_iff i d F hF p hp

private theorem original_homogeneousSection_open (j : Fin (n + 1)) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d) :
    sectionOpen (coordinateHyperplaneTwist (R := R) j (d : ℤ))
      (coordinateHyperplaneTwist_isInvertible j (d : ℤ))
      (ProjectiveHomogeneousSections.sectionHom j d F hF) =
    Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) R) F := by
  ext p
  have hp : p ∈ ⨆ i : Fin (n + 1), coordinateOpen (R := R) i := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hp
  let M := coordinateHyperplanePoleSheafPower (R := R) j d
  let e := coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j d
  let eO := overTrivializationOfRestrictIso M (coordinateOpen (R := R) i) e
  change (p ∉ (LineSectionZeroIdeal.zeroIdeal M
    (coordinateHyperplaneTwist_isInvertible j (d : ℤ))
    (SchemeModuleGlobalSections.sectionHom M (ProjectiveHomogeneousSections.homogeneousSection j d F hF))).support) ↔ _
  rw [SchemeLineZeroSupportPullback.mem_support_iff_coefficient_zero M _ _
    (coordinateOpen (R := R) i) p hi eO]
  have hc : eO.hom.val.app (op (Over.mk (𝟙 (coordinateOpen (R := R) i))))
      ((SchemeModuleGlobalSections.sectionHom M
        (ProjectiveHomogeneousSections.homogeneousSection j d F hF)).val.app
          (op (coordinateOpen (R := R) i)) (1 : Γ(P, coordinateOpen (R := R) i))) =
      ProjectiveHomogeneousSections.coefficient i d F hF := by
    change eO.hom.val.app (op (Over.mk (𝟙 (coordinateOpen (R := R) i))))
      ((1 : Γ(P, coordinateOpen (R := R) i)) •
        M.val.map (homOfLE (le_top : coordinateOpen (R := R) i ≤ ⊤)).op
          (ProjectiveHomogeneousSections.homogeneousSection j d F hF)) = _
    rw [one_smul]
    exact ProjectiveHomogeneousSections.section_coefficient i j d F hF
  rw [hc, (P).evaluation_eq_zero_iff_notMem_basicOpen p hi, not_not,
    (P).mem_basicOpen _ p hi]
  exact coefficient_germ_isUnit_iff i d F hF p hi

/-- The actual global homogeneous-form section of the SAME native O(1)
tensor power; it reuses the original genuine section and whole power iso. -/
def homogeneousPowerSection (j : Fin (n + 1)) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d) :
    unitObj P ⟶ bundleTensorPower (coordinateHyperplaneTwist (R := R) j (1 : ℤ)) d :=
  ProjectiveHomogeneousSections.sectionHom j d F hF ≫
    (PositivePowerProjectiveGeneration.twistPowerIso j d).inv

/-- The SAME actual homogeneous form has exactly its ORIGINAL homogeneous
basic open as its literal zero-ideal-complement section-open. All coefficient,
stalk, frame and power identifications are derived internally. -/
theorem homogeneousPowerSection_open (j : Fin (n + 1)) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d) :
    sectionOpen (bundleTensorPower (coordinateHyperplaneTwist (R := R) j (1 : ℤ)) d)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible
        (coordinateHyperplaneTwist_isInvertible j (1 : ℤ)) d)
      (homogeneousPowerSection j d F hF) =
      Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) R) F :=
  (sectionOpen_postcompose_iso (coordinateHyperplaneTwist_isInvertible j (d : ℤ))
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible
      (coordinateHyperplaneTwist_isInvertible j (1 : ℤ)) d)
    (ProjectiveHomogeneousSections.sectionHom j d F hF)
    (PositivePowerProjectiveGeneration.twistPowerIso j d).symm).trans
      (original_homogeneousSection_open j d F hF)

end EnvelopeProperty.SchemeProjectiveSectionOpenBasis
