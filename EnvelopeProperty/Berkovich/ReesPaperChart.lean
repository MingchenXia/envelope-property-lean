import EnvelopeProperty.ReesChart
import EnvelopeProperty.Berkovich.Blowup
import EnvelopeProperty.Berkovich.ClosedImmersion
import EnvelopeProperty.Berkovich.SchemeValuedPoints

/-!
# The original paper blowup charts are the actual Rees degree-zero charts

The finite family is the original finite-set subtype inclusion. The entire
fraction algebra is proved equal to the existing paper chart before any
native or original-field point homeomorphism is constructed.
-/

open CategoryTheory AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
namespace EnvelopeProperty.ReesPaper
variable {A : Type*} [CommRing A] [IsDomain A]

/-- The ACTUAL original finite family, without enumerating or replacing its elements. -/
abbrev family (s : Finset A) : s → A := Subtype.val

/-- The actual degree-zero chart of the original finite-set Rees presentation. -/
abbrev Chart (s : Finset A) (j : s) := ReesChart.Chart (family s) j

private local instance chartOriginalAlgebra (s : Finset A) (j : s) : Algebra A (Chart s j) :=
  ReesChart.chartAlgebra (family s) j

/-- Both fraction-adjoin rings contain EXACTLY the original finite-set ratios. -/
theorem fractionAlgebra_eq_blowupChart (s : Finset A) (j : s) :
    ReesChart.fractionAlgebra (family s) j = blowupChart s (j : A) := by
  unfold ReesChart.fractionAlgebra blowupChart
  congr 1
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

/-- The original whole paper blowup ring is GENUINELY this actual Rees chart. -/
def chartEquiv (s : Finset A) (j : s) (hj : (j : A) ≠ 0) :
    Chart s j ≃ₐ[A] blowupChart s (j : A) :=
  (ReesChart.fractionEquiv (family s) j hj).trans
    (Subalgebra.equivOfEq _ _ (fractionAlgebra_eq_blowupChart s j))

/-- Every ORIGINAL homogeneous fraction follows the same entire fraction-field map. -/
@[simp]
theorem chartEquiv_coe (s : Finset A) (j : s) (hj : (j : A) ≠ 0) (z : Chart s j) :
    (chartEquiv s j hj z : FractionRing A) = ReesChart.toFractionRing (family s) j hj z := rfl

/-- The genuine chart equivalence retains EVERY original coefficient. -/
@[simp]
theorem chartEquiv_algebraMap (s : Finset A) (j : s) (hj : (j : A) ≠ 0) (a : A) :
    chartEquiv s j hj (algebraMap A (Chart s j) a) =
      algebraMap A (blowupChart s (j : A)) a := (chartEquiv s j hj).commutes a

/-- Every original actual degree-zero ratio is the EXISTING entire chartFrac element. -/
@[simp]
theorem chartEquiv_coordinateRatio (s : Finset A) (j i : s) (hj : (j : A) ≠ 0) :
    chartEquiv s j hj (ReesChart.coordinateRatio (family s) j i) =
      chartFrac s (j : A) i.2 := by
  apply Subtype.ext
  rw [chartEquiv_coe, ReesChart.toFractionRing_coordinateRatio]
  rfl

/-- Whole absolute affine point transport comes from the SAME actual ring equivalence. -/
def spectrumHomeomorph (s : Finset A) (j : s) (hj : (j : A) ≠ 0) :
    Spectrum (blowupChart s (j : A)) ≃ₜ Spectrum (Chart s j) :=
  Spectrum.ringEquivHomeomorph (chartEquiv s j hj).toRingEquiv

/-- Every original chart element has its true value under the ENTIRE ring map. -/
@[simp]
theorem spectrumHomeomorph_val (s : Finset A) (j : s) (hj : (j : A) ≠ 0)
    (y : Spectrum (blowupChart s (j : A))) (z : Chart s j) :
    (spectrumHomeomorph s j hj y).val z = y.val (chartEquiv s j hj z) := rfl

/-- The WHOLE original base seminorm agrees under actual chart transport. -/
theorem spectrumHomeomorph_comap_base (s : Finset A) (j : s) (hj : (j : A) ≠ 0)
    (y : Spectrum (blowupChart s (j : A))) :
    Spectrum.comap (algebraMap A (Chart s j)) (spectrumHomeomorph s j hj y) =
      Spectrum.comap (algebraMap A (blowupChart s (j : A))) y := by
  apply Spectrum.ext_val
  intro a
  change y.val (chartEquiv s j hj (algebraMap A (Chart s j) a)) = _
  rw [chartEquiv_algebraMap]
  rfl

/-- Actual NATIVE affine point homeomorphism, through genuine whole affine-spectrum maps. -/
def nativeHomeomorph (s : Finset A) (j : s) (hj : (j : A) ≠ 0) :
    SchemeValuedPoint (Spec (CommRingCat.of (blowupChart s (j : A)))) ≃ₜ
      SchemeValuedPoint (Spec (CommRingCat.of (Chart s j))) :=
  SchemeValuedPoint.spectrumHomeomorph.trans
    ((spectrumHomeomorph s j hj).trans SchemeValuedPoint.spectrumHomeomorph.symm)

/-- The whole native map is the actual Spec map, not a chosen point bijection. -/
@[simp]
theorem nativeHomeomorph_apply (s : Finset A) (j : s) (hj : (j : A) ≠ 0)
    (y : SchemeValuedPoint (Spec (CommRingCat.of (blowupChart s (j : A))))) :
    nativeHomeomorph s j hj y =
      SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom (chartEquiv s j hj).toRingHom)) y := by
  apply SchemeValuedPoint.spectrumHomeomorph.injective
  rw [SchemeValuedPoint.spectrumHomeomorph_map]
  exact Homeomorph.apply_symm_apply _ _

/-- Every native chart value follows the WHOLE original algebra equivalence. -/
@[simp]
theorem nativeHomeomorph_val (s : Finset A) (j : s) (hj : (j : A) ≠ 0)
    (y : SchemeValuedPoint (Spec (CommRingCat.of (blowupChart s (j : A))))) (z : Chart s j) :
    (SchemeValuedPoint.spectrumHomeomorph (nativeHomeomorph s j hj y)).val z =
      (SchemeValuedPoint.spectrumHomeomorph y).val (chartEquiv s j hj z) := by
  rw [nativeHomeomorph_apply, SchemeValuedPoint.spectrumHomeomorph_map]
  rfl

/-- The entire original NATIVE base point triangle commutes. -/
theorem nativeHomeomorph_map_base (s : Finset A) (j : s) (hj : (j : A) ≠ 0)
    (y : SchemeValuedPoint (Spec (CommRingCat.of (blowupChart s (j : A))))) :
    SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom (algebraMap A (Chart s j))))
      (nativeHomeomorph s j hj y) =
    SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom
      (algebraMap A (blowupChart s (j : A))))) y := by
  apply SchemeValuedPoint.spectrumHomeomorph.injective
  rw [SchemeValuedPoint.spectrumHomeomorph_map, SchemeValuedPoint.spectrumHomeomorph_map]
  apply Spectrum.ext_val
  intro a
  change (SchemeValuedPoint.spectrumHomeomorph (nativeHomeomorph s j hj y)).val
    (algebraMap A (Chart s j) a) = _
  rw [nativeHomeomorph_val, chartEquiv_algebraMap]
  rfl

section OriginalCoefficients
variable (k : Type*) [CommRing k] [Algebra k A]

/-- The ACTUAL inherited coefficient action, through the original A action on the Rees chart. -/
@[instance_reducible]
def scalarAlgebra (s : Finset A) (j : s) : Algebra k (Chart s j) :=
  ((algebraMap A (Chart s j)).comp (algebraMap k A)).toAlgebra

private local instance chartScalarAlgebra (s : Finset A) (j : s) : Algebra k (Chart s j) :=
  scalarAlgebra k s j

/-- The original whole base ring map with its ACTUAL inherited k-coefficient action. -/
def baseMap (s : Finset A) (j : s) : A →ₐ[k] Chart s j where
  __ := algebraMap A (Chart s j)
  commutes' _ := rfl

/-- Restrict the SAME whole chart equivalence through ANY actual commutative coefficient ring. -/
def chartEquivScalar (s : Finset A) (j : s) (hj : (j : A) ≠ 0) :
    Chart s j ≃ₐ[k] blowupChart s (j : A) where
  __ := (chartEquiv s j hj).toRingEquiv
  commutes' c := by
    change chartEquiv s j hj (algebraMap A (Chart s j) (algebraMap k A c)) = _
    rw [chartEquiv_algebraMap, ← IsScalarTower.algebraMap_apply k A (blowupChart s (j : A))]

end OriginalCoefficients

section OriginalPaperPoints
variable (k : Type*) [Field k] [Algebra k A]

private local instance paperScalarAlgebra (s : Finset A) (j : s) : Algebra k (Chart s j) :=
  scalarAlgebra k s j

/-- The whole original paper coefficient triangle commutes, on EVERY original A element. -/
theorem chartEquivScalar_comp_base (s : Finset A) (j : s) (hj : (j : A) ≠ 0) :
    (chartEquivScalar k s j hj).toAlgHom.comp (baseMap k s j) =
      chartMap k s (j : A) := by
  apply AlgHom.ext
  intro a
  exact chartEquiv_algebraMap s j hj a

/-- The EXISTING original paper points are transported by the SAME full k-algebra equivalence. -/
def berkHomeomorph (s : Finset A) (j : s) (hj : (j : A) ≠ 0) :
    Berk k (blowupChart s (j : A)) ≃ₜ Berk k (Chart s j) :=
  Berk.algEquivHomeomorph (chartEquivScalar k s j hj)

/-- Every actual original chart element retains its full paper point value. -/
@[simp]
theorem berkHomeomorph_val (s : Finset A) (j : s) (hj : (j : A) ≠ 0)
    (y : Berk k (blowupChart s (j : A))) (z : Chart s j) :
    (berkHomeomorph k s j hj y).val z = y.val (chartEquiv s j hj z) := rfl

/-- The whole old-to-absolute bridge is natural for this ACTUAL entire chart map. -/
@[simp]
theorem berkHomeomorph_toSpectrum (s : Finset A) (j : s) (hj : (j : A) ≠ 0)
    (y : Berk k (blowupChart s (j : A))) :
    Berk.toSpectrum (berkHomeomorph k s j hj y) =
      spectrumHomeomorph s j hj (Berk.toSpectrum y) := rfl

/-- The EXISTING original paper base point is retained as an ENTIRE point. -/
theorem berkHomeomorph_comap_base (s : Finset A) (j : s) (hj : (j : A) ≠ 0)
    (y : Berk k (blowupChart s (j : A))) :
    Berk.comap (baseMap k s j) (berkHomeomorph k s j hj y) =
      Berk.comap (chartMap k s (j : A)) y := by
  apply Berk.ext_val
  intro a
  change y.val (chartEquiv s j hj (algebraMap A (Chart s j) a)) = _
  rw [chartEquiv_algebraMap]
  rfl

/-- Every original paper chartFrac has the value of its genuine Rees coordinate fraction. -/
@[simp]
theorem berkHomeomorph_coordinateRatio (s : Finset A) (j i : s) (hj : (j : A) ≠ 0)
    (y : Berk k (blowupChart s (j : A))) :
    (berkHomeomorph k s j hj y).val (ReesChart.coordinateRatio (family s) j i) =
      y.val (chartFrac s (j : A) i.2) := by
  rw [berkHomeomorph_val, chartEquiv_coordinateRatio]

end OriginalPaperPoints
end EnvelopeProperty.ReesPaper
