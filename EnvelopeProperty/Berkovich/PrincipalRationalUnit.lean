/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumLocalization
import EnvelopeProperty.Berkovich.SchemeSectionLogs
import EnvelopeProperty.Berkovich.SchemeRelativeValuedPoints
import EnvelopeProperty.Berkovich.SchemeOpenImmersion
import Mathlib.AlgebraicGeometry.Restrict

/-! # The ORIGINAL rational unit on the actual principal open D(pq) -/
open scoped NNReal ENNReal Topology
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace EnvelopeProperty.Berkovich.PrincipalRationalUnit
variable {A : Type*} [CommRing A]

private theorem isUnit_left (p q : A) : IsUnit (algebraMap A (Localization.Away (p*q)) p) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p*q)) (p*q)
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_left h

private theorem isUnit_right (p q : A) : IsUnit (algebraMap A (Localization.Away (p*q)) q) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p*q)) (p*q)
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_right h

/-- The ORIGINAL factor becomes a true unit in the literal product localization. -/
def leftUnit (p q : A) : (Localization.Away (p*q))ˣ := (isUnit_left p q).unit

/-- The ORIGINAL denominator becomes a true unit in that SAME literal localization. -/
def rightUnit (p q : A) : (Localization.Away (p*q))ˣ := (isUnit_right p q).unit

@[simp]
theorem coe_leftUnit (p q : A) : (leftUnit p q : Localization.Away (p*q)) = algebraMap A _ p :=
  (isUnit_left p q).unit_spec

@[simp]
theorem coe_rightUnit (p q : A) : (rightUnit p q : Localization.Away (p*q)) = algebraMap A _ q :=
  (isUnit_right p q).unit_spec

/-- The actual ORIGINAL quotient is a genuine unit; no rational-function representative is assumed. -/
def ratioUnit (p q : A) : (Localization.Away (p*q))ˣ := leftUnit p q * (rightUnit p q)⁻¹

/-- EVERY original point of D(pq) evaluates the SAME actual unit as the original factor quotient. -/
theorem lift_val_ratioUnit (p q : A) (x : Spectrum A) (hx : x.val (p*q) ≠ 0) :
    (Spectrum.Away.lift (Localization.Away (p*q)) (p*q) x hx).val (ratioUnit p q) =
      x.val p / x.val q := by
  let y := Spectrum.Away.lift (Localization.Away (p*q)) (p*q) x hx
  have hp : y.val (leftUnit p q) = x.val p := by
    rw [coe_leftUnit]
    exact Spectrum.Away.lift_val_algebraMap _ _ _ _ _
  have hq : y.val (rightUnit p q) = x.val q := by
    rw [coe_rightUnit]
    exact Spectrum.Away.lift_val_algebraMap _ _ _ _ _
  have hi : y.val ((rightUnit p q)⁻¹ : (Localization.Away (p*q))ˣ) = (x.val q)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc
      _ = y.val (↑((rightUnit p q)⁻¹) * ↑(rightUnit p q)) := by rw [map_mul, hq]
      _ = 1 := by rw [Units.inv_mul, map_one]
  change y.val (↑(leftUnit p q) * ↑((rightUnit p q)⁻¹)) = _
  rw [map_mul, hp, hi, div_eq_mul_inv]

/-- The genuine original unit logarithm is the SAME original all-point logarithmic difference. -/
theorem lift_logAbs_ratioUnit (p q : A) (x : Spectrum A) (hx : x.val (p*q) ≠ 0) :
    Spectrum.logAbs (ratioUnit p q : Localization.Away (p*q))
      (Spectrum.Away.lift (Localization.Away (p*q)) (p*q) x hx) =
      Spectrum.logAbs p x - Spectrum.logAbs q x := by
  have hq : x.val q ≠ 0 := by
    intro h
    exact hx (by rw [map_mul, h, mul_zero])
  rw [Spectrum.logAbs, lift_val_ratioUnit, ENNReal.coe_div hq, div_eq_mul_inv,
    ENNReal.log_mul_add, ENNReal.log_inv]
  rfl

/-- This SAME literal localization is the ACTUAL principal-open scheme, with no chart certificate. -/
def principalOpenIso (p q : A) :
    Scheme.Opens.toScheme (X := Spec (CommRingCat.of A)) (PrimeSpectrum.basicOpen (p*q)) ≅
      Spec (CommRingCat.of (Localization.Away (p*q))) :=
  basicOpenIsoSpecAway (R := CommRingCat.of A) (p*q)

/-- The whole original structure map is retained through the actual principal-open identification. -/
theorem principalOpenIso_hom_projection (p q : A) :
    (principalOpenIso p q).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (p*q)))) =
      Scheme.Opens.ι (X := Spec (CommRingCat.of A)) (PrimeSpectrum.basicOpen (p*q)) :=
  basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of A) (p*q)

/-- The genuine original principal localization projection. -/
abbrev projection (p q : A) : Spec (CommRingCat.of (Localization.Away (p*q))) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (p*q))))

/-- The ACTUAL original principal open, expressed as the whole open-immersion image. -/
def ratioOpen (p q : A) : (Spec (CommRingCat.of A)).Opens := projection p q ''ᵁ ⊤

/-- The entire open is EXACTLY D(pq), including empty and nilpotent cases. -/
theorem ratioOpen_eq_basicOpen (p q : A) : ratioOpen p q = PrimeSpectrum.basicOpen (p*q) := by
  rw [ratioOpen, Scheme.Hom.image_top_eq_opensRange]
  exact Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of A) (p*q)

/-- The literal quotient is a genuine ORIGINAL regular-section unit on D(pq). -/
def sectionUnit (p q : A) : Γ(Spec (CommRingCat.of A), ratioOpen p q)ˣ :=
  Units.map ((projection p q).appIso ⊤).inv.hom.toMonoidHom
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (p*q)))).inv.hom.toMonoidHom (ratioUnit p q))

/-- The true localization native lift projects to the ENTIRE original point. -/
theorem map_nativeLift (p q : A) (x : Spectrum A) (hx : x.val (p*q) ≠ 0) :
    SchemeValuedPoint.map (projection p q)
      (SchemeValuedPoint.spectrumHomeomorph.symm
        (Spectrum.Away.lift (Localization.Away (p*q)) (p*q) x hx)) =
      SchemeValuedPoint.spectrumHomeomorph.symm x := by
  apply SchemeValuedPoint.spectrumHomeomorph.injective
  rw [SchemeValuedPoint.spectrumHomeomorph_map, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]
  exact Spectrum.Away.comap_lift _ _ _ _

/-- EVERY original point of D(pq) has its true support in that SAME regular-section open. -/
theorem nativePoint_mem_ratioOpen (p q : A) (x : Spectrum A) (hx : x.val (p*q) ≠ 0) :
    (SchemeValuedPoint.spectrumHomeomorph.symm x).point ∈ ratioOpen p q := by
  rw [← map_nativeLift p q x hx]
  exact Set.mem_image_of_mem (projection p q) (show _ ∈ (⊤ : (Spec (CommRingCat.of
    (Localization.Away (p*q)))).Opens) from trivial)

/-- The actual original section unit retains its WHOLE original all-point quotient evaluation. -/
theorem eval_sectionUnit (p q : A) (x : Spectrum A) (hx : x.val (p*q) ≠ 0) :
    SchemeValuedPoint.eval (SchemeValuedPoint.spectrumHomeomorph.symm x) (ratioOpen p q)
      (nativePoint_mem_ratioOpen p q x hx) (sectionUnit p q) = x.val p / x.val q := by
  let y := SchemeValuedPoint.spectrumHomeomorph.symm
    (Spectrum.Away.lift (Localization.Away (p*q)) (p*q) x hx)
  have he := SchemeValuedPoint.eval_map_appIso_inv (projection p q) y ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (p*q)))).inv (ratioUnit p q))
  have hp : (⟨SchemeValuedPoint.map (projection p q) y,
      Set.mem_image_of_mem (projection p q) (show y.point ∈ (⊤ : (Spec (CommRingCat.of
        (Localization.Away (p*q)))).Opens) from trivial)⟩ :
      {z : SchemeValuedPoint (Spec (CommRingCat.of A)) // z.point ∈ ratioOpen p q}) =
      ⟨SchemeValuedPoint.spectrumHomeomorph.symm x, nativePoint_mem_ratioOpen p q x hx⟩ :=
    Subtype.ext (map_nativeLift p q x hx)
  have he' := congrArg (fun z : {z : SchemeValuedPoint (Spec (CommRingCat.of A)) //
      z.point ∈ ratioOpen p q} => SchemeValuedPoint.eval z.1 (ratioOpen p q) z.2 (sectionUnit p q)) hp
  calc
    _ = SchemeValuedPoint.eval (SchemeValuedPoint.map (projection p q) y) (ratioOpen p q)
        (Set.mem_image_of_mem (projection p q) trivial) (sectionUnit p q) := he'.symm
    _ = _ := he
    _ = _ := by
      rw [← SchemeValuedPoint.spectrumHomeomorph_val_apply, Homeomorph.apply_symm_apply]
      exact lift_val_ratioUnit p q x hx

/-- On the ACTUAL original principal open the genuine section log is exactly log|p|−log|q|. -/
theorem sectionLogAbs_sectionUnit (p q : A) (x : Spectrum A) (hx : x.val (p*q) ≠ 0) :
    SchemeValuedPoint.sectionLogAbs (ratioOpen p q) (sectionUnit p q)
      (SchemeValuedPoint.spectrumHomeomorph.symm x) = Spectrum.logAbs p x - Spectrum.logAbs q x := by
  rw [SchemeValuedPoint.sectionLogAbs_of_mem _ _ _ (nativePoint_mem_ratioOpen p q x hx),
    eval_sectionUnit p q x hx]
  rw [← lift_val_ratioUnit p q x hx]
  exact lift_logAbs_ratioUnit p q x hx

end EnvelopeProperty.Berkovich.PrincipalRationalUnit
