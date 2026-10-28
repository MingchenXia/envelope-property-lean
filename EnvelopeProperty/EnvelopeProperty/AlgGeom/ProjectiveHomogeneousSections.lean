import EnvelopeProperty.AlgGeom.SchemeModuleFrameGluing
import EnvelopeProperty.AlgGeom.SchemeModuleGlobalSections
import ModularCurves.EllipticCurve.ProjectiveSpaceTwist

/-! # Actual original homogeneous forms as global sections of native O(d) -/

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open scoped Classical
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveHomogeneousSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ORIGINAL homogeneous fraction F/X_i^d on its original entire affine chart. -/
def fraction (i : σ) (d : ℕ) (F : MvPolynomial σ R) (hF : F.IsHomogeneous d) :
    Away (homogeneousSubmodule σ R) (X i) :=
  Away.mk (homogeneousSubmodule σ R) (isHomogeneous_X R i) d F (by simpa using hF)

/-- The ORIGINAL homogeneous fraction is an actual WHOLE original scheme section. -/
def coefficient (i : σ) (d : ℕ) (F : MvPolynomial σ R) (hF : F.IsHomogeneous d) :
    Γ(Proj (homogeneousSubmodule σ R), coordinateOpen (R := R) i) :=
  (Proj.awayToSection (homogeneousSubmodule σ R) (X i)).hom (fraction i d F hF)

private def leftMap (i k : σ) : Away (homogeneousSubmodule σ R) (X i) →+*
    Away (homogeneousSubmodule σ R) (X i * X k) :=
  awayMap (homogeneousSubmodule σ R) (isHomogeneous_X R k) rfl

private def rightMap (i k : σ) : Away (homogeneousSubmodule σ R) (X k) →+*
    Away (homogeneousSubmodule σ R) (X i * X k) :=
  awayMap (homogeneousSubmodule σ R) (isHomogeneous_X R i) (mul_comm _ _)

/-- The original whole homogeneous fractions have their exact original
O(d) scalar transition on EVERY original scheme overlap. -/
theorem fraction_overlap (i k : σ) (d : ℕ) (F : MvPolynomial σ R)
    (hF : F.IsHomogeneous d) :
    leftMap i k (fraction i d F hF) =
      leftMap i k (fraction i 1 (X k) (isHomogeneous_X R k)) ^ d *
        rightMap i k (fraction k d F hF) := by
  apply HomogeneousLocalization.val_injective
  simp only [leftMap, rightMap, fraction, awayMap_mk, val_mul, val_pow, Away.val_mk]
  rw [Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow,
    pow_one, mul_pow]
  ring

/-- The degree-one ORIGINAL homogeneous fraction is the LITERAL original
coordinate-hyperplane local equation, including the self-coordinate case. -/
theorem coefficient_X (i k : σ) :
    coefficient i 1 (X k) (isHomogeneous_X R k) =
      coordinateHyperplaneLocalEquation (R := R) i k := by
  rw [coordinateHyperplaneLocalEquation_eq_isLocalizationElem]
  simp [coefficient, fraction, Away.isLocalizationElem, Proj.basicOpenIsoAway]

private theorem coefficient_restrict_left (i k : σ) (d : ℕ)
    (F : MvPolynomial σ R) (hF : F.IsHomogeneous d) :
    (Proj (homogeneousSubmodule σ R)).presheaf.map
      (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op (coefficient i d F hF) =
    (Proj.awayToSection (homogeneousSubmodule σ R) (X i * X k)).hom
      (leftMap i k (fraction i d F hF)) := by
  have h := Proj.awayMap_awayToSection (homogeneousSubmodule σ R)
    (isHomogeneous_X R k) (rfl : X i * X k = X i * X k)
  exact (congrArg (fun q => q.hom (fraction i d F hF)) h).symm

private theorem coefficient_restrict_right (i k : σ) (d : ℕ)
    (F : MvPolynomial σ R) (hF : F.IsHomogeneous d) :
    (Proj (homogeneousSubmodule σ R)).presheaf.map
      (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op (coefficient k d F hF) =
    (Proj.awayToSection (homogeneousSubmodule σ R) (X i * X k)).hom
      (rightMap i k (fraction k d F hF)) := by
  have h := Proj.awayMap_awayToSection (homogeneousSubmodule σ R)
    (isHomogeneous_X R i) (mul_comm (X i) (X k))
  exact (congrArg (fun q => q.hom (fraction k d F hF)) h).symm

/-- EVERY actual original homogeneous form has the exact native O(d) scalar
transition on the WHOLE original overlap, as equality of actual scheme sections. -/
theorem coefficient_overlap (i k : σ) (d : ℕ) (F : MvPolynomial σ R)
    (hF : F.IsHomogeneous d) :
    (Proj (homogeneousSubmodule σ R)).presheaf.map
      (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op (coefficient i d F hF) =
      (coordinateOpenTransitionUnit (R := R) i k :
        Γ(Proj (homogeneousSubmodule σ R), coordinateOpenOverlap (R := R) i k)) ^ d *
      (Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op (coefficient k d F hF) := by
  change _ = ((Proj (homogeneousSubmodule σ R)).presheaf.map
    (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
    (coordinateHyperplaneLocalEquation (R := R) i k)) ^ d * _
  rw [← coefficient_X, coefficient_restrict_left, coefficient_restrict_left,
    coefficient_restrict_right, ← map_pow, ← map_mul, fraction_overlap]

/-- An ORIGINAL homogeneous form times the ACTUAL original O(d) frame gives
its genuine whole original local line section. -/
def localSection (i j : σ) (d : ℕ) (F : MvPolynomial σ R) (hF : F.IsHomogeneous d) :
    Γ(coordinateHyperplanePoleSheafPower (R := R) j d, coordinateOpen (R := R) i) :=
  coefficient i d F hF • coordinateHyperplanePoleSheafPowerFrameSection (R := R) i j d

/-- The ACTUAL original local line sections of EVERY original homogeneous
form agree on every entire original coordinate overlap. -/
theorem localSection_overlap (i k j : σ) (d : ℕ) (F : MvPolynomial σ R)
    (hF : F.IsHomogeneous d) :
    (coordinateHyperplanePoleSheafPower (R := R) j d).presheaf.map
      (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op (localSection i j d F hF) =
    (coordinateHyperplanePoleSheafPower (R := R) j d).presheaf.map
      (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op (localSection k j d F hF) := by
  let M := coordinateHyperplanePoleSheafPower (R := R) j d
  rw [localSection, localSection, M.map_smul, M.map_smul,
    coefficient_overlap, mul_comm (_ ^ d), mul_smul,
    coordinateHyperplanePoleSheafPowerFrameSection_restrict_transition]

private theorem overlap_compatibility {P : Scheme.{u}} (M : P.Modules)
    (U V W : P.Opens) (hW : W = U ⊓ V) (hU : W ≤ U) (hV : W ≤ V)
    (s : Γ(M, U)) (t : Γ(M, V))
    (h : M.presheaf.map (homOfLE hU).op s = M.presheaf.map (homOfLE hV).op t) :
    M.presheaf.map (TopologicalSpace.Opens.infLELeft U V).op s =
      M.presheaf.map (TopologicalSpace.Opens.infLERight U V).op t := by
  subst W
  exact h

/-- Genuine original sheaf gluing constructs a global section of the ACTUAL
original O(d) from EVERY original homogeneous polynomial; no section certificate is supplied. -/
theorem exists_section (j : σ) (d : ℕ) (F : MvPolynomial σ R) (hF : F.IsHomogeneous d) :
    ∃ s : Γ(coordinateHyperplanePoleSheafPower (R := R) j d, ⊤), ∀ i : σ,
      (coordinateHyperplanePoleSheafPower (R := R) j d).presheaf.map
        (homOfLE (le_top : coordinateOpen (R := R) i ≤ ⊤)).op s = localSection i j d F hF := by
  let M := coordinateHyperplanePoleSheafPower (R := R) j d
  let U : σ → (Proj (homogeneousSubmodule σ R)).Opens := coordinateOpen (R := R)
  have hcover : (⊤ : (Proj (homogeneousSubmodule σ R)).Opens) ≤ iSup U := by
    rw [show iSup U = ⊤ from iSup_coordinateOpen_eq_top (R := R)]
  have hcpt : ∀ i k, M.presheaf.map (TopologicalSpace.Opens.infLELeft (U i) (U k)).op
      (localSection i j d F hF) =
        M.presheaf.map (TopologicalSpace.Opens.infLERight (U i) (U k)).op
          (localSection k j d F hF) := by
    intro i k
    exact overlap_compatibility M (U i) (U k) (coordinateOpenOverlap (R := R) i k)
      (coordinateOpenOverlap_eq (R := R) i k)
      (coordinateOpenOverlap_le_left (R := R) i k)
      (coordinateOpenOverlap_le_right (R := R) i k)
      _ _ (localSection_overlap i k j d F hF)
  obtain ⟨s, hs, _⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩ U ⊤
    (fun _ => homOfLE le_top) hcover (fun i => localSection i j d F hF) hcpt
  exact ⟨s, hs⟩

/-- The global ACTUAL original O(d) section of the ORIGINAL homogeneous form. -/
def homogeneousSection (j : σ) (d : ℕ) (F : MvPolynomial σ R) (hF : F.IsHomogeneous d) :
    Γ(coordinateHyperplanePoleSheafPower (R := R) j d, ⊤) :=
  (exists_section j d F hF).choose

/-- Every whole original coordinate restriction of the genuine global section
is EXACTLY F/X_i^d times the ACTUAL original O(d) frame. -/
theorem section_restrict (i j : σ) (d : ℕ) (F : MvPolynomial σ R) (hF : F.IsHomogeneous d) :
    (coordinateHyperplanePoleSheafPower (R := R) j d).presheaf.map
      (homOfLE (le_top : coordinateOpen (R := R) i ≤ ⊤)).op (homogeneousSection j d F hF) =
        localSection i j d F hF :=
  (exists_section j d F hF).choose_spec i

private theorem coefficient_smul_frame {P : Scheme.{u}} (M : P.Modules) (U : P.Opens)
    (e : M.over U ≅ SheafOfModules.unit (P.ringCatSheaf.over U)) (c : Γ(P, U)) :
    e.hom.val.app (.op (Over.mk (𝟙 U)))
      (c • ModularCurves.overTrivializationSection M U e 1) = c := by
  have h := (e.hom.val.app (.op (Over.mk (𝟙 U)))).hom.map_smul c
    (ModularCurves.overTrivializationSection M U e 1)
  rw [ModularCurves.overTrivializationSection_coefficient] at h
  exact h.trans (mul_one c)

private theorem coefficient_of_restrict {P : Scheme.{u}} (M : P.Modules) (U : P.Opens)
    (e : M.over U ≅ SheafOfModules.unit (P.ringCatSheaf.over U))
    (s : Γ(M, ⊤)) (c : Γ(P, U))
    (hs : M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s =
      c • ModularCurves.overTrivializationSection M U e 1) :
    ModularCurves.overTrivializationCoefficient M U e s = c := by
  exact (congrArg (fun z : Γ(M, U) => e.hom.val.app (.op (Over.mk (𝟙 U))) z) hs).trans
    (coefficient_smul_frame M U e c)

/-- The actual ORIGINAL line-frame coefficient of the genuine global
homogeneous section is EXACTLY the ORIGINAL whole scheme fraction F/X_i^d. -/
theorem section_coefficient (i j : σ) (d : ℕ) (F : MvPolynomial σ R)
    (hF : F.IsHomogeneous d) :
    ModularCurves.overTrivializationCoefficient
      (coordinateHyperplanePoleSheafPower (R := R) j d) (coordinateOpen (R := R) i)
      (Scheme.Modules.overTrivializationOfRestrictIso
        (coordinateHyperplanePoleSheafPower (R := R) j d) (coordinateOpen (R := R) i)
        (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j d))
      (homogeneousSection j d F hF) = coefficient i d F hF := by
  exact coefficient_of_restrict _ _ _ _ _ (section_restrict i j d F hF)

/-- The ORIGINAL homogeneous form defines a genuine morphism from the
ORIGINAL whole structure line to the ACTUAL original O(d). -/
def sectionHom (j : σ) (d : ℕ) (F : MvPolynomial σ R) (hF : F.IsHomogeneous d) :
    Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)) ⟶
      coordinateHyperplaneTwist (R := R) j (d : ℤ) :=
  SchemeModuleGlobalSections.sectionHom _ (homogeneousSection j d F hF)

end EnvelopeProperty.ProjectiveHomogeneousSections
