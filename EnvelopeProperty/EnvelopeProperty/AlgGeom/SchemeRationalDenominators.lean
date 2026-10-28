import EnvelopeProperty.Algebra.RationalDenominatorIdeals
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal

/-! # Denominator ideals on the same original integral scheme -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
namespace EnvelopeProperty.SchemeRationalDenominators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open RationalDenominatorIdeals
variable (X : Scheme.{u}) [IsIntegral X]

/-- The denominator ideal in the original affine section ring, embedded by
its original generic germ into the same original function field. -/
def affineIdeal (f : X.functionField) (U : X.affineOpens) : Ideal Γ(X, U) := by
  classical
  exact if h : Nonempty U.1 then
    letI := h
    denominatorIdeal Γ(X, U) X.functionField f
  else ⊤

/-- On a nonempty affine open the ideal has its literal original clearing identity. -/
theorem affineIdeal_eq (f : X.functionField) (U : X.affineOpens) [Nonempty U.1] :
    affineIdeal X f U = denominatorIdeal Γ(X, U) X.functionField f := by
  rw [affineIdeal, dif_pos (inferInstance : Nonempty U.1)]

private theorem basicOpen_scalarTower (U : X.Opens) [Nonempty U]
    (s : Γ(X, U)) [Nonempty (X.basicOpen s)] :
    IsScalarTower Γ(X, U) Γ(X, X.basicOpen s) X.functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  ext a
  exact (X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le s))
    (genericPoint X) (((genericPoint_spec X).mem_open_set_iff (X.basicOpen s).isOpen).mpr
      (by simpa using (inferInstance : Nonempty (X.basicOpen s)))) a).symm

/-- Genuine original basic-open localization of the same denominator ideals. -/
theorem affineIdeal_basicOpen (f : X.functionField) (U : X.affineOpens)
    (s : Γ(X, U)) :
    (affineIdeal X f U).map (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom =
      affineIdeal X f (X.affineBasicOpen s) := by
  by_cases h : Nonempty (X.basicOpen s)
  · let := h
    let : Nonempty ((X.affineBasicOpen s).1) := h
    let : Nonempty U.1 := Nonempty.map (fun x => ⟨x.val, X.basicOpen_le s x.property⟩) h
    let := basicOpen_scalarTower X U.1 s
    let := U.2.isLocalization_basicOpen s
    rw [affineIdeal_eq, affineIdeal_eq]
    exact denominatorIdeal_map Γ(X, U) X.functionField Γ(X, X.basicOpen s)
      (Submonoid.powers s) f
  · have he : X.basicOpen s = ⊥ := by
      apply SetLike.ext
      intro x
      simp only [Opens.mem_bot, iff_false]
      exact fun hx => h ⟨⟨x, hx⟩⟩
    let : Subsingleton Γ(X, X.basicOpen s) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty he)
    apply le_antisymm <;> intro a ha
    · rw [Subsingleton.elim a 0]
      exact Ideal.zero_mem _
    · rw [Subsingleton.elim a 0]
      exact Ideal.zero_mem _

/-- The actual denominator ideal sheaf of an arbitrary original rational
function. Its affine ideals are glued by genuine original localization. -/
def idealSheaf (f : X.functionField) : X.IdealSheafData where
  ideal := affineIdeal X f
  map_ideal_basicOpen := affineIdeal_basicOpen X f

/-- Exact original affine section ideal of the constructed denominator sheaf. -/
theorem idealSheaf_ideal (f : X.functionField) (U : X.affineOpens) [Nonempty U.1] :
    (idealSheaf X f).ideal U = denominatorIdeal Γ(X, U) X.functionField f :=
  affineIdeal_eq X f U

/-- Every nonempty original affine chart has a genuinely nonzero denominator ideal. -/
theorem idealSheaf_ideal_ne_bot (f : X.functionField) (U : X.affineOpens) [Nonempty U.1] :
    (idealSheaf X f).ideal U ≠ ⊥ := by
  let := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  rw [idealSheaf_ideal]
  exact denominatorIdeal_ne_bot Γ(X, U) X.functionField f


/-- The SAME original denominator ideal at every original stalk, with the
actual original stalk-to-function-field map. -/
theorem stalkIdeal_eq (f : X.functionField) (x : X) :
    (idealSheaf X f).stalkIdeal x =
      denominatorIdeal (X.presheaf.stalk x) X.functionField f := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (U := ⊤) (x := x) (by trivial)
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  let := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  let := hU.isLocalization_stalk (⟨x, hx⟩ : U)
  let := functionField_isScalarTower X U (⟨x, hx⟩ : U)
  rw [(idealSheaf X f).stalkIdeal_eq_map_germ ⟨U, hU⟩ hx, idealSheaf_ideal]
  exact denominatorIdeal_map Γ(X, U) X.functionField (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl f

/-- Every original denominator stalk is nonzero, DERIVED from the SAME
original function field's actual fraction presentation. -/
theorem stalkIdeal_ne_bot (f : X.functionField) (x : X) :
    (idealSheaf X f).stalkIdeal x ≠ ⊥ := by
  rw [stalkIdeal_eq]
  exact denominatorIdeal_ne_bot (X.presheaf.stalk x) X.functionField f

end EnvelopeProperty.SchemeRationalDenominators
