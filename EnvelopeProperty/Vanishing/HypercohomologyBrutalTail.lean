import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.Single
import Mathlib.Tactic

/-! # Actual brutal tails and their consecutive short exact sequences

The differential is the original differential wherever both terms survive.
All inclusions and projections are constructed, not supplied as filtration data.
-/

open CategoryTheory CategoryTheory.Limits ZeroObject

noncomputable section
universe u v

namespace EnvelopeProperty.Vanishing.HypercohomologyBrutalTail

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The original term in degrees at least the cutoff, and the zero object below it. -/
def term (K : CochainComplex C ℤ) (a i : ℤ) : C :=
  if a ≤ i then K.X i else 0

/-- The surviving original differential, with zero source or target otherwise. -/
def differential (K : CochainComplex C ℤ) (a i j : ℤ) : term K a i ⟶ term K a j :=
  if hi : a ≤ i then
    if hj : a ≤ j then
      eqToHom (by simp only [term, if_pos hi]) ≫ K.d i j ≫
        eqToHom (by simp only [term, if_pos hj])
    else 0
  else 0

/-- The brutal tail of the actual original cochain complex. -/
def tail (K : CochainComplex C ℤ) (a : ℤ) : CochainComplex C ℤ where
  X := term K a
  d := differential K a
  shape i j hij := by
    unfold differential
    split_ifs <;> simp [K.shape i j hij]
  d_comp_d' i j k _ _ := by
    unfold differential
    split_ifs <;> simp [Category.assoc]

/-- The original term comparison above the cutoff. -/
def termIso (K : CochainComplex C ℤ) (a i : ℤ) (hi : a ≤ i) :
    (tail K a).X i ≅ K.X i :=
  eqToIso (by simp only [tail, term, if_pos hi])

/-- Below the cutoff the actual brutal-tail term is zero. -/
theorem isZero_term (K : CochainComplex C ℤ) (a i : ℤ) (hi : i < a) :
    IsZero ((tail K a).X i) := by
  dsimp [tail, term]
  rw [if_neg (by omega)]
  exact isZero_zero C

/-- The actual surviving differential through the original term comparisons. -/
theorem differential_eq (K : CochainComplex C ℤ) (a i j : ℤ)
    (hi : a ≤ i) (hj : a ≤ j) :
    (tail K a).d i j =
      (termIso K a i hi).hom ≫ K.d i j ≫ (termIso K a j hj).inv := by
  simp only [tail, differential, dif_pos hi, dif_pos hj, termIso]
  rfl

/-- The inclusion of one actual brutal tail into the original complex. -/
def inclusion (K : CochainComplex C ℤ) (a : ℤ) : tail K a ⟶ K where
  f i := if hi : a ≤ i then (termIso K a i hi).hom else 0
  comm' i j hij := by
    by_cases hi : a ≤ i
    · have hj : a ≤ j := by
        have : i + 1 = j := hij
        omega
      simp only [dif_pos hi, dif_pos hj, differential_eq K a i j hi hj,
        Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · by_cases hj : a ≤ j
      · simp only [dif_neg hi, dif_pos hj, zero_comp]
        exact (isZero_term K a i (by omega)).eq_of_src _ _
      · simp only [dif_neg hi, dif_neg hj, zero_comp, comp_zero]

/-- The inclusion between consecutive actual brutal tails. -/
def stepInclusion (K : CochainComplex C ℤ) (a : ℤ) : tail K (a + 1) ⟶ tail K a where
  f i := if hi : a + 1 ≤ i then
    (termIso K (a + 1) i hi).hom ≫ (termIso K a i (by omega)).inv else 0
  comm' i j hij := by
    by_cases hi : a + 1 ≤ i
    · have hj : a + 1 ≤ j := by
        have : i + 1 = j := hij
        omega
      simp only [dif_pos hi, dif_pos hj,
        differential_eq K (a + 1) i j hi hj,
        differential_eq K a i j (by omega) (by omega), Category.assoc,
        Iso.inv_hom_id_assoc]
    · by_cases hj : a + 1 ≤ j
      · simp only [dif_neg hi, dif_pos hj, zero_comp]
        exact (isZero_term K (a + 1) i (by omega)).eq_of_src _ _
      · simp only [dif_neg hi, dif_neg hj, zero_comp, comp_zero]

/-- The degree-cutoff quotient onto the actual original single-term complex. -/
def projection (K : CochainComplex C ℤ) (a : ℤ) :
    tail K a ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) a).obj (K.X a) where
  f i := if hi : i = a then
    (termIso K a i (by omega)).hom ≫ (K.XIsoOfEq hi).hom ≫
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) a (K.X a) i hi).inv
    else 0
  comm' i j hij := by
    rw [HomologicalComplex.single_obj_d, comp_zero]
    by_cases hj : j = a
    · have hi : i < a := by
        have : i + 1 = j := hij
        omega
      exact (isZero_term K a i hi).eq_of_src _ _
    · simp only [dif_neg hj, comp_zero]

/-- The consecutive-tail inclusion followed by its quotient is zero. -/
theorem stepInclusion_projection (K : CochainComplex C ℤ) (a : ℤ) :
    stepInclusion K a ≫ projection K a = 0 := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = a
  · subst i
    simp [stepInclusion, projection]
  · simp [projection, hi]

/-- The actual consecutive-tail short complex. -/
def sequence (K : CochainComplex C ℤ) (a : ℤ) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (stepInclusion K a) (projection K a) (stepInclusion_projection K a)

/-- The actual consecutive-tail sequence is short exact, as verified in
each degree of the original complex. -/
theorem sequence_shortExact (K : CochainComplex C ℤ) (a : ℤ) :
    (sequence K a).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  let S := (sequence K a).map (HomologicalComplex.eval C (ComplexShape.up ℤ) i)
  change S.ShortExact
  by_cases hi : i = a
  · subst i
    have hfirst : IsZero S.X₁ := isZero_term K (a + 1) a (by omega)
    have hg : IsIso S.g := by
      change IsIso ((projection K a).f a)
      dsimp only [projection]
      rw [dif_pos rfl]
      infer_instance
    let := hg
    exact {
      exact := (S.exact_iff_mono (hfirst.eq_of_src _ 0)).mpr inferInstance
      mono_f := hfirst.mono _
      epi_g := inferInstance }
  · have hlast : IsZero S.X₃ :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (K.X a) i hi
    by_cases hia : i < a
    · have hfirst : IsZero S.X₁ := isZero_term K (a + 1) i (by omega)
      have hmiddle : IsZero S.X₂ := isZero_term K a i hia
      exact {
        exact := S.exact_of_isZero_X₂ hmiddle
        mono_f := hfirst.mono _
        epi_g := hlast.epi _ }
    · have hf : IsIso S.f := by
        change IsIso ((stepInclusion K a).f i)
        dsimp only [stepInclusion]
        rw [dif_pos (show a + 1 ≤ i by omega)]
        infer_instance
      let := hf
      exact {
        exact := (S.exact_iff_epi (hlast.eq_of_tgt _ 0)).mpr inferInstance
        mono_f := inferInstance
        epi_g := hlast.epi _ }

/-- An actual brutal tail whose surviving original terms are all zero is
itself the zero object in the category of complexes. -/
theorem isZero_tail (K : CochainComplex C ℤ) (a : ℤ)
    (h : ∀ i : ℤ, a ≤ i → IsZero (K.X i)) : IsZero (tail K a) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext i
  by_cases hi : a ≤ i
  · exact ((h i hi).of_iso (termIso K a i hi)).eq_of_src _ _
  · exact (isZero_term K a i (by omega)).eq_of_src _ _

/-- If the original complex is zero below the cutoff, the actual tail
inclusion is an isomorphism of whole original complexes. -/
def inclusionIso (K : CochainComplex C ℤ) (a : ℤ)
    (h : ∀ i : ℤ, i < a → IsZero (K.X i)) : tail K a ≅ K := by
  have (i : ℤ) : IsIso ((inclusion K a).f i) := by
    by_cases hi : a ≤ i
    · dsimp only [inclusion]
      rw [dif_pos hi]
      infer_instance
    · exact (isZero_term K a i (by omega)).isIso (h i (by omega)) _
  let : IsIso (inclusion K a) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (inclusion K a)

end EnvelopeProperty.Vanishing.HypercohomologyBrutalTail
