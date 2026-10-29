import EnvelopeProperty.Vanishing.RelativeNadelBertiniSnc
import EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamily

/-! # Actual relative auxiliary sections and whole SNC root-cover branches

The original field-smooth finite-type X, original SNC family and original
very-ample lines over an arbitrary original affine R produce all auxiliary
sections, Cartier ideals, whole joined SNC and empty row intersections.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.RelativeNadelAuxiliaryFamily
open NadelBertiniUniversal NadelBertiniFibreSection NadelBertiniAuxiliaryFamilyIndices
  NadelBertiniAuxiliaryFamilyIndexed
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k R : Type u} [Field k] [CharZero k] [CommRing R] {X : Scheme.{u}}

/-- A SAME original relatively very-ample line internally produces a genuine
smooth Cartier section transverse to the whole original SNC family. -/
theorem exists_veryAmple_snc_section
    (p : X ⟶ Spec (.of k)) [Smooth p] [FiniteType p] (π : X ⟶ Spec (.of R))
    (F : X.DivisorFamily) (hF : F.IsSnc) (M : X.Modules)
    (hM : SchemeLineAmpleness.IsVeryAmple π M) :
    ∃ σ : unitObj X ⟶ M,
      (LineSectionZeroIdeal.zeroIdeal M hM.isInvertible σ).IsInvertible ∧
      Smooth ((LineSectionZeroIdeal.zeroIdeal M hM.isInvertible σ).subschemeι ≫ p) ∧
      (F.append (LineSectionZeroIdeal.zeroIdeal M hM.isInvertible σ)).IsSnc ∧
      F.HasSncWith (LineSectionZeroIdeal.zeroIdeal M hM.isInvertible σ) := by
  have hMI := hM.isInvertible
  obtain ⟨m, j, hj, _hjp, ⟨e⟩⟩ := hM
  let : IsClosedImmersion j := hj
  obtain ⟨a, _, hCartier, hSmooth, hSnc, hWith⟩ :=
    RelativeNadelBertiniSnc.exists_relative_projective_snc_selected p j F hF
  let α : unitObj X ⟶ projectiveLine j := SchemeModuleGlobalSections.sectionHom
    (projectiveLine j) (selectedSection p a (projectiveLine j) (projectiveSections j))
  let σ : unitObj X ⟶ M := α ≫ e.hom
  have hEq : RelativeNadelBertiniProjective.selectedIdeal p j a =
      LineSectionZeroIdeal.zeroIdeal M hMI σ :=
    NadelBertiniFibreIdeals.zeroIdeal_iso (projectiveLine j) M
      (RelativeNadelBertiniProjective.lineInvertible j) hMI e α
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · rw [← hEq]; exact hCartier
  · rw [← hEq]; exact hSmooth
  · rw [← hEq]; exact hSnc
  · rw [← hEq]; exact hWith

/-- Finite simultaneous repetition constructs every actual original
relatively very-ample section and proves SNC of their whole finite join. -/
theorem exists_fin_snc_sections
    (p : X ⟶ Spec (.of k)) [Smooth p] [FiniteType p] (π : X ⟶ Spec (.of R))
    (F : X.DivisorFamily) (hF : F.IsSnc) (r : ℕ) :
    ∀ (M : Fin r → X.Modules) (hM : ∀ i, SchemeLineAmpleness.IsVeryAmple π (M i)),
    ∃ σ : ∀ i, unitObj X ⟶ M i,
      (∀ i, (LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i)).IsInvertible ∧
        Smooth ((LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i)).subschemeι ≫ p)) ∧
      (joinedFin F (fun i => LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i))).IsSnc := by
  induction r with
  | zero =>
    intro M hM
    exact ⟨fun i => i.elim0, fun i => i.elim0, joinedFin_zero_isSnc F hF _⟩
  | succ r ih =>
    intro M hM
    obtain ⟨τ, hτ, htail⟩ := ih (fun i => M i.succ) (fun i => hM i.succ)
    let A : Fin r → X.IdealSheafData := fun i =>
      LineSectionZeroIdeal.zeroIdeal (M i.succ) (hM i.succ).isInvertible (τ i)
    obtain ⟨σ₀, hCartier, hSmooth, hAppend, _⟩ :=
      exists_veryAmple_snc_section p π (joinedFin F A) htail (M 0) (hM 0)
    let H := LineSectionZeroIdeal.zeroIdeal (M 0) (hM 0).isInvertible σ₀
    let σ : ∀ i, unitObj X ⟶ M i := Fin.cons σ₀ τ
    refine ⟨σ, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hCartier, hSmooth⟩
      · exact hτ j
    · have hA : (fun i => LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i)) =
          Fin.cons H A := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      rw [hA]
      exact joinedFin_cons_isSnc F A H hAppend

/-- The original finite labels are retained in every actual whole zero ideal. -/
theorem exists_indexed_snc_sections {I : Type u} [Fintype I]
    (p : X ⟶ Spec (.of k)) [Smooth p] [FiniteType p] (π : X ⟶ Spec (.of R))
    (F : X.DivisorFamily) (hF : F.IsSnc)
    (M : I → X.Modules) (hM : ∀ i, SchemeLineAmpleness.IsVeryAmple π (M i)) :
    ∃ σ : ∀ i, unitObj X ⟶ M i,
      (∀ i, (LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i)).IsInvertible ∧
        Smooth ((LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i)).subschemeι ≫ p)) ∧
      (joined F (fun i => LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i))).IsSnc := by
  classical
  let e := Fintype.equivFin I
  let M' : Fin (Fintype.card I) → X.Modules := fun j => M (e.symm j)
  let hM' : ∀ j, SchemeLineAmpleness.IsVeryAmple π (M' j) := fun j => hM (e.symm j)
  obtain ⟨τ, hτ, hSnc⟩ := exists_fin_snc_sections p π F hF (Fintype.card I) M' hM'
  let σ : ∀ i, unitObj X ⟶ M i := fun i =>
    τ (e i) ≫ eqToHom (congrArg M (e.symm_apply_apply i))
  let A : I → X.IdealSheafData := fun i =>
    LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i)
  let B : Fin (Fintype.card I) → X.IdealSheafData := fun j =>
    LineSectionZeroIdeal.zeroIdeal (M' j) (hM' j).isInvertible (τ j)
  have hA : ∀ i, A i = B (e i) := by
    intro i
    exact (NadelBertiniFibreIdeals.zeroIdeal_iso (M' (e i)) (M i)
      (hM' (e i)).isInvertible (hM i).isInvertible
      (eqToIso (congrArg M (e.symm_apply_apply i))) (τ (e i))).symm
  refine ⟨σ, ?_, ?_⟩
  · intro i
    change (A i).IsInvertible ∧ Smooth ((A i).subschemeι ≫ p)
    rw [hA]
    exact hτ (e i)
  · have hAB : (fun j => A (e.symm j)) = B := by
      funext j
      rw [hA, e.apply_symm_apply]
    change (joinedFin F (fun j => A (e.symm j))).IsSnc
    rw [hAB]
    exact hSnc

/-- Genuine relative auxiliary-family Bertini.  Original very ampleness is
over the SAME arbitrary R.  Every whole Cartier ideal, all joined SNC and
every whole empty row intersection are internally produced over the original
characteristic-zero field; no properness over that field is assumed. -/
theorem exists_veryAmple_auxiliary_family {I : Type u} [Fintype I]
    (p : X ⟶ Spec (.of k)) [FiniteType p] (π : X ⟶ Spec (.of R))
    (n : ℕ) [SmoothOfRelativeDimension n p]
    (F : X.DivisorFamily) (hF : F.IsSnc) (M : I → X.Modules)
    (hM : ∀ i, SchemeLineAmpleness.IsVeryAmple π (M i)) :
    ∃ σ : ∀ i, Fin (n + 1) → (unitObj X ⟶ M i),
      (∀ i j, (LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i j)).IsInvertible ∧
        Smooth ((LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i j)).subschemeι ≫ p)) ∧
      (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (fun i j =>
        LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i j))).IsSnc ∧
      ∀ i, (⨆ j, LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i j)) = ⊤ := by
  let : Smooth p := SmoothOfRelativeDimension.smooth n p
  obtain ⟨τ, hτ, hSNC⟩ := exists_indexed_snc_sections (I := I × Fin (n + 1)) p π F hF
    (fun ij => M ij.1) (fun ij => hM ij.1)
  let σ : ∀ i, Fin (n + 1) → (unitObj X ⟶ M i) := fun i j => τ (i, j)
  let A : I → Fin (n + 1) → X.IdealSheafData := fun i j =>
    LineSectionZeroIdeal.zeroIdeal (M i) (hM i).isInvertible (σ i j)
  let B : I × Fin (n + 1) → X.IdealSheafData := fun ij => A ij.1 ij.2
  refine ⟨σ, (fun i j => hτ (i, j)), hSNC, ?_⟩
  intro i
  let v : Fin (n + 1) → (joined F B).ι := fun j => memberIndex F B (i, j)
  have hv : Function.Injective v := by
    intro j j' h
    exact congrArg Prod.snd (memberIndex_injective F B h)
  have hzero := NadelBertiniAuxiliaryFamilyDimension.sum_eq_top_of_injective_succ
    p n (joined F B) hSNC v hv
  have hcomp : (⨆ j, (joined F B).component (v j)) = ⨆ j, A i j :=
    iSup_congr (fun j => component_memberIndex F B (i, j))
  rw [hcomp] at hzero
  exact hzero

end EnvelopeProperty.Vanishing.RelativeNadelAuxiliaryFamily
