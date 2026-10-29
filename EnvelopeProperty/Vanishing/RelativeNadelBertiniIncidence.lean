import EnvelopeProperty.Vanishing.RelativeNadelBertiniGenericOpen
import EnvelopeProperty.Vanishing.NadelBertiniGlobalSmooth
import EnvelopeProperty.Vanishing.NadelBertiniRationalParameterIncidence
import Mathlib.AlgebraicGeometry.Noetherian
import Hironaka.Scheme.FiniteType

/-! # Actual nonproper Bertini incidence from the original section system

The original finite section system and its normalized local generator frames
produce the whole smooth incidence and a rational good parameter.  Relative
projective coordinate sections over an arbitrary original coefficient ring
give such frames without making X proper over the original field.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.RelativeNadelBertiniIncidence
open NadelBertiniUniversal NadelBertiniRestrictionCover SchemeLineSectionEvaluation
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}}

/-- The parameter projection of the actual incidence is finite type whenever
the original source is finite type over the original field. -/
instance toParameters_finiteType (p : X ⟶ Spec (.of k)) [FiniteType p]
    (L : X.Modules) (hL : IsInvertible L) (s : Fin (m + 1) → Γ(L, ⊤)) :
    FiniteType (toParameters p L hL s) := by
  unfold toParameters
  infer_instance

/-- The actual incidence is Noetherian from original field finite type,
including compactness from the finite-type parameter projection. -/
instance incidence_isNoetherian (p : X ⟶ Spec (.of k)) [FiniteType p]
    (L : X.Modules) (hL : IsInvertible L) (s : Fin (m + 1) → Γ(L, ⊤)) :
    IsNoetherian (incidence p L hL s) := by
  let F := toParameters p L hL s
  let : FiniteType F := toParameters_finiteType p L hL s
  let : IsLocallyNoetherian (incidence p L hL s) :=
    LocallyOfFiniteType.isLocallyNoetherian F
  let : CompactSpace (incidence p L hL s) :=
    (quasiCompact_iff_compactSpace F).mp inferInstance
  exact ⟨⟩

/-- Original normalized generator frames produce smoothness of the entire
incidence over the same original field, without projectivity over that field. -/
theorem total_smooth_of_cover (p : X ⟶ Spec (.of k)) [Smooth p]
    (L : X.Modules) (hL : IsInvertible L) (s : Fin (m + 1) → Γ(L, ⊤))
    {T : Type*} (W : T → X.affineOpens) (hW : ⨆ t, (W t).1 = ⊤)
    (e : ∀ t, (pullback (W t).1.ι).obj L ≅ unitObj (W t).1.toScheme)
    (pivot : T → Fin (m + 1))
    (hpivot : ∀ t, (show Γ((W t).1.toScheme, ⊤) from
      (e t).hom.app ⊤ (affinePullbackUnitTop (W t).1.ι L (s (pivot t)))) = 1) :
    Smooth (toSource p L hL s ≫ p) := by
  let := NadelBertiniGlobalSmooth.toSource_smooth_of_cover p L hL s W hW e pivot hpivot
  infer_instance

/-- Actual sections, local frames and original finite type produce a rational
coefficient tuple in the actual nonproper smooth good open. -/
theorem exists_good_parameter_of_cover [CharZero k] (p : X ⟶ Spec (.of k)) [Smooth p] [FiniteType p]
    (L : X.Modules) (hL : IsInvertible L) (s : Fin (m + 1) → Γ(L, ⊤))
    {T : Type*} (W : T → X.affineOpens) (hW : ⨆ t, (W t).1 = ⊤)
    (e : ∀ t, (pullback (W t).1.ι).obj L ≅ unitObj (W t).1.toScheme)
    (pivot : T → Fin (m + 1))
    (hpivot : ∀ t, (show Γ((W t).1.toScheme, ⊤) from
      (e t).hom.app ⊤ (affinePullbackUnitTop (W t).1.ι L (s (pivot t)))) = 1) :
    ∃ a : Fin (m + 1) → k, a 0 ≠ 0 ∧
      ∀ t : Spec (.of k), NadelBertiniRationalParameter.parameterMap a t ∈
        RelativeNadelBertiniGenericOpen.goodOpen (toParameters p L hL s) := by
  let F := toParameters p L hL s
  let : FiniteType F := toParameters_finiteType p L hL s
  let : Smooth (toSource p L hL s ≫ p) :=
    total_smooth_of_cover p L hL s W hW e pivot hpivot
  have hU := RelativeNadelBertiniGenericOpen.goodOpen_specification_of_smooth
    (Spec.map (CommRingCat.ofHom (algebraMap k (parameterRing k m)))) F
    (toSource p L hL s ≫ p)
  obtain ⟨a, ha0, ha⟩ :=
    NadelBertiniRationalParameterIncidence.exists_nonzero_parameter_mem_finite_opens
      (fun _ : Unit => RelativeNadelBertiniGenericOpen.goodOpen F) (fun _ => hU.1)
  exact ⟨a, ha0, ha ()⟩

/-- The original relative projective coordinate sections over an arbitrary
original coefficient ring produce a rational smooth whole zero scheme over k.
No properness over k, domain hypothesis on R, or supplied good parameter occurs. -/
theorem exists_relative_projective_smooth_selected [CharZero k] {R : Type u} [CommRing R]
    (p : X ⟶ Spec (.of k)) [Smooth p] [FiniteType p]
    (j : X ⟶ Alterations.projectiveSpace R m) [IsClosedImmersion j] :
    ∃ a : Fin (m + 1) → k, a 0 ≠ 0 ∧
      Smooth ((NadelBertiniFibreGeometry.selectedIdeal p a (projectiveLine j)
        ((MvPolynomial.coordinateHyperplaneTwist_isInvertible
          (R := R) (0 : Fin (m + 1)) 1).pullback j)
        (projectiveSections j)).subschemeι ≫ p) := by
  let W : Fin (m + 1) → X.affineOpens := fun i =>
    ⟨NadelBertiniProjectiveFrames.sourceOpen j i,
      NadelBertiniProjectiveFrames.sourceOpen_affine j i⟩
  have hW : ⨆ i, (W i).1 = ⊤ := by
    change ⨆ i, j ⁻¹ᵁ MvPolynomial.coordinateOpen (R := R) i = ⊤
    exact j.iSup_preimage_eq_top (MvPolynomial.iSup_coordinateOpen_eq_top (R := R))
  have hpivot : ∀ i, (show Γ((W i).1.toScheme, ⊤) from
      (NadelBertiniProjectiveFrames.coordinateFrame j i).hom.app ⊤
        (affinePullbackUnitTop (W i).1.ι (projectiveLine j) (projectiveSections j i))) = 1 := by
    intro i
    change (NadelBertiniProjectiveFrames.coordinateFrame j i).hom.app ⊤
      (affinePullbackUnitTop (NadelBertiniProjectiveFrames.sourceOpen j i).ι
        (projectiveLine j) (sectionAtOne (NadelBertiniProjectiveFrames.sectionHom j i))) = _
    rw [pullback_sectionAtOne]
    exact congrArg sectionAtOne (NadelBertiniProjectiveFrames.coordinateFrame_section j i)
  let hL := (MvPolynomial.coordinateHyperplaneTwist_isInvertible
    (R := R) (0 : Fin (m + 1)) 1).pullback j
  obtain ⟨a, ha0, ha⟩ := exists_good_parameter_of_cover p (projectiveLine j) hL
    (projectiveSections j) W hW (NadelBertiniProjectiveFrames.coordinateFrame j) id hpivot
  let : FiniteType (toParameters p (projectiveLine j) hL (projectiveSections j)) :=
    toParameters_finiteType p (projectiveLine j) hL (projectiveSections j)
  exact ⟨a, ha0, RelativeNadelBertiniGenericOpen.selected_smooth p a
    (projectiveLine j) hL (projectiveSections j) ha⟩

end EnvelopeProperty.Vanishing.RelativeNadelBertiniIncidence
