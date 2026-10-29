import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionDimensionDrop
import EnvelopeProperty.AlgGeom.SchemePointClosureIntegral
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionDimensionZeroAmpleness
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionIntersectionPositivity

/-!
# Seshadri Ampleness Criterion Integral Strata

Actual predecessor integral strata and the full Euler positivity base. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Order
open Scheme.Modules
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion

private def restrictIrreducibleClosed {X : Type u} [TopologicalSpace X]
    (Z : Closeds X) (C : IrreducibleCloseds X) (hC : (C : Set X) ⊆ Z) :
    IrreducibleCloseds Z where
  carrier := Subtype.val ⁻¹' (C : Set X)
  isClosed' := C.isClosed.preimage continuous_subtype_val
  isIrreducible' := by
    let g : C → Z := fun x => ⟨x.val, hC x.property⟩
    have hg : Continuous g := by fun_prop
    let : IrreducibleSpace C := Subtype.irreducibleSpace C.isIrreducible
    have hi := (IrreducibleSpace.isIrreducible_univ C).image g hg.continuousOn
    have he : g '' Set.univ = Subtype.val ⁻¹' (C : Set X) := by
      ext z
      constructor
      · rintro ⟨x, _, rfl⟩
        exact x.property
      · intro hz
        exact ⟨⟨z.val, hz⟩, trivial, Subtype.ext rfl⟩
    exact he ▸ hi

theorem exists_irreducibleClosed_dimension_eq
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    (d : ℕ) (hdim : topologicalKrullDim X = (d + 1 : ℕ)) :
    ∃ Z : Closeds X, Z ≠ ⊤ ∧ IsIrreducible (Z : Set X) ∧ topologicalKrullDim Z = d := by
  obtain ⟨l, hlen⟩ := Order.le_krullDim_iff.mp hdim.ge
  have hpos : l.length ≠ 0 := by omega
  let p := l.eraseLast
  let C := p.last
  let Z : Closeds X := ⟨(C : Set X), C.isClosed⟩
  have hC : C < l.last := l.eraseLast_last_rel_last hpos
  have hproper : Z ≠ ⊤ := by
    intro hZ
    apply (not_le_of_gt hC)
    intro x _hx
    change x ∈ (Z : Set X)
    rw [hZ]
    trivial
  have hpC (i : Fin (p.length + 1)) : (p i : Set X) ⊆ (Z : Set X) :=
    LTSeries.monotone p (Fin.le_last i)
  let A : Fin (p.length + 1) → IrreducibleCloseds Z :=
    fun i => restrictIrreducibleClosed Z (p i) (hpC i)
  have hm : StrictMono A := by
    intro i j hij
    apply lt_iff_le_not_ge.mpr
    constructor
    · intro z hz
      exact (LTSeries.strictMono p hij).le hz
    · intro hrev
      apply (not_le_of_gt (LTSeries.strictMono p hij))
      intro x hx
      exact hrev (show (⟨x, hpC j hx⟩ : Z) ∈ A j from hx)
  let q := LTSeries.mk p.length A hm
  have hlenp : p.length = d := by simp [p, hlen]
  have hlower : (d : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
    have hq := Order.LTSeries.length_le_krullDim q
    change (p.length : WithBot ℕ∞) ≤ topologicalKrullDim Z at hq
    simpa only [hlenp] using hq
  exact ⟨Z, hproper, C.isIrreducible,
    le_antisymm (properClosed_dimension_drop Z hproper d hdim.le) hlower⟩

theorem exists_pointClosure_dimension_eq
    {X : Scheme.{u}} [IsIntegral X] (d : ℕ)
    (hdim : topologicalKrullDim X = (d + 1 : ℕ)) :
    ∃ eta : X,
      let Z : Closeds X := ⟨closure ({eta} : Set X), isClosed_closure⟩
      Z ≠ ⊤ ∧ topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = d := by
  obtain ⟨Z, hZ, hI, hdimZ⟩ := exists_irreducibleClosed_dimension_eq d hdim
  let eta := hI.genericPoint
  have hc : closure ({eta} : Set X) = (Z : Set X) := hI.closure_genericPoint Z.isClosed
  let W : Closeds X := ⟨closure ({eta} : Set X), isClosed_closure⟩
  have hW : W = Z := SetLike.coe_injective hc
  refine ⟨eta, ?_, ?_⟩
  · change W ≠ ⊤
    simpa only [hW] using hZ
  · let I := Scheme.IdealSheafData.vanishingIdeal W
    change topologicalKrullDim I.support = d
    have hs : I.support = Z := by
      apply SetLike.coe_injective
      exact (Scheme.IdealSheafData.coe_support_vanishingIdeal W).trans hc
    rw [hs]
    exact hdimZ


theorem isAffine_of_dimension_le_zero {X : Scheme.{u}} [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 0) : IsAffine X := by
  obtain ⟨U, hU, hgen, _hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  let Z : Closeds X := ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  have hZ : Z ≠ ⊤ := by
    intro heq
    have hg : genericPoint X ∈ (Z : Set X) := by rw [heq]; trivial
    exact hg hgen
  let : IsEmpty Z := properClosed_isEmpty_of_dimension_le_zero Z hZ hdim
  have htop : U = ⊤ := by
    apply top_unique
    intro x _hx
    by_contra hxi
    exact isEmptyElim (⟨x, hxi⟩ : Z)
  have ha : IsAffineOpen (⊤ : X.Opens) := htop ▸ hU
  let : IsAffine (⊤ : X.Opens).toScheme := ha
  exact IsAffine.of_isIso X.topIso.inv

theorem eulerCharacteristic_unit_pos_of_dimension_le_zero
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ 0) :
    0 < SchemeCoherentEulerCharacteristic.eulerCharacteristic p (unitObj X) := by
  let : IsAffine X := isAffine_of_dimension_le_zero hdim
  let : (unitObj X).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj X).IsFinitePresentation := isInvertible_unit.isFinitePresentation
  let : (unitObj X).IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := X.ringCatSheaf) (unitObj X)
  let : Module.Finite k (SchemeCoherentEulerIndex.fieldSections p (unitObj X)) :=
    SchemeCoherentEulerIndex.fieldSections_finite p
      (ProjectiveFactorizationRingIso.of_isProjective p) (unitObj X)
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let : IsDomain Γ(X, ⊤) := IsIntegral.component_integral ⊤
  let : Nontrivial (SchemeCoherentEulerIndex.fieldSections p (unitObj X)) :=
    inferInstanceAs (Nontrivial Γ(X, ⊤))
  rw [SchemeCoherentEulerAffine.eulerCharacteristic_eq_finrank_sections]
  exact_mod_cast (Module.finrank_pos (R := k)
    (M := SchemeCoherentEulerIndex.fieldSections p (unitObj X)))

theorem eulerCharacteristic_invertible_pos_of_dimension_le_zero
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
    (p : X ⟶ Spec (.of k)) [IsProjective p] (hdim : topologicalKrullDim X ≤ 0)
    (L : X.Modules) (hL : IsInvertible L) :
    0 < SchemeCoherentEulerCharacteristic.eulerCharacteristic p L := by
  obtain ⟨e⟩ := SeshadriAmplenessCriterionDimensionZeroAmpleness.nonempty_unitIso_of_dimension_le_zero
    hdim L hL
  rw [SchemeCoherentEulerCharacteristic.eulerCharacteristic_eq_of_iso p e]
  exact eulerCharacteristic_unit_pos_of_dimension_le_zero p hdim

#check @exists_irreducibleClosed_dimension_eq
#print axioms exists_irreducibleClosed_dimension_eq
#check @exists_pointClosure_dimension_eq
#print axioms exists_pointClosure_dimension_eq
#check @isAffine_of_dimension_le_zero
#print axioms isAffine_of_dimension_le_zero
#check @eulerCharacteristic_unit_pos_of_dimension_le_zero
#print axioms eulerCharacteristic_unit_pos_of_dimension_le_zero
#check @eulerCharacteristic_invertible_pos_of_dimension_le_zero
#print axioms eulerCharacteristic_invertible_pos_of_dimension_le_zero
end EnvelopeProperty.SeshadriAmplenessCriterion
