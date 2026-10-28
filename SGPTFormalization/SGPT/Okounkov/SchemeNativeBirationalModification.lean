import SGPT.Okounkov.SchemeNativeAnalyticSubset
import SGPT.Okounkov.SchemeNativeOpenImmersionInverse
import BingWangEntropy.NativeFanoAlgebraicFiniteness
import TranscendentalNakamaye.Pending.AnalyticModificationLocalDiscrepancy

/-!
# The SAME original morphism is an actual analytic modification

The original algebraic open restriction supplies the genuine inverse. Both
exceptional sets are the actual original closed complements. Their analyticity
and empty interior are produced internally in the SAME native atlases.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Algebra BingWangEntropy Set
open TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open TranscendentalNakamaye.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold ContDiff

variable {X Y : Scheme} (f : X ⟶ Spec (.of ℂ)) (π : Y ⟶ X) (n : ℕ)
  [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (π ≫ f)]
  [IsSeparated f] [QuasiCompact f] [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)]
  [IsIntegral X] [IsIntegral Y]

local instance birationalTargetTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance birationalSourceTopology : TopologicalSpace (SchemeComplexPoint (π ≫ f)) :=
  schemeAnalyticPointTopology (π ≫ f)
local instance birationalTargetCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance birationalSourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint (π ≫ f)) :=
  schemeAnalyticTNChartedSpace (π ≫ f) n
local instance birationalTargetManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
local instance birationalSourceManifold : IsComplexManifold n (SchemeComplexPoint (π ≫ f)) :=
  schemeAnalyticTN_isComplexManifold (π ≫ f) n

/-- Native properness and an actual nonempty original isomorphism open produce the full
analytic-modification property for the SAME original morphism, with no analytic inverse
or exceptional-set premise. -/
theorem schemeNative_isAnalyticModification_of_isIso_restrict
    (U : X.Opens) [IsIso (π ∣_ U)] (hU : (U : Set X).Nonempty)
    (hproper : IsProperMap (schemeComplexPointMap (π ≫ f) f π rfl)) :
    IsAnalyticModification (n := n) (schemeComplexPointMap (π ≫ f) f π rfl) := by
  let W := π ⁻¹ᵁ U
  let r : U.toScheme ⟶ X := U.ι
  let h : U.toScheme ⟶ Y := inv (π ∣_ U) ≫ W.ι
  let : IsOpenImmersion h := inferInstanceAs (IsOpenImmersion (inv (π ∣_ U) ≫ W.ι))
  have hsec : h ≫ π = r := by
    dsimp only [h, r, W]
    rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have heq : h ≫ (π ≫ f) = r ≫ f := by
    rw [← Category.assoc, hsec]
  let : Smooth (π ≫ f) := SmoothOfRelativeDimension.smooth n (π ≫ f)
  obtain ⟨p₀⟩ := integralFiniteTypeSchemeComplexPoint_nonempty (π ≫ f)
  let s := schemeNativeOpenInverseMap f (π ≫ f) r h heq p₀
  let A := schemeNativeAlgebraicTrace (π ≫ f) ((W : Set Y)ᶜ)
  let B := schemeNativeAlgebraicTrace f ((U : Set X)ᶜ)
  have hAc : IsClosed ((W : Set Y)ᶜ) := W.isOpen.isClosed_compl
  have hBc : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  have hA : IsComplexAnalyticSubset (n := n) A :=
    schemeNativeAlgebraicTrace_isComplexAnalyticSubset (π ≫ f) n _ hAc
  have hB : IsComplexAnalyticSubset (n := n) B :=
    schemeNativeAlgebraicTrace_isComplexAnalyticSubset f n _ hBc
  have hUne : (U : Set X)ᶜ ≠ Set.univ := by
    obtain ⟨x, hx⟩ := hU
    intro he
    exact (show x ∈ (U : Set X)ᶜ from he.symm ▸ Set.mem_univ x) hx
  have hW : (W : Set Y).Nonempty := by
    obtain ⟨x, hx⟩ := hU
    let z : U.toScheme := ⟨x, hx⟩
    exact ⟨(inv (π ∣_ U) z).val, (inv (π ∣_ U) z).property⟩
  have hWne : (W : Set Y)ᶜ ≠ Set.univ := by
    obtain ⟨y, hy⟩ := hW
    intro he
    exact (show y ∈ (W : Set Y)ᶜ from he.symm ▸ Set.mem_univ y) hy
  have hAi : interior A = ∅ :=
    schemeNativeAlgebraicTrace_interior_eq_empty (π ≫ f) n _ hAc hWne
  have hBi : interior B = ∅ :=
    schemeNativeAlgebraicTrace_interior_eq_empty f n _ hBc hUne
  have hpre : schemeComplexPointMap (π ≫ f) f π rfl ⁻¹' B = A := by
    ext y
    change (y.val ≫ π) default ∉ (U : Set X) ↔ y.val default ∉ (W : Set Y)
    rw [Scheme.Hom.comp_apply]
    rfl
  have hUrange (x : SchemeComplexPoint f) : x ∉ B ↔ schemeComplexPointImage f x ∈ Set.range r := by
    change ¬ (schemeComplexPointImage f x ∉ (U : Set X)) ↔ _
    rw [not_not]
    change schemeComplexPointImage f x ∈ (U : Set X) ↔ schemeComplexPointImage f x ∈ Set.range U.ι
    rw [Scheme.Opens.range_ι]
  have hWrange (y : SchemeComplexPoint (π ≫ f)) (hy : y ∉ A) :
      schemeComplexPointImage (π ≫ f) y ∈ Set.range h := by
    have hyW : schemeComplexPointImage (π ≫ f) y ∈ (W : Set Y) := by
      change ¬ (schemeComplexPointImage (π ≫ f) y ∉ (W : Set Y)) at hy
      exact not_not.mp hy
    let w : W.toScheme := ⟨schemeComplexPointImage (π ≫ f) y, hyW⟩
    refine ⟨(π ∣_ U) w, ?_⟩
    have hi : inv (π ∣_ U) ((π ∣_ U) w) = w := by
      have he := congrArg (fun a : W.toScheme ⟶ W.toScheme => a w)
        (IsIso.hom_inv_id (π ∣_ U))
      rw [Scheme.Hom.comp_apply] at he
      exact he.trans (by rfl)
    change W.ι (inv (π ∣_ U) ((π ∣_ U) w)) = _
    rw [hi]
    rfl
  refine ⟨schemeComplexPointMap_contMDiff f π n n ∞, hproper, A, B, s,
    hA.isClosed, hA, hAi, hB.isClosed, hB, hBi, hpre, ?_, ?_, ?_⟩
  · exact (schemeNativeOpenInverseMap_contMDiffOn f (π ≫ f) n n r h heq p₀ ∞).mono
      (fun x hx => (hUrange x).mp hx)
  · intro x hx
    exact schemeNativeOpenInverseMap_right_inv f (π ≫ f) r h heq p₀ π rfl hsec x
      ((hUrange x).mp hx)
  · intro y hy
    exact schemeNativeOpenInverseMap_left_inv f (π ≫ f) r h heq p₀ π rfl hsec y (hWrange y hy)

end SGPT.Okounkov
