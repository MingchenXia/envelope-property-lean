import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsCartier
import EnvelopeProperty.Vanishing.NadelGlobalNormalizationOriginalRaw
import Hironaka.Scheme.BlowUp.Glue.Global

/-! # The same literal whole row ideal is globally Cartier

Original closed-point SNC geometry constructs the actual normalized charts.
Their proved whole-row Cartier property is transported by native open-cover
locality. No chart, row-ideal regularity, or Cartier certificate is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules TopologicalSpace
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelGlobalAdaptedModel NadelAdaptedChartMatching

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
  (L : F.ι → X.Modules) (m : F.ι → ℕ)
  (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
    tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
  (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
  {k : Type u} [Field k] [PerfectField k]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
  (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
    (OriginalData.ideals F n L m σ hL hD)).IsSnc)
  (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
  (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))

include hD f hG hRows hm hfield

private theorem exists_actual_row_cartier_chart
    (z : normalizedScheme (OriginalData.data F n L m σ)) :
    ∃ (T : Scheme.{u}) (j : T ⟶ normalizedScheme (OriginalData.data F n L m σ)),
      IsOpenImmersion j ∧ (∃ t : T, j t = z) ∧
        ∀ i, ((wholeRowIdeal F n L m σ hL i).comap j).IsInvertible := by
  classical
  let D := OriginalData.data F n L m σ
  let π := normalizedToOriginal D
  let x : X := π z
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, _, hxy⟩ :=
    exists_isClosed_singleton_mem_specializes isClosed_univ (Set.mem_univ x)
  obtain ⟨j₀, hj₀⟩ := Joined.exists_absent_copies F n
    (OriginalData.ideals F n L m σ hL hD) hRows y
  obtain ⟨U, v, hyU, het, e, c, hcinj, hcomp, _hAbsent, w, hw⟩ :=
    OriginalData.exists_framed_coefficients_at_closed F n L m σ hL hD f hG hy
  let : Nonempty U.1 := ⟨⟨y, hyU⟩⟩
  have htame (i : F.ι) : IsUnit (m i : Γ(X, U.1)) := by
    let _ := f.sectionsAlgebra U.1
    simpa only [map_natCast] using (hfield i).map (algebraMap k Γ(X, U.1))
  let B := RatioRing F n L m σ hL hD y U v c j₀ w
  let C : Spec (.of B) ≅ (π ⁻¹ᵁ U.1).toScheme :=
    Model.canonicalChart F n L m σ hL hD y U v c j₀ w
      f het hcinj hm htame hG hcomp hyU hj₀ e hw
  let j : Spec (.of B) ⟶ normalizedScheme D := C.hom ≫ (π ⁻¹ᵁ U.1).ι
  have hopen : IsOpenImmersion j := by
    dsimp only [j]
    infer_instance
  have hxU : x ∈ U.1 := hxy.mem_open U.1.isOpen hyU
  let zU : (π ⁻¹ᵁ U.1).toScheme := ⟨z, hxU⟩
  have hpoint : ∃ t : Spec (.of B), j t = z := by
    obtain ⟨t, ht⟩ := (Scheme.homeoOfIso C).surjective zU
    have ht' : C.hom t = zU := by
      rw [← Scheme.homeoOfIso_apply]
      exact ht
    refine ⟨t, ?_⟩
    change (π ⁻¹ᵁ U.1).ι (C.hom t) = z
    rw [ht']
    rfl
  refine ⟨Spec (.of B), j, hopen, hpoint, ?_⟩
  intro i
  exact canonicalRowIdeal_comap_isInvertible F n L m σ hL hD y U v c j₀ w
    f het hcinj hm htame hG hcomp hyU hj₀ e hw i

/-- Original tame smooth/SNC/empty-row data INTERNALLY constructs a genuine
Cartier cover for the SAME literal global sum of ALL original row-root zero
ideals. The conclusion holds on the ENTIRE native normalization. -/
theorem wholeRowIdeal_isInvertible (i : F.ι) :
    (wholeRowIdeal F n L m σ hL i).IsInvertible := by
  classical
  choose T j hopen hpoint hcartier using fun z =>
    exists_actual_row_cartier_chart F n L m σ hL hD f hG hRows hm hfield z
  let : ∀ z, IsOpenImmersion (j z) := hopen
  apply Scheme.IdealSheafData.IsInvertible.of_forall_comap_isOpenImmersion
    (wholeRowIdeal F n L m σ hL i) j
  · intro z
    exact ⟨z, Scheme.Hom.mem_opensRange.mpr (hpoint z)⟩
  · intro z
    exact hcartier z i

end EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
