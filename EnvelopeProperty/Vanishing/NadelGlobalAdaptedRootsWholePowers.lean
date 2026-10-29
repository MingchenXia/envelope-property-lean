import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsPowers
import EnvelopeProperty.Vanishing.NadelGlobalNormalizationOriginalRaw
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUp.GlueIdealSheaf

/-! # Exact original divisor powers of the SAME literal whole row-root sum

Original geometry internally constructs actual whole normalized charts whose
absent original auxiliary head has unit ideal. The proved same-head ideal
equality and individual-root power theorem then compute the whole sum power.
Native open-immersion stalk locality proves the entire global ideal equality.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules TopologicalSpace
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelGlobalAdaptedModel NadelAdaptedChartMatching NadelAuxiliaryBranchSectionsSnc

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

private theorem exists_actual_row_power_chart
    (z : normalizedScheme (OriginalData.data F n L m σ)) :
    ∃ (T : Scheme.{u}) (j : T ⟶ normalizedScheme (OriginalData.data F n L m σ)),
      IsOpenImmersion j ∧ (∃ t : T, j t = z) ∧
        ∀ i, (wholeRowIdeal F n L m σ hL i ^ m i).comap j =
          ((F.component i).comap
            (normalizedToOriginal (OriginalData.data F n L m σ))).comap j := by
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
  obtain ⟨U, v, hyU, het, e, c, hcinj, hcomp, hAbsent, w, hw⟩ :=
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
  let A := OriginalData.ideals F n L m σ hL hD
  have hhead : (wholeRowIdeal F n L m σ hL i).comap j =
      (normalizedRootIdeal D (rowPosition F n L m σ i (j₀ i))
        (OriginalData.get_isInvertible F n L m σ hL
          (rowPosition F n L m σ i (j₀ i)))).comap j :=
    canonicalRowIdeal_comap_eq_head F n L m σ hL hD y U v c j₀ w
      f het hcinj hm htame hG hcomp hyU hj₀ e hw i
  have hauxU : (A i (j₀ i)).comap U.1.ι = ⊤ := by
    have habs : y ∉ ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A).component
        (auxiliaryIndex F n A i (j₀ i))).support := by
      simpa only [component_auxiliaryIndex] using hj₀ i
    simpa only [A, component_auxiliaryIndex] using
      hAbsent (auxiliaryIndex F n A i (j₀ i)) habs
  let q : Spec (.of B) ⟶ U.1.toScheme := C.hom ≫ (π ∣_ U.1)
  have hq : q ≫ U.1.ι = j ≫ π := by
    simp only [q, j, Category.assoc, morphismRestrict_ι]
  have haux : ((A i (j₀ i)).comap π).comap j = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_comp, ← hq,
      Scheme.IdealSheafData.comap_comp, hauxU, Scheme.IdealSheafData.comap_top]
  calc
    (wholeRowIdeal F n L m σ hL i ^ m i).comap j =
        (normalizedRootIdeal D (rowPosition F n L m σ i (j₀ i))
          (OriginalData.get_isInvertible F n L m σ hL
            (rowPosition F n L m σ i (j₀ i))) ^ m i).comap j := by
      rw [Scheme.IdealSheafData.comap_pow, hhead, ← Scheme.IdealSheafData.comap_pow]
    _ = ((F.component i * A i (j₀ i)).comap π).comap j :=
      congrArg (fun I : (normalizedScheme D).IdealSheafData => I.comap j)
        (originalRowRootIdeal_power F n L m σ hL hD i (j₀ i))
    _ = ((F.component i).comap π).comap j := by
      rw [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_mul,
        haux, Scheme.IdealSheafData.mul_top]

/-- The SAME literal sum of ALL original normalized row-root zero ideals
has its exact original divisor power on the ENTIRE native normalization.
All actual charts and absent-head unit ideals are produced internally from
original geometry; no expected power or local matching certificate is input. -/
theorem wholeRowIdeal_power (i : F.ι) :
    wholeRowIdeal F n L m σ hL i ^ m i =
      (F.component i).comap (normalizedToOriginal (OriginalData.data F n L m σ)) := by
  classical
  apply Scheme.IdealSheafData.ext_stalkIdeal
  intro z
  obtain ⟨T, j, hopen, hpoint, hpowers⟩ :=
    exists_actual_row_power_chart F n L m σ hL hD f hG hRows hm hfield z
  obtain ⟨t, ht⟩ := hpoint
  let : IsOpenImmersion j := hopen
  have h := Scheme.IdealSheafData.stalkIdeal_eq_of_comap_eq j (hpowers i) t
  have htransport := congrArg
    (fun w : normalizedScheme (OriginalData.data F n L m σ) =>
      (wholeRowIdeal F n L m σ hL i ^ m i).stalkIdeal w =
        ((F.component i).comap
          (normalizedToOriginal (OriginalData.data F n L m σ))).stalkIdeal w) ht
  exact Eq.mp htransport h

end EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
