import TranscendentalNakamaye.Pending.CoordinateDensityGeneral
import TranscendentalNakamaye.Pending.ProperJacobianMultiplierGermDescent
import TranscendentalNakamaye.Pending.BlowupSequenceInjectiveOffNull
import TranscendentalNakamaye.Pending.HironakaAdmissibleCalculus
import TranscendentalNakamaye.Pending.HironakaLocalPrincipalization
import TranscendentalNakamaye.FirstPass.MongeAmpere

set_option autoImplicit false

/-! # Actual Jacobian weighted pullback and finite-blowup multiplier germ equivalence -/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace TranscendentalNakamaye.Pending.BlowupJacobianMultiplierGermEquivalence

open FirstPass FirstPass.HolomorphicMaps FirstPass.BlowupSequences
  DivisorialChangeOfVariables DemaillyApproximantDivisorialLelong

noncomputable section

private theorem differentiableOn_complexJacobian {n : ℕ}
    {F : ComplexModel n → ComplexModel n} {D : Set (ComplexModel n)}
    (hD : IsOpen D) (hF : DifferentiableOn ℂ F D) :
    DifferentiableOn ℂ (complexJacobian F) D := by
  classical
  have hentry (i j : Fin n) : DifferentiableOn ℂ
      (fun z => (fderiv ℂ F z (FirstPass.MongeAmpere.coordinateVector j)) i) D :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp_differentiableOn
      (FirstPass.differentiableOn_fderiv_apply_of_isOpen hF hD
        (FirstPass.MongeAmpere.coordinateVector j))
  have hdet : complexJacobian F = fun z =>
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
        ∏ a : Fin n, (fderiv ℂ F z (FirstPass.MongeAmpere.coordinateVector a)) (σ a) := by
    funext z
    rw [complexJacobian, ContinuousLinearMap.det,
      ← FirstPass.MongeAmpere.det_standardMatrix, Matrix.det_apply]
    simp only [FirstPass.MongeAmpere.standardMatrix_apply]
    rfl
  rw [hdet]
  refine DifferentiableOn.fun_sum fun σ _ =>
    (?_ : DifferentiableOn ℂ _ D).const_smul _
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [differentiableOn_const]
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hentry (σ a) a).mul ih

/-- The actual source weighted germ is produced from the original target germ,
holomorphic geometry and actual off-null injectivity. -/
theorem multiplierIntegrableAt_comp_mul_complexJacobian
    {n : ℕ} {F : ComplexModel n → ComplexModel n} {D : Set (ComplexModel n)}
    (hD : IsOpen D) (hF : ContDiffOn ℂ ∞ F D) {p : ComplexModel n} (hp : p ∈ D)
    {S : Set (ComplexModel n)} (hS : volume S = 0) (hinj : InjOn F (D \ S))
    {w : ComplexModel n → EReal} {g : ComplexModel n → ℂ} {c : ℝ}
    (hw : QuasiPlurisubharmonicAt w (F p))
    (hint : MultiplierIntegrableAt w c g (F p) volume) :
    MultiplierIntegrableAt (fun z => w (F z)) c
      (fun z => g (F z) * complexJacobian F z) p volume := by
  obtain ⟨hc, U, hU, hFpU, hgU, hL2⟩ := hint
  let V := D ∩ F ⁻¹' U
  have hV : IsOpen V := hF.continuousOn.isOpen_inter_preimage hD hU
  have hpV : p ∈ V := ⟨hp, hFpU⟩
  have hFd := hF.differentiableOn (by simp)
  have hgV : DifferentiableOn ℂ (fun z => g (F z)) V :=
    hgU.comp (hFd.mono inter_subset_left) (fun _ hz => hz.2)
  have hprod : DifferentiableOn ℂ (fun z => g (F z) * complexJacobian F z) V :=
    hgV.mul ((differentiableOn_complexJacobian hD hFd).mono inter_subset_left)
  have hwF := HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic hD hF hp hw
  obtain ⟨Q, hQ, hpQ, hwQ⟩ :=
    IEquivalentMax.exists_open_quasiPlurisubharmonicOn_of_at hwF
  let Z := V ∩ Q
  have hZ : IsOpen Z := hV.inter hQ
  have hpZ : p ∈ Z := ⟨hpV, hpQ⟩
  have hZD : Z ⊆ D := fun _ hz => hz.1.1
  have hFi : InjOn F (Z \ S) :=
    hinj.mono (sdiff_subset_sdiff_left hZD)
  have hcov := HolomorphicWeightedImageChangeOfVariables.lintegral_multiplierDensity_comp_eq
    hZ (hFd.mono hZD) hS hFi w c g
  have himage : F '' Z ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact hz.1.2
  have hsource : ∫⁻ z in Z, multiplierDensity (fun z => w (F z)) c
      (fun z => g (F z) * complexJacobian F z) z < ⊤ := by
    rw [hcov]
    exact (lintegral_mono_set himage).trans_lt hL2.2
  have hgZ : DifferentiableOn ℂ (fun z => g (F z) * complexJacobian F z) Z :=
    hprod.mono inter_subset_left
  exact ⟨hc, Z, hZ, hpZ, hgZ,
    IEquivalentMax.aemeasurable_multiplierDensity_restrict hZ
      (hwQ.mono inter_subset_right) hc.ne' hgZ.continuousOn, hsource⟩

/-- Every geometric and finite-fiber hypothesis in the reverse criterion is
internal to the actual finite sequence. -/
theorem multiplierIntegrableAt_iff_fiber_jacobian_germs
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {π : Y → X} (hπ : IsBlowupSequence (m + 1) X Y π) (x : X)
    {w : ComplexModel (m + 1) → EReal} {g : ComplexModel (m + 1) → ℂ}
    {c : ℝ} (hc : 0 < c)
    (hw : QuasiPlurisubharmonicAt w ((complexChartAt (n := m + 1) x).val x))
    (hg : ∀ᶠ z in 𝓝 ((complexChartAt (n := m + 1) x).val x),
      DifferentiableAt ℂ g z) :
    MultiplierIntegrableAt w c g ((complexChartAt (n := m + 1) x).val x) volume ↔
      ∀ y : Y, π y = x → MultiplierIntegrableAt
        (fun z => w (coordinateMap π (complexChartAt (n := m + 1) y)
          (complexChartAt (n := m + 1) x) z)) c
        (fun z => g (coordinateMap π (complexChartAt (n := m + 1) y)
          (complexChartAt (n := m + 1) x) z) *
          complexJacobian (coordinateMap π (complexChartAt (n := m + 1) y)
            (complexChartAt (n := m + 1) x)) z)
        ((complexChartAt (n := m + 1) y).val y) volume := by
  have hn := BlowupSequenceInjectiveOffNull.isInjectiveOffNull_of_isBlowupSequence hπ
  constructor
  · intro hint y hy
    let d := complexChartAt (n := m + 1) x
    let e := complexChartAt (n := m + 1) y
    let F := coordinateMap π e d
    let D := coordinateDomain π e d
    have hD : IsOpen D := coordinateDomain_isOpen hπ.contMDiff e d
    have hpD : e.val y ∈ D := by
      apply mem_coordinateDomain (mem_chart_source _ _)
      rw [hy]
      exact mem_chart_source _ _
    have hFy : F (e.val y) = d.val x := by
      change coordinateMap π e d (e.val y) = d.val x
      rw [coordinateMap_at (f := π) (e := e) (d := d)
        (show y ∈ e.val.source from mem_chart_source _ _), hy]
    obtain ⟨S, hS, hπinj⟩ := hn
    let S' := e.val '' (S ∩ e.val.source)
    have hS' : volume S' = 0 := hS y
    have hFi : InjOn F (D \ S') := by
      intro p hp q hq hpq
      have hpS : e.val.symm p ∉ S := by
        intro h
        exact hp.2 ⟨e.val.symm p, ⟨h, e.val.map_target hp.1.1⟩,
          e.val.right_inv hp.1.1⟩
      have hqS : e.val.symm q ∉ S := by
        intro h
        exact hq.2 ⟨e.val.symm q, ⟨h, e.val.map_target hq.1.1⟩,
          e.val.right_inv hq.1.1⟩
      have hpqπ := d.val.injOn hp.1.2 hq.1.2 hpq
      have hpqe := hπinj hpS hqS hpqπ
      calc p = e.val (e.val.symm p) := (e.val.right_inv hp.1.1).symm
           _ = e.val (e.val.symm q) := congrArg e.val hpqe
           _ = q := e.val.right_inv hq.1.1
    apply multiplierIntegrableAt_comp_mul_complexJacobian hD
      (coordinateMap_contDiffOn hπ.contMDiff e d) hpD hS' hFi
    · change QuasiPlurisubharmonicAt w (F (e.val y))
      rw [hFy]
      exact hw
    · change MultiplierIntegrableAt w c g (F (e.val y)) volume
      rw [hFy]
      exact hint
  · exact ProperJacobianMultiplierGermDescent.multiplierIntegrableAt_of_fiber_jacobian_germs
      hπ.contMDiff (HironakaAdmissibleCalculus.isProperMap_of_isBlowupSequence hπ)
      (HironakaLocalPrincipalization.IsBlowupSequence.surjective hπ) hn x hc hw hg

end
end TranscendentalNakamaye.Pending.BlowupJacobianMultiplierGermEquivalence
