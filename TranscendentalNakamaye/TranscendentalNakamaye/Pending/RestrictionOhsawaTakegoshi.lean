import TranscendentalNakamaye.Pending.OhsawaTakegoshiSubspace
import TranscendentalNakamaye.Pending.SubmanifoldIdealRestriction
import TranscendentalNakamaye.Pending.RestrictedIdealWeight
import TranscendentalNakamaye.Pending.HolomorphicPullback
import TranscendentalNakamaye.Pending.MultiplierIdeals
import TranscendentalNakamaye.Pending.ChartWeightedL2Transfer

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The restriction theorem for multiplier ideals (Ohsawa--Takegoshi): `𝓘(cφ|_W) ⊆ Res_W 𝓘(cφ)`

Sources: Xia, *Singularities in global pluripotential theory*, Theorem 1.4.5
(`references/xia-sgpt/tex/page-0044.tex`; blueprint `trace:multiplier-restriction`), which cites
Demailly, *Analytic methods in algebraic geometry*, Theorem 14.1; used by Darvas--Xia, *The trace
operator*, Theorem 3.16 (`references/dx24-trace-operator/source/main.tex:869-891`, "by the
Ohsawa--Takegoshi extension theorem applied to `φ_j`"), which is the inclusion `(T4)` of Copy-4
`sec:positive-current` (`𝓘(Mu) ⊆ Res_V 𝓘(M V_θ)`, `lem:ideal-comparison`).  Piece C3 of the
positive-current programme (`.archon-horizon/scratch/tn23-envelopes-qea-plan-0117.md` §5.3).

Let `W ⊆ X` be a closed complex submanifold of dimension `k` of a complex manifold of dimension
`n`, with the complex structure of `SubmanifoldChartedSpace` (the flattening atlas; this is the
structure used by `Copy4FixedDataFromInputs.IsLevelPotential` and `PositiveCurrentInput`), and let
`φ` be quasi-plurisubharmonic on `X` (`ManifoldQuasiPlurisubharmonic`; `φ ≡ -∞` is allowed, and
every `θ`-psh potential qualifies by `ThetaPlurisubharmonic.quasiPlurisubharmonic`).

* `exists_extension_mem_multiplierIdeal` — **germ form**: every germ `g ∈ 𝓘_W(c φ|_W)_p` is the
  restriction of a germ `G ∈ 𝓘_X(c φ)_p`, i.e. `G = g` on `W` near `p`.  This is literally the
  definition of `Res_W 𝓘(cφ)` used by Xia (1.16) and Darvas--Xia: holomorphic germs on `W` with local
  extensions in `𝓘(cφ)`.
* `multiplierIdeal_le_restrictIdeal` — **ideal form** on `↥W`:
  `𝓘_W(c φ|_W) ≤ Res_W 𝓘_X(c φ)`, `Res_W` the pullback ideal `SubmanifoldIdealRestriction.restrictIdeal`.
* `isInSpanOnAt_multiplierIdeal_of_mem` — **ambient form at a point**: an ambient germ `g` at
  `x ∈ W` whose restriction lies in `𝓘_W(c φ|_W)` agrees on `W` near `x` with a germ of `𝓘_X(cφ)`;
  `restrictLe_multiplierIdeal_of_forall_mem` — the same for all germs of an ambient ideal `𝔞`:
  `RestrictLe W 𝔞 𝓘(cφ)`, the comparison in which `PositiveCurrentInput` is stated.

No hypothesis `φ|_W ≢ -∞` is needed (Xia assumes it to make `𝓘(φ|_W)` meaningful as a
multiplier ideal of a psh function; where `φ|_W ≡ -∞` near `p` the stalk `𝓘_W(cφ|_W)_p` is zero
and the inclusion is trivial), and none on `c` (for `c ≤ 0` the stalks are empty by definition).

## Proof

Near `p`, the flattening datum of `W` at `p` gives coordinates `z = Φ(e(y))` in which `W` is the
coordinate plane `ℂᵏ × {0}` and `p` is the origin; the chart of `W` at `p` is `ζ ↦ pr_k z`.  In
these coordinates `φ` reads `ψ = φ ∘ e⁻¹ ∘ Φ⁻¹`, quasi-psh (`HolomorphicPullback`), so
`ψ = P + h` near `0` with `P` psh and `h` smooth, hence bounded near `0`.  The hypothesis says
`∫ |g|² e^{-c ψ(ζ, 0)} < ∞` near `0`; since `|h| ≤ M`, also `∫ |g|² e^{-c P(ζ, 0)} < ∞`
(`multiplierIntegrableAt_of_moreSingularAt`).  On a ball `Ω` around `0` on which `P` is psh, the
Ohsawa--Takegoshi theorem from a coordinate subspace (`OhsawaTakegoshiSubspace`, proved in the
tree) extends `g` to `F` on `Ω` with `∫_Ω |F|² e^{-cP} < ∞`; again since `|h| ≤ M`,
`|F|² e^{-cψ}` is integrable near `0`.  Transporting back through the biholomorphism `Φ`
(`ChartWeightedL2.multiplierIntegrableAt_comp`) gives `G = F ∘ Φ ∘ e ∈ 𝓘_X(cφ)_p`, and `G = g` on
`W` near `p` by construction.

Sorry-free.  No existing statement is changed.
-/

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace TranscendentalNakamaye.Pending.RestrictionOhsawaTakegoshi

noncomputable section

open FirstPass FirstPass.RegularLocusDense FirstPass.HolomorphicIdealSheaves
  OhsawaTakegoshiSubspace RestrictedIdealWeight

/-! ### Ohsawa--Takegoshi from the coordinate plane `ℂᵏ × {0} ⊆ ℂⁿ` -/

/-- The flattening charts' inclusion `w ↦ (w, 0)` is the Ohsawa--Takegoshi module's
`subspaceCLM`. -/
theorem coordinateInclusion_add_eq_subspaceCLM (k d : ℕ) (w : ComplexModel k) :
    coordinateInclusion (k + d) k w = subspaceCLM k d w := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [subspaceCLM_apply_castAdd, coordinateInclusion_apply]
    simp
  · rw [subspaceCLM_apply_natAdd, coordinateInclusion_apply]
    simp

/-- **Ohsawa--Takegoshi from the coordinate plane** `ℂᵏ × {0} ⊆ ℂⁿ` (`k ≤ n`), written with the
project's `coordinateInclusion n k` (the inclusion used by the flattening charts of
`SubmanifoldChartedSpace`), for any Borel structures on `ℂᵏ` and `ℂⁿ`. -/
theorem exists_extension_from_coordinatePlane {k n : ℕ}
    [ik : MeasurableSpace (ComplexModel k)] [hik : BorelSpace (ComplexModel k)]
    [i : MeasurableSpace (ComplexModel n)] [hi : BorelSpace (ComplexModel n)]
    (hk : k ≤ n) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Ω : Set (ComplexModel n), IsOpen Ω → Convex ℝ Ω → (∀ z ∈ Ω, ‖z‖ < R) →
      ∀ φ : ComplexModel n → EReal, PlurisubharmonicOn φ Ω → ∀ c : ℝ, 0 < c →
      ∀ f : ComplexModel k → ℂ, DifferentiableOn ℂ f (coordinateInclusion n k ⁻¹' Ω) →
      ∃ F : ComplexModel n → ℂ, DifferentiableOn ℂ F Ω ∧
        (∀ w ∈ coordinateInclusion n k ⁻¹' Ω, F (coordinateInclusion n k w) = f w) ∧
        (∫⁻ z in Ω, multiplierDensity φ c F z) ≤
          ENNReal.ofReal C * ∫⁻ w in coordinateInclusion n k ⁻¹' Ω,
              multiplierDensity (fun w => φ (coordinateInclusion n k w)) c f w := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain rfl : i = borel _ := hi.measurable_eq
  obtain rfl : ik = borel _ := hik.measurable_eq
  have hfun : (⇑(coordinateInclusion (k + d) k) : ComplexModel k → ComplexModel (k + d)) =
      ⇑(subspaceCLM k d) := funext (coordinateInclusion_add_eq_subspaceCLM k d)
  rw [hfun]
  exact exists_extension_from_subspace k d R hR

/-- The inclusion `ℂᵏ → ℂⁿ`, `w ↦ (w, 0)`, preserves norms. -/
theorem norm_coordinateInclusion_of_le {k n : ℕ} (hk : k ≤ n) (w : ComplexModel k) :
    ‖coordinateInclusion n k w‖ = ‖w‖ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [coordinateInclusion_add_eq_subspaceCLM, norm_subspaceCLM]

/-- The multiplier weight density of an upper semicontinuous weight and a continuous function is
a.e.-measurable on an open set. -/
theorem aemeasurable_multiplierDensity_of_upperSemicontinuousOn {m : ℕ}
    [MeasurableSpace (ComplexModel m)] [BorelSpace (ComplexModel m)]
    {μ : Measure (ComplexModel m)} {P : ComplexModel m → EReal} {F : ComplexModel m → ℂ}
    {Ω : Set (ComplexModel m)} (hΩ : IsOpen Ω) (hP : UpperSemicontinuousOn P Ω)
    (hF : ContinuousOn F Ω) {c : ℝ} (hc : c ≠ 0) :
    AEMeasurable (multiplierDensity P c F) (μ.restrict Ω) := by
  have hPmeas : AEMeasurable P (μ.restrict Ω) :=
    ChartWeightedL2.aemeasurable_restrict_of_upperSemicontinuousOn hP hΩ
  have hcmul : AEMeasurable (fun y => (c : EReal) * P y) (μ.restrict Ω) :=
    (continuous_eReal_const_mul hc).measurable.comp_aemeasurable' hPmeas
  have hneg : AEMeasurable (fun y => -((c : EReal) * P y)) (μ.restrict Ω) :=
    continuous_neg.measurable.comp_aemeasurable' hcmul
  have hweight : AEMeasurable (fun y => multiplierWeight c (P y)) (μ.restrict Ω) := by
    simpa only [multiplierWeight] using EReal.measurable_exp.comp_aemeasurable' hneg
  have hFcont : ContinuousOn (fun z => ENNReal.ofReal (‖F z‖ ^ 2)) Ω :=
    ENNReal.continuous_ofReal.comp_continuousOn ((continuous_norm.comp_continuousOn hF).pow 2)
  exact (hFcont.aemeasurable hΩ.measurableSet).mul hweight

/-! ### The restriction inclusion -/

section Restriction

open SubmanifoldChartedSpace SubmanifoldChartedSpace.FlatData

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}

/-- **Ohsawa--Takegoshi restriction, germ form.**  Let `W ⊆ X` be a closed complex submanifold of
dimension `k` (with the flattening complex structure of `SubmanifoldChartedSpace`) and `φ` a
quasi-psh function on `X` (`φ ≡ -∞` allowed).  Every germ `g` of `𝓘_W(c φ|_W)` at `p ∈ W` is the
restriction of a germ `F` of `𝓘_X(c φ)` at `p`: `F = f` on `W` near `p`.  (`0 < c` is not a
hypothesis: membership in `𝓘_W(c φ|_W)` already forces it.) -/
theorem exists_extension_mem_multiplierIdeal (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {c : ℝ} :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∀ (p : W) (f : W → ℂ), (multiplierIdeal (n := k) c (fun q : W => φ q.1)).mem p f →
      ∃ F : X → ℂ, (multiplierIdeal (n := n) c φ).mem p.1 F ∧ (fun q : W => F q.1) =ᶠ[𝓝 p] f := by
  let := chartedSpace hk hW
  intro p g hg
  obtain ⟨-, hint⟩ := hg
  set x : X := p.1 with hxdef
  have hreg := hW x p.2
  set Fd : FlatData n k X W := FlatData.ofRegularAtDim hreg with hFd
  set amb : ComplexChart n X := Fd.amb with hamb
  set flat := Fd.flat with hflat
  set ι : ComplexModel k →L[ℂ] ComplexModel n := coordinateInclusion n k with hι
  have hamb_eq : amb = complexChartAt (n := n) x := rfl
  have hchart_eq : (complexChartAt (n := k) p).val = Fd.chart hk := rfl
  have hpsrc : p ∈ (Fd.chart hk).source := FlatData.mem_ambSource_ofRegularAtDim hreg
  have hxsrc : x ∈ Fd.ambSource := hpsrc
  have hz0 : flat (amb.val x) = 0 := hreg.2.2.choose_spec.2.1
  have hζ0 : (Fd.chart hk) p = 0 := by
    rw [FlatData.chart_apply, FlatData.toCoord]
    rw [show Fd.flat (Fd.amb.val p.1) = 0 from hz0, map_zero]
  -- the weight in flattened coordinates and the germ in the chart of `W`
  set ψ : ComplexModel n → EReal := fun z => chartFunction φ amb (flat.symm z) with hψdef
  set f : ComplexModel k → ℂ := fun ζ => g ((complexChartAt (n := k) p).val.symm ζ) with hfdef
  -- Step 1: the weight of `φ|_W` in the chart of `W` at `p` is `ψ ∘ ι`
  have h0T : (0 : ComplexModel k) ∈ Fd.coordTarget := by
    rw [← hζ0]; exact Fd.toCoord_mem_coordTarget p hxsrc
  have hweightW : chartFunction (fun q : W => φ q.1) (complexChartAt (n := k) p) =ᶠ[𝓝 0]
      fun ζ => ψ (ι ζ) := by
    filter_upwards [Fd.isOpen_coordTarget.mem_nhds h0T] with ζ hζ
    show φ (((Fd.chart hk).symm ζ : W) : X) = φ (amb.val.symm (flat.symm (ι ζ)))
    rw [show (((Fd.chart hk).symm ζ : W) : X) = Fd.ofCoord ζ from Fd.invPoint_val hζ]
    rfl
  have hintW : MultiplierIntegrableAt (fun ζ => ψ (ι ζ)) c f 0 volume := by
    have h1 := hint
    rw [show (complexChartAt (n := k) p).val p = 0 from hζ0] at h1
    exact h1.congr hweightW (EventuallyEq.refl _ _)
  -- Step 2: `ψ` is quasi-psh at the origin
  have hflat_symm_cd : ContDiffOn ℂ ∞ flat.symm flat.target :=
    contDiffOn_of_differentiableOn_complex Fd.differentiableOn_flat_symm flat.open_target
  have hxflat : amb.val x ∈ flat.source := hxsrc.2
  have h0flat : (0 : ComplexModel n) ∈ flat.target := by
    rw [← hz0]; exact flat.map_source hxflat
  have hsymm0 : flat.symm 0 = amb.val x := by rw [← hz0]; exact flat.left_inv hxflat
  have hφamb : QuasiPlurisubharmonicOn (chartFunction φ amb) amb.val.target := hφ amb
  have hψ0 : QuasiPlurisubharmonicAt ψ 0 := by
    have hq : QuasiPlurisubharmonicAt (chartFunction φ amb) (flat.symm 0) := by
      rw [hsymm0]; exact hφamb _ (amb.val.map_source hxsrc.1)
    exact HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic flat.open_target
      hflat_symm_cd h0flat hq
  -- Step 3: `ψ = P + h` near the origin, `P` psh, `h` smooth and bounded
  obtain ⟨P, hs, hP, hhs, heq⟩ := id hψ0
  obtain ⟨UP, hUP, h0UP, hPdisc⟩ := id hP
  have hscont : ContinuousAt hs 0 := hhs.self_of_nhds.continuousAt
  set M : ℝ := |hs 0| + 1 with hM
  have hsbd : ∀ᶠ y in 𝓝 (0 : ComplexModel n), |hs y| ≤ M := by
    filter_upwards [hscont.eventually_mem (Metric.ball_mem_nhds (hs 0) one_pos)] with y hy
    rw [mem_ball, Real.dist_eq] at hy
    have := abs_sub_abs_le_abs_sub (hs y) (hs 0)
    linarith
  -- Step 4: the slice integral of `|f|² e^{-c P(·, 0)}` is finite near the origin
  have hιcont : Tendsto ι (𝓝 0) (𝓝 0) := by simpa using ι.continuous.tendsto 0
  have hmoreW : MoreSingularAt (fun w => ψ (ι w)) (fun w => P (ι w)) 0 := by
    refine ⟨M, ?_⟩
    filter_upwards [hιcont.eventually heq, hιcont.eventually hsbd] with w hw hwb
    rw [hw]
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_of_abs_le hwb))
  have hPι : QuasiPlurisubharmonicAt (fun w => P (ι w)) 0 := by
    refine (HolomorphicPullback.plurisubharmonicAt_comp_holomorphic isOpen_univ
      ι.differentiable.differentiableOn (mem_univ 0) ?_).quasiPlurisubharmonicAt
    simpa using hP
  obtain ⟨hc, U', hU', h0U', hfU', hfint⟩ :=
    multiplierIntegrableAt_of_moreSingularAt hPι hmoreW hintW
  -- Step 5: a ball on which `P` is psh and whose slice lies in the integrability domain
  obtain ⟨r1, hr1, hr1U'⟩ := Metric.isOpen_iff.mp hU' 0 h0U'
  obtain ⟨r2, hr2, hr2UP⟩ := Metric.isOpen_iff.mp hUP 0 h0UP
  set r : ℝ := min r1 r2 with hr
  have hr0 : 0 < r := lt_min hr1 hr2
  set Ω : Set (ComplexModel n) := ball 0 r with hΩ
  have hΩUP : Ω ⊆ UP := fun y hy => hr2UP (ball_subset_ball (min_le_right _ _) hy)
  have hPΩ : PlurisubharmonicOn P Ω := fun y hy => ⟨UP, hUP, hΩUP hy, hPdisc⟩
  have hsliceΩ : ι ⁻¹' Ω ⊆ U' := by
    intro w hw
    apply hr1U'
    have h1 : ‖ι w‖ < r := mem_ball_zero_iff.mp hw
    rw [hι, norm_coordinateInclusion_of_le hk] at h1
    exact mem_ball_zero_iff.mpr (h1.trans_le (min_le_left _ _))
  -- Step 6: Ohsawa--Takegoshi on `Ω`
  obtain ⟨C, hC, hOT⟩ := exists_extension_from_coordinatePlane (k := k) (n := n) hk hr0
  obtain ⟨Fx, hFhol, hFext, hFint⟩ := hOT Ω isOpen_ball (convex_ball 0 r)
    (fun z hz => mem_ball_zero_iff.mp hz) P hPΩ c hc f (hfU'.mono hsliceΩ)
  have hFP : MultiplierIntegrableAt P c Fx 0 volume := by
    refine ⟨hc, Ω, isOpen_ball, mem_ball_self hr0, hFhol, ?_, ?_⟩
    · exact aemeasurable_multiplierDensity_of_upperSemicontinuousOn isOpen_ball
        (hPdisc.upperSemicontinuousOn.mono hΩUP) hFhol.continuousOn hc.ne'
    · calc (∫⁻ z in Ω, multiplierDensity P c Fx z)
          ≤ ENNReal.ofReal C * ∫⁻ w in ι ⁻¹' Ω, multiplierDensity (fun w => P (ι w)) c f w :=
            hFint
        _ ≤ ENNReal.ofReal C * ∫⁻ w in U', multiplierDensity (fun w => P (ι w)) c f w :=
            mul_le_mul' le_rfl (lintegral_mono_set hsliceΩ)
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfint.2
  -- Step 7: back to the weight `ψ`
  have hmore' : MoreSingularAt P ψ 0 := by
    refine ⟨M, ?_⟩
    filter_upwards [heq, hsbd] with y hy hyb
    rw [hy, add_assoc, ← EReal.coe_add]
    have h1 : 0 ≤ hs y + M := by have := neg_abs_le (hs y); linarith
    exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr h1)
  have hFψ : MultiplierIntegrableAt ψ c Fx 0 volume :=
    multiplierIntegrableAt_of_moreSingularAt hψ0 hmore' hFP
  -- Step 8: back to the ambient chart
  have hσ1 : ContDiffOn ℝ 1 flat.symm flat.target :=
    (hflat_symm_cd.restrict_scalars ℝ).of_le (by simp)
  have hφusc : UpperSemicontinuousOn (chartFunction φ amb) flat.source :=
    hφamb.upperSemicontinuousOn.mono Fd.flat_source_subset
  have hambint : MultiplierIntegrableAt (chartFunction φ amb) c (fun z => Fx (flat z))
      (amb.val x) volume :=
    ChartWeightedL2.multiplierIntegrableAt_comp (φ := chartFunction φ amb) (ψ := ψ)
      flat.open_source flat.open_target
      Fd.differentiableOn_flat hσ1 (fun z hz => flat.map_source hz)
      (fun z hz => flat.map_target hz) (fun z hz => flat.left_inv hz)
      (fun z hz => flat.right_inv hz)
      (fun z hz => by
        show chartFunction φ amb (flat.symm (flat z)) = chartFunction φ amb z
        rw [flat.left_inv hz])
      hφusc hc.ne' hxflat (by rw [hz0]; exact hFψ)
  -- Step 9: the ambient germ
  refine ⟨fun y => Fx (flat (amb.val y)), ⟨?_, ?_⟩, ?_⟩
  · have hev : ∀ᶠ z in 𝓝 (amb.val x), DifferentiableAt ℂ (fun z => Fx (flat z)) z := by
      have hΩnhds : Ω ∈ 𝓝 (flat (amb.val x)) := by
        rw [hz0]; exact isOpen_ball.mem_nhds (mem_ball_self hr0)
      filter_upwards [flat.open_source.mem_nhds hxflat,
        (flat.continuousAt hxflat).eventually_mem hΩnhds] with z hz hzΩ
      exact (hFhol.differentiableAt (isOpen_ball.mem_nhds hzΩ)).comp z
        (Fd.differentiableOn_flat.differentiableAt (flat.open_source.mem_nhds hz))
    filter_upwards [amb.val.open_source.mem_nhds hxsrc.1,
      (amb.val.continuousAt hxsrc.1).eventually hev] with y hy hWy
    have hWm : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (fun z => Fx (flat z))
        (amb.val y) := by
      rw [mdifferentiableAt_iff_differentiableAt]; exact hWy
    exact hWm.comp y (mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n)) amb.2 hy)
  · refine hambint.congr (EventuallyEq.refl _ _) ?_
    filter_upwards [amb.val.open_target.mem_nhds (amb.val.map_source hxsrc.1)] with z hz
    show Fx (flat z) = Fx (flat (amb.val (amb.val.symm z)))
    rw [amb.val.right_inv hz]
  · have hball : ball (0 : ComplexModel k) r ∈ 𝓝 ((Fd.chart hk) p) := by
      rw [hζ0]; exact ball_mem_nhds 0 hr0
    filter_upwards [(Fd.chart hk).open_source.mem_nhds hpsrc,
      ((Fd.chart hk).continuousAt hpsrc).eventually_mem hball] with q hq hqb
    have hqx : q.1 ∈ Fd.ambSource := hq
    have hιq : ι (Fd.toCoord q) = flat (amb.val q.1) := Fd.coordinateInclusion_toCoord q hqx
    have hmemΩ : Fd.toCoord q ∈ ι ⁻¹' Ω := by
      show ι (Fd.toCoord q) ∈ ball 0 r
      rw [mem_ball_zero_iff, hι, norm_coordinateInclusion_of_le hk]
      exact mem_ball_zero_iff.mp hqb
    show Fx (flat (amb.val q.1)) = g q
    rw [← hιq, hFext _ hmemΩ]
    show g ((Fd.chart hk).symm ((Fd.chart hk) q)) = g q
    rw [(Fd.chart hk).left_inv hq]

/-- **Ohsawa--Takegoshi restriction, ideal form: `𝓘_W(c φ|_W) ⊆ Res_W 𝓘_X(c φ)`.**  The inclusion
of ideal sheaves on the submanifold `↥W`, `Res_W` being the pullback along the inclusion
(`SubmanifoldIdealRestriction.restrictIdeal`). -/
theorem multiplierIdeal_le_restrictIdeal (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {c : ℝ} :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    (multiplierIdeal (n := k) c (fun q : W => φ q.1)).Le
      (SubmanifoldIdealRestriction.restrictIdeal (k := k) (W := W)
        (multiplierIdeal (n := n) c φ)) := by
  let := chartedSpace hk hW
  intro p g hg
  obtain ⟨G, hG, hGg⟩ := exists_extension_mem_multiplierIdeal hk hW hφ p g hg
  show IsInSpanAt (n := k)
    (fun s => ∃ a, (multiplierIdeal (n := n) c φ).mem p.1 a ∧ s = a ∘ Subtype.val) p g
  refine isInSpanAt_of_eq_mul ⟨G, hG, rfl⟩ hg.1 (holomorphicAt_const 1) ?_
  filter_upwards [hGg] with q hq
  simp [← hq]

/-- **Ohsawa--Takegoshi restriction, ambient form at a point.**  If the restriction to `W` of an
ambient germ `g` at `x ∈ W` lies in `𝓘_W(c φ|_W)`, then `g` agrees on `W`, near `x`, with a germ of
`𝓘_X(c φ)` (`IsInSpanOnAt` with one generator and coefficient `1`). -/
theorem isInSpanOnAt_multiplierIdeal_of_mem (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {c : ℝ} :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∀ (x : X) (hx : x ∈ W) (g : X → ℂ),
      (multiplierIdeal (n := k) c (fun q : W => φ q.1)).mem ⟨x, hx⟩ (fun q : W => g q.1) →
      IsInSpanOnAt (n := n) W ((multiplierIdeal (n := n) c φ).mem x) x g := by
  let := chartedSpace hk hW
  intro x hx g hg
  obtain ⟨G, hG, hGg⟩ := exists_extension_mem_multiplierIdeal hk hW hφ ⟨x, hx⟩ _ hg
  refine ⟨1, fun _ => G, fun _ => fun _ => 1, fun _ => hG, fun _ => holomorphicAt_const 1, ?_⟩
  have h1 := (eventually_nhds_subtype_iff W ⟨x, hx⟩ (fun y => G y = g y)).mp hGg
  filter_upwards [eventually_nhdsWithin_iff.mp h1] with y hy hyW
  simp [hy hyW]

/-- **Ohsawa--Takegoshi restriction, `RestrictLe` form.**  If the restriction to `W` of every germ
of an ambient ideal `𝔞` (at points of `W`) lies in `𝓘_W(c φ|_W)`, then `RestrictLe W 𝔞 𝓘(c φ)`,
the ambient comparison in which `PositiveCurrentInput` is stated. -/
theorem restrictLe_multiplierIdeal_of_forall_mem (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {c : ℝ} {𝔞 : GermIdeal n X} :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    (∀ (p : W) (a : X → ℂ), 𝔞.mem p.1 a →
      (multiplierIdeal (n := k) c (fun q : W => φ q.1)).mem p (fun q : W => a q.1)) →
      RestrictLe W 𝔞 (multiplierIdeal (n := n) c φ) := by
  let := chartedSpace hk hW
  intro h x hx a ha
  exact isInSpanOnAt_multiplierIdeal_of_mem hk hW hφ x hx a (h ⟨x, hx⟩ a ha)

end Restriction

end

end TranscendentalNakamaye.Pending.RestrictionOhsawaTakegoshi
