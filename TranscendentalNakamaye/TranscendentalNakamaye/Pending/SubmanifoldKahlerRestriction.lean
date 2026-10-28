import TranscendentalNakamaye.Pending.SubmanifoldChartedSpace
import TranscendentalNakamaye.FirstPass.ClosedFormPullback
import TranscendentalNakamaye.FirstPass.HolomorphicMaps
import TranscendentalNakamaye.FirstPass.PositiveClasses

set_option autoImplicit false

/-!
# A Kähler form restricts to a Kähler form on a closed complex submanifold

Source: Copy-4, `sec:setup` (`setup`: "We write `ω_V := ω|_V` and `γ := θ|_V`",
`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1388-1396`), used
throughout `sec:positive-current`, where `V` is treated as a compact Kähler manifold with Kähler
form `ω_V`.

`Pending.SubmanifoldChartedSpace` makes a closed complex submanifold `W` of dimension `k` a
complex manifold `↥W` with holomorphic inclusion.  Here:

* `injective_fderiv_coordinateMap_val` — the inclusion is an **immersion**: in every pair of
  charts its coordinate representative has an injective real differential.  The proof exhibits
  a differentiable left inverse near the point (`ζ ↦ pr_k (Φ (amb (d⁻¹ ζ)))`, the flattening
  coordinate read through the ambient chart `d`), so the differential has a left inverse.
* `isHermitian_pullback` — the pullback of a Hermitian form is Hermitian (type `(1,1)` because
  the differential is `ℂ`-linear, strict positivity because it is injective);
* `isKahler_pullback` and `kahlerBackground` — the pullback of the Kähler form of a
  `KahlerBackground` is a Kähler form on `↥W`, i.e. `ω|_W` is a Kähler background of `↥W`.

Programme `TN.2.3.PCI` (positive-current input).  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace TranscendentalNakamaye.Pending.SubmanifoldKahlerRestriction

noncomputable section

open FirstPass FirstPass.RegularLocusDense FirstPass.BlowupSequences FirstPass.PositiveClasses
  FirstPass.HolomorphicMaps SubmanifoldChartedSpace

variable {n k : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {W : Set X} (hk : k ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)

include hk hW in
/-- **The inclusion of a closed complex submanifold is an immersion.**  In every chart `e` of
`↥W` and every chart `d` of `X`, the coordinate representative of the inclusion has an injective
real differential at every point of its domain. -/
theorem injective_fderiv_coordinateMap_val :
    letI := chartedSpace hk hW
    ∀ (e : ComplexChart k W) (d : ComplexChart n X) (z : ComplexModel k),
      z ∈ coordinateDomain (Subtype.val : W → X) e d →
        Function.Injective (fderiv ℝ (coordinateMap (Subtype.val : W → X) e d) z) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro e d z hz
  have hι := contMDiff_val hk hW
  obtain ⟨F, hF⟩ := e.property
  set g := coordinateMap (Subtype.val : W → X) e d with hg
  -- the left inverse, read through the ambient chart `d`
  set L : ComplexModel n → ComplexModel k :=
    fun y => coordinateProjection n k (F.flat (F.amb.val (d.val.symm y))) with hL
  have hzt : z ∈ e.val.target := hz.1
  have hpsrc : e.val.symm z ∈ e.val.source := e.val.map_target hzt
  have hpF : (e.val.symm z : X) ∈ F.ambSource := by
    have h : e.val.symm z ∈ (F.chart hk).source := by rw [← hF]; exact hpsrc
    exact h
  have hpd : (e.val.symm z : X) ∈ d.val.source := hz.2
  -- `L ∘ g = id` near `z`
  have hleft : L ∘ g =ᶠ[𝓝 z] id := by
    have hopen : IsOpen (coordinateDomain (Subtype.val : W → X) e d) :=
      coordinateDomain_isOpen hι e d
    filter_upwards [hopen.mem_nhds hz] with ζ hζ
    have hζsrc : e.val.symm ζ ∈ e.val.source := e.val.map_target hζ.1
    simp only [Function.comp_apply, hL, hg, coordinateMap, id]
    rw [d.val.left_inv hζ.2]
    have hchart : (F.chart hk) (e.val.symm ζ) = ζ := by
      rw [← hF]; exact e.val.right_inv hζ.1
    simpa only [FlatData.chart_apply, FlatData.toCoord] using hchart
  -- differentiability of `g` at `z` and of `L` at `g z`
  have hgd : DifferentiableAt ℝ g z :=
    (coordinateMap_contDiffAt_real hι e d hz).differentiableAt (by simp)
  have hgz : g z = d.val (e.val.symm z : X) := rfl
  have hdt : g z ∈ d.val.target := coordinateMap_mem_target hz
  have htrans : g z ∈ (chartTransition d F.amb).source := by
    refine ⟨hdt, ?_⟩
    show d.val.symm (g z) ∈ F.amb.val.source
    rw [hgz, d.val.left_inv hpd]
    exact hpF.1
  have hTd : DifferentiableAt ℝ (chartTransition d F.amb) (g z) :=
    (chartTransition_contDiffAt_real d F.amb htrans).differentiableAt (by simp)
  have hflatsrc : chartTransition d F.amb (g z) ∈ F.flat.source := by
    show F.amb.val (d.val.symm (g z)) ∈ F.flat.source
    rw [hgz, d.val.left_inv hpd]
    exact hpF.2
  have hflatd : DifferentiableAt ℝ F.flat (chartTransition d F.amb (g z)) :=
    ((F.differentiableOn_flat.differentiableAt
      (F.flat.open_source.mem_nhds hflatsrc))).restrictScalars ℝ
  have hLd : DifferentiableAt ℝ L (g z) := by
    have h1 : DifferentiableAt ℝ (fun y => F.flat (chartTransition d F.amb y)) (g z) :=
      hflatd.comp (g z) hTd
    have h2 := ((coordinateProjection n k).restrictScalars ℝ).differentiableAt.comp (g z) h1
    exact h2
  -- the chain rule
  have hcomp : (fderiv ℝ L (g z)).comp (fderiv ℝ g z) = ContinuousLinearMap.id ℝ _ := by
    rw [← fderiv_comp z hLd hgd, hleft.fderiv_eq, fderiv_id]
  intro a b hab
  have := congrArg (fderiv ℝ L (g z)) hab
  have ha := congrArg (fun T : ComplexModel k →L[ℝ] ComplexModel k => T a) hcomp
  have hb := congrArg (fun T : ComplexModel k →L[ℝ] ComplexModel k => T b) hcomp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at ha hb
  rw [← ha, ← hb, this]

include hk hW in
/-- **The pullback of a Hermitian form to a closed complex submanifold is Hermitian.** -/
theorem isHermitian_pullback {β : SmoothRealForm n X 2} (hβ : β.IsHermitian) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    (SmoothRealForm.pullback (contMDiff_val hk hW) β).IsHermitian := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  have hι := contMDiff_val hk hW
  intro e z hz
  set d := complexChartAt (n := n) ((e.val.symm z : W) : X) with hd
  have hzd : z ∈ coordinateDomain (Subtype.val : W → X) e d :=
    ⟨hz, mem_complexChartAt_source _⟩
  have hinj := injective_fderiv_coordinateMap_val hk hW e d z hzd
  set D := fderiv ℝ (coordinateMap (Subtype.val : W → X) e d) z with hD
  have hDI : ∀ v, D (Complex.I • v) = Complex.I • D v := fun v =>
    coordinateMap_fderiv_map_smul_complex hι e d hzd Complex.I v
  have hvec : ∀ u v : ComplexModel k, (⇑D ∘ ![u, v]) = ![D u, D v] := by
    intro u v
    funext i
    fin_cases i <;> rfl
  obtain ⟨hβ11, hβpos⟩ := hβ d _ (coordinateMap_mem_target hzd)
  rw [SmoothRealForm.pullback_coeff hι β e d hzd]
  refine ⟨fun u v => ?_, fun u hu => ?_⟩
  · simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ← hD]
    rw [hvec, hvec, hDI, hDI]
    exact hβ11 (D u) (D v)
  · simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ← hD]
    rw [hvec, hDI]
    refine hβpos (D u) ?_
    intro h0
    exact hu (hinj (h0.trans (map_zero D).symm))

include hk hW in
/-- **The pullback of a Kähler form to a closed complex submanifold is a Kähler form.** -/
theorem isKahler_pullback (a : ClosedRealOneOneForm n X) (ha : a.val.IsKahler) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    (ClosedRealOneOneForm.pullback (contMDiff_val hk hW) a).val.IsKahler := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  exact ⟨isHermitian_pullback hk hW ha.1, (ClosedRealOneOneForm.pullback (contMDiff_val hk hW) a).property.1⟩

/-- **`ω|_W` is a Kähler background of the submanifold `↥W`** (Copy-4's `ω_V`). -/
def kahlerBackground (omega : KahlerBackground n X) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    KahlerBackground k W :=
  letI := chartedSpace hk hW
  haveI := isComplexManifold_chartedSpace hk hW
  { form := ClosedRealOneOneForm.pullback (contMDiff_val hk hW) omega.form
    isKahler := isKahler_pullback hk hW omega.form omega.isKahler }

theorem kahlerBackground_form (omega : KahlerBackground n X) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    (kahlerBackground hk hW omega).form =
      ClosedRealOneOneForm.pullback (contMDiff_val hk hW) omega.form := rfl

end

end TranscendentalNakamaye.Pending.SubmanifoldKahlerRestriction
