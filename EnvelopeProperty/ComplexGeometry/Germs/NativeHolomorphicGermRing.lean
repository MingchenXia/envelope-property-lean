import EnvelopeProperty.ComplexGeometry.Germs.OriginalFlagGeometry
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.HolomorphicGermAlgebra
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.HolomorphicGermNoetherian
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.HolomorphicZeroSetThin
import Mathlib.RingTheory.LocalRing.RingHom.Basic

set_option autoImplicit false

noncomputable section

universe u v

namespace HolomorphicGerms

open Set Filter
open scoped Topology Manifold ContDiff
open ComplexGeometry ComplexGeometry.Pluripotential
open ComplexGeometry.Pluripotential.HolomorphicIdealSheaves
open ComplexGeometry.AnalyticGeometry

/-- The actual subring of original germs represented by functions holomorphic
near the original manifold point, with no valuation data in the definition. -/
def nativeHolGermSubring (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] (x : M) : Subring (Germ (𝓝 x) ℂ) where
  carrier := {g | ∃ f : M → ℂ, HolomorphicAt n f x ∧ (f : Germ (𝓝 x) ℂ) = g}
  zero_mem' := ⟨0, holomorphicAt_const 0, rfl⟩
  one_mem' := ⟨1, holomorphicAt_const 1, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun y => f y + g y, hf.add hg, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun y => f y * g y, hf.mul hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨fun y => -f y, hf.mono (fun _ h => h.neg), rfl⟩

/-- The actual original local ring `O_(M,x)`. -/
abbrev NativeHolGerm (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] (x : M) := nativeHolGermSubring n M x

namespace NativeHolGerm

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  {x : M}

/-- An actual original holomorphic function gives its actual germ. -/
def mk (f : M → ℂ) (hf : HolomorphicAt n f x) : NativeHolGerm n M x :=
  ⟨(f : Germ (𝓝 x) ℂ), f, hf, rfl⟩

theorem mk_eq_mk_iff {f g : M → ℂ} {hf : HolomorphicAt n f x}
    {hg : HolomorphicAt n g x} : mk f hf = mk g hg ↔ f =ᶠ[𝓝 x] g :=
  Subtype.ext_iff.trans Germ.coe_eq

theorem exists_eq_mk (g : NativeHolGerm n M x) :
    ∃ (f : M → ℂ) (hf : HolomorphicAt n f x), g = mk f hf := by
  obtain ⟨g, f, hf, rfl⟩ := g
  exact ⟨f, hf, rfl⟩

/-- Actual evaluation at the original point. -/
def eval : NativeHolGerm n M x →+* ℂ :=
  Germ.valueRingHom.comp (nativeHolGermSubring n M x).subtype

@[simp] theorem eval_mk (f : M → ℂ) (hf : HolomorphicAt n f x) : eval (mk f hf) = f x :=
  rfl

/-- Constants in the original germ ring. -/
def constHom : ℂ →+* NativeHolGerm n M x where
  toFun c := mk (fun _ => c) (holomorphicAt_const c)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

section Charts

variable [IsComplexManifold n M]

private def centeredPoint (x : M) (z : ComplexModel n) : M :=
  (complexChartAt (n := n) x).val.symm (z + (complexChartAt (n := n) x).val x)

private def centeredCoord (x : M) (y : M) : ComplexModel n :=
  (complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x

omit [IsComplexManifold n M] in
private theorem centeredPoint_tendsto (x : M) :
    Tendsto (centeredPoint (n := n) x) (𝓝 (0 : ComplexModel n)) (𝓝 x) := by
  let e := (complexChartAt (n := n) x).val
  have hx : x ∈ e.source := mem_complexChartAt_source x
  have hAdd : Tendsto (fun z : ComplexModel n => z + e x) (𝓝 0) (𝓝 (e x)) := by
    simpa only [zero_add] using (continuous_add_const (e x)).tendsto (0 : ComplexModel n)
  have h := (e.continuousAt_symm (e.map_source hx)).tendsto.comp hAdd
  change Tendsto (fun z : ComplexModel n => e.symm (z + e x)) (𝓝 0) (𝓝 x)
  simpa only [e.left_inv hx, Function.comp_def] using h

omit [IsComplexManifold n M] in
private theorem centeredCoord_tendsto (x : M) :
    Tendsto (centeredCoord (n := n) x) (𝓝 x) (𝓝 (0 : ComplexModel n)) := by
  have h : ContinuousAt (centeredCoord (n := n) x) x :=
    ((complexChartAt (n := n) x).val.continuousAt
      (mem_complexChartAt_source x)).sub continuousAt_const
  simpa only [centeredCoord, sub_self] using h.tendsto

omit [IsComplexManifold n M] in
private theorem eventually_centeredPoint_coord (x : M) :
    ∀ᶠ y in 𝓝 x, centeredPoint (n := n) x (centeredCoord (n := n) x y) = y := by
  filter_upwards [(complexChartAt (n := n) x).val.open_source.mem_nhds
    (mem_complexChartAt_source x)] with y hy
  simp only [centeredPoint, centeredCoord, sub_add_cancel,
    (complexChartAt (n := n) x).val.left_inv hy]

omit [IsComplexManifold n M] in
private theorem eventually_centeredCoord_point (x : M) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), centeredCoord (n := n) x (centeredPoint (n := n) x z) = z := by
  let e := (complexChartAt (n := n) x).val
  have hAdd : Tendsto (fun z : ComplexModel n => z + e x) (𝓝 0) (𝓝 (e x)) := by
    simpa only [zero_add] using (continuous_add_const (e x)).tendsto (0 : ComplexModel n)
  filter_upwards [hAdd.eventually (e.open_target.mem_nhds
    (e.map_source (mem_complexChartAt_source x)))] with z hz
  change e (e.symm (z + e x)) - e x = z
  rw [e.right_inv hz, add_sub_cancel_right]

private theorem holomorphicAt_comp_centeredPoint (x : M) {f : M → ℂ}
    (hf : HolomorphicAt n f x) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (f ∘ centeredPoint (n := n) x) z := by
  let e := (complexChartAt (n := n) x).val
  have hAdd : Tendsto (fun z : ComplexModel n => z + e x) (𝓝 0) (𝓝 (e x)) := by
    simpa only [zero_add] using (continuous_add_const (e x)).tendsto (0 : ComplexModel n)
  filter_upwards [(centeredPoint_tendsto (n := n) x).eventually hf,
    hAdd.eventually (e.open_target.mem_nhds
      (e.map_source (mem_complexChartAt_source x)))] with z hfz hz
  have hSymm : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      e.symm (z + e x) :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ, ComplexModel n)) (n := ∞) (x := x)).contMDiffAt
      (e.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
  have hPlus : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (fun w : ComplexModel n => w + e x) z :=
    (differentiableAt_id.add_const (e x)).mdifferentiableAt
  exact mdifferentiableAt_iff_differentiableAt.mp (hfz.comp z (hSymm.comp z hPlus))

private theorem holomorphicAt_comp_centeredCoord (x : M) {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ f z) :
    HolomorphicAt n (f ∘ centeredCoord (n := n) x) x := by
  filter_upwards [(centeredCoord_tendsto (n := n) x).eventually hf,
    (complexChartAt (n := n) x).val.open_source.mem_nhds
      (mem_complexChartAt_source x)] with y hfy hy
  have hChart : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (complexChartAt (n := n) x).val y :=
    ((contMDiffOn_chart (I := 𝓘(ℂ, ComplexModel n)) (n := ∞) (x := x)).contMDiffAt
      ((complexChartAt (n := n) x).val.open_source.mem_nhds hy)).mdifferentiableAt (by simp)
  exact hfy.mdifferentiableAt.comp y (hChart.sub mdifferentiableAt_const)

private def toChart (x : M) : NativeHolGerm n M x →+* HolGerm (ComplexModel n) where
  toFun g := ⟨g.1.compTendsto (centeredPoint (n := n) x) (centeredPoint_tendsto (n := n) x), by
    obtain ⟨_, f, hf, rfl⟩ := g
    exact ⟨f ∘ centeredPoint (n := n) x, holomorphicAt_comp_centeredPoint (n := n) x hf, rfl⟩⟩
  map_one' := rfl
  map_mul' g h := by
    obtain ⟨f, hf, rfl⟩ := exists_eq_mk g
    obtain ⟨g, hg, rfl⟩ := exists_eq_mk h
    rfl
  map_zero' := rfl
  map_add' g h := by
    obtain ⟨f, hf, rfl⟩ := exists_eq_mk g
    obtain ⟨g, hg, rfl⟩ := exists_eq_mk h
    rfl

private def fromChart (x : M) : HolGerm (ComplexModel n) →+* NativeHolGerm n M x where
  toFun g := ⟨g.1.compTendsto (centeredCoord (n := n) x) (centeredCoord_tendsto (n := n) x), by
    obtain ⟨_, f, hf, rfl⟩ := g
    exact ⟨f ∘ centeredCoord (n := n) x, holomorphicAt_comp_centeredCoord (n := n) x hf, rfl⟩⟩
  map_one' := rfl
  map_mul' g h := by
    obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
    obtain ⟨g, hg, rfl⟩ := HolGerm.exists_eq_mk h
    rfl
  map_zero' := rfl
  map_add' g h := by
    obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
    obtain ⟨g, hg, rfl⟩ := HolGerm.exists_eq_mk h
    rfl

/-- The actual centered original chart and its genuine inverse induce whole
inverse ring maps on original holomorphic germs. -/
def chartEquiv (x : M) : NativeHolGerm n M x ≃+* HolGerm (ComplexModel n) :=
  RingEquiv.ofRingHom (toChart x) (fromChart x)
    (by
      ext g
      obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
      apply Germ.coe_eq.mpr
      change (fun z => f (centeredCoord (n := n) x (centeredPoint (n := n) x z))) =ᶠ[𝓝 0] f
      exact (eventually_centeredCoord_point (n := n) x).mono fun z hz => congrArg f hz)
    (by
      ext g
      obtain ⟨f, hf, rfl⟩ := exists_eq_mk g
      apply Germ.coe_eq.mpr
      change (fun y => f (centeredPoint (n := n) x (centeredCoord (n := n) x y))) =ᶠ[𝓝 x] f
      exact (eventually_centeredPoint_coord (n := n) x).mono fun y hy => congrArg f hy)

theorem chartEquiv_mk (f : M → ℂ) (hf : HolomorphicAt n f x) :
    ((chartEquiv x (mk f hf) : HolGerm (ComplexModel n)) : Germ (𝓝 (0 : ComplexModel n)) ℂ) =
      (fun z : ComplexModel n =>
        f ((complexChartAt (n := n) x).val.symm (z + (complexChartAt (n := n) x).val x))) :=
  rfl

theorem eval_chartEquiv (g : NativeHolGerm n M x) : HolGerm.eval (chartEquiv x g) = eval g := by
  obtain ⟨f, hf, rfl⟩ := exists_eq_mk g
  change f ((complexChartAt (n := n) x).val.symm
    ((0 : ComplexModel n) + (complexChartAt (n := n) x).val x)) = f x
  rw [zero_add, (complexChartAt (n := n) x).val.left_inv (mem_complexChartAt_source x)]

instance isDomain : IsDomain (NativeHolGerm n M x) :=
  (chartEquiv x).toMulEquiv.isDomain (HolGerm (ComplexModel n))

instance isNoetherianRing : IsNoetherianRing (NativeHolGerm n M x) := by
  let : IsNoetherianRing (HolGerm (ComplexModel n)) := isNoetherianRing_holGerm_euclidean n
  exact isNoetherianRing_of_ringEquiv _ (chartEquiv x).symm

instance isLocalRing : IsLocalRing (NativeHolGerm n M x) := (chartEquiv x).symm.isLocalRing

theorem isUnit_iff_eval_ne_zero (g : NativeHolGerm n M x) : IsUnit g ↔ eval g ≠ 0 := by
  constructor
  · intro hg
    have h := (HolGerm.isUnit_iff_eval_ne_zero _).mp (hg.map (chartEquiv x).toRingHom)
    change HolGerm.eval (chartEquiv x g) ≠ 0 at h
    rwa [eval_chartEquiv] at h
  · intro hg
    have h : HolGerm.eval (chartEquiv x g) ≠ 0 := by rwa [eval_chartEquiv]
    have hunit := ((HolGerm.isUnit_iff_eval_ne_zero _).mpr h).map (chartEquiv x).symm.toRingHom
    change IsUnit ((chartEquiv x).symm (chartEquiv x g)) at hunit
    simpa only [RingEquiv.symm_apply_apply] using hunit

end Charts

/-- Actual holomorphic pullback of original manifold germs. -/
def comap {k : ℕ} {N : Type v} [TopologicalSpace N] [ChartedSpace (ComplexModel k) N]
    [IsComplexManifold n M] [IsComplexManifold k N]
    (b : N → M) (hb : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ b) (y : N) :
    NativeHolGerm n M (b y) →+* NativeHolGerm k N y where
  toFun g := ⟨g.1.compTendsto b hb.continuous.continuousAt, by
    obtain ⟨_, f, hf, rfl⟩ := g
    exact ⟨f ∘ b, hf.comp_contMDiff (Eventually.of_forall fun z => hb z), rfl⟩⟩
  map_one' := rfl
  map_mul' g h := by
    obtain ⟨f, hf, rfl⟩ := exists_eq_mk g
    obtain ⟨g, hg, rfl⟩ := exists_eq_mk h
    rfl
  map_zero' := rfl
  map_add' g h := by
    obtain ⟨f, hf, rfl⟩ := exists_eq_mk g
    obtain ⟨g, hg, rfl⟩ := exists_eq_mk h
    rfl

theorem comap_mk {k : ℕ} {N : Type v} [TopologicalSpace N] [ChartedSpace (ComplexModel k) N]
    [IsComplexManifold n M] [IsComplexManifold k N]
    (b : N → M) (hb : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ b) (y : N)
    (f : M → ℂ) (hf : HolomorphicAt n f (b y)) :
    ((comap b hb y (mk f hf) : NativeHolGerm k N y) : Germ (𝓝 y) ℂ) = f ∘ b :=
  rfl

theorem eval_comap {k : ℕ} {N : Type v} [TopologicalSpace N] [ChartedSpace (ComplexModel k) N]
    [IsComplexManifold n M] [IsComplexManifold k N]
    (b : N → M) (hb : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ b) (y : N)
    (g : NativeHolGerm n M (b y)) : eval (comap b hb y g) = eval g := by
  obtain ⟨f, hf, rfl⟩ := exists_eq_mk g
  rfl

end NativeHolGerm
end HolomorphicGerms
