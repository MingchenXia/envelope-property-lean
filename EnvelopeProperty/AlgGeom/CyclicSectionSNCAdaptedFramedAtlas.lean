import EnvelopeProperty.AlgGeom.CyclicSectionSNCUniformFramedCharts
import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverGluing
import Mathlib.AlgebraicGeometry.RelativeGluing

/-! # The actual original adapted framed affine atlas

All chart equations retain the SAME original divisor-family index and
multiplicity function. Original geometry produces the charts internally;
native affine restriction and the original frame cocycle produce the
locally directed actual cover and its actual coefficient laws.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Modules
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.CyclicSectionSNCAdaptedFramedAtlas
open CanonicalGeometry CyclicSectionGlobalCoverFrames
variable {X : Scheme.{u}}

/-- Actual framed affine data, with the same original labelled whole components. -/
abbrev ChartData (L : X.Modules) (n : ℕ)
    (s : unitObj X ⟶ bundleTensorPower L n) (F : Scheme.DivisorFamily X) (a : F.ι → ℕ) :=
  Σ U : X.affineOpens,
    Σ e : (Scheme.Modules.pullback U.1.ι).obj L ≅ unitObj U.1.toScheme,
      {gb : (F.ι → Γ(X, U.1)) × (Γ(X, U.1))ˣ //
        Nonempty U.1 ∧
        (∀ i, (F.component i).ideal U = Ideal.span {gb.1 i}) ∧
        (∀ i, gb.1 i ≠ 0) ∧
        U.1.topIso.hom (sectionCoefficient L n s U.1.ι e) =
          (gb.2 : Γ(X, U.1)) * ∏ i, gb.1 i ^ a i}

section Charts

variable {L : X.Modules} {n : ℕ} {s : unitObj X ⟶ bundleTensorPower L n}
variable {F : Scheme.DivisorFamily X} {a : F.ι → ℕ}

abbrev chartAffine (c : ChartData L n s F a) : X.affineOpens := c.1

abbrev chartFrame (c : ChartData L n s F a) :
    (Scheme.Modules.pullback (chartAffine c).1.ι).obj L ≅ unitObj (chartAffine c).1.toScheme := c.2.1

abbrev chartBranches (c : ChartData L n s F a) : F.ι → Γ(X, (chartAffine c).1) := c.2.2.1.1

abbrev chartUnit (c : ChartData L n s F a) : (Γ(X, (chartAffine c).1))ˣ := c.2.2.1.2

theorem chart_nonempty (c : ChartData L n s F a) : Nonempty (chartAffine c).1 := c.2.2.2.1

theorem chart_branches_ideal (c : ChartData L n s F a) (i : F.ι) :
    (F.component i).ideal (chartAffine c) = Ideal.span {chartBranches c i} := c.2.2.2.2.1 i

theorem chart_branches_nonzero (c : ChartData L n s F a) (i : F.ι) :
    chartBranches c i ≠ 0 := c.2.2.2.2.2.1 i

abbrev chartCoefficient (c : ChartData L n s F a) : Γ(X, (chartAffine c).1) :=
  (chartAffine c).1.topIso.hom (sectionCoefficient L n s (chartAffine c).1.ι (chartFrame c))

theorem chart_coefficient_eq (c : ChartData L n s F a) :
    chartCoefficient c = (chartUnit c : Γ(X, (chartAffine c).1)) *
      ∏ i, chartBranches c i ^ a i := c.2.2.2.2.2.2

/-- Original base integrality, rather than cyclic-cover integrality, gives the actual nonzero coefficient. -/
theorem chart_coefficient_nonzero [IsIntegral X] (c : ChartData L n s F a) :
    chartCoefficient c ≠ 0 := by
  let : Nonempty (chartAffine c).1 := chart_nonempty c
  rw [chart_coefficient_eq]
  exact mul_ne_zero (chartUnit c).ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (chart_branches_nonzero c i))

private theorem topIso_hom_appTop {U W : X.Opens} (h : W ≤ U) (z : Γ(U.toScheme, ⊤)) :
    W.topIso.hom ((X.homOfLE h).appTop z) =
      X.presheaf.map (homOfLE h).op (U.topIso.hom z) := by
  have hn := X.restrictFunctorΓ.hom.naturality (homOfLE h).op
  change (X.homOfLE h).appTop ≫ W.topIso.hom =
    U.topIso.hom ≫ X.presheaf.map (homOfLE h).op at hn
  exact congrArg (fun q : Γ(U.toScheme, ⊤) ⟶ Γ(X, W) => q z) hn

/-- Literal restriction of the actual equations, unit and native transported original frame. -/
def restrictChart [IsIntegral X] (c : ChartData L n s F a)
    (W : X.affineOpens) (hW : Nonempty W.1) (h : W.1 ≤ (chartAffine c).1) :
    ChartData L n s F a := by
  let : Nonempty W.1 := hW
  let ρ := X.presheaf.map (homOfLE h).op
  refine ⟨W, frameViaFactor (X.homOfLE h) (chartAffine c).1.ι W.1.ι
    (X.homOfLE_ι h) (chartFrame c),
    ⟨⟨fun i => ρ (chartBranches c i), Units.map ρ.hom.toMonoidHom (chartUnit c)⟩,
      hW, ?_, ?_, ?_⟩⟩
  · intro i
    change (F.component i).ideal W = Ideal.span {ρ.hom (chartBranches c i)}
    rw [← (F.component i).map_ideal h, chart_branches_ideal c i,
      Ideal.map_span, Set.image_singleton]
    rfl
  · intro i hz
    apply chart_branches_nonzero c i
    apply map_injective_of_isIntegral X (homOfLE h)
    simpa only [map_zero] using hz
  · rw [sectionCoefficient_factor, topIso_hom_appTop h]
    change ρ (chartCoefficient c) =
      (Units.map ρ.hom.toMonoidHom (chartUnit c) : Γ(X, W.1)) *
        ∏ i, ρ (chartBranches c i) ^ a i
    rw [chart_coefficient_eq c, map_mul, map_prod]
    simp only [map_pow]
    rfl

theorem restrictChart_affine [IsIntegral X] (c : ChartData L n s F a)
    (W : X.affineOpens) (hW : Nonempty W.1) (h : W.1 ≤ (chartAffine c).1) :
    chartAffine (restrictChart c W hW h) = W := rfl

theorem restrictChart_branches [IsIntegral X] (c : ChartData L n s F a)
    (W : X.affineOpens) (hW : Nonempty W.1) (h : W.1 ≤ (chartAffine c).1) (i : F.ι) :
    chartBranches (restrictChart c W hW h) i =
      X.presheaf.map (homOfLE h).op (chartBranches c i) := rfl

theorem restrictChart_frame [IsIntegral X] (c : ChartData L n s F a)
    (W : X.affineOpens) (hW : Nonempty W.1) (h : W.1 ≤ (chartAffine c).1) :
    chartFrame (restrictChart c W hW h) =
      frameViaFactor (X.homOfLE h) (chartAffine c).1.ι W.1.ι
        (X.homOfLE_ι h) (chartFrame c) := rfl

theorem restrictChart_unit [IsIntegral X] (c : ChartData L n s F a)
    (W : X.affineOpens) (hW : Nonempty W.1) (h : W.1 ≤ (chartAffine c).1) :
    chartUnit (restrictChart c W hW h) =
      Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom (chartUnit c) := rfl

/-- Actual adapted charts retain exactly the actual inclusion category of their original opens. -/
abbrev Chart (L : X.Modules) (n : ℕ) (s : unitObj X ⟶ bundleTensorPower L n)
    (F : Scheme.DivisorFamily X) (a : F.ι → ℕ) :=
  InducedCategory X.Opens (fun c : ChartData L n s F a => (chartAffine c).1)

instance chart_isThin : Quiver.IsThin (Chart L n s F a) :=
  fun _ _ => ⟨fun f g => InducedCategory.hom_ext (Subsingleton.elim f.hom g.hom)⟩

/-- The actual original framed open, with no equation or compatibility certificate added. -/
def framedOpen (c : ChartData L n s F a) : CyclicSectionGlobalCoverGluing.FramedOpen L :=
  ⟨(chartAffine c).1, chartFrame c⟩

def framedArrow {c d : Chart L n s F a} (h : c ⟶ d) : framedOpen c ⟶ framedOpen d :=
  InducedCategory.homMk h.hom

def framedFunctor : Chart L n s F a ⥤ CyclicSectionGlobalCoverGluing.FramedOpen L where
  obj := framedOpen
  map := framedArrow
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The native original frame unit, in the SAME actual affine section ring. -/
def frameUnit {c d : Chart L n s F a} (h : c ⟶ d) : (Γ(X, (chartAffine c).1))ˣ :=
  Units.map (chartAffine c).1.topIso.hom.hom.toMonoidHom
    (CyclicSectionGlobalCoverGluing.frameUnit L (framedArrow h))

private theorem topIso_map_units {U W : X.Opens} (h : W ≤ U) (v : Γ(U.toScheme, ⊤)ˣ) :
    Units.map W.topIso.hom.hom.toMonoidHom
        (Units.map (X.homOfLE h).appTop.hom.toMonoidHom v) =
      Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom
        (Units.map U.topIso.hom.hom.toMonoidHom v) := by
  apply Units.ext
  exact topIso_hom_appTop h v

theorem frameUnit_id (c : Chart L n s F a) : frameUnit (𝟙 c) = 1 := by
  unfold frameUnit
  rw [show framedArrow (𝟙 c) = 𝟙 (framedOpen c) from rfl,
    CyclicSectionGlobalCoverGluing.frameUnit_id, map_one]

theorem frameUnit_comp {c d e : Chart L n s F a} (h : c ⟶ d) (k : d ⟶ e) :
    frameUnit (h ≫ k) = frameUnit h *
      Units.map (X.presheaf.map h.hom.op).hom.toMonoidHom (frameUnit k) := by
  unfold frameUnit
  rw [show framedArrow (h ≫ k) = framedArrow h ≫ framedArrow k from rfl,
    CyclicSectionGlobalCoverGluing.frameUnit_comp, map_mul]
  congr 1
  exact topIso_map_units h.hom.le _

/-- The actual original coefficient law is derived from the original native frame cocycle. -/
theorem coefficient_transition {c d : Chart L n s F a} (h : c ⟶ d) :
    X.presheaf.map h.hom.op (chartCoefficient d) =
      (frameUnit h : Γ(X, (chartAffine c).1)) ^ n * chartCoefficient c := by
  have hv := congrArg (fun z => (chartAffine c).1.topIso.hom z)
    (CyclicSectionGlobalCoverGluing.coefficient_transition L n s (framedArrow h))
  change (chartAffine c).1.topIso.hom ((X.homOfLE h.hom.le).appTop
      (sectionCoefficient L n s (chartAffine d).1.ι (chartFrame d))) = _ at hv
  rw [topIso_hom_appTop, map_mul, map_pow] at hv
  exact hv

end Charts

variable (L : X.Modules) (hL : IsInvertible L) (n : ℕ)
  (s : unitObj X ⟶ bundleTensorPower L n)
local notation "J₀" => LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L n)
  (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n) s

theorem exists_chart_at [IsIntegral X] {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) (d : ℕ) [SmoothOfRelativeDimension d f]
    {F : Scheme.DivisorFamily X} (hF : F.IsSnc) (a : F.ι → ℕ)
    (hJF : J₀ = ∏ i, F.component i ^ a i) (y : X) :
    ∃ c : ChartData L n s F a, y ∈ (chartAffine c).1 := by
  obtain ⟨U, hy, e, g, b, hI, hg, hcoef, _⟩ :=
    CyclicSectionSNCUniformFramedCharts.exists_uniform_framed_chart_at L hL n s f d hF a hJF y
  exact ⟨⟨U, e, ⟨⟨g, b⟩, ⟨⟨y, hy⟩⟩, hI, hg, hcoef⟩⟩, hy⟩

theorem exists_finite_chart_opens [IsIntegral X] {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) (d : ℕ) [SmoothOfRelativeDimension d f] [CompactSpace X]
    {F : Scheme.DivisorFamily X} (hF : F.IsSnc) (a : F.ι → ℕ)
    (hJF : J₀ = ∏ i, F.component i ^ a i) :
    ∃ t : Finset X.affineOpens, (∀ y : X, ∃ U ∈ t, y ∈ U.1) ∧
      ∀ U ∈ t, ∃ c : ChartData L n s F a, chartAffine c = U := by
  obtain ⟨t, hcover, hdata⟩ :=
    CyclicSectionSNCUniformFramedCharts.exists_finite_uniform_framed_cover L hL n s f d hF a hJF
  refine ⟨t, hcover, ?_⟩
  intro U hU
  obtain ⟨hU_nonempty, e, g, b, hI, hg, hcoef, _⟩ := hdata U hU
  exact ⟨⟨U, e, ⟨⟨g, b⟩, hU_nonempty, hI, hg, hcoef⟩⟩, rfl⟩

variable [IsIntegral X] {k : Type u} [Field k] [PerfectField k]
variable (f : X ⟶ Spec (.of k)) (d : ℕ) [SmoothOfRelativeDimension d f]
variable {F : Scheme.DivisorFamily X} (hF : F.IsSnc) (a : F.ι → ℕ)

/-- A native cover by all actual adapted charts, internally generated from the ORIGINAL data. -/
abbrev atlasCover (hJF : J₀ = ∏ i, F.component i ^ a i) : X.OpenCover where
  I₀ := Chart L n s F a
  X c := (chartAffine c).1.toScheme
  f c := (chartAffine c).1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun y => ?_, inferInstance⟩
    obtain ⟨c, hy⟩ := exists_chart_at L hL n s f d hF a hJF y
    exact ⟨c, ⟨⟨y, hy⟩, rfl⟩⟩

/-- Genuine common affine neighborhoods, with actual restricted chart data, give local directedness. -/
@[instance_reducible] def atlasCover_locallyDirected (hJF : J₀ = ∏ i, F.component i ^ a i) :
    (atlasCover L hL n s f d hF a hJF).LocallyDirected where
  trans h := X.homOfLE h.hom.le
  trans_id c := Scheme.homOfLE_rfl _ _
  trans_comp h k := (Scheme.homOfLE_homOfLE X h.hom.le k.hom.le).symm
  w h := Scheme.homOfLE_ι _ _
  directed {c e} x := by
    let xc := pullback.fst ((chartAffine c).1.ι) ((chartAffine e).1.ι) x
    let xe := pullback.snd ((chartAffine c).1.ι) ((chartAffine e).1.ι) x
    have he : xc.1 = xe.1 :=
      congrArg (fun q : pullback ((chartAffine c).1.ι) ((chartAffine e).1.ι) ⟶ X => q x)
        (pullback.condition (f := (chartAffine c).1.ι) (g := (chartAffine e).1.ι))
    obtain ⟨W, hWa, hxW, hW⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (U := (chartAffine c).1 ⊓ (chartAffine e).1) ⟨xc.2, he ▸ xe.2⟩
    have hWc : W ≤ (chartAffine c).1 := hW.trans inf_le_left
    have hWe : W ≤ (chartAffine e).1 := hW.trans inf_le_right
    let cW : Chart L n s F a := restrictChart c ⟨W, hWa⟩ ⟨⟨xc.1, hxW⟩⟩ hWc
    refine ⟨cW, InducedCategory.homMk (homOfLE hWc),
      InducedCategory.homMk (homOfLE hWe), ⟨xc.1, hxW⟩, ?_⟩
    apply (pullback.fst ((chartAffine c).1.ι) ((chartAffine e).1.ι)).injective
    have hw : X.homOfLE hWc ≫ (chartAffine c).1.ι =
        X.homOfLE hWe ≫ (chartAffine e).1.ι := by
      rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
    have hfst := congrArg (fun q : W.toScheme ⟶ (chartAffine c).1.toScheme => q ⟨xc.1, hxW⟩)
      (pullback.lift_fst _ _ hw)
    exact hfst.trans (Subtype.ext (Scheme.homOfLE_apply _ _))

end EnvelopeProperty.CyclicSectionSNCAdaptedFramedAtlas

