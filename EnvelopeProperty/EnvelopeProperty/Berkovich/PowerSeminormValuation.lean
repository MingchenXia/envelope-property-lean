/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.CompactMinimal
import Mathlib.Analysis.Normed.Unbundled.SeminormFromConst
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.RingTheory.Valuation.Basic

open scoped NNReal
open Set Topology
noncomputable section
namespace EnvelopeProperty.Berkovich
variable {A : Type*} [CommRing A]

/-- The genuine closed bounded cone of normalized power-multiplicative seminorm functions, fixing original multiplicative elements. -/
def powerSeminormCone (μ : RingSeminorm A) (M : Set A) : Set (A → ℝ) :=
  {f | (∀ a, 0 ≤ f a) ∧ (∀ a, f a ≤ μ a) ∧ f 0 = 0 ∧ f 1 = 1 ∧
    (∀ a, f (-a) = f a) ∧ IsNonarchimedean f ∧
    (∀ a b, f (a*b) ≤ f a * f b) ∧ IsPowMul f ∧
    ∀ c ∈ M, f c = μ c ∧ ∀ a, f (c*a) = f c * f a}

private theorem closed_forall {X : Type*} {ι : Sort*} [TopologicalSpace X] (p : ι → X → Prop)
    (hp : ∀ i, IsClosed {x | p i x}) : IsClosed {x | ∀ i, p i x} := by
  have he : {x | ∀ i, p i x} = ⋂ i, {x | p i x} := by ext x; simp
  rw [he]
  exact isClosed_iInter hp

/-- Every original seminorm-cone identity is a closed coordinate condition. -/
theorem isClosed_powerSeminormCone (μ : RingSeminorm A) (M : Set A) :
    IsClosed (powerSeminormCone μ M) := by
  unfold powerSeminormCone
  refine (closed_forall _ fun a => isClosed_le continuous_const (continuous_apply a)).inter ?_
  refine (closed_forall _ fun a => isClosed_le (continuous_apply a) continuous_const).inter ?_
  refine (isClosed_eq (continuous_apply 0) continuous_const).inter ?_
  refine (isClosed_eq (continuous_apply 1) continuous_const).inter ?_
  refine (closed_forall _ fun a => isClosed_eq (continuous_apply (-a)) (continuous_apply a)).inter ?_
  refine (closed_forall _ fun a => closed_forall _ fun b =>
    isClosed_le (continuous_apply (a+b)) ((continuous_apply a).max (continuous_apply b))).inter ?_
  refine (closed_forall _ fun a => closed_forall _ fun b =>
    isClosed_le (continuous_apply (a*b)) ((continuous_apply a).mul (continuous_apply b))).inter ?_
  refine (closed_forall _ fun (a : A) => closed_forall _ fun (n : ℕ) =>
    closed_forall _ fun (_ : 1 ≤ n) =>
      isClosed_eq (f := fun f : A → ℝ => f (a^n))
        (g := fun f : A → ℝ => (f a)^n) (continuous_apply (a^n))
        ((continuous_apply a).pow n)).inter ?_
  exact closed_forall _ fun c => closed_forall _ fun _ =>
    (isClosed_eq (continuous_apply c) continuous_const).inter
      (closed_forall _ fun a => isClosed_eq (continuous_apply (c*a))
        ((continuous_apply c).mul (continuous_apply a)))

/-- The whole original seminorm cone is compact in the product topology, even if its conditions are inconsistent. -/
theorem isCompact_powerSeminormCone (μ : RingSeminorm A) (M : Set A) :
    IsCompact (powerSeminormCone μ M) := by
  apply (isCompact_univ_pi fun a => isCompact_Icc (a := (0 : ℝ)) (b := μ a)).of_isClosed_subset
    (isClosed_powerSeminormCone μ M)
  intro f hf a _
  exact ⟨hf.1 a, hf.2.1 a⟩

private theorem self_mem_powerSeminormCone (μ : RingSeminorm A) (h1 : μ 1 = 1)
    (hna : IsNonarchimedean μ) (hpow : IsPowMul μ) (M : Set A)
    (hM : ∀ c ∈ M, ∀ a, μ (c*a) = μ c * μ a) : (μ : A → ℝ) ∈ powerSeminormCone μ M := by
  exact ⟨apply_nonneg μ, fun _ => le_rfl, map_zero μ, h1, map_neg_eq_map μ,
    hna, fun a b => map_mul_le_mul μ a b, hpow, fun c hc => ⟨rfl, hM c hc⟩⟩

/-- The actual compact cone constructs a genuine minimal ORIGINAL ring seminorm preserving the specified values. -/
theorem exists_minimal_powerSeminormCone (μ : RingSeminorm A) (hμ1 : μ 1 = 1)
    (hμna : IsNonarchimedean μ) (hμpow : IsPowMul μ) (M : Set A)
    (hM : ∀ c ∈ M, ∀ a, μ (c*a) = μ c * μ a) :
    ∃ F : RingSeminorm A, (F : A → ℝ) ∈ powerSeminormCone μ M ∧
      ∀ G : RingSeminorm A, (G : A → ℝ) ∈ powerSeminormCone μ M →
        (∀ a, G a ≤ F a) → ∀ a, F a ≤ G a := by
  classical
  obtain ⟨f, hf, hmin⟩ := EnvelopeProperty.exists_minimal_mem_of_isCompact
    (isCompact_powerSeminormCone μ M) ⟨μ, self_mem_powerSeminormCone μ hμ1 hμna hμpow M hM⟩
  rcases hf with ⟨hpos, hbound, hzero, hone, hneg, hadd, hmul, hpow, hMf⟩
  let F : RingSeminorm A :=
    { toFun := f
      map_zero' := hzero
      add_le' := fun a b => (hadd a b).trans
        (max_le (le_add_of_nonneg_right (hpos b)) (le_add_of_nonneg_left (hpos a)))
      neg' := hneg
      mul_le' := hmul }
  exact ⟨F, ⟨hpos, hbound, hzero, hone, hneg, hadd, hmul, hpow, hMf⟩,
    fun G hG hle => hmin G hG hle⟩

/-- Construct a genuine bounded valuation preserving ALL original elements multiplicative for the given seminorm. -/
theorem exists_valuation_le_preserving_mul (μ : RingSeminorm A) (hμ1 : μ 1 = 1)
    (hμna : IsNonarchimedean μ) (hμpow : IsPowMul μ) (M : Set A)
    (hM : ∀ c ∈ M, ∀ a, μ (c*a) = μ c * μ a) :
    ∃ v : Valuation A ℝ≥0, (∀ a, (v a : ℝ) ≤ μ a) ∧ ∀ c ∈ M, (v c : ℝ) = μ c := by
  classical
  obtain ⟨F, hf, hmin⟩ := exists_minimal_powerSeminormCone μ hμ1 hμna hμpow M hM
  rcases hf with ⟨hpos, hbound, hzero, hone, hneg, hadd, hmul, hpow, hMf⟩
  have hF1 : F 1 ≤ 1 := hone.le
  have hfull : ∀ a b, F (a*b) = F a * F b := by
    intro a b
    by_cases ha : F a = 0
    · rw [ha, zero_mul]
      exact le_antisymm (by simpa only [ha, zero_mul] using hmul a b) (hpos (a*b))
    let G := seminormFromConst hF1 (show F a ≠ 0 from ha) (show IsPowMul F from hpow)
    have hle : (G : A → ℝ) ≤ F := fun x =>
      seminormFromConst_le_seminorm hF1 ha hpow x
    have hG1 : G 1 = 1 := seminormFromConst_one hF1 ha hpow
    have hGna : IsNonarchimedean G := seminormFromConst_isNonarchimedean hF1 ha hpow hadd
    have hGpow : IsPowMul G := seminormFromConst_isPowMul hF1 ha hpow
    have hGM : ∀ c ∈ M, G c = μ c ∧ ∀ x, G (c*x) = G c * G x := by
      intro c hc
      have hc_mul : ∀ x, F (c*x) = F c * F x := (hMf c hc).2
      constructor
      · exact (seminormFromConst_apply_of_isMul hF1 ha hpow hc_mul).trans (hMf c hc).1
      · exact seminormFromConst_isMul_of_isMul hF1 ha hpow hc_mul
    have hG : (G : A → ℝ) ∈ powerSeminormCone μ M :=
      ⟨apply_nonneg G, fun x => (hle x).trans (hbound x), map_zero G, hG1,
        map_neg_eq_map G, hGna, fun x y => map_mul_le_mul G x y, hGpow, hGM⟩
    have heq : ∀ x, F x = G x := fun x => le_antisymm (hmin G hG hle x) (hle x)
    have hGmul : G (a*b) = G a * G b := seminormFromConst_const_mul hF1 ha hpow b
    exact (heq (a*b)).trans (hGmul.trans (congrArg₂ (fun x y : ℝ => x*y) (heq a).symm (heq b).symm))
  let v : Valuation A ℝ≥0 :=
    { toFun := fun a => ⟨F a, hpos a⟩
      map_zero' := Subtype.ext hzero
      map_one' := Subtype.ext hone
      map_mul' := fun a b => Subtype.ext (hfull a b)
      map_add_le_max' := fun a b => hadd a b }
  exact ⟨v, hbound, fun c hc => (hMf c hc).1⟩

/-- A genuine original-ring bounded valuation ATTAINS the seminorm of any chosen original element. -/
theorem exists_valuation_le_attaining (μ : RingSeminorm A) (hμ1 : μ 1 = 1)
    (hμna : IsNonarchimedean μ) (hμpow : IsPowMul μ) (b : A) :
    ∃ v : Valuation A ℝ≥0, (∀ a, (v a : ℝ) ≤ μ a) ∧ (v b : ℝ) = μ b := by
  classical
  by_cases hb : μ b = 0
  · obtain ⟨v, hv, _⟩ := exists_valuation_le_preserving_mul μ hμ1 hμna hμpow ∅ (by simp)
    refine ⟨v, hv, le_antisymm (hv b) ?_⟩
    rw [hb]
    exact NNReal.coe_nonneg _
  · let G := seminormFromConst hμ1.le hb hμpow
    have hG1 : G 1 = 1 := seminormFromConst_one hμ1.le hb hμpow
    have hGna : IsNonarchimedean G := seminormFromConst_isNonarchimedean hμ1.le hb hμpow hμna
    have hGpow : IsPowMul G := seminormFromConst_isPowMul hμ1.le hb hμpow
    have hGM : ∀ c ∈ ({b} : Set A), ∀ a, G (c*a) = G c * G a := by
      intro c hc a
      have hc' : c = b := Set.mem_singleton_iff.mp hc
      subst c
      exact seminormFromConst_const_mul hμ1.le hb hμpow a
    obtain ⟨v, hv, hval⟩ := exists_valuation_le_preserving_mul G hG1 hGna hGpow {b} hGM
    refine ⟨v, fun a => (hv a).trans (seminormFromConst_le_seminorm hμ1.le hb hμpow a), ?_⟩
    exact (hval b (by simp)).trans (seminormFromConst_apply_c hμ1.le hb hμpow)

end EnvelopeProperty.Berkovich
