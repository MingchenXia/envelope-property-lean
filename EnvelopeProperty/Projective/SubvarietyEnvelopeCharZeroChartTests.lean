/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietyComparison

/-!
# Shilov comparison with the original chart valuation witnesses retained

The finite sets in the original Shilov argument consist of the original
trivial point and actual chart points attached to Rees DVRs of `A_j[t]`.
This file retains those witnesses while following the same comparison
proof. No restriction of an arbitrary cone DVR to a smaller field is used.
-/

open scoped NNReal ENNReal Topology Polynomial

open Set Topology Filter IsDiscreteValuationRing

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace EnvelopeProperty

open ProjBerk (gaussExt logAbs gaussRadius coneGen coneSup)

universe u

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}

/-- The actual original chart points used by the Shilov proof, together with
its original trivial point. The chart, birational DVR, positive parameter
order and torus identity are retained as genuine mathematical witnesses. -/
def IsChartTestPoint (X : ProjSubvariety k M) (v : X.an) : Prop :=
  v = X.triv ∨ ∃ (j : X.ChartIdx) (V : BirationalDVR k (X.ChartRing j.1)) (b : ℕ),
    0 < b ∧ (∀ F : X.ChartRing j.1, V.ord F = F.support.inf fun ℓ =>
      V.ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞)) ∧
    v = X.chartDivPoint j.1 V b

/-- Actual chart data give an actual chart test point. -/
theorem isChartTestPoint_chartDivPoint (j : X.ChartIdx)
    (V : BirationalDVR k (X.ChartRing j.1)) (b : ℕ) (hb : 0 < b)
    (htorus : ∀ F : X.ChartRing j.1, V.ord F = F.support.inf fun ℓ =>
      V.ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞)) :
    X.IsChartTestPoint (X.chartDivPoint j.1 V b) :=
  Or.inr ⟨j, V, b, hb, htorus, rfl⟩

/-- Every retained chart test is a divisorial point in the original sense. -/
theorem IsChartTestPoint.isDivisorial {v : X.an} (hv : X.IsChartTestPoint v) :
    X.IsDivisorial v := by
  rcases hv with rfl | ⟨j, V, b, hb, htorus, rfl⟩
  · exact isDivisorial_triv X
  · exact isDivisorial_chartDivPoint V b hb htorus

/-- The retained positive integer is the actual order of the original
parameter, rather than an auxiliary label on the chart valuation. -/
theorem chartTest_ord_X (j : X.ChartIdx) (V : BirationalDVR k (X.ChartRing j.1))
    (b : ℕ) (htorus : ∀ F : X.ChartRing j.1, V.ord F = F.support.inf fun ℓ =>
      V.ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞)) :
    V.ord Polynomial.X = (b : ℕ∞) := by
  simpa using htorus (Polynomial.X : X.ChartRing j.1)

section Rees

variable [IsAlgClosed k] {ι : Type*} [Fintype ι]
  (s : ι → MvPolynomial (Fin (M + 1)) k) (e : ι → ℕ)

attribute [local instance] isNoetherianRing_reesNormalChart_dehomGen finite_reesIndex_dehomGen

/-- The original Rees/Shilov polynomial comparison, retaining the actual
chart valuation witness at every point of the finite comparison set. -/
theorem exists_finset_chartTest_shilov_core {d : ℕ} (hs : ∀ i, (s i).IsHomogeneous d)
    (hz : ∀ v : X.an, ∃ i, v.1.1.val (s i) ≠ 0) :
    ∃ S : Finset X.an, X.triv ∈ S ∧ (∀ w ∈ S, X.IsChartTestPoint w) ∧
      ∀ (c : ℕ) (F : (MvPolynomial (Fin (M + 1)) k)[X]), (∀ ℓ, (F.coeff ℓ).IsHomogeneous c) →
        ∀ r : ℕ, (∀ w ∈ S, (gaussExt w.1).val F ≤
          (Finset.univ.sup fun i => (gaussExt w.1).val (coneGen s e i)) ^ r) →
        ∀ v : X.an, (gaussExt v.1).val F ≤
          (Finset.univ.sup fun i => (gaussExt v.1).val (coneGen s e i)) ^ r := by
  have hN : ∀ j : X.ChartIdx, ∃ N : ℕ, (Polynomial.X : X.ChartRing j.1) ^ N ∈
      Ideal.span (Set.range (X.dehomGen s e j.1)) := fun j =>
    X_pow_mem_span_dehomGen s e (fun i => ⟨d, hs i⟩) hz j.1
  have : Nonempty ι := let ⟨i, _⟩ := hz X.triv; ⟨i⟩
  have hfin : (insert X.triv (⋃ j : X.ChartIdx, Set.range (reesPoint s e j)) :
      Set X.an).Finite :=
    (Set.finite_iUnion fun j => Set.finite_range _).insert _
  have hmem : ∀ (j : X.ChartIdx) x, reesPoint s e j x ∈ hfin.toFinset := fun j x =>
    hfin.mem_toFinset.2 (Or.inr (Set.mem_iUnion.2 ⟨j, x, rfl⟩))
  refine ⟨hfin.toFinset, hfin.mem_toFinset.2 (Or.inl rfl), fun w hw => ?_,
    fun c F hF r h v => ?_⟩
  · rcases hfin.mem_toFinset.1 hw with rfl | hw
    · exact Or.inl rfl
    · obtain ⟨j, x, rfl⟩ := Set.mem_iUnion.1 hw
      exact isChartTestPoint_chartDivPoint j (reesDVR s e j x) (reesOrdX s e j x)
        (reesOrdX_pos s e j x (hN j)) (reesDVR_torus s e j x)
  · obtain ⟨j₀, hj⟩ := ProjBerk.exists_val_X_eq_one v.1
    have hjI : MvPolynomial.X j₀ ∉ X.ideal :=
      notMem_ideal_of_val_ne_zero (val_X_ne_zero_of_eq_one hj)
    have : Fact (MvPolynomial.X j₀ ∉ X.ideal) := ⟨hjI⟩
    have : ∀ ℓ, IsNoetherianRing
        (reesNormalChart (FractionRing (X.ChartRing j₀)) (X.dehomGen s e j₀) ℓ) := fun ℓ =>
      isNoetherianRing_reesNormalChart (FractionRing (X.ChartRing j₀)) (X.dehomGen s e j₀) k ℓ
    have hwg : ∀ i, (chartGauss v j₀ hj).val (X.dehomGen s e j₀ i) =
        (gaussExt v.1).val (coneGen s e i) := fun i =>
      chartGauss_val_map hj (ProjBerk.isHomogeneous_coeff_coneGen s e hs i)
    have key := valuation_le_sup_pow_of_forall_dvd (K := FractionRing (X.ChartRing j₀))
      (g := X.dehomGen s e j₀)
      (chartGauss v j₀ hj).val (chartGauss_val_le_one hj) (by
        obtain ⟨i, hi⟩ := hz v
        refine ⟨i, ?_⟩
        rw [hwg, ProjBerk.gaussExt_val_coneGen]
        exact mul_ne_zero hi (pow_ne_zero _ ProjBerk.gaussRadius_ne_zero))
      (F := F.map (X.quotDehom j₀).toRingHom) (r := r)
      fun x => exists_dvd_of_le_reesPoint (j := ⟨j₀, hjI⟩) x hs (hN ⟨j₀, hjI⟩) hF
        (h _ (hmem ⟨j₀, hjI⟩ x))
    rw [chartGauss_val_map hj hF] at key
    simpa only [hwg] using key

/-- Logarithmic single-form comparison on the same witnessed chart tests. -/
theorem exists_finset_chartTest_shilov_coneSup {d : ℕ} (hs : ∀ i, (s i).IsHomogeneous d)
    (hz : ∀ v : X.an, ∃ i, v.1.1.val (s i) ≠ 0) :
    ∃ S : Finset X.an, X.triv ∈ S ∧ (∀ w ∈ S, X.IsChartTestPoint w) ∧
      ∀ (c : ℕ) (σ : MvPolynomial (Fin (M + 1)) k), σ.IsHomogeneous c → ∀ (z : ℤ) (r : ℕ),
        (∀ w ∈ S, logAbs σ w.1 + ((z : ℝ) : EReal) ≤ ((r : ℝ) : EReal) * coneSup s e w.1) →
        ∀ v : X.an, logAbs σ v.1 + ((z : ℝ) : EReal) ≤ ((r : ℝ) : EReal) * coneSup s e v.1 := by
  obtain ⟨S, hS, hSdiv, hcore⟩ := exists_finset_chartTest_shilov_core s e hs hz
  refine ⟨S, hS, hSdiv, fun c σ hσ z r h v => ?_⟩
  by_cases hσI : σ ∈ X.ideal
  · rw [(ProjBerk.logAbs_eq_bot_iff σ v.1).2 (v.2 σ hσI), EReal.bot_add]
    exact bot_le
  -- evaluation at `⋆ ∈ Σ` gives `z ≤ 0`
  have hz0 : z ≤ 0 := by
    have h1 := h X.triv hS
    rw [X.logAbs_triv_of_notMem hσI, zero_add] at h1
    have h2 : ((r : ℝ) : EReal) * coneSup s e (X.triv : ProjBerk k M) ≤ 0 := by
      have := ProjBerk.ereal_coe_mul_monotone (Nat.cast_nonneg r)
        (ProjBerk.coneSup_le_zero s e (X.triv : ProjBerk k M))
      simpa only [mul_zero] using this
    have h3 : ((z : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) := h1.trans h2
    exact_mod_cast EReal.coe_le_coe_iff.1 h3
  set a := z.natAbs
  have hza : ((z : ℝ) : EReal) = -((a : ℕ) : EReal) := by
    have h1 : ((a : ℕ) : ℤ) = -z := Int.ofNat_natAbs_of_nonpos hz0
    have h2 : (z : ℝ) = -((a : ℕ) : ℝ) := by
      have := congrArg (fun m : ℤ => (m : ℝ)) h1
      push_cast at this
      linarith
    rw [h2, EReal.coe_neg]
    rfl
  -- `log|σ| + z = log|σ t^{-z}|_{σ(·)}`
  have key : ∀ w : ProjBerk k M, logAbs σ w + ((z : ℝ) : EReal) =
      Berk.logAbs (Polynomial.C σ * Polynomial.X ^ a) (gaussExt w) := fun w => by
    rw [ProjBerk.logAbs_C_mul_X_pow_gaussExt, hza, sub_eq_add_neg]
  have hF : ∀ ℓ, ((Polynomial.C σ * Polynomial.X ^ a :
      (MvPolynomial (Fin (M + 1)) k)[X]).coeff ℓ).IsHomogeneous c := fun ℓ => by
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs
    · exact hσ
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  rw [key, ProjBerk.logAbs_le_mul_coneSup_iff]
  refine hcore c _ hF r (fun w hw => ?_) v
  rw [← ProjBerk.logAbs_le_mul_coneSup_iff, ← key]
  exact h w hw

end Rees

variable [IsAlgClosed k]

/-- Finite rational FS comparison on a finite set of witnessed chart tests. -/
theorem IsFinFS.exists_finset_chartTest_le_of_le {b : ℚ} {ψ : X.an → EReal} (hψ : X.IsFinFS b ψ) :
    ∃ S : Finset X.an, X.triv ∈ S ∧ (∀ w ∈ S, X.IsChartTestPoint w) ∧
      ∀ (a : ℚ) (D : ProjBerk.FSData k M a), D.IsRational → (∀ w ∈ S, D.eval w.1 ≤ ψ w) →
        ∀ v : X.an, D.eval v.1 ≤ ψ v := by
  have hψfin := hψ.ne_bot
  obtain ⟨ι, _, s, d, e, K, Z, hK, hs, hz, hψe⟩ := hψ.exists_coneSup
  obtain ⟨S, hS, hSdiv, hB⟩ := exists_finset_chartTest_shilov_coneSup s e hs hz
  refine ⟨S, hS, hSdiv, fun a D' hD' h v => ?_⟩
  obtain ⟨Q, hQ, hQz⟩ := ProjBerk.exists_pos_nat_mul_eq_int D'.terms (fun t => t.2) hD'
  choose w hw using hQz
  have hPbot : ∀ v : X.an, coneSup s e v.1 ≠ ⊥ := fun v h0 => hψfin v (by
    rw [hψe v, h0, EReal.bot_add]
    exact EReal.coe_mul_bot_of_pos (inv_pos.2 (by exact_mod_cast hK)))
  have hPtop : ∀ v : X.an, coneSup s e v.1 ≠ ⊤ := fun v =>
    ne_top_of_le_ne_top EReal.zero_ne_top (ProjBerk.coneSup_le_zero s e v.1)
  -- each term `m'⁻¹ (log|σ| + μ)` of `φ` gives a single inequality `log|σ^{KQ}| + z ≤ r φ_𝔦`
  have key : ∀ t (ht : t ∈ D'.terms) (v : X.an),
      (((D'.m : ℝ)⁻¹ : ℝ) : EReal) * ProjBerk.termVal t v.1 ≤ ψ v ↔
        logAbs (t.1 ^ (K * Q)) v.1 + (((K * w t ht - D'.m * Q * Z : ℤ) : ℝ) : EReal) ≤
          (((D'.m * Q : ℕ) : ℝ) : EReal) * coneSup s e v.1 := fun t ht v => by
    rw [hψe v, ProjBerk.termVal_def, ProjBerk.logAbs_pow]
    exact ProjBerk.fsTerm_le_iff (ProjBerk.logAbs_ne_top _ _) (hPbot v) (hPtop v) D'.m_pos hK hQ
      (hw t ht)
  rw [ProjBerk.FSData.eval_def, ProjBerk.ereal_coe_mul_finset_sup D'.inv_m_pos, Finset.sup_le_iff]
  intro t ht
  rw [key t ht v]
  refine hB _ _ ((D'.isHomogeneous t ht).pow _) _ _ (fun w' hw' => ?_) v
  rw [← key t ht w']
  exact (D'.termVal_le_eval_mul w'.1 ht).trans (h w' hw')

/-- The original finite FS Shilov maximum formula with a finite set `Σ` of
actual chart test points containing `⋆`: for every `ψ ∈ 𝓗_fin(X, b)`,
`sup_{X^an} (φ - ψ) = max_Σ (φ - ψ)` for every `a ∈ ℚ` and every Fubini–Study function `φ` of
class `a` on `X^an` with rational weights (`φ = D.eval` for rational data `D`). -/
theorem IsFinFS.exists_finset_chartTest_iSup_sub_eq {b : ℚ} {ψ : X.an → EReal} (hψ : X.IsFinFS b ψ) :
    ∃ S : Finset X.an, X.triv ∈ S ∧ (∀ w ∈ S, X.IsChartTestPoint w) ∧
      ∀ (a : ℚ) (φ : X.an → EReal),
        (∃ D : ProjBerk.FSData k M a, D.IsRational ∧ ∀ v : X.an, φ v = D.eval v.1) →
        ⨆ v, (φ v - ψ v) = S.sup fun v => φ v - ψ v := by
  obtain ⟨S, hS, hSdiv, hle⟩ := hψ.exists_finset_chartTest_le_of_le
  refine ⟨S, hS, hSdiv, fun a φ hφ => le_antisymm (iSup_le fun v => ?_)
    (Finset.sup_le fun w _ => le_iSup (fun v => φ v - ψ v) w)⟩
  obtain ⟨D, hD, hφD⟩ := hφ
  have hψr : ∀ v, ψ v = (((ψ v).toReal : ℝ) : EReal) := fun v =>
    (hψ.coe_toReal v).symm
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  obtain ⟨q, hMq, hqc⟩ := EReal.lt_iff_exists_rat_btwn.1 hc
  -- apply the comparison form to `φ - q`
  obtain ⟨D', hD', hD'eq⟩ := (ProjBerk.IsRatFS.add_const ⟨D, hD, rfl⟩ (-q) :
    ProjBerk.IsRatFS a fun v => D.eval v + (((-q : ℚ) : ℝ) : EReal))
  have hD'v : ∀ v : ProjBerk k M, D'.eval v = D.eval v + (((-q : ℚ) : ℝ) : EReal) := fun v =>
    (congrFun hD'eq v).symm
  have h := hle a D' hD' (fun w hw => by
    have h1 : φ w - ψ w ≤ ((q : ℝ) : EReal) :=
      (Finset.le_sup (f := fun v => φ v - ψ v) hw).trans hMq.le
    rw [hψr w, hφD w] at h1
    rw [hψr w, hD'v]
    rw [ereal_sub_coe_le_coe_iff] at h1
    simpa only [Rat.cast_neg] using h1) v
  have h2 : φ v - ψ v ≤ ((q : ℝ) : EReal) := by
    rw [hψr v, hφD v]
    rw [hψr v, hD'v] at h
    rw [ereal_sub_coe_le_coe_iff]
    simpa only [Rat.cast_neg] using h
  exact h2.trans hqc.le

/-- The original PL/PSH maximum argument, with the actual chart witnesses
retained throughout the decreasing-net proof. -/
theorem IsPL.exists_finset_chartTest_iSup_sub_eq {f : X.an → ℝ} (hf : X.IsPL f) :
    ∃ S : Finset X.an, X.triv ∈ S ∧ (∀ w ∈ S, X.IsChartTestPoint w) ∧
      ∀ (θ : ℝ) (u : X.an → EReal), X.IsPSH θ u →
        ⨆ v, (u v - (f v : EReal)) = S.sup fun v => u v - (f v : EReal) := by
  classical
  obtain ⟨a, b, φ₁, ψ₁, hφ₁, hψ₁, hf⟩ := hf
  have hφ₁' : X.IsFinFS (a 0) φ₁ := hφ₁
  have hψ₁' : X.IsFinFS (b 0) ψ₁ := hψ₁
  obtain ⟨S, hS, hSdiv, hsup⟩ := hφ₁'.exists_finset_chartTest_iSup_sub_eq
  refine ⟨S, hS, hSdiv, fun θ u hu => le_antisymm (iSup_le fun v => ?_)
    (Finset.sup_le fun w _ => le_iSup (fun v => u v - (f v : EReal)) w)⟩
  obtain ⟨ι, _, _, _, c, uα, huα, -, hanti, hinf⟩ :=
    FSSystem.IsPSH.exists_isFinFS_net (F := X.fsSystem) hu
  -- `u_α - f = (u_α + ψ₁) - φ₁`
  have hid : ∀ α v, uα α v - (f v : EReal) = (uα α v + ψ₁ v) - φ₁ v := fun α v => by
    obtain ⟨x, hx⟩ : ∃ x : ℝ, φ₁ v = x := ⟨_, (hφ₁'.coe_toReal v).symm⟩
    obtain ⟨y, hy⟩ : ∃ y : ℝ, ψ₁ v = y := ⟨_, (hψ₁'.coe_toReal v).symm⟩
    rw [hf v, hx, hy, EReal.toReal_coe, EReal.toReal_coe]
    calc uα α v - ((x - y : ℝ) : EReal) = uα α v + ((y - x : ℝ) : EReal) := by
          rw [sub_eq_add_neg, ← EReal.coe_neg, neg_sub]
      _ = uα α v + (y : EReal) - (x : EReal) := by
          rw [sub_eq_add_neg (uα α v + _), add_assoc, ← EReal.coe_neg, ← EReal.coe_add,
            sub_eq_add_neg]
  -- the Shilov lemma for `u_α + ψ₁ ∈ 𝓗_fin(X, a_α + b)`
  have hS' : ∀ α v, uα α v - (f v : EReal) ≤ S.sup fun w => uα α w - (f w : EReal) := by
    intro α v
    have hadd : X.IsFinFS (c α 0 + b 0) fun v => uα α v + ψ₁ v :=
      IsFinFS.add (huα α) hψ₁'
    obtain ⟨D, hD, -, hDeq⟩ := hadd
    have h := hsup (c α 0 + b 0) (fun v => uα α v + ψ₁ v) ⟨D, hD, hDeq⟩
    simp only [← hid] at h
    rw [← h]
    exact le_iSup (fun v => uα α v - (f v : EReal)) v
  -- pass to the limit in the maximum over the finite set `Σ`
  by_contra hlt
  push Not at hlt
  obtain ⟨c', hc1, hc2⟩ := exists_between hlt
  have hex : ∀ w ∈ S, ∃ α, uα α w - (f w : EReal) < c' := by
    intro w hw
    have h1 : u w - (f w : EReal) < c' :=
      (Finset.le_sup (f := fun v => u v - (f v : EReal)) hw).trans_lt hc1
    rw [hinf w, sub_eq_add_neg, ← EReal.coe_neg, ereal_iInf_add_coe] at h1
    obtain ⟨α, hα⟩ := iInf_lt_iff.1 h1
    exact ⟨α, by rwa [sub_eq_add_neg, ← EReal.coe_neg]⟩
  choose! α hα using hex
  obtain ⟨β, hβ⟩ := Finset.exists_le (S.image α)
  have h3 : (S.sup fun w => uα β w - (f w : EReal)) < c' := by
    rw [Finset.sup_lt_iff (bot_le.trans_lt hc1)]
    intro w hw
    refine lt_of_le_of_lt ?_ (hα w hw)
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact add_le_add_left (hanti w (hβ _ (Finset.mem_image_of_mem α hw))) _
  have h4 : u v - (f v : EReal) ≤ uα β v - (f v : EReal) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, hinf v]
    exact add_le_add_left (iInf_le _ β) _
  exact absurd ((h4.trans (hS' β v)).trans_lt h3) (not_lt.2 hc2.le)

/-- For every PL function `f` there is a finite set `Σ` of actual chart test
points containing `⋆` such that every `u ∈ PSH(X, θ)` with `u ≤ f` on `Σ` satisfies
`u ≤ f` on `X^an`. -/
theorem IsPL.exists_finset_chartTest_le_of_le {f : X.an → ℝ} (hf : X.IsPL f) :
    ∃ S : Finset X.an, X.triv ∈ S ∧ (∀ w ∈ S, X.IsChartTestPoint w) ∧
      ∀ (θ : ℝ) (u : X.an → EReal), X.IsPSH θ u → (∀ w ∈ S, u w ≤ f w) →
        ∀ v, u v ≤ f v := by
  obtain ⟨S, hS, hSdiv, hsup⟩ := hf.exists_finset_chartTest_iSup_sub_eq
  refine ⟨S, hS, hSdiv, fun θ u hu h v => ?_⟩
  have h1 : u v - (f v : EReal) ≤ 0 := by
    refine (le_iSup (fun v => u v - (f v : EReal)) v).trans ?_
    rw [hsup θ u hu]
    exact Finset.sup_le fun w hw => EReal.sub_nonpos.2 (h w hw)
  exact EReal.sub_nonpos.1 h1

/-- Comparison with a PL obstacle needs only actual witnessed chart tests. -/
theorem IsPSH.le_of_forall_isChartTestPoint_le_isPL {θ : ℝ} {u : X.an → EReal} (hu : X.IsPSH θ u)
    {f : X.an → ℝ} (hf : X.IsPL f) (hle : ∀ v, X.IsChartTestPoint v → u v ≤ f v) (v : X.an) :
    u v ≤ f v := by
  obtain ⟨S, -, hSdiv, hcomp⟩ := hf.exists_finset_chartTest_le_of_le
  exact hcomp θ u hu (fun w hw => hle w (hSdiv w hw)) v

/-! ### Divisorial comparison (`thm:sg-comparison`) -/

/-- The original usc comparison argument with bounds required only at actual
witnessed chart tests. For a PL function `ψ > h`, comparison on the chart tests
gives comparison everywhere,
(`lem:sg-sup-pl`), and `h` is the infimum of such `ψ` (`lem:sg-pl`(3), which applies by
`lem:sg-pl-separate`). -/
theorem IsPSH.le_of_forall_isChartTestPoint_le {θ : ℝ} {u h : X.an → EReal} (hu : X.IsPSH θ u)
    (hh : UpperSemicontinuous h) (htop : ∀ v, h v ≠ ⊤)
    (hle : ∀ v, X.IsChartTestPoint v → u v ≤ h v) : u ≤ h :=
  FSSystem.le_of_forall_isPL_gt (F := X.fsSystem) (separatesPoints_isPL X) hh htop
    fun _ hψ hgt v =>
      hu.le_of_forall_isChartTestPoint_le_isPL hψ (fun w hw => (hle w hw).trans (hgt w).le) v

end ProjSubvariety

end EnvelopeProperty
