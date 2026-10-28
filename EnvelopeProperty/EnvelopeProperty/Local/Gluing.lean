/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.Rossi
import EnvelopeProperty.Local.PrincipalExtension
import EnvelopeProperty.Local.HullCriterion
import EnvelopeProperty.Local.ExhaustionDef

/-!
# Gluing

FHX Proposition 5.20(1) (`prop:gluing`): the hull inequality for `u + cρ` at points outside a
closed subset `Z`, when `u` is regularizable on principal opens covering `Y \ Z` and `ρ` is a strict
exhaustion.

We state it for upper semicontinuous `u` (weakly psh functions are upper semicontinuous, which is
the only property the argument uses) and for covers by principal opens `Y_g` (equivalent to affine
open covers by Lemma 5.11(4)). The closed subset is `Z = V(S)` for a finite set `S ⊆ A`, so
`Z^an = {x | |f|_x = 0 for all f ∈ S}`.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open Berk

universe u v

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- Regularizable functions are upper semicontinuous (infima of continuous functions). -/
theorem IsRegularizable.upperSemicontinuous {u : Berk k A → EReal} (hu : IsRegularizable u) :
    UpperSemicontinuous u := by
  obtain ⟨-, g, -, hg⟩ := hu
  have : u = fun x => ⨅ j, (g j).eval x := funext hg
  rw [this]
  exact upperSemicontinuous_iInf fun j => (g j).continuous_eval.upperSemicontinuous

/-- The function `max_{f ∈ S} log|f|`. -/
def logMaxAbs (S : Finset A) (x : Berk k A) : EReal := S.sup fun f => logAbs f x

theorem continuous_logMaxAbs (S : Finset A) : Continuous (logMaxAbs (k := k) S) := by
  classical
  unfold logMaxAbs
  induction S using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert a S ha ih =>
    simp only [Finset.sup_insert]
    exact (continuous_logAbs a).max ih

theorem logMaxAbs_ne_top (S : Finset A) (x : Berk k A) : logMaxAbs S x ≠ ⊤ := by
  unfold logMaxAbs
  exact ne_of_lt ((Finset.sup_lt_iff bot_lt_top).2 fun f _ => logAbs_lt_top f x)

theorem logMaxAbs_ne_bot_iff (S : Finset A) (x : Berk k A) :
    logMaxAbs S x ≠ ⊥ ↔ ∃ f ∈ S, x.val f ≠ 0 := by
  unfold logMaxAbs
  simp [Finset.sup_eq_bot_iff]

theorem fsTerm_one_zero (f : A) (x : Berk k A) :
    fsTerm (f, (1 : ℚ), (0 : ℚ)) x = logAbs f x := by
  simp [fsTerm]

open Classical in
/-- The terms `(f, 1, 0)`, `f ∈ S`. -/
def logTerms (S : Finset A) : Finset (A × ℚ × ℚ) := S.image fun f => (f, (1 : ℚ), (0 : ℚ))

theorem logMaxAbs_eq_sup_fsTerm (S : Finset A) (x : Berk k A) :
    logMaxAbs S x = (logTerms S).sup fun t => fsTerm t x := by
  classical
  unfold logMaxAbs logTerms
  rw [Finset.sup_image]
  congr 1
  funext f
  simp [Function.comp, fsTerm_one_zero]

theorem isRegularizable_logMaxAbs [Algebra.FiniteType k A] (S : Finset A)
    (hne : ∃ x : Berk k A, ∃ f ∈ S, x.val f ≠ 0) : IsRegularizable (logMaxAbs (k := k) S) := by
  classical
  have h := isRegularizable_finsetSup_fsTerm (k := k) (A := A)
    (s := logTerms S)
    (by intro t ht; unfold logTerms at ht; obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 ht; norm_num)
    (by
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, by rw [← logMaxAbs_eq_sup_fsTerm]; exact (logMaxAbs_ne_bot_iff S x).2 hx⟩)
  exact h.congr fun x => (logMaxAbs_eq_sup_fsTerm S x).symm

section gluing

variable {k : Type u} [Field k] [IsAlgClosed k] [Countable k] [WuRegularization.{u, v} k]
  {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
  [IsIntegrallyClosed A]

/-- A point of an open set in a locally compact Hausdorff space has an open neighbourhood with
compact closure inside the open set. -/
theorem exists_isOpen_isCompact_closure_subset {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] {U : Set X} (hU : IsOpen U) {y : X} (hy : y ∈ U) :
    ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ IsCompact (closure W) ∧ closure W ⊆ U := by
  obtain ⟨L, hL, hyL, hLU⟩ := exists_compact_subset hU hy
  refine ⟨interior L, isOpen_interior, hyL, ?_, ?_⟩
  · exact hL.of_isClosed_subset isClosed_closure
      (closure_minimal interior_subset hL.isClosed)
  · exact (closure_minimal interior_subset hL.isClosed).trans hLU

omit [Countable k] in
/-- **Gluing, hull inequality off `Z`** (FHX Proposition 5.20(1)). -/
theorem gluing_hullIneq {u : Berk k A → EReal} (husc : UpperSemicontinuous u)
    (hlog : HasLogGrowth u) (S : Finset A)
    (hcover : ∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y))
    {ρ : Berk k A → EReal} (hρ : IsStrictExhaustion ρ) {c : ℚ} (hc : 0 < c)
    {K : Set (Berk k A)} (hK : IsCompact K) {x : Berk k A} (hx : x ∈ hull K)
    (hxZ : ∃ f ∈ S, x.val f ≠ 0) :
    u x + ((c : ℝ) : EReal) * ρ x ≤ ⨆ y ∈ K, (u y + ((c : ℝ) : EReal) * ρ y) := by
  classical
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  obtain ⟨hρreg, hρ0, hρstrict⟩ := hρ
  -- finiteness of `u` and `ρ`
  have hutop : ∀ y, u y ≠ ⊤ := by
    obtain ⟨g0, C0, hg0⟩ := hlog
    exact fun y => ne_top_of_le_ne_top
      (EReal.add_ne_top (g0.eval_ne_top y) (EReal.coe_ne_top C0)) (hg0 y)
  have hρbot : ∀ y, ρ y ≠ ⊥ := fun y => ne_bot_of_le_ne_bot (by simp) (hρ0 y)
  set ρr : Berk k A → ℝ := fun y => (ρ y).toReal with hρr
  have hρeq : ∀ y, ρ y = ((ρr y : ℝ) : EReal) := fun y =>
    (EReal.coe_toReal (hρreg.ne_top y) (hρbot y)).symm
  have hcρ : ∀ y, ((c : ℝ) : EReal) * ρ y = (((c : ℝ) * ρr y : ℝ) : EReal) := fun y => by
    rw [hρeq y, EReal.coe_mul]
  set v : Berk k A → EReal := logMaxAbs S with hv
  have hvreg : IsRegularizable v := isRegularizable_logMaxAbs S ⟨x, hxZ⟩
  have hvcont : Continuous v := continuous_logMaxAbs S
  -- argue by contradiction
  by_contra hcon
  rw [not_le] at hcon
  set M := ⨆ y ∈ K, (u y + ((c : ℝ) : EReal) * ρ y) with hM
  -- real values at `x`
  have hucx : u x + ((c : ℝ) : EReal) * ρ x ≠ ⊥ := ne_bot_of_gt hcon
  have hux : u x ≠ ⊥ := by
    intro h; apply hucx; rw [h, EReal.bot_add]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, (a : EReal) = u x + ((c : ℝ) : EReal) * ρ x :=
    ⟨_, EReal.coe_toReal (EReal.add_ne_top (hutop x) (by rw [hcρ]; exact EReal.coe_ne_top _))
      hucx⟩
  have hvx : v x ≠ ⊥ := (logMaxAbs_ne_bot_iff S x).2 hxZ
  obtain ⟨b, hb⟩ : ∃ b : ℝ, (b : EReal) = v x :=
    ⟨_, EReal.coe_toReal (logMaxAbs_ne_top S x) hvx⟩
  -- an upper bound for `v` on `K`
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ y ∈ K, v y ≤ (B : EReal) := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨0, by simp [hKe]⟩
    · obtain ⟨y₀, hy₀, hmax⟩ := hK.exists_isMaxOn hKne hvcont.continuousOn
      by_cases hb0 : v y₀ = ⊥
      · exact ⟨0, fun y hy => (hmax hy).trans (by rw [hb0]; exact bot_le)⟩
      · exact ⟨(v y₀).toReal, fun y hy => (hmax hy).trans
          (EReal.le_coe_toReal (logMaxAbs_ne_top S y₀))⟩
  -- choose a small rational `ε`
  obtain ⟨ε, hε, hεM⟩ : ∃ ε : ℚ, 0 < ε ∧
      M + (((ε : ℝ) * B : ℝ) : EReal) < (((a + ε * b : ℝ)) : EReal) := by
    by_cases hMbot : M = ⊥
    · exact ⟨1, one_pos, by rw [hMbot, EReal.bot_add]; exact EReal.bot_lt_coe _⟩
    · have hMtop : M ≠ ⊤ := ne_top_of_lt hcon
      obtain ⟨m, hm⟩ : ∃ m : ℝ, (m : EReal) = M := ⟨_, EReal.coe_toReal hMtop hMbot⟩
      have hma : m < a := by
        have := hcon; rw [← hm, ← ha] at this; exact_mod_cast this
      set D : ℝ := |B - b| + 1 with hD
      have hDpos : 0 < D := by positivity
      obtain ⟨ε, hε0, hε1⟩ := exists_rat_btwn (div_pos (sub_pos.2 hma) hDpos)
      refine ⟨ε, by exact_mod_cast hε0, ?_⟩
      rw [← hm, ← EReal.coe_add, EReal.coe_lt_coe_iff]
      have hε0' : (0 : ℝ) < ε := by exact_mod_cast hε0
      have h1 : (ε : ℝ) * D < a - m := by
        rw [lt_div_iff₀ hDpos] at hε1; linarith
      have h2 : (ε : ℝ) * (B - b) ≤ ε * D := by
        apply mul_le_mul_of_nonneg_left _ hε0'.le
        rw [hD]; linarith [le_abs_self (B - b)]
      nlinarith
  set εe : EReal := ((ε : ℝ) : EReal) with hεe
  have hε0 : (0 : ℝ) < ε := by exact_mod_cast hε
  -- the function `F = u + cρ + εv`
  set F : Berk k A → EReal := fun y => u y + ((c : ℝ) : EReal) * ρ y + εe * v y with hF
  have hεv : ∀ y, εe * v y ≠ ⊤ := by
    intro y
    by_cases hvy : v y = ⊥
    · rw [hvy, hεe, EReal.coe_mul_bot_of_pos hε0]; exact bot_ne_top
    · obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : EReal) = v y :=
        ⟨_, EReal.coe_toReal (logMaxAbs_ne_top S y) hvy⟩
      rw [← hr, hεe, ← EReal.coe_mul]; exact EReal.coe_ne_top _
  have hFx : F x = (((a + ε * b : ℝ)) : EReal) := by
    simp only [hF, ← ha, ← hb, hεe, ← EReal.coe_mul, ← EReal.coe_add]
  have hFK : ∀ y ∈ K, F y < F x := by
    intro y hy
    rw [hFx]
    refine lt_of_le_of_lt ?_ hεM
    have h1 : u y + ((c : ℝ) : EReal) * ρ y ≤ M :=
      le_iSup₂ (f := fun y (_ : y ∈ K) => u y + ((c : ℝ) : EReal) * ρ y) y hy
    have h2 : εe * v y ≤ (((ε : ℝ) * B : ℝ) : EReal) := by
      rw [EReal.coe_mul]
      exact mul_le_mul_of_nonneg_left (hB y hy) (by rw [hεe]; exact_mod_cast hε0.le)
    exact add_le_add h1 h2
  -- `F` is upper semicontinuous and attains its maximum on the hull
  have hcρusc : UpperSemicontinuous fun y => ((c : ℝ) : EReal) * ρ y :=
    (hρreg.smul hc).upperSemicontinuous
  have hFusc : UpperSemicontinuous F := by
    refine upperSemicontinuous_add_of_ne_top
      (upperSemicontinuous_add_of_ne_top husc hcρusc hutop
        (fun y => by rw [hcρ]; exact EReal.coe_ne_top _)) ?_
      (fun y => EReal.add_ne_top (hutop y) (by rw [hcρ]; exact EReal.coe_ne_top _)) hεv
    exact (hvreg.smul hε).upperSemicontinuous
  have hhullc : IsCompact (hull K) := isCompact_hull hK
  obtain ⟨y, hyhull, hymax⟩ := (hFusc.upperSemicontinuousOn (hull K)).exists_isMaxOn
    ⟨x, hx⟩ hhullc
  have hxy : F x ≤ F y := hymax hx
  have hyK : y ∉ K := fun hyK => absurd hxy (not_le.2 (hFK y hyK))
  have hFybot : F y ≠ ⊥ := ne_bot_of_le_ne_bot (by rw [hFx]; exact EReal.coe_ne_bot _) hxy
  have hFytop : F y ≠ ⊤ := EReal.add_ne_top
    (EReal.add_ne_top (hutop y) (by rw [hcρ]; exact EReal.coe_ne_top _)) (hεv y)
  have hvy : v y ≠ ⊥ := by
    intro h
    apply hFybot
    simp only [hF, h, hεe, EReal.coe_mul_bot_of_pos hε0]
    exact EReal.add_bot _
  have hyZ : ∃ f ∈ S, y.val f ≠ 0 := (logMaxAbs_ne_bot_iff S y).1 hvy
  obtain ⟨g, hg0, hyg, hug⟩ := hcover y hyZ
  -- a neighbourhood `W` of `y`
  have hUopen : IsOpen ({z : Berk k A | z.val g ≠ 0} ∩ Kᶜ) :=
    (isOpen_setOf_abs_ne_zero g).inter hK.isClosed.isOpen_compl
  obtain ⟨W, hWopen, hyW, hWc, hWU⟩ :=
    exists_isOpen_isCompact_closure_subset hUopen ⟨hyg, hyK⟩
  obtain ⟨ρ', δ, hδ, hρ'reg, hρ'le, hρ'y, hρ'off⟩ := hρstrict y W (hWopen.mem_nhds hyW)
  -- the auxiliary function `q`
  set q : Berk k A → EReal := fun z => u z + ((c : ℝ) : EReal) * ρ' z + εe * v z with hq
  have hqF : ∀ z, q z ≤ F z := by
    intro z
    simp only [hq, hF]
    refine add_le_add (add_le_add le_rfl ?_) le_rfl
    exact mul_le_mul_of_nonneg_left (hρ'le z) (by exact_mod_cast hcpos.le)
  have hqy : q y = F y := by simp only [hq, hF, hρ'y]
  -- regularizability of `q` on `Y_g` and logarithmic growth on `Y`
  have := isDomain_localizationAway hg0
  have := isIntegrallyClosed_localizationAway hg0
  have hqreg : IsRegularizable fun w => q (awayComap g w) :=
    (hug.add ((hρ'reg.comp_awayComap hg0).smul hc)).add ((hvreg.comp_awayComap hg0).smul hε)
  have hqlog : HasLogGrowth q :=
    ((hlog.add (hρreg.hasLogGrowth.smul (c := (c : ℝ)) hcpos.le)).add
      (hvreg.hasLogGrowth.smul (c := (ε : ℝ)) hε0.le)).mono hqF
  obtain ⟨G, C', hG⟩ := hqlog
  -- the compact set `C = ∂W ∩ K̂` and Rossi's principle
  set C := frontier W ∩ hull K with hC
  have hCsub : C ⊆ closure W := fun z hz => frontier_subset_closure hz.1
  have hCc : IsCompact C :=
    hWc.of_isClosed_subset (isClosed_frontier.inter (isClosed_hull K)) hCsub
  have hdisj : Disjoint (closure W) K := by
    rw [Set.disjoint_left]
    intro z hz hzK
    exact (hWU hz).2 hzK
  have hyC : y ∈ hull C := mem_hull_frontier_inter_hull hK hyhull hWopen hyW hWc hdisj
  have hph := le_iSup_of_mem_hull_awayExtend hg0 hqreg G C' (fun w => hG _) hCc hyC hyg
  have hext : ∀ z, z.val g ≠ 0 → awayExtend g (fun w => q (awayComap g w)) z = q z := by
    intro z hz
    rw [awayExtend_of_ne_zero g _ hz, awayComap_awayLift]
  rw [hext y hyg, hqy] at hph
  -- on `C`, `q ≤ F y - c δ`
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, (φ : EReal) = F y := ⟨_, EReal.coe_toReal hFytop hFybot⟩
  have hbound : ∀ z ∈ C, awayExtend g (fun w => q (awayComap g w)) z ≤
      ((φ - c * δ : ℝ) : EReal) := by
    intro z hz
    have hzg : z.val g ≠ 0 := (hWU (hCsub hz)).1
    rw [hext z hzg]
    have hzW : z ∉ W := by
      have := hz.1
      rw [hWopen.frontier_eq] at this
      exact this.2
    have hoff := hρ'off z hzW
    have hFz : F z ≤ F y := hymax hz.2
    -- `q z + c δ ≤ F z`
    have hkey : q z + (((c : ℝ) * δ : ℝ) : EReal) ≤ F z := by
      simp only [hq, hF]
      by_cases hρ'bot : ρ' z = ⊥
      · rw [hρ'bot, EReal.coe_mul_bot_of_pos hcpos, EReal.add_bot, EReal.bot_add,
          EReal.bot_add]
        exact bot_le
      · have hρ'top : ρ' z ≠ ⊤ := ne_top_of_le_ne_top (hρreg.ne_top z) (hρ'le z)
        obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : EReal) = ρ' z := ⟨_, EReal.coe_toReal hρ'top hρ'bot⟩
        rw [← hr] at hoff ⊢
        rw [hρeq z] at hoff ⊢
        have hoff' : r + δ ≤ ρr z := by
          rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hoff; exact hoff
        have : ((c : ℝ) : EReal) * (r : EReal) + (((c : ℝ) * δ : ℝ) : EReal) ≤
            ((c : ℝ) : EReal) * (ρr z : EReal) := by
          rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
          nlinarith
        calc u z + ((c : ℝ) : EReal) * (r : EReal) + εe * v z + (((c : ℝ) * δ : ℝ) : EReal)
            = u z + (((c : ℝ) : EReal) * (r : EReal) + (((c : ℝ) * δ : ℝ) : EReal)) +
                εe * v z := by
              ac_rfl
          _ ≤ u z + ((c : ℝ) : EReal) * (ρr z : EReal) + εe * v z := by
              gcongr
    by_cases hqbot : q z = ⊥
    · rw [hqbot]; exact bot_le
    · have hqtop : q z ≠ ⊤ := ne_top_of_le_ne_top hFytop ((hqF z).trans hFz)
      obtain ⟨t, ht⟩ : ∃ t : ℝ, (t : EReal) = q z := ⟨_, EReal.coe_toReal hqtop hqbot⟩
      rw [← ht] at hkey ⊢
      have := hkey.trans (hFz.trans_eq hφ.symm)
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at this
      rw [EReal.coe_le_coe_iff]; linarith
  have hsup := (hph.trans (iSup₂_le hbound))
  rw [← hφ, EReal.coe_le_coe_iff] at hsup
  have : (0 : ℝ) < c * δ := mul_pos hcpos hδ
  linarith

end gluing

section poly

open Polynomial

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- The `k`-algebra map `A_g → A[w]_{g}` induced by `A → A[w]`. -/
def awayPolyMap (g : A) :
    Localization.Away g →ₐ[k] Localization.Away (Polynomial.CAlgHom (R := k) (A := A) g) :=
  Localization.awayMapₐ (Polynomial.CAlgHom (R := k) (A := A)) g

theorem awayPolyMap_algebraMap (g a : A) :
    awayPolyMap (k := k) g (algebraMap A (Localization.Away g) a) =
      algebraMap A[X] (Localization.Away (Polynomial.CAlgHom (R := k) (A := A) g)) (C a) := by
  simp [awayPolyMap, Localization.awayMapₐ, IsLocalization.Away.mapₐ, IsLocalization.Away.map,
    IsLocalization.map_eq]

/-- The projection `Ỹ_g → Y_g` read through the principal-open identifications. -/
theorem proj_awayComap_C (g : A)
    (z : Berk k (Localization.Away (Polynomial.CAlgHom (R := k) (A := A) g))) :
    proj (awayComap (Polynomial.CAlgHom (R := k) (A := A) g) z) =
      awayComap g (comap (awayPolyMap g) z) := by
  refine ext_val fun a => ?_
  simp only [proj_val_apply, awayComap_val_apply, comap_val_apply, awayPolyMap_algebraMap]

end poly

end EnvelopeProperty
