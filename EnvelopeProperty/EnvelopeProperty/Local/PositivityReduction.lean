/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PositivityReductionCharts
import EnvelopeProperty.Local.BoundaryPresentation

/-!
# Approximation of convex PL functions standard at infinity from local positivity

Let `k` be algebraically closed with the trivial absolute value and `Y = Spec A` a normal affine
variety over `k`. This file derives, from the imported FHX Lemma 5.5 (`LocalPositivity k`,
`Local/PositivityImport.lean`), the approximation statement `ConvexPLApproximation k`
(`thm:wu-pl-approx`, `Local/PLApproxImport.lean`), and hence, through
`ConvexPLApproximation.toWuRegularization` (`Local/WuReduction.lean`), the statements of
Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Lemma 5.11(5),(6)
(`WuRegularization k`). Blueprint: `wu-discharge.tex`, subsection `subsec:wu-compactification`
(`lem:wu-fs-restriction`, `thm:wu-pl-approx-uniform`) and `thm:wu-pl-approx`.

## The argument

* **Restriction** (`lem:wu-fs-restriction`, `ProjSubvariety.exists_fsData_eval_affineChart`): for
  a projective model `P = V(I) ⊆ ℙᴹ` of `Y` given by a Rees presentation `R_M → A[T]` with
  `U_{x_{j₀}} ∩ P^an = Y^an` (`ProjBerk.IsReesPresentation`, `ProjSubvariety.affineChart`), and a
  finite Fubini–Study function `Ψ = m⁻¹ max_ℓ (log|τ_ℓ| + μ_ℓ)` of class `O(1)` on `P^an`,
  `Ψ - log|x_{j₀}|` is an affine FS function on `Y^an`:
  `Ψ - log|x_{j₀}| = max{m⁻¹ max_ℓ (log|f_ℓ| + μ_ℓ), max_i (log|uᵢ| - C₀), -C₀}` with
  `f_ℓ ↔ τ̄_ℓ / x̄_{j₀}^m`, `uᵢ ↔ x̄ᵢ / x̄_{j₀}` (generators of `A`) and `-C₀ ≤ min Ψ`.
* **Uniform approximation** (`thm:wu-pl-approx-uniform`,
  `LocalPositivity.exists_fsData_abs_sub_le`): for `w` convex PL on `Y^an` with `w = h` outside a
  compact set `E` (`h ∈ FS(Y)`), take the normal compactification `P` of `h`
  (`def:wu-compactification`, `FSData.exists_boundaryPresentation`, lane W2c) with
  `h = (ψ - log|x₀|)/(e N) + λ₀/N` on `Y^an`. The function `φ` equal to `e N w - e λ₀ + log|x₀|` on
  `U_{x₀}` and to `ψ` outside `E` is locally `O(1)`-convex (in the chart of `x₀` it is
  `e N w - e λ₀`; outside `E` it is the finite FS function `ψ`,
  `ProjSubvariety.IsFiniteFS.isLocallyConvex`). Uniform positivity (`thm:wu-pos`,
  `LocalPositivity.exists_isFiniteFS_abs_sub_le`) gives a finite FS function `Ψ` of class `O(1)`
  with `|φ - Ψ| ≤ e N ε`, and `v = (Ψ - log|x₀| + e λ₀)/(e N) ∈ FS(Y)` satisfies `|v - w| ≤ ε`.
* **Decreasing approximation with growth control** (`thm:wu-pl-approx`,
  `LocalPositivity.exists_antitone_fsData`): with `|v_j - w| ≤ 2^{-j}`, the functions
  `h_j = v_j + 3 · 2^{-j}` decrease to `w`, and `h_j ≤ w + 4 ≤ h + C + 4 ≤ c h + C_j`.
* The instance `LocalPositivity.toConvexPLApproximation : ConvexPLApproximation k`.

## Circularity

Nothing here uses `WuRegularization k` or a result conditional on it: the imports are
`Local/{PositivityImport, PositivityReductionCharts, PLApproxImport, BoundaryPresentation}` and
their dependencies (none of which mentions `WuRegularization` except the class declaration in
`Local/Imports.lean`), and the instance is the last declaration. In particular `Local/WeaklyPSH`
(which imports `Local/ProjectionStep`) is not imported; the pullback of convex PL functions along
an algebra map is reproved here (`isConvexPLOn_comp_comap_aux`, private).
-/

open scoped NNReal ENNReal Topology

open Topology

noncomputable section

namespace EnvelopeProperty

open Berk

universe u v

/-- Pullback of convex PL functions along the map induced by a `k`-algebra map (the argument of
`IsConvexPLOn.comp_comap` in `Local/WeaklyPSH.lean`, repeated to keep the imports free of
`WuRegularization`). -/
private theorem isConvexPLOn_comp_comap_aux {k : Type*} [Field k] {A : Type*} [CommRing A]
    [Algebra k A] {C : Type*} [CommRing C] [Algebra k C] (φ : A →ₐ[k] C) {U : Set (Berk k A)}
    {u : Berk k A → EReal} (h : IsConvexPLOn U u) :
    IsConvexPLOn (comap φ ⁻¹' U) fun y => u (comap φ y) := by
  intro y hy
  obtain ⟨W, hW, hyW, hWU, n, f, s, hs, hf, hu⟩ := h (comap φ y) hy
  exact ⟨comap φ ⁻¹' W, hW.preimage (continuous_comap φ), hyW, Set.preimage_mono hWU, n,
    fun i => φ (f i), s, hs, fun z hz i => hf _ hz i, fun z hz => hu _ hz⟩

/-! ### Restriction of Fubini–Study functions (`lem:wu-fs-restriction`) -/

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M) {A : Type*} [CommRing A]
  [Algebra k A] [IsDomain A] {φ : MvPolynomial (Fin (M + 1)) k →ₐ[k] Polynomial A} {e : ℕ}
  {j₀ : Fin (M + 1)}

/-- For a Rees presentation, the functions `uᵢ = x̄ᵢ / x̄_{j₀}` (the coefficients of `T^e` in
`φ(xᵢ)`) generate `A`: `τ ↦ φ(τ)_{N e}` is a surjective `k`-algebra map `R_M → A` on forms
(`S''_{(T^e)} = A`), namely evaluation of `φ` at `T = 1`. -/
theorem adjoin_range_coeff_map_X (hφ : ProjBerk.IsReesPresentation k X.ideal φ e j₀) :
    Algebra.adjoin k (Set.range fun i => (φ (MvPolynomial.X i)).coeff (1 * e)) = ⊤ := by
  set ψ : MvPolynomial (Fin (M + 1)) k →ₐ[k] A := ProjBerk.evalOne.comp φ
  have hψX : ∀ i, ψ (MvPolynomial.X i) = (φ (MvPolynomial.X i)).coeff (1 * e) := fun i =>
    hφ.evalOne_comp_of_isHomogeneous (MvPolynomial.isHomogeneous_X k i)
  have hsurj : Function.Surjective ψ := fun a => by
    obtain ⟨N, τ, hτ, hτa⟩ := hφ.exists_isHomogeneous_map_eq a
    refine ⟨τ, ?_⟩
    rw [hφ.evalOne_comp_of_isHomogeneous hτ, hτa, Polynomial.coeff_monomial, if_pos rfl]
  have h1 : ψ.range = ⊤ := (AlgHom.range_eq_top _).2 hsurj
  rw [MvPolynomial.aeval_unique ψ, MvPolynomial.aeval_range] at h1
  rw [← h1]
  congr 1
  ext a
  simp [hψX]

/-- **Restriction of Fubini–Study functions** (`lem:wu-fs-restriction`). Let `φ : R_M → A[T]` be
a Rees presentation of `X` (`U_{x_{j₀}} ∩ X^an ≃ₜ Y^an = (Spec A)^an`, `X.affineChart`) and `Ψ` a
finite Fubini–Study function of class `O(1)` on `X^an`. Then `Ψ - log|x_{j₀}|`, read on `Y^an`,
is an affine Fubini–Study function: writing `Ψ = m⁻¹ max_ℓ (log|τ_ℓ| + μ_ℓ)`,
`Ψ - log|x_{j₀}| = max{max_ℓ (m⁻¹ log|f_ℓ| + μ_ℓ / m), max_i (log|uᵢ| - C₀), -C₀}` with
`f_ℓ = φ(τ_ℓ)_{m e} ↔ τ̄_ℓ / x̄_{j₀}^m`, `uᵢ = φ(xᵢ)_e ↔ x̄ᵢ / x̄_{j₀}` and `C₀ ∈ ℚ` with
`-C₀ ≤ Ψ`; the extra terms are dominated since `log|xᵢ| ≤ 0 ≤ -log|x_{j₀}|`. -/
theorem exists_fsData_eval_affineChart (hφ : ProjBerk.IsReesPresentation k X.ideal φ e j₀)
    {Ψ : X.an → ℝ} (hΨ : X.IsFiniteFS 1 Ψ) :
    ∃ g : FSData k A, ∀ v : {v : X.an // (v : ProjBerk k M).1.val (MvPolynomial.X j₀) ≠ 0},
      g.eval (X.affineChart hφ v) =
        ((Ψ v.1 - Real.log ((v.1 : ProjBerk k M).1.val (MvPolynomial.X j₀) : ℝ) : ℝ) : EReal) := by
  classical
  have hΨc := hΨ.continuous
  obtain ⟨D, hDrat, -, hΨD⟩ := hΨ
  have hdeg : D.deg = D.m := by
    have h := D.deg_eq
    rw [mul_one] at h
    exact_mod_cast h
  have hm : (0 : ℝ) < D.m := by exact_mod_cast D.m_pos
  -- a rational lower bound `-C₀ ≤ Ψ`
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℚ, ∀ v, -(C₀ : ℝ) ≤ Ψ v := by
    obtain ⟨v₀, -, hv₀⟩ := isCompact_univ.exists_isMinOn ⟨X.triv, Set.mem_univ _⟩
      hΨc.continuousOn
    obtain ⟨q, hq⟩ := exists_rat_gt (-(Ψ v₀))
    exact ⟨q, fun v => by linarith [isMinOn_iff.1 hv₀ v (Set.mem_univ v)]⟩
  -- the rational constants of `Ψ`
  let q : MvPolynomial (Fin (M + 1)) k × ℝ → ℚ :=
    fun t => if h : ∃ q : ℚ, t.2 = q then h.choose else 0
  have hq : ∀ t ∈ D.terms, ((q t : ℚ) : ℝ) = t.2 := by
    intro t ht
    have h' : ∃ q : ℚ, t.2 = q := hDrat t ht
    simp only [q, dif_pos h']
    exact h'.choose_spec.symm
  let T₁ : Finset (A × ℚ × ℚ) :=
    D.terms.image fun t => ((φ t.1).coeff (D.deg * e), (1 : ℚ) / D.m, q t / D.m)
  let T₂ : Finset (A × ℚ × ℚ) :=
    Finset.univ.image fun i : Fin (M + 1) => ((φ (MvPolynomial.X i)).coeff (1 * e), (1 : ℚ), -C₀)
  let g : FSData k A :=
    { terms := T₁ ∪ T₂
      const := -C₀
      pos := by
        intro t ht
        rcases Finset.mem_union.1 ht with ht | ht
        · obtain ⟨t', -, rfl⟩ := Finset.mem_image.1 ht
          exact div_pos one_pos (by exact_mod_cast D.m_pos)
        · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht
          exact one_pos
      gen := by
        refine eq_top_iff.2 ((X.adjoin_range_coeff_map_X hφ).symm.le.trans
          (Algebra.adjoin_mono ?_))
        rintro _ ⟨i, rfl⟩
        exact ⟨_, Finset.mem_coe.2 (Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (Finset.mem_univ i))), rfl⟩ }
  refine ⟨g, fun v => ?_⟩
  set L := Real.log ((v.1 : ProjBerk k M).1.val (MvPolynomial.X j₀) : ℝ) with hL_def
  have hL0 : L ≤ 0 := Real.log_nonpos (NNReal.coe_nonneg _)
    (by exact_mod_cast ProjBerk.val_le_one _ _)
  have hLx : ProjBerk.logAbs (MvPolynomial.X j₀) (v.1 : ProjBerk k M) = (L : EReal) := by
    rw [ProjBerk.logAbs_def, ENNReal.log_of_nnreal v.2]
  -- the terms of `T₁`
  have hterm : ∀ t ∈ D.terms,
      fsTerm ((φ t.1).coeff (D.deg * e), (1 : ℚ) / D.m, q t / D.m) (X.affineChart hφ v) =
        (((D.m : ℝ)⁻¹ : ℝ) : EReal) * ProjBerk.termVal t (v.1 : ProjBerk k M) +
          ((-L : ℝ) : EReal) := by
    intro t ht
    rw [fsTerm_def, X.logAbs_affineChart_coeff hφ v (D.isHomogeneous t ht), ProjBerk.termVal_def,
      hLx]
    have h1 : (0 : ℝ) < (((1 : ℚ) / D.m : ℚ) : ℝ) := by
      have : (0 : ℚ) < (1 : ℚ) / D.m := div_pos one_pos (by exact_mod_cast D.m_pos)
      exact_mod_cast this
    by_cases h0 : (v.1 : ProjBerk k M).1.val t.1 = 0
    · rw [(ProjBerk.logAbs_eq_bot_iff _ _).2 h0, EReal.bot_sub, EReal.bot_add,
        EReal.coe_mul_bot_of_pos h1, EReal.bot_add, EReal.coe_mul_bot_of_pos (inv_pos.2 hm),
        EReal.bot_add]
    · rw [ProjBerk.logAbs_def, ENNReal.log_of_nnreal h0, ← EReal.coe_natCast, ← EReal.coe_mul,
        ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_mul,
        ← EReal.coe_add]
      congr 1
      push_cast
      rw [hq t ht, hdeg]
      field_simp
      ring
  have hsup₁ : T₁.sup (fun t => fsTerm t (X.affineChart hφ v)) = ((Ψ v.1 - L : ℝ) : EReal) := by
    simp only [T₁, Finset.sup_image, Function.comp_def]
    rw [Finset.sup_congr rfl fun t ht => hterm t ht]
    rw [← FSData.sup_add_coe, ← ProjBerk.ereal_coe_mul_finset_sup (inv_pos.2 hm),
      ← ProjBerk.FSData.eval_def, ← hΨD v.1, ← EReal.coe_add, sub_eq_add_neg]
  have hle : ((Ψ v.1 - L : ℝ) : EReal) =
      max (((-C₀ : ℚ) : ℝ) : EReal) ((T₁ ∪ T₂).sup fun t => fsTerm t (X.affineChart hφ v)) := by
    rw [Finset.sup_union, hsup₁]
    refine le_antisymm (le_max_of_le_right (le_max_left _ _)) (max_le ?_ (max_le le_rfl ?_))
    · rw [EReal.coe_le_coe_iff]
      push_cast
      linarith [hC₀ v.1]
    · refine Finset.sup_le fun t ht => ?_
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht
      rw [fsTerm_def, X.logAbs_affineChart_coeff hφ v (MvPolynomial.isHomogeneous_X k i), hLx]
      have hxi := ProjBerk.logAbs_le_zero (MvPolynomial.X i) (v.1 : ProjBerk k M)
      rw [Rat.cast_one, EReal.coe_one, one_mul]
      calc ProjBerk.logAbs (MvPolynomial.X i) (v.1 : ProjBerk k M) -
            ((1 : ℕ) : EReal) * (L : EReal) + (((-C₀ : ℚ) : ℝ) : EReal)
          ≤ (0 : EReal) - ((1 : ℕ) : EReal) * (L : EReal) + (((-C₀ : ℚ) : ℝ) : EReal) :=
            add_le_add_left (EReal.sub_le_sub hxi le_rfl) _
        _ = ((-L - C₀ : ℝ) : EReal) := by
            rw [← EReal.coe_natCast, ← EReal.coe_mul, zero_sub, ← EReal.coe_neg, ← EReal.coe_add]
            congr 1
            push_cast
            ring
        _ ≤ ((Ψ v.1 - L : ℝ) : EReal) := by
            rw [EReal.coe_le_coe_iff]
            linarith [hC₀ v.1]
  rw [hle]
  rfl

end ProjSubvariety

/-! ### Uniform and decreasing approximation -/

namespace LocalPositivity

variable {k : Type u} [Field k] [IsAlgClosed k] [LocalPositivity k] {A : Type*} [CommRing A]
  [IsDomain A] [Algebra k A] [IsIntegrallyClosed A]

/-- **Uniform approximation of convex PL functions standard at infinity**
(`thm:wu-pl-approx-uniform`; Wu26 Lemma 3.24(1)), from FHX Lemma 5.5 (`LocalPositivity`). Let `w`
be convex PL on `Y^an` with `w = h` outside a compact set `E`, `h ∈ FS(Y)`. For every `ε > 0` there
is `v ∈ FS(Y)` with `|v - w| ≤ ε` on `Y^an`. -/
theorem exists_fsData_abs_sub_le {w : Berk k A → EReal} {h : FSData k A} {E : Set (Berk k A)}
    (hE : IsCompact E) (hw : IsConvexPLOn Set.univ w) (hwE : ∀ x, x ∉ E → w x = h.eval x)
    {ε : ℝ} (hε : 0 < ε) : ∃ v : FSData k A, ∀ x, |v.evalReal x - (w x).toReal| ≤ ε := by
  obtain ⟨M, e, N, c₀, P, φ, hφ, ψ, hN, hP, hψ, hheval⟩ := h.exists_boundaryPresentation
  have he := hφ.pos
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hσ : (MvPolynomial.X 0 : MvPolynomial (Fin (M + 1)) k).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X k 0
  have hreal : ∀ x, w x = ((w x).toReal : EReal) := fun x => by
    obtain ⟨W, -, hxW, -, n, f, s, hs, -, hu⟩ := hw x (Set.mem_univ x)
    rw [hu x hxW, EReal.toReal_coe]
  -- the glued function `φ` on `P^an`
  let L : P.an → ℝ := fun v => Real.log ((v : ProjBerk k M).1.val (MvPolynomial.X 0) : ℝ)
  let Φ : P.an → ℝ := fun v =>
    if hv : (v : ProjBerk k M).1.val (MvPolynomial.X 0) ≠ 0 then
      (e * N : ℝ) * (w (P.affineChart hφ ⟨v, hv⟩)).toReal - e * c₀ + L v
    else ψ v
  -- `E`, as a compact subset of `U_{x₀} ⊆ P^an`
  let K : Set P.an := Subtype.val '' (P.affineChart hφ ⁻¹' E)
  have hK : IsClosed K :=
    (((P.affineChart hφ).isCompact_preimage.2 hE).image continuous_subtype_val).isClosed
  have hKU : ∀ v ∈ K, (v : ProjBerk k M).1.val (MvPolynomial.X 0) ≠ 0 := by
    rintro _ ⟨v, -, rfl⟩
    exact v.2
  have hΦψ : ∀ v ∉ K, Φ v = ψ v := by
    intro v hv
    by_cases hv0 : (v : ProjBerk k M).1.val (MvPolynomial.X 0) ≠ 0
    · have hnE : P.affineChart hφ ⟨v, hv0⟩ ∉ E := fun hE' => hv ⟨⟨v, hv0⟩, hE', rfl⟩
      have h1 := hheval ⟨v, hv0⟩
      rw [← hwE _ hnE] at h1
      simp only [Φ, dif_pos hv0, h1, EReal.toReal_coe, L]
      field_simp
      ring
    · simp only [Φ, dif_neg hv0]
  -- `φ` is locally `O(1)`-convex
  have hconv : P.IsLocallyConvex 1 Φ := by
    intro x
    by_cases hx : (x : ProjBerk k M).1.val (MvPolynomial.X 0) ≠ 0
    · refine ⟨{v | (v : ProjBerk k M).1.val (MvPolynomial.X 0) ≠ 0},
        ProjSubvariety.isOpen_setOf_val_ne_zero, hx, MvPolynomial.X 0, 1, hσ, one_pos,
        ProjSubvariety.notMem_ideal_of_val_ne_zero hx, fun v hv => hv, ?_⟩
      have hpre : P.chartInv (MvPolynomial.X 0) 1 hσ one_pos ⁻¹'
          {v | (v : ProjBerk k M).1.val (MvPolynomial.X 0) ≠ 0} = Set.univ :=
        Set.eq_univ_of_forall fun y => ProjSubvariety.chartInv_val_ne_zero hσ one_pos y
      rw [hpre]
      have h1 := ((isConvexPLOn_comp_comap_aux
        (C := ProjBerk.QuotChartAlg P.ideal (MvPolynomial.X 0) 1)
        (ProjBerk.affineChartEquiv hφ).symm.toAlgHom hw).smul
          (c := (e * N : ℚ)) (by positivity)).add_const (-(e * c₀))
      rw [Set.preimage_univ] at h1
      refine h1.congr fun y _ => ?_
      have hy : P.affineChart hφ ⟨P.chartInv (MvPolynomial.X 0) 1 hσ one_pos y,
          ProjSubvariety.chartInv_val_ne_zero hσ one_pos y⟩ =
          comap (ProjBerk.affineChartEquiv hφ).symm.toAlgHom y := by
        rw [ProjSubvariety.affineChart, Homeomorph.trans_apply,
          ProjSubvariety.chartHomeomorph_apply, ProjSubvariety.chartMap_chartInv]
        rfl
      simp only [ProjSubvariety.chartFun, Φ, dif_pos (ProjSubvariety.chartInv_val_ne_zero hσ
        one_pos y), hy, L]
      rw [hreal (comap (ProjBerk.affineChartEquiv hφ).symm.toAlgHom y), EReal.toReal_coe,
        ← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      push_cast
      ring
    · have hxK : x ∉ K := fun h => hx (hKU x h)
      exact (hψ.isLocallyConvex one_pos x).congr hK.isOpen_compl hxK fun v hv => hΦψ v hv
  -- uniform positivity on `P`, and restriction to `Y`
  obtain ⟨Ψ, hΨ, hΨΦ⟩ := LocalPositivity.exists_isFiniteFS_abs_sub_le P hP one_pos hconv
    (ε := e * N * ε) (by positivity)
  obtain ⟨g, hg⟩ := P.exists_fsData_eval_affineChart hφ hΨ
  have hc : (0 : ℚ) < 1 / (e * N) := by
    have : (0 : ℚ) < e * N := by exact_mod_cast Nat.mul_pos he hN
    positivity
  refine ⟨(g.addConst (e * c₀)).smul (1 / (e * N)) hc, fun x => ?_⟩
  set p := (P.affineChart hφ).symm x
  have hpx : P.affineChart hφ p = x := (P.affineChart hφ).apply_symm_apply x
  have hv : ((g.addConst (e * c₀)).smul (1 / (e * N)) hc).evalReal x =
      (Ψ p.1 - L p.1 + e * c₀) / (e * N) := by
    rw [FSData.evalReal, FSData.eval_smul, FSData.eval_addConst, ← hpx, hg p, ← EReal.coe_add,
      ← EReal.coe_mul, EReal.toReal_coe]
    push_cast
    field_simp
    rfl
  have hwx : (w x).toReal = (Φ p.1 - L p.1 + e * c₀) / (e * N) := by
    have hΦp : Φ p.1 = (e * N : ℝ) * (w x).toReal - e * c₀ + L p.1 := by
      simp only [Φ, dif_pos p.2, Subtype.coe_eta, hpx]
    rw [hΦp]
    field_simp
    ring
  have heN : (0 : ℝ) < e * N := mul_pos he' hN'
  rw [hv, hwx, ← sub_div, abs_div, abs_of_pos heN, div_le_iff₀ heN]
  have := hΨΦ p.1
  rw [abs_sub_comm] at this
  calc |Ψ p.1 - L p.1 + e * c₀ - (Φ p.1 - L p.1 + e * c₀)| = |Ψ p.1 - Φ p.1| := by ring_nf
    _ ≤ e * N * ε := this
    _ = ε * (e * N) := by ring

/-- **Approximation of convex PL functions standard at infinity** (`thm:wu-pl-approx`), from FHX
Lemma 5.5 (`LocalPositivity`). Let `w` be convex PL on `Y^an` with `w = h` outside a compact set
`E`, `h ∈ FS(Y)`. For every rational `c > 1` there are `h_j ∈ FS(Y)` decreasing to `w` with
`h_j ≤ c h + C_j`. With `v_j ∈ FS(Y)`, `|v_j - w| ≤ 2^{-j}` (`exists_fsData_abs_sub_le`), take
`h_j = v_j + 3 · 2^{-j}`: then `w + 2^{1-j} ≤ h_j ≤ w + 4 · 2^{-j}`, so the `h_j` decrease to `w`,
and `h_j ≤ w + 4 ≤ h + C + 4 ≤ c h + (C + 4 - (c - 1) b₀)` (`w ≤ h + C`,
`exists_le_eval_add_of_isConvexPLOn_univ`; `h ≥ b₀`). -/
theorem exists_antitone_fsData {w : Berk k A → EReal} {h : FSData k A} {E : Set (Berk k A)}
    (hE : IsCompact E) (hw : IsConvexPLOn Set.univ w) (hwE : ∀ x, x ∉ E → w x = h.eval x)
    {c : ℚ} (hc : 1 < c) :
    ∃ hs : ℕ → FSData k A, (∀ x, Antitone fun j => (hs j).eval x) ∧
      (∀ x, w x = ⨅ j, (hs j).eval x) ∧
      ∀ j, ∃ Cj : ℝ, ∀ x, (hs j).eval x ≤ ((c : ℝ) : EReal) * h.eval x + (Cj : EReal) := by
  have hreal : ∀ x, w x = ((w x).toReal : EReal) := fun x => by
    obtain ⟨W, -, hxW, -, n, f, s, hs, -, hu⟩ := hw x (Set.mem_univ x)
    rw [hu x hxW, EReal.toReal_coe]
  choose v hv using fun j : ℕ =>
    exists_fsData_abs_sub_le hE hw hwE (ε := ((2 : ℝ) ^ j)⁻¹) (by positivity)
  let q : ℕ → ℚ := fun j => 3 / 2 ^ j
  have hq : ∀ j, ((q j : ℚ) : ℝ) = 3 * ((2 : ℝ) ^ j)⁻¹ := fun j => by
    simp only [q]
    push_cast
    ring
  have heval : ∀ j x, ((v j).addConst (q j)).eval x =
      (((v j).evalReal x + 3 * ((2 : ℝ) ^ j)⁻¹ : ℝ) : EReal) := fun j x => by
    rw [FSData.eval_addConst, ← (v j).coe_evalReal, hq, ← EReal.coe_add]
  have hlo : ∀ j x, (w x).toReal + 2 * ((2 : ℝ) ^ j)⁻¹ ≤ (v j).evalReal x + 3 * ((2 : ℝ) ^ j)⁻¹ :=
    fun j x => by
      have := abs_le.1 (hv j x)
      linarith [this.1]
  have hhi : ∀ j x, (v j).evalReal x + 3 * ((2 : ℝ) ^ j)⁻¹ ≤ (w x).toReal + 4 * ((2 : ℝ) ^ j)⁻¹ :=
    fun j x => by
      have := abs_le.1 (hv j x)
      linarith [this.2]
  refine ⟨fun j => (v j).addConst (q j), fun x => ?_, fun x => ?_, fun j => ?_⟩
  · refine antitone_nat_of_succ_le fun j => ?_
    rw [heval, heval, EReal.coe_le_coe_iff]
    have h1 := hhi (j + 1) x
    have h2 := hlo j x
    have h3 : ((2 : ℝ) ^ (j + 1))⁻¹ = ((2 : ℝ) ^ j)⁻¹ / 2 := by
      rw [pow_succ, mul_inv]
      ring
    rw [h3] at h1
    linarith
  · refine le_antisymm (le_iInf fun j => ?_) (le_of_forall_gt fun c' hc' => ?_)
    · rw [heval, hreal x, EReal.coe_le_coe_iff]
      have := hlo j x
      have : (0 : ℝ) ≤ ((2 : ℝ) ^ j)⁻¹ := by positivity
      linarith
    · induction c' using EReal.rec with
      | bot => exact absurd hc' not_lt_bot
      | top =>
        refine lt_of_le_of_lt (iInf_le _ 0) ?_
        rw [heval]
        exact EReal.coe_lt_top _
      | coe r =>
        rw [hreal x, EReal.coe_lt_coe_iff] at hc'
        obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < (r - (w x).toReal) / 4 by linarith)
          (show (2 : ℝ)⁻¹ < 1 by norm_num)
        rw [inv_pow] at hj
        refine lt_of_le_of_lt (iInf_le _ j) ?_
        rw [heval, EReal.coe_lt_coe_iff]
        linarith [hhi j x]
  · obtain ⟨C, hC⟩ := exists_le_eval_add_of_isConvexPLOn_univ hE hw hwE
    refine ⟨C + 4 - ((c : ℝ) - 1) * h.const, fun x => ?_⟩
    rw [heval, ← h.coe_evalReal, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hCx : (w x).toReal ≤ h.evalReal x + C := by
      have := hC x
      rw [hreal x, ← h.coe_evalReal, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
      exact this
    have h1 := hhi j x
    have h2 : ((2 : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hc' : (0 : ℝ) ≤ (c : ℝ) - 1 := by
      have : (1 : ℝ) < c := by exact_mod_cast hc
      linarith
    have h3 := mul_nonneg hc' (sub_nonneg.2 (h.const_le_evalReal x))
    nlinarith

/-- **FHX Lemma 5.5 implies the approximation of convex PL functions standard at infinity**
(`thm:wu-pl-approx`): `LocalPositivity k → ConvexPLApproximation k`, for every universe of the
affine coordinate rings. Composed with `ConvexPLApproximation.toWuRegularization`
(`Local/WuReduction.lean`), it discharges `WuRegularization k` (FHX Lemma 5.11(5),(6)) from
`LocalPositivity k`. This instance is the last declaration of the file; its proof does not use
`WuRegularization`. -/
instance toConvexPLApproximation {k : Type u} [Field k] [IsAlgClosed k] [LocalPositivity.{u} k] :
    ConvexPLApproximation.{u, v} k where
  approx _ _ _ _ _ _ _ _ _ hE hw hwE _ hc := exists_antitone_fsData hE hw hwE hc

end LocalPositivity

end EnvelopeProperty
