import EnvelopeProperty.Global.DeJongBridge.KernelModel
import EnvelopeProperty.Global.DeJongBridge.SectionsGraph
import EnvelopeProperty.Global.DeJongBridge.Alteration
import EnvelopeProperty.AlgGeom.SmoothIntegralSchemeNormal

/-!
# de Jong's alteration theorem implies EnvelopeProperty's `DeJongAlterations` hypothesis

The bridge theorem `DeJongEPBridge.deJongAlterations_of_theorem`: for an algebraically closed
field `k`, de Jong's Theorem 4.1 (`dejong96-alterations:page-0017`, in Codex's form
`DeJongAlterations.DeJongAlterationTheorem k`) implies `EnvelopeProperty.DeJongAlterations k`, the
model form of 4.1 used by Fang–Han–Xia (EnvelopeProperty blueprint `thm:gl-dejong`,
`EnvelopeProperty/Global/DeJongImport.lean`). Plan PLAN-DJ-MAIN §6.2, steps 1–7.

## The mathematics

Let `X = V(I) ⊆ ℙ^N` be a projective variety over `k` (`EnvelopeProperty.ProjSubvariety k N`).

1. `X^s = Proj(k[x] / I)` is a projective variety over `k` (`DeJongEPBridge.Subvariety`).
2. 4.1 with `Z = ∅` gives a smooth projective alteration `φ : Y → X^s` with a closed immersion
   `ι : Y → ℙ^{N'}` (`nonempty_smoothProjectiveAlteration`).
3. Fix `x_{j₀} ∉ I` and `y_{j₁}` not vanishing at the generic point of `ι(Y)`, and put
   `a_i = φ^*(x_i / x_{j₀})`, `b_m = ι^*(y_m / y_{j₁})` in `k(Y)` (`ratioX`). Let
   `I_Y = ker(k[x, y] → k(Y)[T_0, T_1], x_i ↦ a_i T_0, y_m ↦ b_m T_1)`
   (`DeJongEPBridge.kerIdeal`): a bihomogeneous prime, relevant at `(j₀, j₁)`.
4. `I_Y ∩ k[x] = I`: for `G` homogeneous of degree `d`, `G(a) = φ^*(G / x_{j₀}^d)` vanishes iff
   `G ∈ I`, as `φ` is dominant (`aeval_ratioX_eq_zero_iff`, `aeval_monomial_eq_zero_iff`).
5. `k(I_Y) ↪ k(Y)` with `k(X) ↦ k(a)`, and `k(Y)` is finite over `φ^* k(X^s) ⊆ k(a)` since `φ` is
   generically finite (`finiteDimensional_adjoin_ratioX`).
6. A chart `(j₀', j₁')` with `a_{j₀'} ≠ 0 ≠ b_{j₁'}` has chart algebra
   `k[a_i / a_{j₀'}, b_m / b_{j₁'}]`, which is the coordinate ring of the nonempty affine open `ι⁻¹ D₊(y_{j₁'}) ∩ φ⁻¹ D₊(x_{j₀'})` of
   `Y` (`exists_chart`: the graph lemma `closure_range_restrict_appLE_eq_top`, `X^s` separated, and
   the chart computation `ProjChart.range_pullGerm_eq_adjoin`); it is therefore smooth over `k` and
   integrally closed (`smooth_adjoin_ratios`, EnvelopeProperty's `smooth_sectionsAlgebra` and
   `isIntegrallyClosed_sections_of_smooth`).
7. `deJongAlterations_of_theorem`.

Only the `Z = ∅`, projective case of 4.1 is used, and no generic étaleness.
-/

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open DeJongAlterations

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace DeJongEPBridge

open EnvelopeProperty EnvelopeProperty.MultiModel

universe u

section Kernel

variable (k : Type u) [Field k] {K : Type u} [Field K] [Algebra k K]

/-- The image of a homogeneous polynomial under `x_i ↦ a_i T_c`. -/
theorem aeval_monomial_of_isHomogeneous {r : ℕ} (c : Fin r) {n : ℕ} (a : Fin (n + 1) → K)
    {d : ℕ} {G : MvPolynomial (Fin (n + 1)) k} (hG : G.IsHomogeneous d) :
    aeval (fun i => (monomial (Finsupp.single c 1) (a i) : MvPolynomial (Fin r) K)) G =
      monomial (Finsupp.single c d) (aeval a G) := by
  have h1 : (fun i => (monomial (Finsupp.single c 1) (a i) : MvPolynomial (Fin r) K)) =
      fun i => C (a i) * X c := funext fun i => C_mul_X_eq_monomial.symm
  rw [h1, aeval_def, ProjChart.eval₂_mul_of_isHomogeneous _ _ _ hG, aeval_def,
    show (algebraMap k (MvPolynomial (Fin r) K)) =
      (C : K →+* MvPolynomial (Fin r) K).comp (algebraMap k K) from rfl,
    show (fun i => C (a i)) = (C : K →+* MvPolynomial (Fin r) K) ∘ a from rfl,
    ← eval₂_comp_left, X_pow_eq_monomial, mul_comm, C_mul_monomial, mul_one]

/-- **The kernel of `x_i ↦ a_i T_c`.** If a homogeneous ideal `I` consists exactly of the
homogeneous polynomials vanishing at `a`, then it is the kernel of `x_i ↦ a_i T_c`. -/
theorem aeval_monomial_eq_zero_iff {r : ℕ} (c : Fin r) {n : ℕ} (a : Fin (n + 1) → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hI : ∀ F ∈ I, ∀ d, homogeneousComponent d F ∈ I)
    (hX : ∀ (d : ℕ) (G : MvPolynomial (Fin (n + 1)) k), G.IsHomogeneous d →
      (aeval a G = 0 ↔ G ∈ I)) (F : MvPolynomial (Fin (n + 1)) k) :
    aeval (fun i => (monomial (Finsupp.single c 1) (a i) : MvPolynomial (Fin r) K)) F = 0 ↔
      F ∈ I := by
  classical
  have hsum : aeval (fun i => (monomial (Finsupp.single c 1) (a i) : MvPolynomial (Fin r) K)) F =
      ∑ d ∈ Finset.range (F.totalDegree + 1),
        monomial (Finsupp.single c d) (aeval a (homogeneousComponent d F)) := by
    conv_lhs => rw [← sum_homogeneousComponent F]
    rw [map_sum]
    exact Finset.sum_congr rfl fun d _ =>
      aeval_monomial_of_isHomogeneous k c a (homogeneousComponent_isHomogeneous d F)
  constructor
  · intro h
    have hd : ∀ d, homogeneousComponent d F ∈ I := by
      intro d
      by_cases hdF : d ∈ Finset.range (F.totalDegree + 1)
      · have hc := congrArg (fun p => coeff (Finsupp.single c d) p) (hsum.symm.trans h)
        simp only [coeff_sum, coeff_monomial, coeff_zero] at hc
        rw [Finset.sum_eq_single d (fun b _ hb => if_neg fun h' =>
            hb (Finsupp.single_injective c h')) (fun h' => absurd hdF h'), if_pos rfl] at hc
        exact (hX d _ (homogeneousComponent_isHomogeneous d F)).1 hc
      · rw [homogeneousComponent_eq_zero d F (by simp at hdF; omega)]
        exact I.zero_mem
    rw [← sum_homogeneousComponent F]
    exact I.sum_mem fun d _ => hd d
  · intro h
    rw [hsum]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [(hX d _ (homogeneousComponent_isHomogeneous d F)).2 (hI F h d), map_zero]

end Kernel

section Ratios

variable {k : Type u} [Field k] {N : ℕ} (X : ProjSubvariety k N) {Y : Scheme.{u}} [IsIntegral Y]
  (φ : Y ⟶ Subvariety.scheme X) [IsDominant φ]

/-- The homogeneous prime of `φ(η_Y)` is `0`: `φ` is dominant. -/
theorem genPrime_eq_bot : ProjChart.genPrime (Subvariety.grading X) φ = ⊥ := by
  unfold ProjChart.genPrime
  rw [genericPoint_map_of_isDominant φ, Subvariety.genericPoint_asHomogeneousIdeal]
  rfl

theorem notMem_genPrime_iff (x : Subvariety.Ring X) :
    x ∉ ProjChart.genPrime (Subvariety.grading X) φ ↔ x ≠ 0 := by
  rw [genPrime_eq_bot, Ideal.mem_bot]

variable {X} in
theorem aeval_coord (G : MvPolynomial (Fin (N + 1)) k) :
    aeval (Subvariety.coord X) G = Ideal.Quotient.mk _ G := by
  have h := congrArg (fun F => F G) (MvPolynomial.comp_aeval (R := k)
    (Ideal.Quotient.mkₐ k (Subvariety.homIdeal X).toIdeal) (f := MvPolynomial.X))
  simp only [AlgHom.coe_comp, Function.comp_apply, aeval_X_left_apply] at h
  exact h.symm

variable {X} in
theorem mk_mem_grading {d : ℕ} {G : MvPolynomial (Fin (N + 1)) k} (hG : G.IsHomogeneous d) :
    (Ideal.Quotient.mk (Subvariety.homIdeal X).toIdeal G) ∈ Subvariety.grading X d :=
  Submodule.mem_map.2 ⟨G, hG, rfl⟩

variable {X} in
theorem coord_pow_mem (j : Fin (N + 1)) (d : ℕ) :
    Subvariety.coord X j ^ d ∈ Subvariety.grading X d := by
  have h := SetLike.pow_mem_graded d (Subvariety.coord_mem X j)
  rwa [smul_eq_mul, mul_one] at h

/-- The ratio `a_i = φ^*(x_i / x_{j₀}) ∈ k(Y)`. -/
def ratioX {j0 : Fin (N + 1)} (hj0 : Subvariety.coord X j0 ∉ ProjChart.genPrime _ φ)
    (i : Fin (N + 1)) : Y.functionField :=
  ProjChart.genMap _ φ (ProjChart.frac _ (Subvariety.coord_mem X i) (Subvariety.coord_mem X j0) hj0)

/-- **Homogeneous polynomials in the `a_i`.** For a homogeneous `G` of degree `d`,
`G(a) = φ^*(G / x_{j₀}^d)`, which vanishes iff `G ∈ I`. -/
theorem aeval_ratioX_eq_zero_iff (pY : Y ⟶ Spec (.of k)) (hφ : φ ≫ Subvariety.p X = pY)
    {j0 : Fin (N + 1)} (hj0 : Subvariety.coord X j0 ∉ ProjChart.genPrime _ φ) {d : ℕ}
    {G : MvPolynomial (Fin (N + 1)) k} (hG : G.IsHomogeneous d) :
    letI := pY.stalkAlgebra (genericPoint Y)
    aeval (ratioX X φ hj0) G = 0 ↔ G ∈ X.ideal := by
  let := pY.stalkAlgebra (genericPoint Y)
  have hpow : Subvariety.coord X j0 ^ d ∉ ProjChart.genPrime _ φ :=
    fun h => hj0 (Ideal.IsPrime.mem_of_pow_mem inferInstance d h)
  have hGm : aeval (Subvariety.coord X) G ∈ Subvariety.grading X d := by
    rw [aeval_coord]; exact mk_mem_grading hG
  have h := ProjChart.genMap_frac_aeval _ φ pY hφ (Subvariety.coord X) (Subvariety.coord_mem X)
    (Subvariety.coord_mem X j0) hj0 hG hGm (coord_pow_mem j0 d) hpow
  change aeval (fun i => ProjChart.genMap _ φ (ProjChart.frac _ (Subvariety.coord_mem X i)
    (Subvariety.coord_mem X j0) hj0)) G = 0 ↔ _
  rw [← h, ← not_iff_not, ← Ne, ProjChart.genMap_frac_ne_zero_iff, notMem_genPrime_iff,
    aeval_coord, Ne, Ideal.Quotient.eq_zero_iff_mem]
  rfl

omit [IsDominant φ] in
/-- **The image of `k(X)` in `k(Y)` is `k(a_0, …, a_N)`.** -/
theorem genMap_mem_adjoin_ratioX (pY : Y ⟶ Spec (.of k)) (hφ : φ ≫ Subvariety.p X = pY)
    {j0 : Fin (N + 1)} (hj0 : Subvariety.coord X j0 ∉ ProjChart.genPrime _ φ)
    (w : AtPrime (Subvariety.grading X) (ProjChart.genPrime _ φ)) :
    letI := pY.stalkAlgebra (genericPoint Y)
    ProjChart.genMap _ φ w ∈ IntermediateField.adjoin k (Set.range (ratioX X φ hj0)) := by
  let := pY.stalkAlgebra (genericPoint Y)
  obtain ⟨⟨d, ⟨a', ha'⟩, ⟨b', hb'⟩, hb'P⟩, rfl⟩ := mk_surjective w
  have hpow : Subvariety.coord X j0 ^ d ∉ ProjChart.genPrime _ φ :=
    fun h => hj0 (Ideal.IsPrime.mem_of_pow_mem inferInstance d h)
  have hnum : ∀ c : Subvariety.Ring X, ∀ hc : c ∈ Subvariety.grading X d,
      ProjChart.genMap _ φ (ProjChart.frac _ hc (coord_pow_mem j0 d) hpow) ∈
        IntermediateField.adjoin k (Set.range (ratioX X φ hj0)) := by
    intro c hc
    obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.1 hc
    have hGm : aeval (Subvariety.coord X) G ∈ Subvariety.grading X d := by
      rw [aeval_coord]; exact mk_mem_grading hG
    have h := ProjChart.genMap_frac_aeval _ φ pY hφ (Subvariety.coord X)
      (Subvariety.coord_mem X) (Subvariety.coord_mem X j0) hj0 hG hGm (coord_pow_mem j0 d) hpow
    have e : (Ideal.Quotient.mkₐ k (Subvariety.homIdeal X).toIdeal).toLinearMap G =
        aeval (Subvariety.coord X) G := (aeval_coord G).symm
    simp only [e]
    rw [h]
    refine IntermediateField.algebra_adjoin_le_adjoin k _ ?_
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact ⟨G, rfl⟩
  have hmul := ProjChart.frac_mul_frac (ProjChart.genPrime _ φ) ha' hb' (coord_pow_mem j0 d)
    hb'P hpow
  have hne : ProjChart.genMap _ φ (ProjChart.frac _ hb' (coord_pow_mem j0 d) hpow) ≠ 0 :=
    (ProjChart.genMap_frac_ne_zero_iff _ φ hb' _ hpow).2 hb'P
  have e : ProjChart.genMap _ φ (HomogeneousLocalization.mk ⟨d, ⟨a', ha'⟩, ⟨b', hb'⟩, hb'P⟩) =
      ProjChart.genMap _ φ (ProjChart.frac _ ha' (coord_pow_mem j0 d) hpow) /
        ProjChart.genMap _ φ (ProjChart.frac _ hb' (coord_pow_mem j0 d) hpow) := by
    rw [eq_div_iff hne, ← map_mul]
    exact congrArg _ hmul
  rw [e]
  exact div_mem (hnum a' ha') (hnum b' hb')

end Ratios


/-! ### Charts -/

section Chart

variable {k : Type u} [Field k]
  {A₁ : Type u} [CommRing A₁] [Algebra k A₁] (𝒜₁ : ℕ → Submodule k A₁) [GradedAlgebra 𝒜₁]
  {A₂ : Type u} [CommRing A₂] [Algebra k A₂] (𝒜₂ : ℕ → Submodule k A₂) [GradedAlgebra 𝒜₂]
  {Y : Scheme.{u}} [IsIntegral Y] (pY : Y ⟶ Spec (.of k))
  (ψ₁ : Y ⟶ Proj 𝒜₁) (ψ₂ : Y ⟶ Proj 𝒜₂)

/-- The `k`-subalgebras generated by two sets, each containing `k`: the subring generated by
their union is the `k`-subalgebra generated by the union of the generators. -/
theorem coe_closure_union_adjoin {L : Type u} [Field L] [Algebra k L] (S₁ S₂ : Set L) :
    (Subring.closure ((Algebra.adjoin k S₁ : Set L) ∪ Algebra.adjoin k S₂) : Set L) =
      Algebra.adjoin k (S₁ ∪ S₂) := by
  apply le_antisymm
  · have h : Subring.closure ((Algebra.adjoin k S₁ : Set L) ∪ Algebra.adjoin k S₂) ≤
        (Algebra.adjoin k (S₁ ∪ S₂)).toSubring := by
      rw [Subring.closure_le]
      rintro x (hx | hx)
      · exact Algebra.adjoin_mono Set.subset_union_left hx
      · exact Algebra.adjoin_mono Set.subset_union_right hx
    exact h
  · intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact Subring.subset_closure (Or.inl (Algebra.subset_adjoin hx))
      · exact Subring.subset_closure (Or.inr (Algebra.subset_adjoin hx))
    | algebraMap c =>
      exact Subring.subset_closure (Or.inl (Subalgebra.algebraMap_mem _ c))
    | add x y _ _ hx hy => exact Subring.add_mem _ hx hy
    | mul x y _ _ hx hy => exact Subring.mul_mem _ hx hy

/-- **The chart `ψ₂⁻¹ D₊(f₂) ∩ ψ₁⁻¹ D₊(f₁)`.** Let `ψ₁ : Y → Proj 𝒜₁` and the closed immersion
`ψ₂ : Y → Proj 𝒜₂` be morphisms over `k`, with `Proj 𝒜₁` separated over `k`, the graded algebras
generated over `k = 𝒜ᵢ₀` in degree `1` by `v₁`, `v₂`, and `f₁ ∈ 𝒜₁₁`, `f₂ ∈ 𝒜₂₁` not vanishing at
the images of the generic point. Then `V = ψ₂⁻¹ D₊(f₂) ∩ ψ₁⁻¹ D₊(f₁)` is a nonempty affine open of
`Y` whose coordinate ring, in `k(Y)`, is generated by the pull-backs of the ratios `v₁ / f₁` and
`v₂ / f₂`. -/
theorem exists_chart [IsSeparated (ProjChart.structureMap 𝒜₁)] [IsClosedImmersion ψ₂]
    (h₁ : ψ₁ ≫ ProjChart.structureMap 𝒜₁ = pY) (h₂ : ψ₂ ≫ ProjChart.structureMap 𝒜₂ = pY)
    {n₁ n₂ : ℕ} (v₁ : Fin (n₁ + 1) → A₁) (hv₁ : ∀ i, v₁ i ∈ 𝒜₁ 1)
    (hgen₁ : Algebra.adjoin k (Set.range v₁) = ⊤)
    (h0₁ : ∀ a ∈ 𝒜₁ 0, ∃ c : k, algebraMap k A₁ c = a)
    (v₂ : Fin (n₂ + 1) → A₂) (hv₂ : ∀ i, v₂ i ∈ 𝒜₂ 1)
    (hgen₂ : Algebra.adjoin k (Set.range v₂) = ⊤)
    (h0₂ : ∀ a ∈ 𝒜₂ 0, ∃ c : k, algebraMap k A₂ c = a)
    {f₁ : A₁} (hf₁ : f₁ ∈ 𝒜₁ 1) (hf₁P : f₁ ∉ ProjChart.genPrime 𝒜₁ ψ₁)
    {f₂ : A₂} (hf₂ : f₂ ∈ 𝒜₂ 1) (hf₂P : f₂ ∉ ProjChart.genPrime 𝒜₂ ψ₂) :
    letI := pY.stalkAlgebra (genericPoint Y)
    ∃ (V : Y.Opens) (_ : IsAffineOpen V) (_ : Nonempty V),
      (pY.sectionsFunctionFieldSubalgebra V : Set Y.functionField) =
        Algebra.adjoin k
          (Set.range (fun i => ProjChart.genMap 𝒜₁ ψ₁ (ProjChart.frac _ (hv₁ i) hf₁ hf₁P)) ∪
            Set.range (fun m => ProjChart.genMap 𝒜₂ ψ₂ (ProjChart.frac _ (hv₂ m) hf₂ hf₂P))) := by
  let := pY.stalkAlgebra (genericPoint Y)
  have hU : IsAffineOpen (Proj.basicOpen 𝒜₁ f₁) := Proj.isAffineOpen_basicOpen 𝒜₁ f₁ hf₁ one_pos
  have hWP : IsAffineOpen (Proj.basicOpen 𝒜₂ f₂) := Proj.isAffineOpen_basicOpen 𝒜₂ f₂ hf₂ one_pos
  have : IsAffineHom ψ₂ := (isClosedImmersion_iff_isAffineHom.mp ‹_›).1
  have hW : IsAffineOpen (ψ₂ ⁻¹ᵁ Proj.basicOpen 𝒜₂ f₂) := hWP.preimage ψ₂
  set V : Y.Opens := ψ₂ ⁻¹ᵁ Proj.basicOpen 𝒜₂ f₂ ⊓ ψ₁ ⁻¹ᵁ Proj.basicOpen 𝒜₁ f₁ with hVdef
  have hV : IsAffineOpen V := isAffineOpen_inf_preimage (ProjChart.structureMap 𝒜₁) ψ₁ hW hU
  have hηV : genericPoint Y ∈ V := ⟨hf₂P, hf₁P⟩
  have hne : Nonempty V := ⟨⟨_, hηV⟩⟩
  refine ⟨V, hV, hne, ?_⟩
  have hgraph := closure_range_restrict_appLE_eq_top (ProjChart.structureMap 𝒜₁) ψ₁ hW hU
  set ρ := (Y.germToFunctionField V).hom with hρ
  have e1 : (pY.sectionsFunctionFieldSubalgebra V : Set Y.functionField) = Set.range ρ := by
    ext x
    exact Iff.rfl
  have e2 : Set.range ρ = (Subring.closure (Set.range (ρ.comp
      (Y.presheaf.map (homOfLE (inf_le_left : V ≤ ψ₂ ⁻¹ᵁ Proj.basicOpen 𝒜₂ f₂)).op).hom) ∪
      Set.range (ρ.comp (ψ₁.appLE (Proj.basicOpen 𝒜₁ f₁) V inf_le_right).hom)) : Set _) := by
    rw [RingHom.coe_comp, RingHom.coe_comp, Set.range_comp, Set.range_comp, ← Set.image_union,
      ← RingHom.map_closure, hgraph, ← RingHom.range_eq_map]
    rfl
  have e3 : Set.range (ρ.comp
      (Y.presheaf.map (homOfLE (inf_le_left : V ≤ ψ₂ ⁻¹ᵁ Proj.basicOpen 𝒜₂ f₂)).op).hom) =
      Algebra.adjoin k
        (Set.range (fun m => ProjChart.genMap 𝒜₂ ψ₂ (ProjChart.frac _ (hv₂ m) hf₂ hf₂P))) := by
    have hcomp : ρ.comp
        (Y.presheaf.map (homOfLE (inf_le_left : V ≤ ψ₂ ⁻¹ᵁ Proj.basicOpen 𝒜₂ f₂)).op).hom =
        (Y.presheaf.germ (ψ₂ ⁻¹ᵁ Proj.basicOpen 𝒜₂ f₂) (genericPoint Y) hf₂P).hom := by
      ext s
      exact TopCat.Presheaf.germ_res_apply _ _ _ _ s
    rw [hcomp, ← ProjChart.range_pullGerm_eq_adjoin 𝒜₂ ψ₂ pY h₂ v₂ hv₂ hgen₂ h0₂ hf₂ hf₂P]
    have hsurj := (ψ₂.app_surjective _ hWP)
    rw [ProjChart.pullGerm, CommRingCat.hom_comp, RingHom.coe_comp, hsurj.range_comp]
  have e4 : Set.range (ρ.comp (ψ₁.appLE (Proj.basicOpen 𝒜₁ f₁) V inf_le_right).hom) =
      Algebra.adjoin k
        (Set.range (fun i => ProjChart.genMap 𝒜₁ ψ₁ (ProjChart.frac _ (hv₁ i) hf₁ hf₁P))) := by
    rw [← ProjChart.range_pullGerm_eq_adjoin 𝒜₁ ψ₁ pY h₁ v₁ hv₁ hgen₁ h0₁ hf₁ hf₁P]
    congr 1
    ext s
    change Y.presheaf.germ V (genericPoint Y) _ (Y.presheaf.map _ (ψ₁.app _ s)) = _
    rw [TopCat.Presheaf.germ_res_apply]
    rfl
  rw [e1, e2, e3, e4, Set.union_comm, coe_closure_union_adjoin]

/-- **Smoothness of a chart.** Under the hypotheses of `exists_chart`, with `pY` smooth, the
`k`-subalgebra of `k(Y)` generated by the ratios is smooth and integrally closed. -/
theorem smooth_adjoin_ratios [Smooth pY] [IsSeparated (ProjChart.structureMap 𝒜₁)]
    [IsClosedImmersion ψ₂]
    (h₁ : ψ₁ ≫ ProjChart.structureMap 𝒜₁ = pY) (h₂ : ψ₂ ≫ ProjChart.structureMap 𝒜₂ = pY)
    {n₁ n₂ : ℕ} (v₁ : Fin (n₁ + 1) → A₁) (hv₁ : ∀ i, v₁ i ∈ 𝒜₁ 1)
    (hgen₁ : Algebra.adjoin k (Set.range v₁) = ⊤)
    (h0₁ : ∀ a ∈ 𝒜₁ 0, ∃ c : k, algebraMap k A₁ c = a)
    (v₂ : Fin (n₂ + 1) → A₂) (hv₂ : ∀ i, v₂ i ∈ 𝒜₂ 1)
    (hgen₂ : Algebra.adjoin k (Set.range v₂) = ⊤)
    (h0₂ : ∀ a ∈ 𝒜₂ 0, ∃ c : k, algebraMap k A₂ c = a)
    {f₁ : A₁} (hf₁ : f₁ ∈ 𝒜₁ 1) (hf₁P : f₁ ∉ ProjChart.genPrime 𝒜₁ ψ₁)
    {f₂ : A₂} (hf₂ : f₂ ∈ 𝒜₂ 1) (hf₂P : f₂ ∉ ProjChart.genPrime 𝒜₂ ψ₂) :
    letI := pY.stalkAlgebra (genericPoint Y)
    Algebra.Smooth k (Algebra.adjoin k
          (Set.range (fun i => ProjChart.genMap 𝒜₁ ψ₁ (ProjChart.frac _ (hv₁ i) hf₁ hf₁P)) ∪
            Set.range (fun m => ProjChart.genMap 𝒜₂ ψ₂ (ProjChart.frac _ (hv₂ m) hf₂ hf₂P)))) ∧
      IsIntegrallyClosed (Algebra.adjoin k
          (Set.range (fun i => ProjChart.genMap 𝒜₁ ψ₁ (ProjChart.frac _ (hv₁ i) hf₁ hf₁P)) ∪
            Set.range (fun m => ProjChart.genMap 𝒜₂ ψ₂ (ProjChart.frac _ (hv₂ m) hf₂ hf₂P)))) := by
  let := pY.stalkAlgebra (genericPoint Y)
  obtain ⟨V, hV, hne, hVeq⟩ := exists_chart 𝒜₁ 𝒜₂ pY ψ₁ ψ₂ h₁ h₂ v₁ hv₁ hgen₁ h0₁ v₂ hv₂ hgen₂
    h0₂ hf₁ hf₁P hf₂ hf₂P
  have heq := SetLike.coe_injective hVeq
  let := pY.sectionsAlgebra V
  have hsm : Algebra.Smooth k Γ(Y, V) := pY.smooth_sectionsAlgebra hV
  have hic : IsIntegrallyClosed Γ(Y, V) := pY.isIntegrallyClosed_sections_of_smooth hV
  let e := (pY.sectionsFunctionFieldEquiv V).trans (Subalgebra.equivOfEq _ _ heq)
  exact ⟨Algebra.Smooth.of_equiv e, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

end Chart

section Finite

variable {k : Type u} [Field k] {N : ℕ} (X : ProjSubvariety k N) {Y : Scheme.{u}} [IsIntegral Y]
  (φ : Y ⟶ Subvariety.scheme X) [IsAlteration φ]

/-- **Finiteness of `k(Y)` over `k(a_0, …, a_N)`** (de Jong 2.20: `φ` is generically finite). -/
theorem finiteDimensional_adjoin_ratioX (pY : Y ⟶ Spec (.of k)) (hφ : φ ≫ Subvariety.p X = pY)
    {j0 : Fin (N + 1)} (hj0 : Subvariety.coord X j0 ∉ ProjChart.genPrime _ φ) :
    letI := pY.stalkAlgebra (genericPoint Y)
    FiniteDimensional (IntermediateField.adjoin k (Set.range (ratioX X φ hj0)))
      Y.functionField := by
  let := pY.stalkAlgebra (genericPoint Y)
  set L₀ := IntermediateField.adjoin k (Set.range (ratioX X φ hj0))
  have hfin := finiteDimensional_functionField φ
  let ffm := (Geometry.NormalizationInExtension.functionFieldMap φ).hom
  have hrange : ∀ z, ffm z ∈ L₀ := by
    intro z
    have e : ffm z = ProjChart.genMap _ φ ((Proj.stalkIso _ (φ (genericPoint Y))).hom.hom
        (((Subvariety.scheme X).presheaf.stalkCongr
          (.of_eq (genericPoint_map_of_isDominant φ).symm)).hom.hom z)) := by
      simp only [ffm, Geometry.NormalizationInExtension.functionFieldMap, ProjChart.genMap,
        CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
      rw [← CommRingCat.comp_apply (Proj.stalkIso _ _).hom, Iso.hom_inv_id, CommRingCat.id_apply]
    rw [e]
    exact genMap_mem_adjoin_ratioX X φ pY hφ hj0 _
  let := Geometry.FiniteBirationalNormal.functionFieldAlgebra φ
  let : Algebra (Subvariety.scheme X).functionField L₀ := (ffm.codRestrict L₀ hrange).toAlgebra
  have : IsScalarTower (Subvariety.scheme X).functionField L₀ Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite (Subvariety.scheme X).functionField L₀
    Y.functionField

end Finite


/-! ### The bridge -/

section Pair

variable {α : Type*} {N N' : ℕ}

/-- The function on the variables `x_i = x^{(0)}_i`, `y_m = x^{(1)}_m` of `k[x, y]` given by
`a` on the first block and `b` on the second. -/
def pairFun (a : Fin (N + 1) → α) (b : Fin (N' + 1) → α) : QuotVar ![N, N'] → α := fun i =>
  Fin.cases (motive := fun c : Fin 2 => Fin (![N, N'] c + 1) → α) a
    (fun c => Fin.cases (motive := fun c : Fin 1 => Fin (![N, N'] c.succ + 1) → α) b
      (fun c => c.elim0) c) i.1 i.2

/-- The chart index `(j₀, j₁)`. -/
def pairIdx (j0 : Fin (N + 1)) (j1 : Fin (N' + 1)) : (c : Fin 2) → Fin (![N, N'] c + 1) :=
  Fin.cases (motive := fun c : Fin 2 => Fin (![N, N'] c + 1)) j0
    (fun c => Fin.cases (motive := fun c : Fin 1 => Fin (![N, N'] c.succ + 1)) j1
      (fun c => c.elim0) c)

theorem pairFun_zero (a : Fin (N + 1) → α) (b : Fin (N' + 1) → α) (i : Fin (N + 1)) :
    pairFun a b ⟨0, i⟩ = a i :=
  rfl

theorem pairFun_one (a : Fin (N + 1) → α) (b : Fin (N' + 1) → α) (m : Fin (N' + 1)) :
    pairFun a b ⟨1, m⟩ = b m :=
  rfl

theorem range_pairFun_div {K : Type*} [DivisionRing K] (a : Fin (N + 1) → K)
    (b : Fin (N' + 1) → K) (j : (c : Fin 2) → Fin (![N, N'] c + 1)) :
    Set.range (fun i : QuotVar ![N, N'] => pairFun a b i / pairFun a b ⟨i.1, j i.1⟩) =
      Set.range (fun i : Fin (N + 1) => a i / a (j 0)) ∪
        Set.range (fun m : Fin (N' + 1) => b m / b (j 1)) := by
  ext x
  constructor
  · rintro ⟨⟨c, i⟩, rfl⟩
    fin_cases c
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨i, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨m, rfl⟩)
    · exact ⟨⟨0, i⟩, rfl⟩
    · exact ⟨⟨1, m⟩, rfl⟩

end Pair

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **The model form of de Jong's theorem** (EnvelopeProperty's `thm:gl-dejong`) for one
projective subvariety. -/
theorem exists_alteration (h : DeJongAlterationTheorem k) {N : ℕ} (X : ProjSubvariety k N) :
    ∃ (N' : ℕ) (I_Y : Ideal (MvPolynomial (QuotVar ![N, N']) k)) (_ : I_Y.IsPrime)
      (j₀ : (c : Fin 2) → Fin (![N, N'] c + 1)) (hj₀ : IsRelevantAt I_Y j₀),
      IsMultihomogeneous I_Y ∧
        I_Y.comap (rename fun i : Fin (N + 1) => (⟨0, i⟩ : QuotVar ![N, N'])) = X.ideal ∧
        FiniteDimensional (quotBlockField I_Y j₀ 0) (QuotFieldTy I_Y j₀) ∧
        (quotModel I_Y j₀ hj₀).IsSmooth := by
  obtain ⟨A⟩ := nonempty_smoothProjectiveAlteration h (Subvariety.p X)
  obtain ⟨Y, pY, φ, N', ι₀, hvar, hsm, halt, hφ, hι, hιp⟩ := A
  have : IsIntegral Y := hvar.toIsIntegral
  have : IsDominant φ := halt.toIsDominant
  let ι : Y ⟶ Proj (projectiveSpaceGrading k N') := ι₀
  have : IsClosedImmersion ι := hι
  have hιp' : ι ≫ ProjChart.structureMap (projectiveSpaceGrading k N') = pY := by
    rw [← projectiveSpaceStructure_eq]
    exact hιp
  let := pY.stalkAlgebra (genericPoint Y)
  obtain ⟨j0, hj0⟩ := X.exists_X_notMem
  have hj0P : Subvariety.coord X j0 ∉ ProjChart.genPrime _ φ :=
    (notMem_genPrime_iff X φ _).2 ((Subvariety.coord_ne_zero_iff X j0).2 hj0)
  obtain ⟨j1, hj1P⟩ := ProjChart.exists_notMem_genPrime (projectiveSpaceGrading k N') ι
    MvPolynomial.X (X_mem_projectiveSpaceGrading k N') (adjoin_range_X_eq_top k N')
  set a := ratioX X φ hj0P with ha
  set b : Fin (N' + 1) → Y.functionField := fun m => ProjChart.genMap _ ι
    (ProjChart.frac _ (X_mem_projectiveSpaceGrading k N' m) (X_mem_projectiveSpaceGrading k N' j1)
      hj1P) with hb
  set g := pairFun a b with hgdef
  have ha0 : a j0 = 1 := ProjChart.genMap_frac_self _ φ _ hj0P
  have hb1 : b j1 = 1 := ProjChart.genMap_frac_self _ ι _ hj1P
  have hg : ∀ c, g ⟨c, pairIdx j0 j1 c⟩ ≠ 0 := by
    intro c
    fin_cases c
    · change a j0 ≠ 0
      rw [ha0]
      exact one_ne_zero
    · change b j1 ≠ 0
      rw [hb1]
      exact one_ne_zero
  refine ⟨N', kerIdeal k g, inferInstance, pairIdx j0 j1, isRelevantAt_kerIdeal k g hg,
    isMultihomogeneous_kerIdeal k g, ?_, ?_, ?_⟩
  · ext F
    rw [Ideal.mem_comap, mem_kerIdeal, kerMap, aeval_rename]
    exact aeval_monomial_eq_zero_iff k 0 a X.ideal X.isHomogeneousIdeal
      (fun d G hG => aeval_ratioX_eq_zero_iff X φ pY hφ hj0P hG) F
  · refine finiteDimensional_quotBlockField k g hg 0 ?_
    have e : (fun i : Fin (![N, N'] 0 + 1) => g ⟨0, i⟩ / g ⟨0, pairIdx j0 j1 0⟩) = a := by
      funext i
      change a i / a j0 = a i
      rw [ha0, div_one]
    rw [e]
    exact finiteDimensional_adjoin_ratioX X φ pY hφ hj0P
  · refine isSmooth_quotModel_kerIdeal k g hg ?_
    intro j hj
    rw [range_pairFun_div]
    have ha' : a (j 0) ≠ 0 := hj 0
    have hb' : b (j 1) ≠ 0 := hj 1
    have hxP : Subvariety.coord X (j 0) ∉ ProjChart.genPrime _ φ :=
      (ProjChart.genMap_frac_ne_zero_iff _ φ _ _ hj0P).1 ha'
    have hyP : (MvPolynomial.X (j 1) : MvPolynomial (Fin (N' + 1)) k) ∉
        ProjChart.genPrime _ ι :=
      (ProjChart.genMap_frac_ne_zero_iff _ ι _ _ hj1P).1 hb'
    have key := smooth_adjoin_ratios (Subvariety.grading X) (projectiveSpaceGrading k N') pY φ ι
      hφ hιp' (Subvariety.coord X) (Subvariety.coord_mem X) (Subvariety.adjoin_range_coord X)
      (Subvariety.exists_algebraMap_eq_of_mem_grading_zero X) MvPolynomial.X
      (X_mem_projectiveSpaceGrading k N') (adjoin_range_X_eq_top k N')
      (exists_algebraMap_eq_of_mem_projectiveSpaceGrading_zero k N')
      (Subvariety.coord_mem X (j 0)) hxP (X_mem_projectiveSpaceGrading k N' (j 1)) hyP
    have e1 : (fun i => ProjChart.genMap _ φ (ProjChart.frac _ (Subvariety.coord_mem X i)
        (Subvariety.coord_mem X (j 0)) hxP)) = fun i => a i / a (j 0) := by
      funext i
      exact ProjChart.genMap_frac_eq_div _ φ _ _ (Subvariety.coord_mem X j0) hxP hj0P
    have e2 : (fun m => ProjChart.genMap _ ι (ProjChart.frac _ (X_mem_projectiveSpaceGrading k N' m)
        (X_mem_projectiveSpaceGrading k N' (j 1)) hyP)) = fun m => b m / b (j 1) := by
      funext m
      exact ProjChart.genMap_frac_eq_div _ ι _ _ (X_mem_projectiveSpaceGrading k N' j1) hyP hj1P
    rw [e1, e2] at key
    exact key

/-- **de Jong's alteration theorem gives EnvelopeProperty's hypothesis.** For an algebraically
closed field `k`, Theorem 4.1 of de Jong (in Codex's form `DeJongAlterations.DeJongAlterationTheorem
k`) implies the model form `EnvelopeProperty.DeJongAlterations k` used by Fang–Han–Xia
(EnvelopeProperty blueprint `thm:gl-dejong`). -/
theorem deJongAlterations_of_theorem (h : DeJongAlterationTheorem k) :
    EnvelopeProperty.DeJongAlterations k :=
  ⟨fun X => exists_alteration h X⟩

end DeJongEPBridge
