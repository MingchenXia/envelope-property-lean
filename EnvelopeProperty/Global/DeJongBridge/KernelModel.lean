import EnvelopeProperty.Global.DeJongModel

/-!
# The multihomogeneous ideal of a family of rational functions

This is the algebraic half of the bridge from de Jong's Theorem 4.1 (de Jong, *Smoothness,
semi-stability and alterations*) to the hypothesis `EnvelopeProperty.Alterations k` (blueprint
`thm:gl-dejong`; steps 4–6 of the bridge).

Let `K` be a field over `k` and let `g = (g^{(c)}_j)` be elements of `K` indexed by the
variables `x^{(c)}_j` of the multigraded ring `R = k[x^{(c)}_j]`
(`EnvelopeProperty.MultiModel.QuotVar M`), with `g^{(c)}_{j₀ c} ≠ 0` for every block `c`.
Geometrically `g^{(c)}_j = x^{(c)}_j / x^{(c)}_{j₀ c}` are the pull-backs of the coordinate ratios
of a morphism `Y → ℙ^{M_1} × ⋯ × ℙ^{M_r}` to the function field `K = k(Y)`.

* `DeJongEPBridge.kerMap g : R → K[T_1, …, T_r]`, `x^{(c)}_j ↦ g^{(c)}_j T_c`, sends the
  multihomogeneous component of degree `a` of `F` to the monomial of degree `a` of the image of `F`
  (`kerMap_weightedHomogeneousComponent`). Its kernel `kerIdeal g` is therefore a
  multihomogeneous (`isMultihomogeneous_kerIdeal`) prime ideal, relevant at `j₀`
  (`isRelevantAt_kerIdeal`): it is the multihomogeneous ideal of the closure of the image of `Y`.
* `quotFieldToK g hg : k(I_g) →ₐ[k] K`: the degree-zero fraction field
  `MultiModel.QuotFieldTy (kerIdeal g) j₀` embeds into `K`, sending
  `x̄^{(c)}_j / x̄^{(c)}_{j₀ c}` to `g^{(c)}_j / g^{(c)}_{j₀ c}` (`quotFieldToK_quotCoord`).
* Under this embedding the chart algebra of the quotient model at a chart index `j` with all
  `g^{(c)}_{j c} ≠ 0` is the subalgebra `k[g^{(c)}_i / g^{(c)}_{j c}] ⊆ K` (`map_chartAlg`), so the
  quotient model is smooth as soon as these subalgebras are smooth and integrally closed
  (`isSmooth_quotModel_kerIdeal`); and `k(I_g)` is finite over its block field `c` as soon as `K`
  is finite over `k(g^{(c)}_i / g^{(c)}_{j₀ c})` (`finiteDimensional_quotBlockField`).
-/

open MvPolynomial

noncomputable section

namespace DeJongEPBridge

open EnvelopeProperty EnvelopeProperty.MultiModel

universe u

variable (k : Type u) [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ} {M : Fin r → ℕ}

section KerMap

variable (g : QuotVar M → K)

/-- The generator `g^{(c)}_j T_c ∈ K[T]` attached to the variable `i = x^{(c)}_j`. -/
def kerGen (i : QuotVar M) : MvPolynomial (Fin r) K :=
  monomial (Finsupp.single i.1 1) (g i)

/-- The map `Θ_g : k[x^{(c)}_j] → K[T_1, …, T_r]`, `x^{(c)}_j ↦ g^{(c)}_j T_c`. -/
def kerMap : MvPolynomial (QuotVar M) k →ₐ[k] MvPolynomial (Fin r) K :=
  aeval (kerGen g)

/-- The ideal `I_g = ker Θ_g ⊆ k[x^{(c)}_j]`. -/
def kerIdeal : Ideal (MvPolynomial (QuotVar M) k) :=
  RingHom.ker (kerMap k g)

instance isPrime_kerIdeal : (kerIdeal k g).IsPrime :=
  RingHom.ker_isPrime _

theorem mem_kerIdeal {F : MvPolynomial (QuotVar M) k} : F ∈ kerIdeal k g ↔ kerMap k g F = 0 :=
  RingHom.mem_ker

theorem kerMap_X (i : QuotVar M) : kerMap k g (X i) = kerGen g i :=
  aeval_X _ _

/-- The coefficient `∏ (g^{(c)}_j)^{β^{(c)}_j} ∈ K` of the image of `x^β`. -/
def kerZ (β : QuotVar M →₀ ℕ) : K :=
  β.prod fun i n => g i ^ n

theorem kerZ_add (β γ : QuotVar M →₀ ℕ) : kerZ g (β + γ) = kerZ g β * kerZ g γ :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _

theorem kerZ_single (i : QuotVar M) (n : ℕ) : kerZ g (Finsupp.single i n) = g i ^ n :=
  Finsupp.prod_single_index (pow_zero _)

/-- `∏ (g^{(c)}_j T_c)^{β^{(c)}_j} = (∏ (g^{(c)}_j)^{β^{(c)}_j}) T^{deg β}`. -/
theorem prod_kerGen_pow (β : QuotVar M →₀ ℕ) :
    (β.prod fun i n => kerGen g i ^ n) = monomial (Finsupp.mapDomain Sigma.fst β) (kerZ g β) := by
  induction β using Finsupp.induction with
  | zero => simp [kerZ, ← C_apply]
  | single_add i n β hi hn ih =>
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _, ih,
      Finsupp.prod_single_index (h := fun i n => kerGen g i ^ n) (pow_zero _), kerZ_add,
      kerZ_single, Finsupp.mapDomain_add, Finsupp.mapDomain_single, kerGen, monomial_pow,
      monomial_mul, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The image of a monomial: `c x^β ↦ (c ∏ (g^{(c)}_j)^{β^{(c)}_j}) T^{deg β}`. -/
theorem kerMap_monomial (β : QuotVar M →₀ ℕ) (c : k) :
    kerMap k g (monomial β c) =
      monomial (Finsupp.mapDomain Sigma.fst β) (algebraMap k K c * kerZ g β) := by
  rw [kerMap, aeval_monomial, prod_kerGen_pow, MvPolynomial.algebraMap_apply, C_mul_monomial]

/-- The coefficients of the image of `F`. -/
theorem coeff_kerMap (F : MvPolynomial (QuotVar M) k) (a : Fin r →₀ ℕ) :
    (kerMap k g F).coeff a = ∑ β ∈ F.support with Finsupp.mapDomain Sigma.fst β = a,
      algebraMap k K (F.coeff β) * kerZ g β := by
  classical
  conv_lhs => rw [F.as_sum, map_sum]
  rw [coeff_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [kerMap_monomial, coeff_monomial]

/-- **`Θ_g` is multigraded**: the image of the multihomogeneous component of degree `a` of `F` is
the monomial of degree `a` of the image of `F`. -/
theorem kerMap_weightedHomogeneousComponent (F : MvPolynomial (QuotVar M) k) (a : Fin r →₀ ℕ) :
    kerMap k g (weightedHomogeneousComponent (quotWeight M) a F) =
      monomial a ((kerMap k g F).coeff a) := by
  classical
  rw [weightedHomogeneousComponent_apply, map_sum, coeff_kerMap, map_sum]
  simp_rw [weight_quotWeight]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [kerMap_monomial, (Finset.mem_filter.1 hβ).2]

/-- `I_g` is multihomogeneous. -/
theorem isMultihomogeneous_kerIdeal : IsMultihomogeneous (kerIdeal k g) := by
  intro F hF a
  rw [mem_kerIdeal] at hF ⊢
  rw [kerMap_weightedHomogeneousComponent, hF, coeff_zero, map_zero]

theorem X_mem_kerIdeal_iff (i : QuotVar M) :
    (X i : MvPolynomial (QuotVar M) k) ∈ kerIdeal k g ↔ g i = 0 := by
  rw [mem_kerIdeal, kerMap_X, kerGen, monomial_eq_zero]

/-- `I_g` is relevant at `j₀` when all `g^{(c)}_{j₀ c} ≠ 0`. -/
theorem isRelevantAt_kerIdeal {j₀ : (c : Fin r) → Fin (M c + 1)}
    (hg : ∀ c, g ⟨c, j₀ c⟩ ≠ 0) : IsRelevantAt (kerIdeal k g) j₀ := fun c => by
  rw [X_mem_kerIdeal_iff]
  exact hg c

end KerMap

/-! ### The embedding of the function field -/

section FieldEmb

variable (K r) in
/-- The field `K(T_1, …, T_r)`. -/
abbrev KT : Type u :=
  FractionRing (MvPolynomial (Fin r) K)

/-- The constants `K → K(T)`. -/
def constKT : K →ₐ[k] KT K r :=
  (IsScalarTower.toAlgHom k (MvPolynomial (Fin r) K) (KT K r)).comp
    (IsScalarTower.toAlgHom k K (MvPolynomial (Fin r) K))

theorem constKT_apply (x : K) :
    constKT k (r := r) x = algebraMap (MvPolynomial (Fin r) K) (KT K r) (C x) :=
  rfl

theorem constKT_injective : Function.Injective (constKT k (K := K) (r := r)) :=
  (constKT k (K := K) (r := r)).toRingHom.injective

variable (g : QuotVar M → K)

/-- `R / I_g → K(T)`, induced by `Θ_g`; it is injective. -/
def quotToKT : (MvPolynomial (QuotVar M) k ⧸ kerIdeal k g) →ₐ[k] KT K r :=
  (IsScalarTower.toAlgHom k (MvPolynomial (Fin r) K) (KT K r)).comp
    (Ideal.kerLiftAlg (kerMap k g))

theorem quotToKT_injective : Function.Injective (quotToKT k g) :=
  (IsFractionRing.injective (MvPolynomial (Fin r) K) (KT K r)).comp
    (Ideal.kerLiftAlg_injective (kerMap k g))

theorem quotToKT_mk (F : MvPolynomial (QuotVar M) k) :
    quotToKT k g (Ideal.Quotient.mk _ F) =
      algebraMap (MvPolynomial (Fin r) K) (KT K r) (kerMap k g F) :=
  rfl

/-- `Frac(R / I_g) → K(T)`. -/
def fracToKT : FractionRing (MvPolynomial (QuotVar M) k ⧸ kerIdeal k g) →ₐ[k] KT K r :=
  IsFractionRing.liftAlgHom (quotToKT_injective k g)

theorem fracToKT_algebraMap (x : MvPolynomial (QuotVar M) k ⧸ kerIdeal k g) :
    fracToKT k g (algebraMap _ _ x) = quotToKT k g x := by
  rw [fracToKT, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

theorem fracToKT_quotVarImage (i : QuotVar M) :
    fracToKT k g (quotVarImage (kerIdeal k g) i) =
      constKT k (g i) * algebraMap (MvPolynomial (Fin r) K) (KT K r) (X i.1) := by
  rw [quotVarImage, fracToKT_algebraMap, quotToKT_mk, kerMap_X, kerGen, ← C_mul_X_eq_monomial,
    map_mul, constKT_apply]

variable {j₀ : (c : Fin r) → Fin (M c + 1)}

theorem fracToKT_quotRatio (hg : ∀ c, g ⟨c, j₀ c⟩ ≠ 0) (i : QuotVar M) :
    fracToKT k g (quotRatio (kerIdeal k g) j₀ i) = constKT k (g i / g ⟨i.1, j₀ i.1⟩) := by
  have hX : algebraMap (MvPolynomial (Fin r) K) (KT K r) (X i.1) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (X_ne_zero _)
  have hc : constKT k (r := r) (g ⟨i.1, j₀ i.1⟩) ≠ 0 :=
    (map_ne_zero_iff _ (constKT_injective k)).2 (hg i.1)
  rw [quotRatio, map_div₀, fracToKT_quotVarImage, fracToKT_quotVarImage, map_div₀,
    mul_div_mul_right _ _ hX]

theorem fracToKT_quotFieldEmb_mem (hg : ∀ c, g ⟨c, j₀ c⟩ ≠ 0)
    (x : QuotFieldTy (kerIdeal k g) j₀) :
    fracToKT k g (quotFieldEmb (kerIdeal k g) j₀ x) ∈ (constKT k (K := K) (r := r)).range := by
  have hmem : fracToKT k g (quotFieldEmb (kerIdeal k g) j₀ x) ∈
      (QuotField (kerIdeal k g) j₀).map (fracToKT k g) :=
    ⟨_, quotFieldEmb_mem (kerIdeal k g) j₀ x, rfl⟩
  rw [QuotField, IntermediateField.adjoin_map] at hmem
  have hle : IntermediateField.adjoin k (fracToKT k g '' Set.range (quotRatio (kerIdeal k g) j₀)) ≤
      (constKT k (K := K) (r := r)).fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨_, (fracToKT_quotRatio k g hg i).symm⟩
  obtain ⟨y, hy⟩ := hle hmem
  exact ⟨y, hy⟩

/-- **The embedding `k(I_g) → K`** of the degree-zero fraction field of `R / I_g`, sending
`x̄^{(c)}_j / x̄^{(c)}_{j₀ c}` to `g^{(c)}_j / g^{(c)}_{j₀ c}` (`quotFieldToK_quotCoord`). -/
def quotFieldToK (hg : ∀ c, g ⟨c, j₀ c⟩ ≠ 0) : QuotFieldTy (kerIdeal k g) j₀ →ₐ[k] K :=
  (AlgEquiv.ofInjectiveField (constKT k (K := K) (r := r))).symm.toAlgHom.comp
    (((fracToKT k g).comp (quotFieldEmb (kerIdeal k g) j₀)).codRestrict _
      (fracToKT_quotFieldEmb_mem k g hg))

theorem constKT_quotFieldToK (hg : ∀ c, g ⟨c, j₀ c⟩ ≠ 0) (x : QuotFieldTy (kerIdeal k g) j₀) :
    constKT k (r := r) (quotFieldToK k g hg x) = fracToKT k g (quotFieldEmb (kerIdeal k g) j₀ x) :=
  congrArg Subtype.val ((AlgEquiv.ofInjectiveField (constKT k (K := K) (r := r))).apply_symm_apply
    ⟨_, fracToKT_quotFieldEmb_mem k g hg x⟩)

theorem quotFieldToK_quotCoord (hg : ∀ c, g ⟨c, j₀ c⟩ ≠ 0) (c : Fin r) (j : Fin (M c + 1)) :
    quotFieldToK k g hg (quotCoord (kerIdeal k g) j₀ c j) = g ⟨c, j⟩ / g ⟨c, j₀ c⟩ := by
  apply constKT_injective k (r := r)
  rw [constKT_quotFieldToK, quotFieldEmb_quotCoord, fracToKT_quotRatio k g hg]

theorem quotFieldToK_injective (hg : ∀ c, g ⟨c, j₀ c⟩ ≠ 0) :
    Function.Injective (quotFieldToK k g hg) :=
  (quotFieldToK k g hg).toRingHom.injective

theorem quotCoord_ne_zero_iff (hg : ∀ c, g ⟨c, j₀ c⟩ ≠ 0) (c : Fin r) (j : Fin (M c + 1)) :
    quotCoord (kerIdeal k g) j₀ c j ≠ 0 ↔ g ⟨c, j⟩ ≠ 0 := by
  rw [← (map_ne_zero_iff _ (quotFieldToK_injective k g hg)), quotFieldToK_quotCoord,
    div_ne_zero_iff, and_iff_left (hg c)]

/-! ### Chart algebras and block fields -/

/-- **The chart algebras of the quotient model of `I_g`**: at a chart index `j` with all
`g^{(c)}_{j c} ≠ 0`, the image of the chart algebra in `K` is `k[g^{(c)}_i / g^{(c)}_{j c}]`. -/
theorem map_chartAlg (hg : ∀ c, g ⟨c, j₀ c⟩ ≠ 0)
    (j : (quotModel (kerIdeal k g) j₀ (isRelevantAt_kerIdeal k g hg)).ChartIndex) :
    ((quotModel (kerIdeal k g) j₀ (isRelevantAt_kerIdeal k g hg)).chartAlg j).map
        (quotFieldToK k g hg) =
      Algebra.adjoin k (Set.range fun i : QuotVar M => g i / g ⟨i.1, j i.1⟩) := by
  rw [MultiModel.chartAlg_eq_adjoin _ j (G := Set.range (quotGen (kerIdeal k g) j₀)) rfl,
    AlgHom.map_adjoin, ← Set.range_comp, ← Set.range_comp]
  refine congrArg (Algebra.adjoin k) (congrArg Set.range (funext fun i => ?_))
  rw [Function.comp_apply, Function.comp_apply, quotGen, MultiModel.dehom_monomial,
    MultiModel.chartDen_single, quotModel_coord, map_div₀,
    quotFieldToK_quotCoord k g hg i.1 i.2, quotFieldToK_quotCoord k g hg i.1 (j i.1),
    div_div_div_cancel_right₀ (hg i.1)]

/-- **Smoothness of the quotient model of `I_g`** (`def:gl-smooth`): it suffices that every
subalgebra `k[g^{(c)}_i / g^{(c)}_{j c}] ⊆ K` with all `g^{(c)}_{j c} ≠ 0` is smooth and integrally
closed. -/
theorem isSmooth_quotModel_kerIdeal (hg : ∀ c, g ⟨c, j₀ c⟩ ≠ 0)
    (hsm : ∀ j : (c : Fin r) → Fin (M c + 1), (∀ c, g ⟨c, j c⟩ ≠ 0) →
      Algebra.Smooth k (Algebra.adjoin k (Set.range fun i : QuotVar M => g i / g ⟨i.1, j i.1⟩)) ∧
      IsIntegrallyClosed
        (Algebra.adjoin k (Set.range fun i : QuotVar M => g i / g ⟨i.1, j i.1⟩))) :
    (quotModel (kerIdeal k g) j₀ (isRelevantAt_kerIdeal k g hg)).IsSmooth := by
  intro j hj
  have hj' : ∀ c, g ⟨c, j c⟩ ≠ 0 := fun c => (quotCoord_ne_zero_iff k g hg c (j c)).1 (hj c)
  obtain ⟨h1, h2⟩ := hsm j hj'
  let e := (Subalgebra.equivMapOfInjective _ _ (quotFieldToK_injective k g hg)).trans
    (Subalgebra.equivOfEq _ _ (map_chartAlg k g hg j))
  exact ⟨Algebra.Smooth.of_equiv e.symm, IsIntegrallyClosed.of_equiv e.symm.toRingEquiv⟩

/-- **Finiteness over a block field**: if `K` is finite over `k(g^{(c)}_i / g^{(c)}_{j₀ c})`, then
`k(I_g)` is finite over its block field `c`. -/
theorem finiteDimensional_quotBlockField (hg : ∀ c, g ⟨c, j₀ c⟩ ≠ 0) (c : Fin r)
    (hfin : FiniteDimensional
      (IntermediateField.adjoin k (Set.range fun i : Fin (M c + 1) => g ⟨c, i⟩ / g ⟨c, j₀ c⟩)) K) :
    FiniteDimensional (quotBlockField (kerIdeal k g) j₀ c) (QuotFieldTy (kerIdeal k g) j₀) := by
  set ε := quotFieldToK k g hg
  set L₀ := IntermediateField.adjoin k (Set.range fun i : Fin (M c + 1) => g ⟨c, i⟩ / g ⟨c, j₀ c⟩)
  have hmap : (quotBlockField (kerIdeal k g) j₀ c).map ε = L₀ := by
    rw [quotBlockField, IntermediateField.adjoin_map, ← Set.range_comp]
    exact congrArg (IntermediateField.adjoin k)
      (congrArg Set.range (funext fun i => quotFieldToK_quotCoord k g hg c i))
  have hle : L₀ ≤ ε.fieldRange := by
    rw [← hmap, AlgHom.fieldRange_eq_map]
    exact IntermediateField.map_mono _ le_top
  have hrel : IntermediateField.relfinrank (quotBlockField (kerIdeal k g) j₀ c) ⊤ =
      IntermediateField.relfinrank L₀ ε.fieldRange := by
    rw [← IntermediateField.relfinrank_map_map _ _ ε, hmap, ← AlgHom.fieldRange_eq_map]
  have hmul := IntermediateField.relfinrank_mul_relfinrank hle (le_top : ε.fieldRange ≤ ⊤)
  have hpos : 0 < IntermediateField.relfinrank L₀ (⊤ : IntermediateField k K) := by
    rw [IntermediateField.relfinrank_top_right]
    exact Module.finrank_pos
  rw [← hmul] at hpos
  refine Module.finite_of_finrank_pos ?_
  rw [← IntermediateField.relfinrank_top_right, hrel]
  exact Nat.pos_of_ne_zero fun h => by simp [h] at hpos

end FieldEmb

end DeJongEPBridge
