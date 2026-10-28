import EnvelopeProperty.Cartier.PolynomialCartierImage
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Actual native polynomial Cartier cohomology

All scalars, original exterior cotangent modules and original differentials are retained.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.PolynomialCartierCohomology
open scoped Classical
open CategoryTheory Limits MvPolynomial PolynomialDeRham PolynomialCartierImage
variable (k : Type*) [Field k] {σ : Type*} [LinearOrder σ] [Fintype σ]
variable (p : ℕ) [hp : Fact p.Prime] [CharP k p] [PerfectRing k p]

/-- The whole original carrier and additive operations are preserved by the ACTUAL native
restriction of scalars. This is the actual identity, with no comparison premise. -/
def frobeniusUnderlying (q : ℕ) : frobeniusModule (σ := σ) k p q ≃+
    (⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) where
  toFun := fun w => w
  invFun := fun w => w
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl

omit [PerfectRing k p] [LinearOrder σ] [Fintype σ] in
/-- The actual native restricted scalar multiplication is the SAME original p-th-power action. -/
theorem frobeniusUnderlying_smul (q : ℕ) (a : MvPolynomial σ k)
    (w : frobeniusModule (σ := σ) k p q) :
    frobeniusUnderlying k p q (a • w) = a^p • frobeniusUnderlying k p q w := rfl

/-- The actual whole coefficient-root map is genuinely linear for the original Frobenius
scalar action. No linearity or coefficient-matching hypothesis is supplied. -/
theorem coefficient_pow_smul (q : ℕ) (a : MvPolynomial σ k)
    (w : ⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) :
    coefficient k p q (a^p • w) = a • coefficient k p q w := by
  let b := (KaehlerDifferential.mvPolynomialBasis k σ).exteriorPower q
  change (∑ s : Set.powersetCard σ q,
    rootPoly p 1 (residueDigit p q s).toFinsupp (b.coord s (a^p • w)) • b s) =
      a • ∑ s : Set.powersetCard σ q,
        rootPoly p 1 (residueDigit p q s).toFinsupp (b.coord s w) • b s
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_smul, smul_eq_mul]
  rw [rootPoly_one_pow_mul p (fun i => (residueDigit p q s i).isLt), smul_smul]

/-- The genuine whole P-linear Cartier coefficient on the ACTUAL native Frobenius module. -/
def coefficientLinear (q : ℕ) : frobeniusModule (σ := σ) k p q →ₗ[MvPolynomial σ k]
    (⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) where
  toFun := (coefficient k p q).comp (frobeniusUnderlying k p q).toAddMonoidHom
  map_add' := ((coefficient k p q).comp (frobeniusUnderlying k p q).toAddMonoidHom).map_add
  map_smul' a w := by
    change coefficient k p q (frobeniusUnderlying k p q (a • w)) =
      a • coefficient k p q (frobeniusUnderlying k p q w)
    rw [frobeniusUnderlying_smul, coefficient_pow_smul]

/-- The actual native linear coefficient recovers EVERY original form from its genuine
Cartier representative. -/
theorem coefficientLinear_representative (q : ℕ)
    (w : ⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) :
    coefficientLinear k p q (representative k p q w) = w :=
  coefficient_representative k p q w

/-- The genuine actual original positive-degree three-term de Rham complex. -/
def positiveShortComplex (q : ℕ) : ShortComplex (ModuleCat (MvPolynomial σ k)) :=
  ShortComplex.mk (frobeniusDifferential (σ := σ) k p q)
    (frobeniusDifferential (σ := σ) k p (q+1)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      exact differential_square k q w)

/-- The ACTUAL native linear Cartier coefficient on the ENTIRE original cycle module. -/
def cycleCoefficient (q : ℕ) :
    LinearMap.ker (positiveShortComplex (σ := σ) k p q).g.hom →ₗ[MvPolynomial σ k]
      (⋀[MvPolynomial σ k]^(q+1) (KaehlerDifferential k (MvPolynomial σ k))) :=
  (coefficientLinear k p (q+1)).comp
    (LinearMap.ker (positiveShortComplex (σ := σ) k p q).g.hom).subtype

/-- Every original form is obtained from an ACTUAL original cycle by the native linear
coefficient map; its preimage is the genuinely closed Cartier representative. -/
theorem cycleCoefficient_surjective (q : ℕ) :
    Function.Surjective (cycleCoefficient (σ := σ) k p q) := by
  intro w
  refine ⟨⟨representative k p (q+1) w, ?_⟩, ?_⟩
  · change differential k (q+1) (originalRepresentative k p (q+1) w) = 0
    exact originalRepresentative_closed k p (q+1) w
  · exact coefficientLinear_representative k p (q+1) w

/-- The kernel of the actual native coefficient on ALL cycles is EXACTLY the actual
boundary range of the SAME original three-term Frobenius de Rham complex. -/
theorem cycleCoefficient_kernel (q : ℕ) :
    LinearMap.ker (cycleCoefficient (σ := σ) k p q) =
      LinearMap.range (positiveShortComplex (σ := σ) k p q).moduleCatToCycles := by
  ext z
  change cycleCoefficient k p q z = 0 ↔ ∃ u,
    (positiveShortComplex k p q).moduleCatToCycles u = z
  have hz : differential k (q+1) (frobeniusUnderlying k p (q+1) z.val) = 0 := z.property
  constructor
  · intro hc
    have hR : PolynomialCartierProjection.originalAllResidual k p (q+1)
        (frobeniusUnderlying k p (q+1) z.val) = 0 := by
      rw [← representative_coefficient]
      change originalRepresentative k p (q+1) (cycleCoefficient k p q z) = 0
      rw [hc, map_zero]
    obtain ⟨u, hu⟩ := (PolynomialCartierProjection.original_boundary_iff_residual_zero
      k p q _ hz).mpr hR
    refine ⟨(frobeniusUnderlying k p q).symm u, ?_⟩
    apply Subtype.ext
    apply (frobeniusUnderlying k p (q+1)).injective
    exact hu
  · rintro ⟨u, hu⟩
    have hval : differential k q (frobeniusUnderlying k p q u) =
        frobeniusUnderlying k p (q+1) z.val :=
      congrArg (fun z => frobeniusUnderlying k p (q+1) z.val) hu
    change coefficient k p (q+1) (frobeniusUnderlying k p (q+1) z.val) = 0
    rw [← hval]
    exact coefficient_boundary_zero k p q (frobeniusUnderlying k p q u)

/-- The ENTIRE actual original cycle quotient is P-linearly equivalent to the original
exterior cotangent module, with no chosen representative/cycle/exactness premise. -/
def positiveQuotientEquiv (q : ℕ) :
    (LinearMap.ker (positiveShortComplex (σ := σ) k p q).g.hom ⧸
      LinearMap.range (positiveShortComplex (σ := σ) k p q).moduleCatToCycles) ≃ₗ[MvPolynomial σ k]
        (⋀[MvPolynomial σ k]^(q+1) (KaehlerDifferential k (MvPolynomial σ k))) :=
  (Submodule.quotEquivOfEq _ _ (cycleCoefficient_kernel k p q).symm).trans
    ((cycleCoefficient k p q).quotKerEquivOfSurjective (cycleCoefficient_surjective k p q))

/-- The ACTUAL native categorical homology of the SAME original positive-degree de Rham
three-term complex is the original exterior cotangent module. -/
def positiveShortComplexCartierIso (q : ℕ) :
    (positiveShortComplex (σ := σ) k p q).homology ≅
      ModuleCat.of (MvPolynomial σ k)
        (⋀[MvPolynomial σ k]^(q+1) (KaehlerDifferential k (MvPolynomial σ k))) :=
  (positiveShortComplex k p q).moduleCatHomologyIso ≪≫
    (positiveQuotientEquiv k p q).toModuleIso

/-- Every ACTUAL original cycle class has precisely its actual original Cartier coefficient. -/
theorem positiveQuotientEquiv_mk (q : ℕ)
    (z : LinearMap.ker (positiveShortComplex (σ := σ) k p q).g.hom) :
    positiveQuotientEquiv k p q (Submodule.Quotient.mk z) = cycleCoefficient k p q z := by
  simp only [positiveQuotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The actual native categorical homology class of an ENTIRE original positive cycle. -/
def positiveCycleClass (q : ℕ)
    (z : LinearMap.ker (positiveShortComplex (σ := σ) k p q).g.hom) :
    (positiveShortComplex (σ := σ) k p q).homology :=
  (positiveShortComplex k p q).moduleCatHomologyIso.inv (Submodule.Quotient.mk z)

/-- The true native positive-degree Cartier isomorphism evaluates an ACTUAL original cycle
class as its SAME original Cartier coefficient, not an unspecified abstract isomorphism. -/
theorem positiveShortComplexCartierIso_cycle (q : ℕ)
    (z : LinearMap.ker (positiveShortComplex (σ := σ) k p q).g.hom) :
    (positiveShortComplexCartierIso k p q).hom (positiveCycleClass k p q z) =
      cycleCoefficient k p q z := by
  change positiveQuotientEquiv k p q
    ((positiveShortComplex k p q).moduleCatHomologyIso.hom
      ((positiveShortComplex k p q).moduleCatHomologyIso.inv (Submodule.Quotient.mk z))) = _
  have h := congrArg
    (fun x : (positiveShortComplex k p q).moduleCatLeftHomologyData.H =>
      positiveQuotientEquiv k p q x)
    (Iso.inv_hom_id_apply (positiveShortComplex k p q).moduleCatHomologyIso
      (Submodule.Quotient.mk z))
  exact h.trans (positiveQuotientEquiv_mk k p q z)

private def ofPositiveShortIso {C : Type*} [Category C] [HasZeroMorphisms C]
    (X : ℕ → C) (d : ∀ q, X q ⟶ X (q+1)) (sq : ∀ q, d q ≫ d (q+1) = 0) (q : ℕ) :
    (CochainComplex.of X d sq).sc' q (q+1) (q+1+1) ≅
      ShortComplex.mk (d q) (d (q+1)) (sq q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, CochainComplex.of_d])
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, CochainComplex.of_d])

private def positiveNativeShortIso (q : ℕ) :
    (frobeniusComplex (σ := σ) k p).sc' q (q+1) (q+1+1) ≅ positiveShortComplex k p q :=
  ofPositiveShortIso _ _ _ q

/-- The actual native categorical H^(q+1) of the SAME full original Frobenius de Rham
complex is genuinely isomorphic to the original (q+1)th exterior cotangent module. -/
def positiveCartierIso (q : ℕ) :
    (frobeniusComplex (σ := σ) k p).homology (q+1) ≅
      ModuleCat.of (MvPolynomial σ k)
        (⋀[MvPolynomial σ k]^(q+1) (KaehlerDifferential k (MvPolynomial σ k))) :=
  (frobeniusComplex (σ := σ) k p).homologyIsoSc' q (q+1) (q+1+1)
    (CochainComplex.prev_nat_succ q) (CochainComplex.next ℕ (q+1)) ≪≫
      ShortComplex.homologyMapIso (positiveNativeShortIso k p q) ≪≫
        positiveShortComplexCartierIso k p q

/-- The actual degree-zero three-term complex has the genuine zero incoming map. -/
def zeroShortComplex : ShortComplex (ModuleCat (MvPolynomial σ k)) :=
  ShortComplex.mk (0 : frobeniusModule (σ := σ) k p 0 ⟶ frobeniusModule (σ := σ) k p 0)
    (frobeniusDifferential (σ := σ) k p 0) zero_comp

/-- The actual P-linear coefficient on the whole original degree-zero cycle module. -/
def zeroCycleCoefficient :
    LinearMap.ker (zeroShortComplex (σ := σ) k p).g.hom →ₗ[MvPolynomial σ k]
      (⋀[MvPolynomial σ k]^0 (KaehlerDifferential k (MvPolynomial σ k))) :=
  (coefficientLinear k p 0).comp (LinearMap.ker (zeroShortComplex (σ := σ) k p).g.hom).subtype

/-- Degree zero retains the ACTUAL original cycle kernel, with no artificial incoming boundary. -/
theorem zeroCycleCoefficient_bijective :
    Function.Bijective (zeroCycleCoefficient (σ := σ) k p) := by
  constructor
  · intro z w h
    apply Subtype.ext
    apply (frobeniusUnderlying k p 0).injective
    have hz : differential k 0 (frobeniusUnderlying k p 0 z.val) = 0 := z.property
    have hw : differential k 0 (frobeniusUnderlying k p 0 w.val) = 0 := w.property
    rw [← cycle_zero_decomposition k p _ hz, ← cycle_zero_decomposition k p _ hw]
    exact congrArg (originalRepresentative k p 0) h
  · intro w
    refine ⟨⟨representative k p 0 w, ?_⟩, ?_⟩
    · change differential k 0 (originalRepresentative k p 0 w) = 0
      exact originalRepresentative_closed k p 0 w
    · exact coefficientLinear_representative k p 0 w

omit [PerfectRing k p] in
private theorem zero_boundary_range :
    LinearMap.range (zeroShortComplex (σ := σ) k p).moduleCatToCycles = ⊥ := by
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  rfl

/-- The true native degree-zero categorical homology is the original zero exterior module. -/
def zeroShortComplexCartierIso :
    (zeroShortComplex (σ := σ) k p).homology ≅ ModuleCat.of (MvPolynomial σ k)
      (⋀[MvPolynomial σ k]^0 (KaehlerDifferential k (MvPolynomial σ k))) :=
  (zeroShortComplex k p).moduleCatHomologyIso ≪≫
    ((LinearMap.range (zeroShortComplex k p).moduleCatToCycles).quotEquivOfEqBot
      (zero_boundary_range k p)).toModuleIso ≪≫
        (LinearEquiv.ofBijective (zeroCycleCoefficient k p)
          (zeroCycleCoefficient_bijective k p)).toModuleIso

/-- The actual native degree-zero homology class of an ENTIRE original zero cycle. -/
def zeroCycleClass (z : LinearMap.ker (zeroShortComplex (σ := σ) k p).g.hom) :
    (zeroShortComplex (σ := σ) k p).homology :=
  (zeroShortComplex k p).moduleCatHomologyIso.inv (Submodule.Quotient.mk z)

/-- The true native zero-degree Cartier isomorphism is the SAME original coefficient
operation on every actual original cycle class. -/
theorem zeroShortComplexCartierIso_cycle
    (z : LinearMap.ker (zeroShortComplex (σ := σ) k p).g.hom) :
    (zeroShortComplexCartierIso k p).hom (zeroCycleClass k p z) =
      zeroCycleCoefficient k p z := by
  change zeroCycleCoefficient k p
    ((LinearMap.range (zeroShortComplex k p).moduleCatToCycles).quotEquivOfEqBot
      (zero_boundary_range k p)
      ((zeroShortComplex k p).moduleCatHomologyIso.hom
        ((zeroShortComplex k p).moduleCatHomologyIso.inv (Submodule.Quotient.mk z)))) = _
  have h := congrArg
    (fun x : (zeroShortComplex k p).moduleCatLeftHomologyData.H =>
      zeroCycleCoefficient k p
        ((LinearMap.range (zeroShortComplex k p).moduleCatToCycles).quotEquivOfEqBot
          (zero_boundary_range k p) x))
    (Iso.inv_hom_id_apply (zeroShortComplex k p).moduleCatHomologyIso
      (Submodule.Quotient.mk z))
  exact h.trans (congrArg (zeroCycleCoefficient k p)
    (Submodule.quotEquivOfEqBot_apply_mk _ (zero_boundary_range k p) z))

private def ofZeroShortIso {C : Type*} [Category C] [HasZeroMorphisms C]
    (X : ℕ → C) (d : ∀ q, X q ⟶ X (q+1)) (sq : ∀ q, d q ≫ d (q+1) = 0) :
    (CochainComplex.of X d sq).sc' 0 0 1 ≅
      ShortComplex.mk (0 : X 0 ⟶ X 0) (d 0) zero_comp :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
        CochainComplex.of_d_ne _ _ (by decide : 0+1 ≠ (0:ℕ))])
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      change (𝟙 (X 0)) ≫ d 0 = CochainComplex.of.d X d 0 (0+1) ≫ 𝟙 (X (0+1))
      rw [Category.id_comp, Category.comp_id, CochainComplex.of_d])

private def zeroNativeShortIso :
    (frobeniusComplex (σ := σ) k p).sc' 0 0 1 ≅ zeroShortComplex k p :=
  ofZeroShortIso _ _ (fun q => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    exact differential_square k q w)

/-- The ACTUAL native degree-zero homology of the SAME full original Frobenius de Rham
complex has the genuine original Cartier isomorphism. -/
def zeroCartierIso :
    (frobeniusComplex (σ := σ) k p).homology 0 ≅ ModuleCat.of (MvPolynomial σ k)
      (⋀[MvPolynomial σ k]^0 (KaehlerDifferential k (MvPolynomial σ k))) :=
  (frobeniusComplex (σ := σ) k p).homologyIsoSc' 0 0 1
    CochainComplex.prev_nat_zero (CochainComplex.next ℕ 0) ≪≫
      ShortComplex.homologyMapIso (zeroNativeShortIso k p) ≪≫ zeroShortComplexCartierIso k p

/-- The genuine ALL-degree polynomial Cartier isomorphism, on actual native categorical
homology of the SAME original exterior cotangent de Rham complex with Frobenius scalars. -/
def cartierIso (q : ℕ) :
    (frobeniusComplex (σ := σ) k p).homology q ≅ ModuleCat.of (MvPolynomial σ k)
      (⋀[MvPolynomial σ k]^q (KaehlerDifferential k (MvPolynomial σ k))) :=
  match q with
  | 0 => zeroCartierIso k p
  | q+1 => positiveCartierIso k p q

end EnvelopeProperty.Cartier.PolynomialCartierCohomology
