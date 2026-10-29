import EnvelopeProperty.AlgGeom.ProjectiveCoordinateCommutativity
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-! # An actual augmented resolution by coordinate tuples

The alternating cancellation adapts the native ordered-Cech argument. Allowing
all tuples permits the local contraction to prepend an invertible coordinate,
without a sorting argument. The actual projective application derives every
commuting square and inverse from the original coordinate maps.
-/
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open scoped ZeroObject
noncomputable section
universe u v
namespace EnvelopeProperty.CoordinateTupleComplex

private def delete {ι : Type} {n : ℕ} (x : Fin (n + 1) → ι) (k : Fin (n + 1)) : Fin n → ι :=
  x ∘ k.succAbove

private theorem delete_delete {ι : Type} {n : ℕ} (x : Fin (n + 2) → ι)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    delete (delete x j.succ) i = delete (delete x i.castSucc) j := by
  cases n with
  | zero => funext a; exact Fin.elim0 a
  | succ n =>
    funext a
    exact congrArg x (ConcreteCategory.congr_hom (SimplexCategory.δ_comp_δ hij) a)

private theorem delete_cons_zero {ι : Type} {n : ℕ} (h : ι) (x : Fin n → ι) :
    delete (Fin.cons h x) 0 = x := by
  funext i
  rfl

private theorem delete_cons_succ {ι : Type} {n : ℕ} (h : ι)
    (x : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    delete (Fin.cons h x) k.succ = Fin.cons h (delete x k) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [delete]
  · simp only [delete, Function.comp_apply, Fin.succ_succAbove_succ, Fin.cons_succ]

section Graded
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
    {ι : Type} [Finite ι] (A : ℕ → C) (c : ∀ n, ι → (A (n + 1) ⟶ A n))

private abbrev tupleObject (n : ℕ) : C := ∐ fun _ : Fin n → ι => A n

private def tupleCoface (n : ℕ) (k : Fin (n + 1)) :
    tupleObject (ι := ι) A (n + 1) ⟶ tupleObject (ι := ι) A n :=
  Sigma.desc fun x : Fin (n + 1) → ι => c n (x k) ≫
    Sigma.ι (fun _ : Fin n → ι => A n) (delete x k)

omit [Preadditive C] in
@[reassoc]
private theorem ι_tupleCoface (n : ℕ) (k : Fin (n + 1)) (x : Fin (n + 1) → ι) :
    Sigma.ι (fun _ : Fin (n + 1) → ι => A (n + 1)) x ≫ tupleCoface A c n k =
      c n (x k) ≫ Sigma.ι (fun _ : Fin n → ι => A n) (delete x k) :=
  Sigma.ι_desc _ x

omit [Preadditive C] in
private theorem tupleCoface_comp
    (hc : ∀ n i j, c (n + 1) i ≫ c n j = c (n + 1) j ≫ c n i)
    (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    tupleCoface A c (n + 1) j.succ ≫ tupleCoface A c n i =
      tupleCoface A c (n + 1) i.castSucc ≫ tupleCoface A c n j := by
  apply colimit.hom_ext
  intro x
  obtain ⟨x⟩ := x
  simp only [ι_tupleCoface, ι_tupleCoface_assoc]
  have hleft : delete x j.succ i = x i.castSucc := by
    change x (j.succ.succAbove i) = _
    rw [Fin.succAbove_succ_of_le _ _ hij]
  have hright : delete x i.castSucc j = x j.succ := by
    change x (i.castSucc.succAbove j) = _
    rw [Fin.succAbove_castSucc_of_le _ _ hij]
  rw [hleft, hright, delete_delete x hij, ← Category.assoc, hc, Category.assoc]

omit [Preadditive C] in
private theorem tupleCoface_comp'
    (hc : ∀ n i j, c (n + 1) i ≫ c n j = c (n + 1) j ≫ c n i)
    (n : ℕ) {i : Fin (n + 2)} {j : Fin (n + 1)} (hij : i ≤ j.castSucc) :
    tupleCoface A c (n + 1) j.succ ≫
        tupleCoface A c n (i.castLT (lt_of_le_of_lt hij j.is_lt)) =
      tupleCoface A c (n + 1) i ≫ tupleCoface A c n j := by
  have hle : i.castLT (lt_of_le_of_lt hij j.is_lt) ≤ j := by
    rw [Fin.le_iff_val_le_val] at hij ⊢
    exact hij
  simpa using tupleCoface_comp A c hc n hle

private def tupleDifferential (n : ℕ) :
    tupleObject (ι := ι) A (n + 1) ⟶ tupleObject (ι := ι) A n :=
  ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • tupleCoface A c n k

private theorem tupleDifferential_comp
    (hc : ∀ n i j, c (n + 1) i ≫ c n j = c (n + 1) j ≫ c n i) (n : ℕ) :
    tupleDifferential A c (n + 1) ≫ tupleDifferential A c n = 0 := by
  dsimp [tupleDifferential]
  rw [sum_comp]
  simp only [comp_sum, ← Finset.sum_product']
  let P := Fin (n + 2) × Fin (n + 1)
  let T : Finset P := {ij : P | (ij.1 : ℕ) ≤ (ij.2 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl T,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ T → P := fun ij hij =>
    (ij.2.succ, Fin.castLT ij.1
      (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.2)))
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [T, φ, Finset.compl_filter, Finset.mem_filter_univ,
      Fin.val_succ, Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.snd h),
      by simpa [φ] using! congr_arg Prod.fst h⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [T, Finset.compl_filter, Finset.mem_filter_univ,
      not_le] at hij'
    refine ⟨(Fin.castSucc j', i'.pred (by
      rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij')), ?_, ?_⟩
    · simpa [T] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.succ_pred, Fin.castLT_castSucc]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, Fin.val_castLT, pow_add, pow_one,
        mul_neg, neg_neg, mul_one]
      apply mul_comm
    · rw [tupleCoface_comp' A c hc n]
      simpa [T] using! hij


private theorem ι_tupleAugmentation_zero (x : Fin 1 → ι) :
    Sigma.ι (fun _ : Fin 1 → ι => A 1) x ≫ tupleDifferential A c 0 ≫
        (coproductUniqueIso (fun _ : Fin 0 → ι => A 0)).hom = c 0 (x 0) := by
  simp only [tupleDifferential, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.val_zero, pow_zero, one_smul]
  rw [← Category.assoc, ι_tupleCoface, Category.assoc, ι_coproductUniqueIso_hom]
  simp only [eqToHom_refl, Category.comp_id]

private def tupleChainComplex
    (hc : ∀ n i j, c (n + 1) i ≫ c n j = c (n + 1) j ≫ c n i) :
    ChainComplex C ℕ :=
  ChainComplex.of (tupleObject (ι := ι) A) (tupleDifferential A c)
    (tupleDifferential_comp A c hc)

variable (h : ι) [∀ n, IsIso (c n h)]

omit [Preadditive C] [HasFiniteCoproducts C] [Finite ι] in
private theorem inverse_coordinate_comm
    (hc : ∀ n i j, c (n + 1) i ≫ c n j = c (n + 1) j ≫ c n i) (n : ℕ) (i : ι) :
    inv (c (n + 1) h) ≫ c (n + 1) i = c n i ≫ inv (c n h) := by
  apply (cancel_epi (c (n + 1) h)).mp
  apply (cancel_mono (c n h)).mp
  simpa only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id,
    Category.comp_id] using hc n i h

private def tupleHomotopy (n : ℕ) :
    tupleObject (ι := ι) A n ⟶ tupleObject (ι := ι) A (n + 1) :=
  Sigma.desc fun x : Fin n → ι => inv (c n h) ≫
    Sigma.ι (fun _ : Fin (n + 1) → ι => A (n + 1)) (Fin.cons h x)

omit [Preadditive C] in
@[reassoc]
private theorem ι_tupleHomotopy (n : ℕ) (x : Fin n → ι) :
    Sigma.ι (fun _ : Fin n → ι => A n) x ≫ tupleHomotopy A c h n =
      inv (c n h) ≫ Sigma.ι (fun _ : Fin (n + 1) → ι => A (n + 1)) (Fin.cons h x) :=
  Sigma.ι_desc _ x

private theorem tupleHomotopy_differential_zero :
    tupleHomotopy A c h 0 ≫ tupleDifferential A c 0 = 𝟙 _ := by
  apply colimit.hom_ext
  intro x
  obtain ⟨x⟩ := x
  simp only [tupleDifferential, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.val_zero, pow_zero, one_smul, Category.comp_id]
  rw [← Category.assoc, ι_tupleHomotopy, Category.assoc, ι_tupleCoface]
  simp only [Fin.cons_zero, delete_cons_zero, IsIso.inv_hom_id_assoc]

private theorem tupleHomotopy_differential_succ
    (hc : ∀ n i j, c (n + 1) i ≫ c n j = c (n + 1) j ≫ c n i) (n : ℕ) :
    tupleHomotopy A c h (n + 1) ≫ tupleDifferential A c (n + 1) =
      𝟙 _ - tupleDifferential A c n ≫ tupleHomotopy A c h n := by
  apply colimit.hom_ext
  intro x
  obtain ⟨x⟩ := x
  simp only [comp_sub, Category.comp_id]
  rw [← Category.assoc, ι_tupleHomotopy]
  simp only [tupleDifferential, comp_sum, sum_comp, zsmul_comp, comp_zsmul,
    Category.assoc, ι_tupleCoface, ι_tupleCoface_assoc]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, delete_cons_zero,
    IsIso.inv_hom_id_assoc, Fin.cons_succ, Fin.val_succ, delete_cons_succ,
    pow_succ, mul_neg_one, neg_smul]
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [← Category.assoc, inverse_coordinate_comm A c h hc n (x k), Category.assoc, ι_tupleHomotopy]

omit [HasFiniteCoproducts C] in
private theorem exact_of_contraction {S : ShortComplex C} [S.HasHomology]
    [HasKernel S.g] [HasCokernel S.f]
    (r : S.X₂ ⟶ S.X₁) (s : S.X₃ ⟶ S.X₂) (h : r ≫ S.f + S.g ≫ s = 𝟙 _) :
    S.Exact := by
  rw [S.exact_iff_kernel_ι_comp_cokernel_π_zero]
  have hh := congrArg (fun f => kernel.ι S.g ≫ f ≫ cokernel.π S.f) h
  simpa only [comp_add, add_comp, Category.assoc, cokernel.condition, comp_zero,
    kernel.condition_assoc, zero_comp, add_zero, zero_add, Category.id_comp] using hh.symm

end Graded
section Exact
variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteCoproducts C]
    {ι : Type} [Finite ι] (A : ℕ → C) (c : ∀ n, ι → (A (n + 1) ⟶ A n))
private theorem tuple_exact (h : ι) [∀ n, IsIso (c n h)]
    (hc : ∀ n i j, c (n + 1) i ≫ c n j = c (n + 1) j ≫ c n i) (n : ℕ) :
    (ShortComplex.mk (tupleDifferential A c (n + 1)) (tupleDifferential A c n)
      (tupleDifferential_comp A c hc n)).Exact := by
  apply exact_of_contraction (tupleHomotopy A c h (n + 1)) (tupleHomotopy A c h n)
  change tupleHomotopy A c h (n + 1) ≫ tupleDifferential A c (n + 1) +
    tupleDifferential A c n ≫ tupleHomotopy A c h n = _
  rw [tupleHomotopy_differential_succ A c h hc n, sub_add_cancel]

end Exact
section Mapping
variable {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type*} [Category D] [Abelian D]
    {ι : Type} [Finite ι] (A : ℕ → C) (c : ∀ n, ι → (A (n + 1) ⟶ A n))
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]

omit [PreservesFiniteColimits F] in
private theorem comparison_differential (n : ℕ) :
    sigmaComparison F (fun _ : Fin (n + 1) → ι => A (n + 1)) ≫
        F.map (tupleDifferential A c n) =
      tupleDifferential (fun n => F.obj (A n)) (fun n i => F.map (c n i)) n ≫
        sigmaComparison F (fun _ : Fin n → ι => A n) := by
  simp only [tupleDifferential, F.map_sum, F.map_zsmul, comp_sum, sum_comp,
    comp_zsmul, zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply colimit.hom_ext
  intro x
  obtain ⟨x⟩ := x
  rw [← Category.assoc, ι_comp_sigmaComparison, ← F.map_comp, ι_tupleCoface, F.map_comp]
  calc
    _ = (F.map (c n (x k)) ≫
        Sigma.ι (fun _ : Fin n → ι => F.obj (A n)) (delete x k)) ≫
          sigmaComparison F (fun _ : Fin n → ι => A n) := by
      rw [Category.assoc, ι_comp_sigmaComparison]
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ sigmaComparison F (fun _ : Fin n → ι => A n))
          (ι_tupleCoface (fun n => F.obj (A n)) (fun n i => F.map (c n i)) n k x).symm

private theorem mapped_tuple_exact (h : ι) [hiso : ∀ n, IsIso (F.map (c n h))]
    (hc : ∀ n i j, c (n + 1) i ≫ c n j = c (n + 1) j ≫ c n i) (n : ℕ) :
    ((ShortComplex.mk (tupleDifferential A c (n + 1)) (tupleDifferential A c n)
      (tupleDifferential_comp A c hc n)).map F).Exact := by
  have hm : ∀ n i j, F.map (c (n + 1) i) ≫ F.map (c n j) =
      F.map (c (n + 1) j) ≫ F.map (c n i) := by
    intro n i j
    rw [← F.map_comp, ← F.map_comp, hc]
  let S := ShortComplex.mk
    (tupleDifferential (fun n => F.obj (A n)) (fun n i => F.map (c n i)) (n + 1))
    (tupleDifferential (fun n => F.obj (A n)) (fun n i => F.map (c n i)) n)
    (tupleDifferential_comp _ _ hm n)
  let e (r : ℕ) := (PreservesCoproduct.iso F (fun _ : Fin r → ι => A r)).symm
  have he (r : ℕ) : (e (r + 1)).hom ≫ F.map (tupleDifferential A c r) =
      tupleDifferential (fun n => F.obj (A n)) (fun n i => F.map (c n i)) r ≫ (e r).hom :=
    comparison_differential A c F r
  exact ShortComplex.exact_of_iso
    (ShortComplex.isoMk (S₁ := S) (e (n + 2)) (e (n + 1)) (e n) (he (n + 1)) (he n))
    (tuple_exact (fun n => F.obj (A n)) (fun n i => F.map (c n i)) h hm n)

private theorem mapped_tuple_differential_epi (h : ι)
    [hiso : ∀ n, IsIso (F.map (c n h))] : Epi (F.map (tupleDifferential A c 0)) := by
  let B := fun n => F.obj (A n)
  let m := fun n i => F.map (c n i)
  have : Epi (tupleDifferential B m 0) :=
    epi_of_epi_fac (tupleHomotopy_differential_zero B m h)
  have : Epi (sigmaComparison F (fun _ : Fin 1 → ι => A 1) ≫
      F.map (tupleDifferential A c 0)) := by
    rw [comparison_differential]
    infer_instance
  exact epi_of_epi (sigmaComparison F (fun _ : Fin 1 → ι => A 1)) _

end Mapping

section Lowering
variable {C : Type u} [Category.{v} C] {ι : Type}
    (P : ℤ → C) (m : ∀ a, ι → (P a ⟶ P (a + 1)))

private theorem step_transport {a b : ℤ} (e : a = b) (i : ι) :
    eqToHom (congrArg P e) ≫ m b i =
      m a i ≫ eqToHom (congrArg P (congrArg (fun z : ℤ => z + 1) e)) := by
  subst b
  simp

private def lowerMap (a : ℤ) (i : ι) : P (a - 1) ⟶ P a :=
  m (a - 1) i ≫ eqToHom (congrArg P (sub_add_cancel a 1))

private theorem lowerMap_comp
    (hm : ∀ a i j, m a i ≫ m (a + 1) j = m a j ≫ m (a + 1) i)
    (a : ℤ) (i j : ι) :
    lowerMap P m (a - 1) i ≫ lowerMap P m a j =
      lowerMap P m (a - 1) j ≫ lowerMap P m a i := by
  let e : a - 1 - 1 + 1 = a - 1 := sub_add_cancel (a - 1) 1
  have ht (k : ι) := step_transport P m e k
  dsimp only [lowerMap]
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom (congrArg P e)) (m (a - 1) j), ht j,
    ← Category.assoc (eqToHom (congrArg P e)) (m (a - 1) i), ht i]
  simpa only [Category.assoc] using congrArg (fun f => f ≫
      eqToHom (congrArg P (congrArg (fun z : ℤ => z + 1) e)) ≫
        eqToHom (congrArg P (sub_add_cancel a 1))) (hm (a - 1 - 1) i j)

end Lowering

private theorem restrict_preservesFiniteLimits {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (restrictFunctor U.ι) := by
  let K := (Functor.whiskeringLeft U.toScheme.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
    U.ι.opensFunctor.op
  have : PreservesFiniteLimits K := by dsimp only [K]; infer_instance
  have : PreservesFiniteLimits (restrictFunctor U.ι ⋙ toPresheaf U.toScheme) := by
    change PreservesFiniteLimits (toPresheaf X ⋙ K)
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves _ (toPresheaf U.toScheme)

private theorem scheme_exact_of_restrict_exact {X : Scheme.{u}} {I : Type*}
    (U : I → X.Opens) (hU : ⨆ i, U i = ⊤) (S : ShortComplex X.Modules)
    (hS : ∀ i, (S.map (restrictFunctor (U i).ι)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology]
  have hz (i : I) : IsZero ((restrictFunctor (U i).ι).obj S.homology) := by
    let F := restrictFunctor (U i).ι
    have : PreservesFiniteLimits F := restrict_preservesFiniteLimits (U i)
    have : PreservesFiniteColimits F := inferInstance
    exact IsZero.of_iso ((S.map F).exact_iff_isZero_homology.mp (hS i)) (S.mapHomologyIso F).symm
  let : Epi (0 : (0 : X.Modules) ⟶ S.homology) :=
    epi_of_restrictFunctor_map_epi_of_iSup_eq_top U hU _ (fun i => (hz i).epi _)
  exact IsZero.of_epi_zero (0 : X.Modules) S.homology

open CategoryTheory.MonoidalCategory MvPolynomial
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {σ : Type}

/-- Recursive descending degree for the coordinate tuple resolution. -/
def tupleTwistDegree (t : ℤ) : ℕ → ℤ
  | 0 => t
  | n + 1 => tupleTwistDegree t n - 1

/-- The recursive tuple degree is the ordinary integer twist index. -/
theorem tupleTwistDegree_eq (t : ℤ) (n : ℕ) : tupleTwistDegree t n = t - (n : ℤ) := by
  induction n with
  | zero => simp [tupleTwistDegree]
  | succ n ih => simp [tupleTwistDegree, ih, Nat.cast_add, sub_sub]

/-- Original coordinate multiplication from twist a−1 to twist a, with the canonical target-degree transport. -/
def coordinateLowerMul (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j i : σ) (a : ℤ) :
    M ⊗ coordinateHyperplaneTwist (R := R) j (a - 1) ⟶
      M ⊗ coordinateHyperplaneTwist (R := R) j a :=
  lowerMap (fun a => M ⊗ coordinateHyperplaneTwist (R := R) j a)
    (fun a i => ProjectiveCoordinateMultiplication.moduleCoordinateMul M j i a) a i

private theorem coordinateLowerMul_comm (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j i k : σ) (a : ℤ) :
    coordinateLowerMul M j i (a - 1) ≫ coordinateLowerMul M j k a =
      coordinateLowerMul M j k (a - 1) ≫ coordinateLowerMul M j i a :=
  lowerMap_comp (fun a => M ⊗ coordinateHyperplaneTwist (R := R) j a)
    (fun a i => ProjectiveCoordinateMultiplication.moduleCoordinateMul M j i a)
    (fun a i k => ProjectiveCoordinateCommutativity.moduleCoordinateMul_comm M j i k a) a i k

private theorem coordinateLowerMul_isIso_on_own_chart
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (j i : σ) (a : ℤ) :
    IsIso ((restrictFunctor (coordinateOpen (R := R) i).ι).map (coordinateLowerMul M j i a)) := by
  let F := restrictFunctor (coordinateOpen (R := R) i).ι
  let := ProjectiveCoordinateMultiplication.moduleCoordinateMul_isIso_on_own_chart M j i (a - 1)
  dsimp only [coordinateLowerMul, lowerMap]
  rw [F.map_comp]
  infer_instance

/-- The actual chain complex indexed by all coordinate tuples, allowing repetitions. -/
def coordinateTupleComplex {ι : Type} [Finite ι]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) (c : ι → σ) (t : ℤ) :
    ChainComplex (Proj (homogeneousSubmodule σ R)).Modules ℕ :=
  tupleChainComplex (fun n => M ⊗ coordinateHyperplaneTwist (R := R) j (tupleTwistDegree t n))
    (fun n i => coordinateLowerMul M j (c i) (tupleTwistDegree t n))
    (fun n i k => coordinateLowerMul_comm M j (c i) (c k) (tupleTwistDegree t n))

/-- The actual original-coordinate tuple complex is exact at every positive degree, without flatness or quasicoherence. -/
theorem coordinateTupleComplex_exact [Finite σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) (t : ℤ) (n : ℕ) :
    (ShortComplex.mk ((coordinateTupleComplex M j id t).d (n + 2) (n + 1))
      ((coordinateTupleComplex M j id t).d (n + 1) n)
      ((coordinateTupleComplex M j id t).d_comp_d (n + 2) (n + 1) n)).Exact := by
  change (ShortComplex.mk ((coordinateTupleComplex M j id t).d (n + 1 + 1) (n + 1))
    ((coordinateTupleComplex M j id t).d (n + 1) n)
    ((coordinateTupleComplex M j id t).d_comp_d (n + 1 + 1) (n + 1) n)).Exact
  simp only [coordinateTupleComplex, tupleChainComplex, ChainComplex.of_d]
  apply scheme_exact_of_restrict_exact (coordinateOpen (R := R))
    (iSup_coordinateOpen_eq_top (R := R))
  intro h
  let F := restrictFunctor (coordinateOpen (R := R) h).ι
  let : F.Additive := Functor.additive_of_iso
    (restrictFunctorIsoPullback (coordinateOpen (R := R) h).ι).symm
  exact mapped_tuple_exact
    (fun r => M ⊗ coordinateHyperplaneTwist (R := R) j (tupleTwistDegree t r))
    (fun r i => coordinateLowerMul M j i (tupleTwistDegree t r)) F h
    (fun r i k => coordinateLowerMul_comm M j i k (tupleTwistDegree t r)) n
    (hiso := fun r => coordinateLowerMul_isIso_on_own_chart M j h (tupleTwistDegree t r))

private theorem coordinateTupleComplex_epi [Finite σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) (t : ℤ) :
    Epi ((coordinateTupleComplex M j id t).d 1 0) := by
  simp only [coordinateTupleComplex, tupleChainComplex]
  apply epi_of_restrictFunctor_map_epi_of_iSup_eq_top (coordinateOpen (R := R))
    (iSup_coordinateOpen_eq_top (R := R))
  intro h
  let F := restrictFunctor (coordinateOpen (R := R) h).ι
  let : F.Additive := Functor.additive_of_iso
    (restrictFunctorIsoPullback (coordinateOpen (R := R) h).ι).symm
  exact mapped_tuple_differential_epi
    (fun r => M ⊗ coordinateHyperplaneTwist (R := R) j (tupleTwistDegree t r))
    (fun r i => coordinateLowerMul M j i (tupleTwistDegree t r)) F h
    (hiso := fun r => coordinateLowerMul_isIso_on_own_chart M j h (tupleTwistDegree t r))

/-- The tuple-resolution terms are actual finite sums of the original twists. -/
def coordinateTupleTermIso {ι : Type} [Finite ι]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) (c : ι → σ) (t : ℤ) (r : ℕ) :
    (coordinateTupleComplex M j c t).X r ≅
      ∐ fun _ : Fin r → ι => M ⊗ coordinateHyperplaneTwist (R := R) j (t - (r : ℤ)) :=
  eqToIso (congrArg (fun a : ℤ => ∐ fun _ : Fin r → ι =>
    M ⊗ coordinateHyperplaneTwist (R := R) j a) (tupleTwistDegree_eq t r))

/-- The unique empty tuple gives the literal original augmentation target. -/
def coordinateTupleAugmentIso {ι : Type} [Finite ι]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) (c : ι → σ) (t : ℤ) :
    (coordinateTupleComplex M j c t).X 0 ≅ M ⊗ coordinateHyperplaneTwist (R := R) j t :=
  coproductUniqueIso (fun _ : Fin 0 → ι => M ⊗ coordinateHyperplaneTwist (R := R) j t)

/-- The actual tuple augmentation into the original module twist. -/
def coordinateTupleAugmentation {ι : Type} [Finite ι]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) (c : ι → σ) (t : ℤ) :
    (coordinateTupleComplex M j c t).X 1 ⟶ M ⊗ coordinateHyperplaneTwist (R := R) j t :=
  (coordinateTupleComplex M j c t).d 1 0 ≫ (coordinateTupleAugmentIso M j c t).hom

/-- On each genuine tuple summand, the differential deletes a position and
multiplies by its original coordinate, with the ordered alternating sign. -/
theorem coordinateTupleComplex_ι_d {ι : Type} [Finite ι]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) (c : ι → σ) (t : ℤ)
    (r : ℕ) (x : Fin (r + 1) → ι) :
    Sigma.ι (fun _ : Fin (r + 1) → ι =>
        M ⊗ coordinateHyperplaneTwist (R := R) j (tupleTwistDegree t (r + 1))) x ≫
      (coordinateTupleComplex M j c t).d (r + 1) r =
    ∑ k : Fin (r + 1), (-1 : ℤ) ^ (k : ℕ) •
      (coordinateLowerMul M j (c (x k)) (tupleTwistDegree t r) ≫
        Sigma.ι (fun _ : Fin r → ι =>
          M ⊗ coordinateHyperplaneTwist (R := R) j (tupleTwistDegree t r)) (x ∘ k.succAbove)) := by
  simp only [coordinateTupleComplex, tupleChainComplex, ChainComplex.of_d,
    tupleDifferential, comp_sum, comp_zsmul]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun f => (-1 : ℤ) ^ (k : ℕ) • f)
    (ι_tupleCoface
      (fun r => M ⊗ coordinateHyperplaneTwist (R := R) j (tupleTwistDegree t r))
      (fun r i => coordinateLowerMul M j (c i) (tupleTwistDegree t r)) r k x)

/-- Each augmentation summand is precisely the original coordinate multiplication,
with its canonical target-degree identification. -/
theorem coordinateTupleAugmentation_ι {ι : Type} [Finite ι]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) (c : ι → σ) (t : ℤ)
    (x : Fin 1 → ι) :
    Sigma.ι (fun _ : Fin 1 → ι => M ⊗ coordinateHyperplaneTwist (R := R) j (t - 1)) x ≫
      coordinateTupleAugmentation M j c t = coordinateLowerMul M j (c (x 0)) t := by
  exact ι_tupleAugmentation_zero
    (fun r => M ⊗ coordinateHyperplaneTwist (R := R) j (tupleTwistDegree t r))
    (fun r i => coordinateLowerMul M j (c i) (tupleTwistDegree t r)) x

/-- The genuine original coordinate tuple augmentation is a sheaf epimorphism. -/
theorem coordinateTupleAugmentation_epi [Finite σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) (t : ℤ) :
    Epi (coordinateTupleAugmentation M j id t) := by
  let := coordinateTupleComplex_epi M j t
  dsimp only [coordinateTupleAugmentation]
  infer_instance

end EnvelopeProperty.CoordinateTupleComplex
