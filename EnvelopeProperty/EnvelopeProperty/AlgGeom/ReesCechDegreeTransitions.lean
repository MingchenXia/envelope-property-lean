import EnvelopeProperty.AlgGeom.ReesCechHomogeneousMultiplication
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # Literal original ideal-power transitions in actual Rees Cech cohomology -/

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FcReesCechDegreeTransitions

open FcReesCechDegreeComplex FcReesFormalRestriction

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
variable [X.IsSeparated] {ι : Type u} [LinearOrder ι] [Fintype ι]
variable (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))

/-- Lower the original ideal-power membership on EVERY original affine
intersection, keeping the ENTIRE original underlying section. -/
def termLower {n m : ℕ} (h : n ≤ m) (q : ℕ) :
    degreeTerm I f U hU m q ⟶ degreeTerm I f U hU n q := by
  let : ∀ i : OrderedCechIndex ι q,
      Algebra R Γ(X, ∏ᶜ fun j : Fin (q + 1) => U (i.1 j)) :=
    fun i => chartAlgebra f (IsAffineOpen.cechIntersection U hU q i.1)
  exact ModuleCat.ofHom {
    toFun := fun x i => ⟨(x i).1, Ideal.pow_le_pow_right h (x i).2⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

omit [Fintype ι] in
/-- EVERY entire original ordered coface commutes with the actual
higher-to-lower ideal-power inclusion. -/
theorem termLower_coface {n m : ℕ} (h : n ≤ m) (q : ℕ) (k : Fin (q + 2)) :
    termLower I f U hU h q ≫ degreeCoface I f U hU n q k =
      degreeCoface I f U hU m q k ≫ termLower I f U hU h (q + 1) := by
  let : ∀ i : OrderedCechIndex ι q,
      Algebra R Γ(X, ∏ᶜ fun j : Fin (q + 1) => U (i.1 j)) :=
    fun i => chartAlgebra f (IsAffineOpen.cechIntersection U hU q i.1)
  let : ∀ i : OrderedCechIndex ι (q + 1),
      Algebra R Γ(X, ∏ᶜ fun j : Fin (q + 2) => U (i.1 j)) :=
    fun i => chartAlgebra f (IsAffineOpen.cechIntersection U hU (q + 1) i.1)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  apply Subtype.ext
  rfl

omit [Fintype ι] in
/-- The WHOLE actual original alternating differential retains the
original higher-to-lower ideal-power inclusion. -/
theorem termLower_differential {n m : ℕ} (h : n ≤ m) (q : ℕ) :
    termLower I f U hU h q ≫ degreeDifferential I f U hU n q =
      degreeDifferential I f U hU m q ≫ termLower I f U hU h (q + 1) := by
  simp only [degreeDifferential, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun a => ((-1 : ℤ) ^ (k : ℕ)) • a) (termLower_coface I f U hU h q k)

/-- The actual literal cochain transition between the SAME original
ideal-power complexes, without changing any original section. -/
def degreeLower {n m : ℕ} (h : n ≤ m) :
    degreeComplex I f U hU m ⟶ degreeComplex I f U hU n where
  f q := termLower I f U hU h q
  comm' q r hqr := by
    have hr : q + 1 = r := hqr
    subst r
    simp only [degreeComplex, CochainComplex.of_d]
    exact termLower_differential I f U hU h q

/-- The actual original equal-power cochain transition is the WHOLE identity. -/
theorem degreeLower_self (n : ℕ) : degreeLower I f U hU (le_refl n) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- ALL original higher-to-lower cochain transitions compose literally. -/
theorem degreeLower_comp {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) :
    degreeLower I f U hU hmk ≫ degreeLower I f U hU hnm =
      degreeLower I f U hU (hnm.trans hmk) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Genuine homogeneous multiplication followed by the original lower
power inclusion is EXACTLY the original coefficient times the original transition. -/
theorem degreeMultiply_lower {e : ℕ} (a : ↥(I ^ e)) {n m : ℕ} (h : n ≤ m) :
    FcReesCechHomogeneousMultiplication.degreeMultiply I f U hU a m ≫
        degreeLower I f U hU (h.trans (Nat.le_add_left m e)) =
      (a : R) • degreeLower I f U hU h := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  apply Subtype.ext
  rfl

/-- The genuine cohomology transition between EVERY pair of original ideal powers. -/
def homologyLower {n m : ℕ} (h : n ≤ m) (q : ℕ) :
    (degreeComplex I f U hU m).homology q ⟶ (degreeComplex I f U hU n).homology q :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
    (degreeLower I f U hU h)

/-- The actual original equal-power cohomology transition is the WHOLE identity. -/
theorem homologyLower_self (n q : ℕ) : homologyLower I f U hU (le_refl n) q = 𝟙 _ := by
  exact (congrArg (fun b =>
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map b)
      (degreeLower_self I f U hU n)).trans (CategoryTheory.Functor.map_id _ _)

/-- ALL original higher-to-lower cohomology transitions compose literally. -/
theorem homologyLower_comp {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) (q : ℕ) :
    homologyLower I f U hU hmk q ≫ homologyLower I f U hU hnm q =
      homologyLower I f U hU (hnm.trans hmk) q :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map_comp _ _).symm.trans
    (congrArg (fun b =>
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map b)
        (degreeLower_comp I f U hU hnm hmk))

/-- The ENTIRE actual cohomology multiplication-lowering square gives
the literal SAME original coefficient times the original cohomology transition. -/
theorem homologyMultiply_lower {e : ℕ} (a : ↥(I ^ e)) {n m : ℕ} (h : n ≤ m) (q : ℕ) :
    FcReesCechHomogeneousMultiplication.homologyMultiply I f U hU a m q ≫
        homologyLower I f U hU (h.trans (Nat.le_add_left m e)) q =
      (a : R) • homologyLower I f U hU h q := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  let S := HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) q
  have hs : S.map ((a : R) • degreeLower I f U hU h) =
      (a : R) • S.map (degreeLower I f U hU h) := by
    apply ShortComplex.Hom.ext <;> rfl
  have hmap : H.map ((a : R) • degreeLower I f U hU h) =
      (a : R) • H.map (degreeLower I f U hU h) := by
    change ShortComplex.homologyMap (S.map ((a : R) • degreeLower I f U hU h)) =
      (a : R) • ShortComplex.homologyMap (S.map (degreeLower I f U hU h))
    rw [hs]
    exact ShortComplex.homologyMap_smul _ _
  exact (H.map_comp _ _).symm.trans
    ((congrArg (fun b => H.map b) (degreeMultiply_lower I f U hU a h)).trans hmap)

end EnvelopeProperty.FcReesCechDegreeTransitions
