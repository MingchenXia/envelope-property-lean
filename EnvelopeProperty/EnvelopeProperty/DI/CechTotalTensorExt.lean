import EnvelopeProperty.DI.CechTotalCup

/-! # Detection on original pure tensor bidegrees of the native total complex -/
noncomputable section
namespace EnvelopeProperty.DI.CechTotalTensorExt
open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.Preadditive
open scoped BigOperators
open CechAlexanderWhitneyProduct
universe u
private theorem tensorMap_comp {Z : Scheme.{u}} {A B D E F G : Z.Modules}
    (a : A ⟶ D) (b : B ⟶ E) (c : D ⟶ F) (d : E ⟶ G) :
    tensorMap a b ≫ tensorMap c d = tensorMap (a ≫ c) (b ≫ d) := by
  apply tensorSection_hom_ext
  intro W x y
  exact (congrArg ((tensorMap c d).val.app (op W))
    (tensorMap_tensorSection a b W x y)).trans
      ((tensorMap_tensorSection c d W (a.val.app (op W) x) (b.val.app (op W) y)).trans
        (tensorMap_tensorSection (a ≫ c) (b ≫ d) W x y).symm)

private theorem tensorMap_id {Z : Scheme.{u}} (A B : Z.Modules) :
    tensorMap (𝟙 A) (𝟙 B) = 𝟙 (CanonicalGeometry.bundleTensor A B) := by
  apply tensorSection_hom_ext
  intro W x y
  exact tensorMap_tensorSection (𝟙 A) (𝟙 B) W x y

private theorem tensor_hom_ext_of_decompositions {Z : Scheme.{u}} {A B D : Z.Modules}
    {I J : Type*} [Fintype I] [Fintype J] (A' : I → Z.Modules) (B' : J → Z.Modules)
    (pa : ∀ i, A ⟶ A' i) (ia : ∀ i, A' i ⟶ A)
    (pb : ∀ j, B ⟶ B' j) (ib : ∀ j, B' j ⟶ B)
    (ha : ∑ i, pa i ≫ ia i = 𝟙 A) (hb : ∑ j, pb j ≫ ib j = 𝟙 B)
    {φ ψ : CanonicalGeometry.bundleTensor A B ⟶ D}
    (h : ∀ i j, tensorMap (ia i) (ib j) ≫ φ = tensorMap (ia i) (ib j) ≫ ψ) : φ = ψ := by
  classical
  have hl : tensorMap (∑ i, pa i ≫ ia i) (∑ j, pb j ≫ ib j) =
      ∑ i, tensorMap (pa i ≫ ia i) (∑ j, pb j ≫ ib j) :=
    map_sum (tensorMapHomLeft (∑ j, pb j ≫ ib j)) _ _
  have hr (i : I) : tensorMap (pa i ≫ ia i) (∑ j, pb j ≫ ib j) =
      ∑ j, tensorMap (pa i ≫ ia i) (pb j ≫ ib j) :=
    map_sum (tensorMapHomRight (pa i ≫ ia i)) _ _
  have hd : tensorMap (∑ i, pa i ≫ ia i) (∑ j, pb j ≫ ib j) =
      ∑ i, ∑ j, tensorMap (pa i) (pb j) ≫ tensorMap (ia i) (ib j) := by
    exact hl.trans (Finset.sum_congr rfl fun i _ =>
      (hr i).trans (Finset.sum_congr rfl fun j _ =>
        (tensorMap_comp (pa i) (pb j) (ia i) (ib j)).symm))
  have hi : (∑ i, ∑ j, tensorMap (pa i) (pb j) ≫ tensorMap (ia i) (ib j)) =
      𝟙 (CanonicalGeometry.bundleTensor A B) :=
    hd.symm.trans ((congrArg₂ (fun a b => tensorMap a b) ha hb).trans (tensorMap_id A B))
  have reconstruct (m : CanonicalGeometry.bundleTensor A B ⟶ D) :
      m = ∑ i, ∑ j, tensorMap (pa i) (pb j) ≫ (tensorMap (ia i) (ib j) ≫ m) := by
    calc
      m = 𝟙 (CanonicalGeometry.bundleTensor A B) ≫ m := (Category.id_comp m).symm
      _ = (∑ i, ∑ j, tensorMap (pa i) (pb j) ≫ tensorMap (ia i) (ib j)) ≫ m :=
        congrArg (fun z => z ≫ m) hi.symm
      _ = _ := by simp only [sum_comp, Category.assoc]
  exact (reconstruct φ).trans
    ((Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      congrArg (fun z => tensorMap (pa i) (pb j) ≫ z) (h i j)).trans
        (reconstruct ψ).symm)

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
variable (n : ℕ) [SmoothOfRelativeDimension n f]
variable {ι : Type u}
variable (U : ι → (Cartier.SchemeRelativeFrobenius.twist p f).Opens)
local notation "Y" => Cartier.SchemeRelativeFrobenius.twist p f
local notation "K" => Cartier.SchemeRelativeFrobeniusBasisDifferential.complex f p n
local notation "C" => Cartier.DeligneIllusieLocalContinuationCechBicomplex.bicomplex U K
local notation "T" => Cartier.DeligneIllusieLocalContinuationCechTotalAugmentation.totalComplex U K
local notation "anti" => _root_.Finset.HasAntidiagonal.antidiagonal

private def totalTerm (a : ℕ) : (Y).Modules := (T).X a
private def totalPiece {a : ℕ} (s : anti a) : (Y).Modules := ((C).X s.val.1).X s.val.2
private def totalProjection {a : ℕ} (s : anti a) :
    totalTerm f p n U a ⟶ totalPiece f p n U s :=
  HomologicalComplex₂.πTotalUpNat (C) s.val.1 s.val.2 a
private def totalInclusion {a : ℕ} (s : anti a) :
    totalPiece f p n U s ⟶ totalTerm f p n U a :=
  HomologicalComplex₂.ιTotal (C) (.up ℕ) s.val.1 s.val.2 a
    (_root_.Finset.HasAntidiagonal.mem_antidiagonal.mp s.property)

private theorem totalIdentity (a : ℕ) :
    (∑ s : anti a, totalProjection f p n U s ≫ totalInclusion f p n U s) =
      𝟙 (totalTerm f p n U a) := by
  classical
  have hs : (∑ s : anti a, totalProjection f p n U s ≫ totalInclusion f p n U s) =
      ∑ s : anti a, HomologicalComplex₂.πTotalUpNat (C) s.val.1 s.val.2 a ≫
        HomologicalComplex₂.ιTotalOrZero (C) (.up ℕ) s.val.1 s.val.2 a := by
    exact Finset.sum_congr rfl fun s _ => congrArg
      (fun z => HomologicalComplex₂.πTotalUpNat (C) s.val.1 s.val.2 a ≫ z)
      (HomologicalComplex₂.ιTotalOrZero_eq (C) (.up ℕ) s.val.1 s.val.2 a
        (_root_.Finset.HasAntidiagonal.mem_antidiagonal.mp s.property)).symm
  exact hs.trans ((Finset.sum_coe_sort (anti a)
    (fun s : ℕ × ℕ => HomologicalComplex₂.πTotalUpNat (C) s.1 s.2 a ≫
      HomologicalComplex₂.ιTotalOrZero (C) (.up ℕ) s.1 s.2 a)).trans
        (HomologicalComplex₂.totalUpNat_decomposition (C) a))

/-- Actual tensor-total maps are determined by every original pure-bidegree input. -/
theorem totalTensor_hom_ext (a b : ℕ) {D : (Y).Modules}
    {φ ψ : CanonicalGeometry.bundleTensor ((T).X a) ((T).X b) ⟶ D}
    (h : ∀ (q j r j' : ℕ) (ha : q+j=a) (hb : r+j'=b),
      tensorMap (HomologicalComplex₂.ιTotal (C) (.up ℕ) q j a ha)
          (HomologicalComplex₂.ιTotal (C) (.up ℕ) r j' b hb) ≫ φ =
        tensorMap (HomologicalComplex₂.ιTotal (C) (.up ℕ) q j a ha)
          (HomologicalComplex₂.ιTotal (C) (.up ℕ) r j' b hb) ≫ ψ) : φ = ψ := by
  classical
  exact tensor_hom_ext_of_decompositions
    (fun s : anti a => totalPiece f p n U s) (fun t : anti b => totalPiece f p n U t)
    (fun s => totalProjection f p n U s) (fun s => totalInclusion f p n U s)
    (fun t => totalProjection f p n U t) (fun t => totalInclusion f p n U t)
    (totalIdentity f p n U a) (totalIdentity f p n U b)
    (fun s t => h s.val.1 s.val.2 t.val.1 t.val.2
      (_root_.Finset.HasAntidiagonal.mem_antidiagonal.mp s.property)
      (_root_.Finset.HasAntidiagonal.mem_antidiagonal.mp t.property))

end EnvelopeProperty.DI.CechTotalTensorExt
