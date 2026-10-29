import EnvelopeProperty.DI.CechTotalCup

/-! # Original pure-bidegree inputs of the actual total cup -/
noncomputable section
namespace EnvelopeProperty.DI.CechTotalCupComponents
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

private theorem tensorMap_zero_left {Z : Scheme.{u}} {A B D E : Z.Modules} (b : B ⟶ E) :
    tensorMap (0 : A ⟶ D) b = 0 := (tensorMapHomLeft b).map_zero

private theorem tensorMap_zero_right {Z : Scheme.{u}} {A B D E : Z.Modules} (a : A ⟶ D) :
    tensorMap a (0 : B ⟶ E) = 0 := (tensorMapHomRight a).map_zero

private theorem precomp_signedTensorMap {Z : Scheme.{u}} {A B D E F G H : Z.Modules}
    (a : A ⟶ D) (b : B ⟶ E) (c : D ⟶ F) (d : E ⟶ G)
    (e : CanonicalGeometry.bundleTensor F G ⟶ H) (z : ℤ) :
    tensorMap a b ≫ (z • (tensorMap c d ≫ e)) =
      z • (tensorMap (a ≫ c) (b ≫ d) ≫ e) := by
  rw [comp_zsmul, ← Category.assoc, tensorMap_comp]

private theorem comp_double_sum_unique {V : Type*} [Category V] [Preadditive V]
    {A B D : V} {I J : Type*} [Fintype I] [Fintype J]
    (m : A ⟶ B) (g : I → J → (B ⟶ D)) (i₀ : I) (j₀ : J) (v : A ⟶ D)
    (same : m ≫ g i₀ j₀ = v)
    (left : ∀ i, i ≠ i₀ → ∀ j, m ≫ g i j = 0)
    (right : ∀ j, j ≠ j₀ → m ≫ g i₀ j = 0) :
    m ≫ (∑ i, ∑ j, g i j) = v := by
  classical
  simp only [comp_sum]
  rw [Finset.sum_eq_single i₀]
  · rw [Finset.sum_eq_single j₀]
    · exact same
    · intro j _ hj
      exact right j hj
    · intro h
      exact (h (Finset.mem_univ j₀)).elim
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    exact left i hi j
  · intro h
    exact (h (Finset.mem_univ i₀)).elim

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

private def componentTail {a b : ℕ} (s : anti a) (t : anti b) :
    CanonicalGeometry.bundleTensor (((C).X s.val.1).X s.val.2)
      (((C).X t.val.1).X t.val.2) ⟶ (T).X (a+b) :=
  orderedCup f p U s.val.1 t.val.1 s.val.2 t.val.2 ≫
    HomologicalComplex₂.ιTotal (C) (.up ℕ) (t.val.1+s.val.1) (s.val.2+t.val.2) (a+b)
      (by
        have hs := _root_.Finset.HasAntidiagonal.mem_antidiagonal.mp s.property
        have ht := _root_.Finset.HasAntidiagonal.mem_antidiagonal.mp t.property
        change (t.val.1+s.val.1)+(s.val.2+t.val.2)=a+b
        omega)

private theorem ι_π_ne (q j a : ℕ) (ha : q+j=a) (s : anti a)
    (hs : s.val ≠ (q,j)) :
    HomologicalComplex₂.ιTotal (C) (.up ℕ) q j a ha ≫
      HomologicalComplex₂.πTotalUpNat (C) s.val.1 s.val.2 a = 0 := by
  have h := HomologicalComplex₂.ιTotal_πTotalUpNat (C) q j a ha s.val.1 s.val.2
  by_cases hq : q = s.val.1
  · have hj : j ≠ s.val.2 := by
      intro hj
      exact hs (Prod.ext hq.symm hj.symm)
    simpa only [dif_pos hq, dif_neg hj] using h
  · simpa only [dif_neg hq] using h

private theorem component_zero_left (a b q j r j' : ℕ)
    (ha : q+j=a) (hb : r+j'=b) (s : anti a) (t : anti b) (hs : s.val ≠ (q,j)) :
    tensorMap (HomologicalComplex₂.ιTotal (C) (.up ℕ) q j a ha)
        (HomologicalComplex₂.ιTotal (C) (.up ℕ) r j' b hb) ≫
      CechTotalCup.totalCupComponent f p n U s t = 0 := by
  have h := precomp_signedTensorMap
    (HomologicalComplex₂.ιTotal (C) (.up ℕ) q j a ha)
    (HomologicalComplex₂.ιTotal (C) (.up ℕ) r j' b hb)
    (HomologicalComplex₂.πTotalUpNat (C) s.val.1 s.val.2 a)
    (HomologicalComplex₂.πTotalUpNat (C) t.val.1 t.val.2 b)
    (componentTail f p n U s t) ((-1 : ℤ)^(s.val.2*t.val.1))
  exact h.trans (by
    rw [ι_π_ne f p n U q j a ha s hs, tensorMap_zero_left, zero_comp, smul_zero])

private theorem component_zero_right (a b q j r j' : ℕ)
    (ha : q+j=a) (hb : r+j'=b) (s : anti a) (t : anti b) (ht : t.val ≠ (r,j')) :
    tensorMap (HomologicalComplex₂.ιTotal (C) (.up ℕ) q j a ha)
        (HomologicalComplex₂.ιTotal (C) (.up ℕ) r j' b hb) ≫
      CechTotalCup.totalCupComponent f p n U s t = 0 := by
  have h := precomp_signedTensorMap
    (HomologicalComplex₂.ιTotal (C) (.up ℕ) q j a ha)
    (HomologicalComplex₂.ιTotal (C) (.up ℕ) r j' b hb)
    (HomologicalComplex₂.πTotalUpNat (C) s.val.1 s.val.2 a)
    (HomologicalComplex₂.πTotalUpNat (C) t.val.1 t.val.2 b)
    (componentTail f p n U s t) ((-1 : ℤ)^(s.val.2*t.val.1))
  exact h.trans (by
    rw [ι_π_ne f p n U r j' b hb t ht, tensorMap_zero_right, zero_comp, smul_zero])

/-- On original pure-bidegree tensor inputs, the entire total cup is exactly
its signed original ordered cup followed by the original total inclusion. -/
theorem totalCup_ιTotal (a b q j r j' : ℕ) (ha : q+j=a) (hb : r+j'=b) :
    tensorMap (HomologicalComplex₂.ιTotal (C) (.up ℕ) q j a ha)
        (HomologicalComplex₂.ιTotal (C) (.up ℕ) r j' b hb) ≫
      CechTotalCup.totalCup f p n U a b =
    ((-1 : ℤ) ^ (j*r)) •
      (orderedCup f p U q r j j' ≫
        HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+q) (j+j') (a+b)
          (by change (r+q)+(j+j')=a+b; omega)) := by
  classical
  subst a b
  let s₀ : anti (q+j) := ⟨(q,j), _root_.Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩
  let t₀ : anti (r+j') := ⟨(r,j'), _root_.Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩
  exact comp_double_sum_unique
    (tensorMap (HomologicalComplex₂.ιTotal (C) (.up ℕ) q j (q+j) rfl)
      (HomologicalComplex₂.ιTotal (C) (.up ℕ) r j' (r+j') rfl))
    (fun s t => CechTotalCup.totalCupComponent f p n U s t) s₀ t₀ _
    (by
      have h := precomp_signedTensorMap
        (HomologicalComplex₂.ιTotal (C) (.up ℕ) q j (q+j) rfl)
        (HomologicalComplex₂.ιTotal (C) (.up ℕ) r j' (r+j') rfl)
        (HomologicalComplex₂.πTotalUpNat (C) q j (q+j))
        (HomologicalComplex₂.πTotalUpNat (C) r j' (r+j'))
        (componentTail f p n U s₀ t₀) ((-1 : ℤ)^(j*r))
      exact h.trans (by
        rw [HomologicalComplex₂.ιTotal_πTotalUpNat_self,
          HomologicalComplex₂.ιTotal_πTotalUpNat_self, tensorMap_id, Category.id_comp]
        rfl))
    (by
      intro s hs t
      apply component_zero_left f p n U (q+j) (r+j') q j r j' rfl rfl s t
      intro h
      exact hs (Subtype.ext h))
    (by
      intro t ht
      apply component_zero_right f p n U (q+j) (r+j') q j r j' rfl rfl s₀ t
      intro h
      exact ht (Subtype.ext h))

end EnvelopeProperty.DI.CechTotalCupComponents
