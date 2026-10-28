import EnvelopeProperty.DI.CechTotalCupComponents
import EnvelopeProperty.DI.CechTotalTensorExt
import EnvelopeProperty.DI.CechCupLeibniz
import EnvelopeProperty.DI.CechCupDeRhamLeibniz
import Mathlib.Tactic.Ring
import EnvelopeProperty.DI.CechTotalCupTransport

/-! # The actual total differential and the original signed cup product -/

noncomputable section
universe u
namespace EnvelopeProperty.DI.CechTotalCup
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.Preadditive
open CechAlexanderWhitneyProduct

private theorem tensorMap_comp {Z : Scheme.{u}} {A B D E F G : Z.Modules}
    (a : A ⟶ D) (b : B ⟶ E) (c : D ⟶ F) (d : E ⟶ G) :
    tensorMap a b ≫ tensorMap c d = tensorMap (a ≫ c) (b ≫ d) := by
  apply tensorSection_hom_ext
  intro W x y
  exact (congrArg ((tensorMap c d).val.app (op W))
    (tensorMap_tensorSection a b W x y)).trans
      ((tensorMap_tensorSection c d W (a.val.app (op W) x) (b.val.app (op W) y)).trans
        (tensorMap_tensorSection (a ≫ c) (b ≫ d) W x y).symm)

private theorem tensorMap_add_left {Z : Scheme.{u}} {A B D E : Z.Modules}
    (a a' : A ⟶ D) (b : B ⟶ E) :
    tensorMap (a+a') b = tensorMap a b + tensorMap a' b :=
  (tensorMapHomLeft b).map_add a a'

private theorem tensorMap_add_right {Z : Scheme.{u}} {A B D E : Z.Modules}
    (a : A ⟶ D) (b b' : B ⟶ E) :
    tensorMap a (b+b') = tensorMap a b + tensorMap a b' :=
  (tensorMapHomRight a).map_add b b'

private theorem tensorMap_zsmul_left {Z : Scheme.{u}} {A B D E : Z.Modules}
    (z : ℤ) (a : A ⟶ D) (b : B ⟶ E) :
    tensorMap (z • a) b = z • tensorMap a b :=
  (tensorMapHomLeft b).map_zsmul z a

private theorem tensorMap_zsmul_right {Z : Scheme.{u}} {A B D E : Z.Modules}
    (z : ℤ) (a : A ⟶ D) (b : B ⟶ E) :
    tensorMap a (z • b) = z • tensorMap a b :=
  (tensorMapHomRight a).map_zsmul z b

private theorem sign_square (j : ℕ) : (-1 : ℤ)^j * (-1 : ℤ)^j = 1 := by
  rw [← mul_pow]
  simp

private theorem sign_right_derham (q j r : ℕ) :
    (-1 : ℤ)^(q+j) * (-1 : ℤ)^(j*(r+1)) = (-1 : ℤ)^(j*r) * (-1 : ℤ)^q := by
  rw [Nat.mul_add, Nat.mul_one, pow_add, pow_add]
  calc
    ((-1 : ℤ)^q * (-1 : ℤ)^j) * ((-1 : ℤ)^(j*r) * (-1 : ℤ)^j) =
      ((-1 : ℤ)^(j*r) * (-1 : ℤ)^q) * ((-1 : ℤ)^j * (-1 : ℤ)^j) := by ring
    _ = _ := by rw [sign_square, mul_one]

private theorem sign_left_cech (q j r : ℕ) :
    (-1 : ℤ)^q * (-1 : ℤ)^((j+1)*r) =
      (-1 : ℤ)^(j*r) * (-1 : ℤ)^(r+q) := by
  rw [Nat.add_mul, Nat.one_mul, pow_add, pow_add]
  ring

private theorem sign_right_cech (q j r : ℕ) :
    ((-1 : ℤ)^(q+j) * (-1 : ℤ)^r) * (-1 : ℤ)^(j*r) =
      ((-1 : ℤ)^(j*r) * (-1 : ℤ)^(r+q)) * (-1 : ℤ)^j := by
  simp only [pow_add]
  ring

private theorem total_four_signs {G : Type*} [AddCommGroup G]
    (q j r : ℕ) (ld rd lv rv : G) :
    (-1 : ℤ)^(j*r) •
        ((ld + (-1 : ℤ)^q • rd) + (-1 : ℤ)^(r+q) • (lv + (-1 : ℤ)^j • rv)) =
      ((-1 : ℤ)^(j*r) • ld +
        (-1 : ℤ)^q • ((-1 : ℤ)^((j+1)*r) • lv)) +
      (-1 : ℤ)^(q+j) •
        ((-1 : ℤ)^(j*(r+1)) • rd + (-1 : ℤ)^r • ((-1 : ℤ)^(j*r) • rv)) := by
  simp only [smul_add, smul_smul]
  rw [sign_left_cech, sign_right_derham]
  rw [← mul_assoc ((-1 : ℤ)^(q+j)), sign_right_cech]
  simp only [mul_assoc]
  abel

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
variable (n : ℕ) [SmoothOfRelativeDimension n f]
variable {ι : Type u}
variable (U : ι → (Cartier.SchemeRelativeFrobenius.twist p f).Opens)
local notation "Y" => Cartier.SchemeRelativeFrobenius.twist p f
local notation "K" => Cartier.SchemeRelativeFrobeniusBasisDifferential.complex f p n
local notation "C" => Cartier.DeligneIllusieLocalContinuationCechBicomplex.bicomplex U K
local notation "T" => Cartier.DeligneIllusieLocalContinuationCechTotalAugmentation.totalComplex U K
local notation "E" q => Cartier.SchemeRelativeFrobeniusDeRham.formModule f p q

private theorem horizontal_eq (q j : ℕ) :
    ((C).d q (q+1)).f j =
      ((Cartier.DeligneIllusieLocalContinuationCechAugmentation.complexFunctor U).map
        (Cartier.SchemeRelativeFrobeniusBasisDifferential.differential f p n q)).f j := by
  exact congrArg
    (fun z : (E q) ⟶ (E (q+1)) =>
      ((Cartier.DeligneIllusieLocalContinuationCechAugmentation.complexFunctor U).map z).f j)
    (CochainComplex.of_d
      (Cartier.SchemeRelativeFrobeniusDeRham.formModule f p)
      (Cartier.SchemeRelativeFrobeniusBasisDifferential.differential f p n) q)

private theorem totalCup_pure_maps (q j r j' a b N : ℕ)
    (ha : q+j=a) (hb : r+j'=b) (hN : a+b=N)
    {A B : (Y).Modules} (ds : A ⟶ ((C).X q).X j) (dt : B ⟶ ((C).X r).X j') :
    tensorMap
        (ds ≫ HomologicalComplex₂.ιTotal (C) (.up ℕ) q j a ha)
        (dt ≫ HomologicalComplex₂.ιTotal (C) (.up ℕ) r j' b hb) ≫
      totalCup f p n U a b ≫ totalDegreeMap f p n U hN =
    (-1 : ℤ)^(j*r) •
      (tensorMap ds dt ≫ orderedCup f p U q r j j' ≫
        HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+q) (j+j') N
          (by change (r+q)+(j+j')=N; omega)) := by
  let is := HomologicalComplex₂.ιTotal (C) (.up ℕ) q j a ha
  let it := HomologicalComplex₂.ιTotal (C) (.up ℕ) r j' b hb
  have hp := CechTotalCupComponents.totalCup_ιTotal f p n U a b q j r j' ha hb
  calc
    _ = tensorMap ds dt ≫ (tensorMap is it ≫ totalCup f p n U a b) ≫
        totalDegreeMap f p n U hN := by
      rw [← tensorMap_comp ds dt is it]
      simp only [Category.assoc]
    _ = tensorMap ds dt ≫
        ((-1 : ℤ)^(j*r) • (orderedCup f p U q r j j' ≫
          HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+q) (j+j') (a+b)
            (by change (r+q)+(j+j')=a+b; omega))) ≫ totalDegreeMap f p n U hN :=
      congrArg (fun z => tensorMap ds dt ≫ z ≫ totalDegreeMap f p n U hN) hp
    _ = _ := by
      simp only [comp_zsmul, zsmul_comp, Category.assoc, totalDegreeMap_ιTotal]

private theorem cup_derham_total (q j r j' N : ℕ) (hN : (r+q+1)+(j+j')=N) :
    orderedCup f p U q r j j' ≫ ((C).d (r+q) (r+q+1)).f (j+j') ≫
        HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+q+1) (j+j') N hN =
    (tensorMap (((C).d q (q+1)).f j) (𝟙 (((C).X r).X j')) ≫
      orderedCup f p U (q+1) r j j' ≫
        HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+(q+1)) (j+j') N (by change (r+(q+1))+(j+j')=N; omega)) +
    (-1 : ℤ)^q •
      (tensorMap (𝟙 (((C).X q).X j)) (((C).d r (r+1)).f j') ≫
        orderedCup f p U q (r+1) j j' ≫
          HomologicalComplex₂.ιTotal (C) (.up ℕ) ((r+1)+q) (j+j') N (by change ((r+1)+q)+(j+j')=N; omega)) := by
  simp only [horizontal_eq]
  have h := congrArg
    (fun z => z ≫ HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+q+1) (j+j') N hN)
    (cup_derham_leibniz f p n U q r j j')
  simp only [add_comp, zsmul_comp, Category.assoc, formDegreeMap_ιTotal] at h
  exact h

private theorem cup_cech_total (q j r j' N : ℕ) (hN : (r+q)+(j+j'+1)=N) :
    orderedCup f p U q r j j' ≫ ((C).X (r+q)).d (j+j') (j+j'+1) ≫
        HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+q) (j+j'+1) N hN =
    (tensorMap (((C).X q).d j (j+1)) (𝟙 (((C).X r).X j')) ≫
      orderedCup f p U q r (j+1) j' ≫
        HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+q) ((j+1)+j') N (by change (r+q)+((j+1)+j')=N; omega)) +
    (-1 : ℤ)^j •
      (tensorMap (𝟙 (((C).X q).X j)) (((C).X r).d j' (j'+1)) ≫
        orderedCup f p U q r j (j'+1) ≫
          HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+q) (j+(j'+1)) N (by change (r+q)+(j+(j'+1))=N; omega)) := by
  have h := congrArg
    (fun z => z ≫ HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+q) (j+j'+1) N hN)
    (cup_cech_leibniz f p U q r j j')
  have hl := orderedCupInDegree_eq f p U q r (j+1) j' (j+j'+1) (by omega)
  have hr := orderedCupInDegree_eq f p U q r j (j'+1) (j+j'+1) (by omega)
  simp only [cupAfterLeft, cupAfterRight] at h
  rw [← hl, ← hr] at h
  simp only [add_comp, zsmul_comp, Category.assoc, degreeMap_ιTotal] at h
  exact h

/-- The actual signed total cup satisfies the whole original total Leibniz identity. -/
theorem totalCup_leibniz (a b : ℕ) :
    totalCup f p n U a b ≫ (T).d (a+b) (a+b+1) =
    (tensorMap ((T).d a (a+1)) (𝟙 ((T).X b)) ≫
      totalCup f p n U (a+1) b ≫
        totalDegreeMap f p n U (show (a+1)+b=a+b+1 by omega)) +
    (-1 : ℤ)^a •
      (tensorMap (𝟙 ((T).X a)) ((T).d b (b+1)) ≫
        totalCup f p n U a (b+1) ≫
          totalDegreeMap f p n U (show a+(b+1)=a+b+1 by omega)) := by
  apply CechTotalTensorExt.totalTensor_hom_ext f p n U a b
  intro q j r j' ha hb
  subst a b
  let N := (q+j)+(r+j')+1
  let is : ((C).X q).X j ⟶ (T).X (q+j) :=
    HomologicalComplex₂.ιTotal (C) (.up ℕ) q j (q+j) rfl
  let it : ((C).X r).X j' ⟶ (T).X (r+j') :=
    HomologicalComplex₂.ιTotal (C) (.up ℕ) r j' (r+j') rfl
  let ld : CanonicalGeometry.bundleTensor (((C).X q).X j) (((C).X r).X j') ⟶ (T).X N :=
    tensorMap (((C).d q (q+1)).f j) (𝟙 (((C).X r).X j')) ≫
      orderedCup f p U (q+1) r j j' ≫
        HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+(q+1)) (j+j') N
          (by change (r+(q+1))+(j+j')=(q+j)+(r+j')+1; omega)
  let rd : CanonicalGeometry.bundleTensor (((C).X q).X j) (((C).X r).X j') ⟶ (T).X N :=
    tensorMap (𝟙 (((C).X q).X j)) (((C).d r (r+1)).f j') ≫
      orderedCup f p U q (r+1) j j' ≫
        HomologicalComplex₂.ιTotal (C) (.up ℕ) ((r+1)+q) (j+j') N
          (by change ((r+1)+q)+(j+j')=(q+j)+(r+j')+1; omega)
  let lv : CanonicalGeometry.bundleTensor (((C).X q).X j) (((C).X r).X j') ⟶ (T).X N :=
    tensorMap (((C).X q).d j (j+1)) (𝟙 (((C).X r).X j')) ≫
      orderedCup f p U q r (j+1) j' ≫
        HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+q) ((j+1)+j') N
          (by change (r+q)+((j+1)+j')=(q+j)+(r+j')+1; omega)
  let rv : CanonicalGeometry.bundleTensor (((C).X q).X j) (((C).X r).X j') ⟶ (T).X N :=
    tensorMap (𝟙 (((C).X q).X j)) (((C).X r).d j' (j'+1)) ≫
      orderedCup f p U q r j (j'+1) ≫
        HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+q) (j+(j'+1)) N
          (by change (r+q)+(j+(j'+1))=(q+j)+(r+j')+1; omega)
  have hout : orderedCup f p U q r j j' ≫
      (HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+q) (j+j') ((q+j)+(r+j'))
        (by change (r+q)+(j+j')=(q+j)+(r+j'); omega) ≫
          (T).d ((q+j)+(r+j')) N) =
      (ld + (-1 : ℤ)^q • rd) + (-1 : ℤ)^(r+q) • (lv + (-1 : ℤ)^j • rv) := by
    rw [totalInclusion_d]
    simp only [comp_add, comp_zsmul]
    exact congrArg₂ (fun x y => x + (-1 : ℤ)^(r+q) • y)
      (cup_derham_total f p n U q j r j' N (by dsimp [N]; omega))
      (cup_cech_total f p n U q j r j' N (by dsimp [N]; omega))
  have hlhs : tensorMap is it ≫
      (totalCup f p n U (q+j) (r+j') ≫ (T).d ((q+j)+(r+j')) N) =
      (-1 : ℤ)^(j*r) •
        ((ld + (-1 : ℤ)^q • rd) + (-1 : ℤ)^(r+q) • (lv + (-1 : ℤ)^j • rv)) := by
    calc
      _ = ((-1 : ℤ)^(j*r) • (orderedCup f p U q r j j' ≫
          HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+q) (j+j') ((q+j)+(r+j'))
            (by change (r+q)+(j+j')=(q+j)+(r+j'); omega))) ≫
              (T).d ((q+j)+(r+j')) N := by
        rw [← Category.assoc, CechTotalCupComponents.totalCup_ιTotal]
      _ = _ := by rw [zsmul_comp, Category.assoc, hout]
  have hld : tensorMap
      (((C).d q (q+1)).f j ≫
        HomologicalComplex₂.ιTotal (C) (.up ℕ) (q+1) j (q+j+1)
          (by change q+1+j=q+j+1; omega)) it ≫
      totalCup f p n U (q+j+1) (r+j') ≫
        totalDegreeMap f p n U (show (q+j+1)+(r+j')=N by dsimp [N]; omega) =
      (-1 : ℤ)^(j*r) • ld := by
    have h := totalCup_pure_maps f p n U (q+1) j r j' (q+j+1) (r+j') N
      (by omega) rfl (by dsimp [N]; omega) (((C).d q (q+1)).f j) (𝟙 (((C).X r).X j'))
    simpa only [Category.id_comp] using h
  have hlv : tensorMap
      (((C).X q).d j (j+1) ≫
        HomologicalComplex₂.ιTotal (C) (.up ℕ) q (j+1) (q+j+1)
          (by change q+(j+1)=q+j+1; omega)) it ≫
      totalCup f p n U (q+j+1) (r+j') ≫
        totalDegreeMap f p n U (show (q+j+1)+(r+j')=N by dsimp [N]; omega) =
      (-1 : ℤ)^((j+1)*r) • lv := by
    have h := totalCup_pure_maps f p n U q (j+1) r j' (q+j+1) (r+j') N
      (by omega) rfl (by dsimp [N]; omega) (((C).X q).d j (j+1)) (𝟙 (((C).X r).X j'))
    simpa only [Category.id_comp] using h
  have hrd : tensorMap is
      (((C).d r (r+1)).f j' ≫
        HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+1) j' (r+j'+1)
          (by change r+1+j'=r+j'+1; omega)) ≫
      totalCup f p n U (q+j) (r+j'+1) ≫
        totalDegreeMap f p n U (show (q+j)+(r+j'+1)=N by dsimp [N]; omega) =
      (-1 : ℤ)^(j*(r+1)) • rd := by
    have h := totalCup_pure_maps f p n U q j (r+1) j' (q+j) (r+j'+1) N
      rfl (by omega) (by dsimp [N]; omega) (𝟙 (((C).X q).X j)) (((C).d r (r+1)).f j')
    simpa only [Category.id_comp] using h
  have hrv : tensorMap is
      (((C).X r).d j' (j'+1) ≫
        HomologicalComplex₂.ιTotal (C) (.up ℕ) r (j'+1) (r+j'+1)
          (by change r+(j'+1)=r+j'+1; omega)) ≫
      totalCup f p n U (q+j) (r+j'+1) ≫
        totalDegreeMap f p n U (show (q+j)+(r+j'+1)=N by dsimp [N]; omega) =
      (-1 : ℤ)^(j*r) • rv := by
    have h := totalCup_pure_maps f p n U q j r (j'+1) (q+j) (r+j'+1) N
      rfl (by omega) (by dsimp [N]; omega) (𝟙 (((C).X q).X j)) (((C).X r).d j' (j'+1))
    simpa only [Category.id_comp] using h
  have hleft : tensorMap is it ≫
      (tensorMap ((T).d (q+j) (q+j+1)) (𝟙 ((T).X (r+j'))) ≫
        totalCup f p n U (q+j+1) (r+j') ≫
          totalDegreeMap f p n U (show (q+j+1)+(r+j')=N by dsimp [N]; omega)) =
      (-1 : ℤ)^(j*r) • ld + (-1 : ℤ)^q • ((-1 : ℤ)^((j+1)*r) • lv) := by
    rw [← Category.assoc (tensorMap is it) (tensorMap ((T).d (q+j) (q+j+1)) _),
      tensorMap_comp, Category.comp_id, totalInclusion_d, tensorMap_add_left, tensorMap_zsmul_left]
    simp only [add_comp, zsmul_comp]
    exact congrArg₂ (fun x y => x + (-1 : ℤ)^q • y) hld hlv
  have hright : tensorMap is it ≫
      (tensorMap (𝟙 ((T).X (q+j))) ((T).d (r+j') (r+j'+1)) ≫
        totalCup f p n U (q+j) (r+j'+1) ≫
          totalDegreeMap f p n U (show (q+j)+(r+j'+1)=N by dsimp [N]; omega)) =
      (-1 : ℤ)^(j*(r+1)) • rd + (-1 : ℤ)^r • ((-1 : ℤ)^(j*r) • rv) := by
    rw [← Category.assoc (tensorMap is it) (tensorMap _ ((T).d (r+j') (r+j'+1))),
      tensorMap_comp, Category.comp_id, totalInclusion_d, tensorMap_add_right, tensorMap_zsmul_right]
    simp only [add_comp, zsmul_comp]
    exact congrArg₂ (fun x y => x + (-1 : ℤ)^r • y) hrd hrv
  change tensorMap is it ≫ (totalCup f p n U (q+j) (r+j') ≫
      (T).d ((q+j)+(r+j')) N) = _
  simp only [comp_add, comp_zsmul]
  rw [hlhs, hleft, hright]
  exact total_four_signs q j r ld rd lv rv

private theorem hom_zsmul_app {Z : Scheme.{u}} {M Q : Z.Modules}
    (c : ℤ) (a : M ⟶ Q) (W : Z.Opens) (s : Γ(M,W)) :
    (c • a).val.app (op W) s = c • a.val.app (op W) s := by
  have h : (c • a).val = c • a.val :=
    Functor.map_zsmul (SheafOfModules.forget Z.ringCatSheaf)
  rw [h, PresheafOfModules.zsmul_app]
  rfl

/-- Actual original total cycles have an actual closed original total cup section. -/
theorem totalCupSection_closed (a b : ℕ) (W : (Y).Opens)
    (x : Γ((T).X a,W)) (y : Γ((T).X b,W))
    (hx : ((T).d a (a+1)).val.app (op W) x = 0)
    (hy : ((T).d b (b+1)).val.app (op W) y = 0) :
    ((T).d (a+b) (a+b+1)).val.app (op W)
      (totalCupSection f p n U a b W x y) = 0 := by
  let t := CanonicalGeometry.tensorSection (X := Y) ((T).X a) ((T).X b) W x y
  let l : CanonicalGeometry.bundleTensor ((T).X a) ((T).X b) ⟶ (T).X (a+b+1) :=
    tensorMap ((T).d a (a+1)) (𝟙 ((T).X b)) ≫ totalCup f p n U (a+1) b ≫
      totalDegreeMap f p n U (show (a+1)+b=a+b+1 by omega)
  let r : CanonicalGeometry.bundleTensor ((T).X a) ((T).X b) ⟶ (T).X (a+b+1) :=
    tensorMap (𝟙 ((T).X a)) ((T).d b (b+1)) ≫ totalCup f p n U a (b+1) ≫
      totalDegreeMap f p n U (show a+(b+1)=a+b+1 by omega)
  have hl : l.val.app (op W) t = 0 := by
    change (totalDegreeMap f p n U (show (a+1)+b=a+b+1 by omega)).val.app (op W)
      ((totalCup f p n U (a+1) b).val.app (op W)
        ((tensorMap ((T).d a (a+1)) (𝟙 ((T).X b))).val.app (op W)
          (CanonicalGeometry.tensorSection (X := Y) ((T).X a) ((T).X b) W x y))) = 0
    rw [tensorMap_tensorSection, hx]
    change (totalDegreeMap f p n U (show (a+1)+b=a+b+1 by omega)).val.app (op W)
      ((totalCup f p n U (a+1) b).val.app (op W)
        (CanonicalGeometry.tensorSection (X := Y) ((T).X (a+1)) ((T).X b) W 0 y)) = 0
    rw [CanonicalGeometry.tensorSection_zero_left]
    simp only [map_zero]
  have hr : r.val.app (op W) t = 0 := by
    change (totalDegreeMap f p n U (show a+(b+1)=a+b+1 by omega)).val.app (op W)
      ((totalCup f p n U a (b+1)).val.app (op W)
        ((tensorMap (𝟙 ((T).X a)) ((T).d b (b+1))).val.app (op W)
          (CanonicalGeometry.tensorSection (X := Y) ((T).X a) ((T).X b) W x y))) = 0
    rw [tensorMap_tensorSection, hy]
    change (totalDegreeMap f p n U (show a+(b+1)=a+b+1 by omega)).val.app (op W)
      ((totalCup f p n U a (b+1)).val.app (op W)
        (CanonicalGeometry.tensorSection (X := Y) ((T).X a) ((T).X (b+1)) W x 0)) = 0
    rw [CanonicalGeometry.tensorSection_zero_right]
    simp only [map_zero]
  have h := congrArg
    (fun z : CanonicalGeometry.bundleTensor ((T).X a) ((T).X b) ⟶ (T).X (a+b+1) =>
      z.val.app (op W) t) (totalCup_leibniz f p n U a b)
  change ((T).d (a+b) (a+b+1)).val.app (op W)
      ((totalCup f p n U a b).val.app (op W) t) =
    l.val.app (op W) t + (((-1 : ℤ)^a) • r).val.app (op W) t at h
  rw [hom_zsmul_app, hl, hr, smul_zero, add_zero] at h
  exact h

end EnvelopeProperty.DI.CechTotalCup
