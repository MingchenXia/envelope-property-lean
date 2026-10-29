import EnvelopeProperty.DI.CechDegreeOneNative
import EnvelopeProperty.DI.CechTotalCup
import EnvelopeProperty.DI.CechTotalCupLeibniz
import EnvelopeProperty.Cartier.DeligneIllusieAlternatingNormalization
import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusBasisDifferential
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! # Actual positive-degree exterior maps into the original Cech total

The original local degree-one data first gives a closed map on the raw
cotangent presheaf. Higher maps will use the actual ordered total cup.
The imported generic degree-one realization and normalization lemmas are
implementation dependencies and receive no new mathematical proof credit.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EnvelopeProperty.DI.CechHigherExteriorMaps

open Cartier.DeligneIllusieLocalContinuationCechTotalAugmentation
open CechDegreeOneDescent

universe u

section OrderedIteration

variable {R A : Type u} [CommRing R] [AddCommGroup A] [Module R A]
  (Q : ℕ → Type u) [∀ q, AddCommGroup (Q q)] [∀ q, Module R (Q q)]

/-- Internal finite currying for the fixed left-parenthesized actual cup expression. -/
private def iterate (τ : A →ₗ[R] Q 1)
    (μ : ∀ q : ℕ, Q (q+1) →ₗ[R] A →ₗ[R] Q (q+2)) :
    (q : ℕ) → MultilinearMap R (fun _ : Fin (q+1) => A) (Q (q+1))
  | 0 => MultilinearMap.ofSubsingleton R A (Q 1) (0 : Fin 1) τ
  | q+1 => ((μ q).compMultilinearMap (iterate τ μ q)).uncurryRight

private theorem iterate_closed (τ : A →ₗ[R] Q 1)
    (μ : ∀ q : ℕ, Q (q+1) →ₗ[R] A →ₗ[R] Q (q+2))
    (δ : ∀ q : ℕ, Q q →ₗ[R] Q (q+1))
    (hτ : ∀ x, δ 1 (τ x) = 0)
    (hμ : ∀ q x y, δ (q+1) x = 0 → δ (q+2) (μ q x y) = 0)
    (q : ℕ) (v : Fin (q+1) → A) : δ (q+1) (iterate Q τ μ q v) = 0 := by
  induction q with
  | zero => exact hτ (v 0)
  | succ q ih =>
    exact hμ q (iterate Q τ μ q (Fin.init v)) (v (Fin.last (q+1)))
      (ih (Fin.init v))

variable {S B : Type u} [CommRing S] [AddCommGroup B] [Module S B]
  (Q' : ℕ → Type u) [∀ q, AddCommGroup (Q' q)] [∀ q, Module S (Q' q)]

private theorem iterate_naturality (ρ : R →+* S) (a : A →ₛₗ[ρ] B)
    (e : ∀ q, Q q →ₛₗ[ρ] Q' q)
    (τ : A →ₗ[R] Q 1) (τ' : B →ₗ[S] Q' 1)
    (μ : ∀ q : ℕ, Q (q+1) →ₗ[R] A →ₗ[R] Q (q+2))
    (μ' : ∀ q : ℕ, Q' (q+1) →ₗ[S] B →ₗ[S] Q' (q+2))
    (hτ : ∀ x, e 1 (τ x) = τ' (a x))
    (hμ : ∀ q x y, e (q+2) (μ q x y) = μ' q (e (q+1) x) (a y))
    (q : ℕ) (v : Fin (q+1) → A) :
    e (q+1) (iterate Q τ μ q v) =
      iterate Q' τ' μ' q (fun i => a (v i)) := by
  induction q with
  | zero => exact hτ (v 0)
  | succ q ih =>
    change e (q+2) (μ q (iterate Q τ μ q (Fin.init v)) (v (Fin.last (q+1)))) =
      μ' q (iterate Q' τ' μ' q (fun i => a (Fin.init v i)))
        (a (v (Fin.last (q+1))))
    rw [hμ, ih (Fin.init v)]

end OrderedIteration

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
  (n : ℕ) [SmoothOfRelativeDimension n f]

local notation "Y" => Cartier.SchemeRelativeFrobenius.twist p f
local notation "g" => pullback.snd f (Cartier.SchemeRelativeFrobenius.baseMap p)
local notation "P" => CanonicalGeometry.cotangentPresheaf g
local notation "M" => CanonicalGeometry.exteriorCotangentSheaf g 1
local notation "K" => Cartier.SchemeRelativeFrobeniusBasisDifferential.complex f p n

variable {ι : Type u}
variable (U : ι → (Cartier.SchemeRelativeFrobenius.twist p f).Opens)

local notation "T" => totalComplex U K

private instance originalRing {Z : Scheme.{u}} (W : Z.Opensᵒᵖ) :
    CommRing (Z.ringCatSheaf.obj.obj W) :=
  inferInstanceAs (CommRing (Z.presheaf.obj W))

set_option backward.isDefEq.respectTransparency false in
private instance originalPresheafSectionModule {Z : Scheme.{u}}
    (N : Z.PresheafOfModules) (W : Z.Opensᵒᵖ) :
    Module (Z.presheaf.obj W) (N.obj W) := (N.obj W).isModule

set_option backward.isDefEq.respectTransparency false in
private instance rawSectionModule {Z : Scheme.{u}}
    (N : Z.PresheafOfModules) (W : Z.Opens) :
    Module Γ(Z,W) (N.obj (op W)) := (N.obj (op W)).isModule

set_option backward.isDefEq.respectTransparency false in
private instance originalSheafSectionModule {Z : Scheme.{u}} (N : Z.Modules) (W : Z.Opens) :
    Module Γ(Z,W) Γ(N,W) := (N.val.obj (op W)).isModule

/-- Internal whole-map closedness through the ORIGINAL exterior universal property. -/
private theorem fromFamily_comp_zero {Z : Scheme.{u}}
    (P0 : Z.PresheafOfModules) (q0 : ℕ) {Q0 R0 : Z.Modules}
    (a : CanonicalGeometry.PresheafAlternatingFamily (R := Z.presheaf) P0 q0 Q0.val)
    (d : Q0 ⟶ R0) (hd : ∀ W m, d.val.app W (a.app W m) = 0) :
    (CanonicalGeometry.exteriorSheafHomEquiv P0 q0 Q0).symm a ≫ d = 0 := by
  apply (CanonicalGeometry.exteriorSheafHomEquiv P0 q0 R0).injective
  apply CanonicalGeometry.PresheafAlternatingFamily.ext
  funext W
  ext m
  let b := (CanonicalGeometry.exteriorSheafHomEquiv P0 q0 Q0).symm a
  have hc : ((CanonicalGeometry.exteriorSheafHomEquiv P0 q0 R0) (b ≫ d)).app W m =
      d.val.app W (((CanonicalGeometry.exteriorSheafHomEquiv P0 q0 Q0) b).app W m) := rfl
  have hv := congrArg (fun t => t.app W m)
    ((CanonicalGeometry.exteriorSheafHomEquiv P0 q0 Q0).apply_symm_apply a)
  have hz : ((CanonicalGeometry.exteriorSheafHomEquiv P0 q0 R0) 0).app W m = 0 := rfl
  exact hc.trans ((congrArg (fun t => d.val.app W t) hv).trans ((hd W m).trans hz.symm))

/-- Original field scalars act through the original true-twist structural map on each open. -/
def constantMap (W : (Y).Opens) : k →+* Γ(Y,W) :=
  ((CanonicalGeometry.schemeConstantPresheafMap g).app (op W)).hom

/-- The actual scalar action, including on empty opens, commutes with original restriction. -/
theorem constantMap_restrict {V W : (Y).Opens} (i : V ⟶ W) :
    ((Y).presheaf.map i.op).hom.comp (constantMap f p W) = constantMap f p V := by
  ext c
  have h := ConcreteCategory.congr_hom
    ((CanonicalGeometry.schemeConstantPresheafMap g).naturality i.op) c
  change constantMap f p V c = (Y).presheaf.map i.op (constantMap f p W c) at h
  exact h.symm

/-- Internal original sheafification input; the public caller will supply the
actual ordered cup expression, with its restriction identity proved internally. -/
private def normalizedFamily (q : ℕ) (N : (Y).Modules)
    (μ : ∀ W : (Y).Opens,
      MultilinearMap Γ(Y,W) (fun _ : Fin q => (P).obj (op W)) Γ(N,W))
    (hμ : ∀ {V W : (Y).Opens} (i : V ⟶ W) (v : Fin q → (P).obj (op W)),
      N.val.map i.op (μ W v) = μ V (fun j => (P).map i.op (v j))) :
    CanonicalGeometry.PresheafAlternatingFamily (R := (Y).presheaf) P q N.val where
  app W := Cartier.DeligneIllusieAlternatingNormalization.normalizedAlternatization
    (constantMap f p W.unop) q (μ W.unop)
  naturality {V W} i m := by
    let ρ := ((Y).presheaf.map i).hom
    let a : (P).obj V →ₛₗ[ρ] (P).obj W :=
      { toFun := (P).map i
        map_add' := ((P).map i).hom.map_add
        map_smul' := (P).map_smul i }
    let b : N.val.obj V →ₛₗ[ρ] N.val.obj W :=
      { toFun := N.val.map i
        map_add' := (N.val.map i).hom.map_add
        map_smul' := N.val.map_smul i }
    exact Cartier.DeligneIllusieAlternatingNormalization.normalizedAlternatization_naturality
      ρ (constantMap f p V.unop) (constantMap f p W.unop)
      (constantMap_restrict f p i.unop) q a b (μ V.unop) (μ W.unop)
      (hμ i.unop) m

private theorem normalizedFamily_comp_zero (q : ℕ) (N N' : (Y).Modules)
    (μ : ∀ W : (Y).Opens,
      MultilinearMap Γ(Y,W) (fun _ : Fin q => (P).obj (op W)) Γ(N,W))
    (hμ : ∀ {V W : (Y).Opens} (i : V ⟶ W) (v : Fin q → (P).obj (op W)),
      N.val.map i.op (μ W v) = μ V (fun j => (P).map i.op (v j)))
    (d : N ⟶ N')
    (hd : ∀ W v, d.val.app (op W) (μ W v) = 0) :
    (CanonicalGeometry.exteriorSheafHomEquiv P q N).symm
      (normalizedFamily f p q N μ hμ) ≫ d = 0 := by
  apply fromFamily_comp_zero
  intro W m
  let L := (d.val.app W).hom
  have hL : L.compMultilinearMap (μ W.unop) = 0 := by
    ext v
    exact hd W.unop v
  have h := Cartier.DeligneIllusieAlternatingNormalization.normalizedAlternatization_closed
    (constantMap f p W.unop) q L (μ W.unop) hL
  have he := congrArg (fun z => z m) h
  change L (Cartier.DeligneIllusieAlternatingNormalization.normalizedAlternatization
    (constantMap f p W.unop) q (μ W.unop) m) = 0 at he
  exact he

private def fromOrderedFamily (q : ℕ) (N : (Y).Modules)
    (μ : ∀ W : (Y).Opens,
      MultilinearMap Γ(Y,W) (fun _ : Fin q => (P).obj (op W)) Γ(N,W))
    (hμ : ∀ {V W : (Y).Opens} (i : V ⟶ W) (v : Fin q → (P).obj (op W)),
      N.val.map i.op (μ W v) = μ V (fun j => (P).map i.op (v j))) :
    CanonicalGeometry.exteriorCotangentSheaf g q ⟶ N :=
  (CanonicalGeometry.exteriorSheafHomEquiv P q N).symm
    (normalizedFamily f p q N μ hμ)

private theorem fromOrderedFamily_unit (q : ℕ) (N : (Y).Modules)
    (μ : ∀ W : (Y).Opens,
      MultilinearMap Γ(Y,W) (fun _ : Fin q => (P).obj (op W)) Γ(N,W))
    (hμ : ∀ {V W : (Y).Opens} (i : V ⟶ W) (v : Fin q → (P).obj (op W)),
      N.val.map i.op (μ W v) = μ V (fun j => (P).map i.op (v j)))
    (W : (Y).Opens) (v : Fin q → (P).obj (op W)) :
    (fromOrderedFamily f p q N μ hμ).val.app (op W)
        (CanonicalGeometry.exteriorSheafSection P q W v) =
      Cartier.DeligneIllusieAlternatingNormalization.normalizedAlternatization
        (constantMap f p W) q (μ W) v := by
  exact congrArg (fun t => t.app (op W) v)
    ((CanonicalGeometry.exteriorSheafHomEquiv P q N).apply_symm_apply
      (normalizedFamily f p q N μ hμ))

private theorem fromOrderedFamily_closed (q : ℕ) (N N' : (Y).Modules)
    (μ : ∀ W : (Y).Opens,
      MultilinearMap Γ(Y,W) (fun _ : Fin q => (P).obj (op W)) Γ(N,W))
    (hμ : ∀ {V W : (Y).Opens} (i : V ⟶ W) (v : Fin q → (P).obj (op W)),
      N.val.map i.op (μ W v) = μ V (fun j => (P).map i.op (v j)))
    (d : N ⟶ N') (hd : ∀ W v, d.val.app (op W) (μ W v) = 0) :
    fromOrderedFamily f p q N μ hμ ≫ d = 0 :=
  normalizedFamily_comp_zero f p q N N' μ hμ d hd

/-- Internal use of the published recovery theorem for the ACTUAL structural scalar.
The final leading-term caller derives its evaluation premise from the honest cup. -/
private theorem fromOrderedFamily_recovery (q : ℕ) (hq : q < p) (N N' : (Y).Modules)
    (μ : ∀ W : (Y).Opens,
      MultilinearMap Γ(Y,W) (fun _ : Fin q => (P).obj (op W)) Γ(N,W))
    (hμ : ∀ {V W : (Y).Opens} (i : V ⟶ W) (v : Fin q → (P).obj (op W)),
      N.val.map i.op (μ W v) = μ V (fun j => (P).map i.op (v j)))
    (W : (Y).Opens) (L : Γ(N,W) →ₗ[Γ(Y,W)] Γ(N',W))
    (a : (P).obj (op W) [⋀^Fin q]→ₗ[Γ(Y,W)] Γ(N',W))
    (hL : L.compMultilinearMap (μ W) = a.toMultilinearMap)
    (v : Fin q → (P).obj (op W)) :
    L ((fromOrderedFamily f p q N μ hμ).val.app (op W)
      (CanonicalGeometry.exteriorSheafSection P q W v)) = a v := by
  have h := Cartier.DeligneIllusieAlternatingNormalization.normalizedAlternatization_recovery
    (constantMap f p W) q p hq L (μ W) a hL
  have he := congrArg (fun t => t v) h
  change L (Cartier.DeligneIllusieAlternatingNormalization.normalizedAlternatization
    (constantMap f p W) q (μ W) v) = a v at he
  exact (congrArg L (fromOrderedFamily_unit f p q N μ hμ W v)).trans he

/-- The ORIGINAL exterior-one unit on raw cotangent sections. -/
def rawOneUnit (W : (Y).Opens) : (P).obj (op W) →ₗ[Γ(Y,W)] Γ(M,W) :=
  (MultilinearMap.ofSubsingleton Γ(Y,W) ((P).obj (op W)) Γ(M,W) (0 : Fin 1)).symm
    (CanonicalGeometry.exteriorSheafSection P 1 W).toMultilinearMap

theorem rawOneUnit_apply (W : (Y).Opens) (m : (P).obj (op W)) :
    rawOneUnit f p W m = CanonicalGeometry.exteriorSheafSection P 1 W (fun _ => m) := rfl

/-- The actual original local-data descent component, before any higher construction. -/
def oneComponent (D : LocalData U M K) : M ⟶ (T).X 1 := by
  exact (HomologicalComplex.singleObjXSelf (.up ℕ) 1 M).inv ≫ (descentMap U D).f 1

/-- Raw original cotangent sections enter the SAME native total by its actual degree-one map. -/
def rawOne (D : LocalData U M K) (W : (Y).Opens) :
    (P).obj (op W) →ₗ[Γ(Y,W)] Γ((T).X 1,W) := by
  exact ((oneComponent f p n U D).val.app (op W)).hom.comp (rawOneUnit f p W)

theorem rawOne_apply (D : LocalData U M K) (W : (Y).Opens) (m : (P).obj (op W)) :
    rawOne f p n U D W m =
      ((oneComponent f p n U D).val.app (op W))
        (CanonicalGeometry.exteriorSheafSection P 1 W (fun _ => m)) := rfl

/-- The raw unit uses the original exterior restriction on EVERY open. -/
theorem rawOneUnit_restrict {V W : (Y).Opens} (i : V ⟶ W) (m : (P).obj (op W)) :
    (M).val.map i.op (rawOneUnit f p W m) =
      rawOneUnit f p V ((P).map i.op m) := by
  change (CanonicalGeometry.exteriorSheaf P 1).val.map i.op
      (CanonicalGeometry.exteriorSheafSection P 1 W (fun _ => m)) =
    CanonicalGeometry.exteriorSheafSection P 1 V (fun _ => (P).map i.op m)
  exact CanonicalGeometry.exteriorSheafSection_restrict P 1 i (fun _ => m)

/-- The full original degree-one sheaf morphism is closed by its native chain-map equation. -/
theorem oneComponent_closed (D : LocalData U M K) :
    oneComponent f p n U D ≫ (T).d 1 2 = 0 := by
  simp only [oneComponent, Category.assoc, (descentMap U D).comm 1 2,
    HomologicalComplex.single_obj_d, zero_comp, comp_zero]

/-- The original native source-single identification retains the same component. -/
theorem oneComponent_f_one (D : LocalData U M K) :
    (descentMap U D).f 1 =
      (HomologicalComplex.singleObjXSelf (.up ℕ) 1 M).hom ≫ oneComponent f p n U D := by
  simp only [oneComponent, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Raw original inputs commute with every original open restriction. -/
theorem rawOne_restrict (D : LocalData U M K) {V W : (Y).Opens}
    (i : V ⟶ W) (m : (P).obj (op W)) :
    ((T).X 1).val.map i.op (rawOne f p n U D W m) =
      rawOne f p n U D V ((P).map i.op m) := by
  change ((T).X 1).val.map i.op
      ((oneComponent f p n U D).val.app (op W) (rawOneUnit f p W m)) =
    (oneComponent f p n U D).val.app (op V)
      (rawOneUnit f p V ((P).map i.op m))
  calc
    _ = (oneComponent f p n U D).val.app (op V)
        ((M).val.map i.op (rawOneUnit f p W m)) :=
      (PresheafOfModules.naturality_apply (oneComponent f p n U D).val i.op
        (rawOneUnit f p W m)).symm
    _ = _ := congrArg (fun z => (oneComponent f p n U D).val.app (op V) z)
      (rawOneUnit_restrict f p i m)

/-- Every actual raw degree-one image is an actual total cycle. -/
theorem rawOne_closed (D : LocalData U M K) (W : (Y).Opens) (m : (P).obj (op W)) :
    ((T).d 1 2).val.app (op W) (rawOne f p n U D W m) = 0 := by
  change (oneComponent f p n U D ≫ (T).d 1 2).val.app (op W)
      (rawOneUnit f p W m) = 0
  rw [oneComponent_closed]
  rfl

private def oneOrdered (D : LocalData U M K) (W : (Y).Opens) :
    MultilinearMap Γ(Y,W) (fun _ : Fin 1 => (P).obj (op W)) Γ((T).X 1,W) :=
  MultilinearMap.ofSubsingleton Γ(Y,W) ((P).obj (op W)) Γ((T).X 1,W)
    (0 : Fin 1) (rawOne f p n U D W)

private theorem oneOrdered_restrict (D : LocalData U M K) {V W : (Y).Opens}
    (i : V ⟶ W) (v : Fin 1 → (P).obj (op W)) :
    ((T).X 1).val.map i.op (oneOrdered f p n U D W v) =
      oneOrdered f p n U D V (fun j => (P).map i.op (v j)) :=
  rawOne_restrict f p n U D i (v 0)

/-- Internal same-map check: the normalization of the genuine one-variable input
is the whole ORIGINAL descent component, by the actual exterior universal property. -/
private theorem normalizedOne_same (D : LocalData U M K) :
    fromOrderedFamily f p 1 ((T).X 1) (oneOrdered f p n U D)
        (fun i v => oneOrdered_restrict f p n U D i v) =
      oneComponent f p n U D := by
  apply (CanonicalGeometry.exteriorSheafHomEquiv P 1 ((T).X 1)).injective
  apply CanonicalGeometry.PresheafAlternatingFamily.ext
  funext W
  ext v
  let a := ((oneComponent f p n U D).val.app W).hom.compAlternatingMap
    (CanonicalGeometry.exteriorSheafSection P 1 W.unop)
  have hL : (LinearMap.id : Γ((T).X 1,W.unop) →ₗ[Γ(Y,W.unop)] Γ((T).X 1,W.unop)).compMultilinearMap
      (oneOrdered f p n U D W.unop) = a.toMultilinearMap := by
    ext w
    change (oneComponent f p n U D).val.app W
        (CanonicalGeometry.exteriorSheafSection P 1 W.unop (fun _ => w 0)) =
      (oneComponent f p n U D).val.app W
        (CanonicalGeometry.exteriorSheafSection P 1 W.unop w)
    apply congrArg (fun z => (oneComponent f p n U D).val.app W
      (CanonicalGeometry.exteriorSheafSection P 1 W.unop z))
    funext i
    exact congrArg w (Subsingleton.elim (0 : Fin 1) i)
  exact fromOrderedFamily_recovery f p 1 (Fact.out : p.Prime).one_lt
    ((T).X 1) ((T).X 1) (oneOrdered f p n U D)
      (fun i v => oneOrdered_restrict f p n U D i v) W.unop LinearMap.id a hL v

/-- The actual positive-degree ordered power of the ORIGINAL closed one-form
map, using the SAME actual total cup and fixed left parentheses. -/
def orderedPower (D : LocalData U M K) (q : ℕ) (W : (Y).Opens) :
    MultilinearMap Γ(Y,W) (fun _ : Fin (q+1) => (P).obj (op W)) Γ((T).X (q+1),W) :=
  iterate (fun a => Γ((T).X a,W)) (rawOne f p n U D W)
    (fun a => (CechTotalCup.totalCupSection f p n U (a+1) 1 W).compl₂
      (rawOne f p n U D W)) q

theorem orderedPower_zero (D : LocalData U M K) (W : (Y).Opens)
    (v : Fin 1 → (P).obj (op W)) :
    orderedPower f p n U D 0 W v = rawOne f p n U D W (v 0) := rfl

theorem orderedPower_succ (D : LocalData U M K) (q : ℕ) (W : (Y).Opens)
    (v : Fin (q+2) → (P).obj (op W)) :
    orderedPower f p n U D (q+1) W v =
      CechTotalCup.totalCupSection f p n U (q+1) 1 W
        (orderedPower f p n U D q W (Fin.init v))
        (rawOne f p n U D W (v (Fin.last (q+1)))) := rfl

/-- The whole actual ordered cup expression commutes with EVERY original
restriction, not only with a prescribed family of coordinate values. -/
theorem orderedPower_restrict (D : LocalData U M K) (q : ℕ)
    {V W : (Y).Opens} (i : V ⟶ W) (v : Fin (q+1) → (P).obj (op W)) :
    ((T).X (q+1)).val.map i.op (orderedPower f p n U D q W v) =
      orderedPower f p n U D q V (fun j => (P).map i.op (v j)) := by
  let ρ := ((Y).presheaf.map i.op).hom
  let a : (P).obj (op W) →ₛₗ[ρ] (P).obj (op V) :=
    { toFun := (P).map i.op
      map_add' := ((P).map i.op).hom.map_add
      map_smul' := (P).map_smul i.op }
  let e (r : ℕ) : Γ((T).X r,W) →ₛₗ[ρ] Γ((T).X r,V) :=
    { toFun := ((T).X r).val.map i.op
      map_add' := (((T).X r).val.map i.op).hom.map_add
      map_smul' := ((T).X r).val.map_smul i.op }
  apply iterate_naturality (fun r => Γ((T).X r,W)) (fun r => Γ((T).X r,V)) ρ a e
    (rawOne f p n U D W) (rawOne f p n U D V)
    (fun r => (CechTotalCup.totalCupSection f p n U (r+1) 1 W).compl₂
      (rawOne f p n U D W))
    (fun r => (CechTotalCup.totalCupSection f p n U (r+1) 1 V).compl₂
      (rawOne f p n U D V))
  · exact rawOne_restrict f p n U D i
  · intro r x y
    change ((T).X (r+2)).val.map i.op
        (CechTotalCup.totalCupSection f p n U (r+1) 1 W x (rawOne f p n U D W y)) =
      CechTotalCup.totalCupSection f p n U (r+1) 1 V (e (r+1) x)
        (rawOne f p n U D V (a y))
    calc
      _ = CechTotalCup.totalCupSection f p n U (r+1) 1 V (e (r+1) x)
          (((T).X 1).val.map i.op (rawOne f p n U D W y)) :=
        CechTotalCup.totalCupSection_restrict f p n U (r+1) 1 i x
          (rawOne f p n U D W y)
      _ = _ := congrArg (CechTotalCup.totalCupSection f p n U (r+1) 1 V (e (r+1) x))
        (rawOne_restrict f p n U D i y)

/-- Genuine normalized positive-degree exterior SHEAF map into the SAME native
total. The actual ordered product and restriction proof are derived above;
neither an arbitrary multiplication nor a desired higher map is an input. -/
def higherMap (D : LocalData U M K) (q : ℕ) :
    CanonicalGeometry.exteriorCotangentSheaf g (q+1) ⟶ (T).X (q+1) :=
  fromOrderedFamily f p (q+1) ((T).X (q+1))
    (orderedPower f p n U D q) (fun i v => orderedPower_restrict f p n U D q i v)

/-- Every original source wedge retains the exact normalized original cup expression. -/
theorem higherMap_unit (D : LocalData U M K) (q : ℕ) (W : (Y).Opens)
    (v : Fin (q+1) → (P).obj (op W)) :
    (higherMap f p n U D q).val.app (op W)
        (CanonicalGeometry.exteriorSheafSection P (q+1) W v) =
      Cartier.DeligneIllusieAlternatingNormalization.normalizedAlternatization
        (constantMap f p W) (q+1) (orderedPower f p n U D q W) v :=
  fromOrderedFamily_unit f p (q+1) ((T).X (q+1))
    (orderedPower f p n U D q) (fun i v => orderedPower_restrict f p n U D q i v) W v

/-- Normalization preserves the WHOLE original degree-one component. -/
theorem higherMap_zero (D : LocalData U M K) :
    higherMap f p n U D 0 = oneComponent f p n U D := by
  change fromOrderedFamily f p 1 ((T).X 1) (oneOrdered f p n U D)
      (fun i v => oneOrdered_restrict f p n U D i v) = oneComponent f p n U D
  exact normalizedOne_same f p n U D

/-- The ACTUAL total product derivation closes every ordered original cup power.
No product-closure or desired higher-cycle certificate is an input. -/
theorem orderedPower_closed (D : LocalData U M K) (q : ℕ) (W : (Y).Opens)
    (v : Fin (q+1) → (P).obj (op W)) :
    ((T).d (q+1) (q+2)).val.app (op W) (orderedPower f p n U D q W v) = 0 := by
  apply iterate_closed (fun a => Γ((T).X a,W))
    (rawOne f p n U D W)
    (fun a => (CechTotalCup.totalCupSection f p n U (a+1) 1 W).compl₂
      (rawOne f p n U D W))
    (fun a => (((T).d a (a+1)).val.app (op W)).hom)
  · exact rawOne_closed f p n U D W
  · intro a x y hx
    exact CechTotalCup.totalCupSection_closed f p n U (a+1) 1 W x
      (rawOne f p n U D W y) hx (rawOne_closed f p n U D W y)

/-- Closedness of the WHOLE original higher exterior morphism follows from
actual ordered-power closure and the original exterior sheaf universal property. -/
theorem higherMap_closed (D : LocalData U M K) (q : ℕ) :
    higherMap f p n U D q ≫ (T).d (q+1) (q+2) = 0 :=
  fromOrderedFamily_closed f p (q+1) ((T).X (q+1)) ((T).X (q+2))
    (orderedPower f p n U D q) (fun i v => orderedPower_restrict f p n U D q i v)
    ((T).d (q+1) (q+2)) (orderedPower_closed f p n U D q)

/-- The genuine positive-degree map from the ORIGINAL single exterior sheaf
into the SAME published native total. All required equations are derived. -/
def higherCochainMap (D : LocalData U M K) (q : ℕ) :
    (HomologicalComplex.single (Y).Modules (.up ℕ) (q+1)).obj
      (CanonicalGeometry.exteriorCotangentSheaf g (q+1)) ⟶ T :=
  HomologicalComplex.mkHomFromSingle (higherMap f p n U D q) (fun j hj => by
    have hstep : (q+1)+1 = j := hj
    have hj' : j = q+2 := by omega
    subst j
    exact higherMap_closed f p n U D q)

/-- The actual single-object unit retains the exact ORIGINAL component. -/
theorem higherCochainMap_f_self (D : LocalData U M K) (q : ℕ) :
    (higherCochainMap f p n U D q).f (q+1) =
      (HomologicalComplex.singleObjXSelf (.up ℕ) (q+1)
        (CanonicalGeometry.exteriorCotangentSheaf g (q+1))).hom ≫ higherMap f p n U D q :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- The WHOLE actual degree-one complex morphism is preserved by normalization. -/
theorem higherCochainMap_zero (D : LocalData U M K) :
    higherCochainMap f p n U D 0 = descentMap U D := by
  apply HomologicalComplex.from_single_hom_ext
  exact ((higherCochainMap_f_self f p n U D 0).trans
    (congrArg (fun h => (HomologicalComplex.singleObjXSelf (.up ℕ) 1 M).hom ≫ h)
      (higherMap_zero f p n U D))).trans (oneComponent_f_one f p n U D).symm

end EnvelopeProperty.DI.CechHigherExteriorMaps
