import EnvelopeProperty.DI.CechFactorDeRhamLeibniz
import EnvelopeProperty.DI.CechAlexanderWhitneyProduct
import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechBicomplex

/-! # The actual whole ordered cup and the original de Rham differential -/
noncomputable section
namespace EnvelopeProperty.DI.CechAlexanderWhitneyProduct
open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.Preadditive
open Cartier.DeligneIllusieLocalContinuationCechModules
open Cartier.DeligneIllusieLocalContinuationCechAugmentation
open Cartier.DeligneIllusieLocalContinuationCechBicomplex
open Cartier.DeligneIllusieCechCupProduct
universe u
private theorem projection_restriction_naturality {V : Type*} [Category V]
    {A B D E F G : V} (d : A ⟶ B) (πM : A ⟶ D) (πN : B ⟶ E)
    (ρM : D ⟶ F) (ρN : E ⟶ G) (v : D ⟶ E) (w : F ⟶ G)
    (hπ : d ≫ πN = πM ≫ v) (hρ : v ≫ ρN = ρM ≫ w) :
    d ≫ (πN ≫ ρN) = (πM ≫ ρM) ≫ w := by
  calc
    d ≫ (πN ≫ ρN) = (d ≫ πN) ≫ ρN := (Category.assoc _ _ _).symm
    _ = (πM ≫ v) ≫ ρN := congrArg (fun z => z ≫ ρN) hπ
    _ = πM ≫ (v ≫ ρN) := Category.assoc _ _ _
    _ = πM ≫ (ρM ≫ w) := congrArg (fun z => πM ≫ z) hρ
    _ = (πM ≫ ρM) ≫ w := (Category.assoc _ _ _).symm

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
variable (n : ℕ) [SmoothOfRelativeDimension n f]
variable {κ : Type u}
variable (U : κ → Scheme.Opens (Cartier.SchemeRelativeFrobenius.twist p f))
local notation "Y" => Cartier.SchemeRelativeFrobenius.twist p f
local notation "E" q => Cartier.SchemeRelativeFrobeniusDeRham.formModule f p q

/-- Original prefix projection and full-tuple restriction commute with every actual module map. -/
theorem prefixProjection_naturality {M N : (Y).Modules} (φ : M ⟶ N)
    (j j' : ℕ) (i : Fin (j+j'+1) → κ) :
    ((complexFunctor U).map φ).f j ≫ prefixProjection f p U N j j' i =
      prefixProjection f p U M j j' i ≫
        (factorFunctor (∏ᶜ fun a : Fin (j+j'+1) => U (i a))).map φ := by
  let V : (Y).Opens := ∏ᶜ fun a : Fin (j+j'+1) => U (i a)
  let P : (Y).Opens := ∏ᶜ fun a : Fin (j+1) => U ((i ∘ tuplePrefix j j') a)
  let πM : (complex M U).X j ⟶ factor M P :=
    Pi.π (fun t : Fin (j+1) → κ => factor M (∏ᶜ fun a : Fin (j+1) => U (t a)))
      (i ∘ tuplePrefix j j')
  let πN : (complex N U).X j ⟶ factor N P :=
    Pi.π (fun t : Fin (j+1) → κ => factor N (∏ᶜ fun a : Fin (j+1) => U (t a)))
      (i ∘ tuplePrefix j j')
  let ρM : factor M P ⟶ factor M V := factorMap M (tupleOpen_le_prefix U j j' i)
  let ρN : factor N P ⟶ factor N V := factorMap N (tupleOpen_le_prefix U j j' i)
  have hπ : ((complexFunctor U).map φ).f j ≫ πN = πM ≫ (factorFunctor P).map φ :=
    complexMap_pi U φ j (i ∘ tuplePrefix j j')
  have hρ : (factorFunctor P).map φ ≫ ρN = ρM ≫ (factorFunctor V).map φ :=
    ((factorPresheafMap φ).naturality (homOfLE (tupleOpen_le_prefix U j j' i)).op).symm
  exact projection_restriction_naturality (((complexFunctor U).map φ).f j)
    πM πN ρM ρN ((factorFunctor P).map φ) ((factorFunctor V).map φ) hπ hρ

/-- Original suffix projection and full-tuple restriction commute with every actual module map. -/
theorem suffixProjection_naturality {M N : (Y).Modules} (φ : M ⟶ N)
    (j j' : ℕ) (i : Fin (j+j'+1) → κ) :
    ((complexFunctor U).map φ).f j' ≫ suffixProjection f p U N j j' i =
      suffixProjection f p U M j j' i ≫
        (factorFunctor (∏ᶜ fun a : Fin (j+j'+1) => U (i a))).map φ := by
  let V : (Y).Opens := ∏ᶜ fun a : Fin (j+j'+1) => U (i a)
  let P : (Y).Opens := ∏ᶜ fun a : Fin (j'+1) => U ((i ∘ tupleSuffix j j') a)
  let πM : (complex M U).X j' ⟶ factor M P :=
    Pi.π (fun t : Fin (j'+1) → κ => factor M (∏ᶜ fun a : Fin (j'+1) => U (t a)))
      (i ∘ tupleSuffix j j')
  let πN : (complex N U).X j' ⟶ factor N P :=
    Pi.π (fun t : Fin (j'+1) → κ => factor N (∏ᶜ fun a : Fin (j'+1) => U (t a)))
      (i ∘ tupleSuffix j j')
  let ρM : factor M P ⟶ factor M V := factorMap M (tupleOpen_le_suffix U j j' i)
  let ρN : factor N P ⟶ factor N V := factorMap N (tupleOpen_le_suffix U j j' i)
  have hπ : ((complexFunctor U).map φ).f j' ≫ πN = πM ≫ (factorFunctor P).map φ :=
    complexMap_pi U φ j' (i ∘ tupleSuffix j j')
  have hρ : (factorFunctor P).map φ ≫ ρN = ρM ≫ (factorFunctor V).map φ :=
    ((factorPresheafMap φ).naturality (homOfLE (tupleOpen_le_suffix U j j' i)).op).symm
  exact projection_restriction_naturality (((complexFunctor U).map φ).f j')
    πM πN ρM ρN ((factorFunctor P).map φ) ((factorFunctor V).map φ) hπ hρ

/-- The original Cech complex functor applied to the original form-degree equality map. -/
def formDegreeMap {a b : ℕ} (h : a=b) (j : ℕ) :
    (complex (E a) U).X j ⟶ (complex (E b) U).X j :=
  ((complexFunctor U).map
    (eqToHom (congrArg (Cartier.SchemeRelativeFrobeniusDeRham.formModule f p) h))).f j

/-- Every original projection retains the same original factor degree transport. -/
theorem formDegreeMap_pi {a b : ℕ} (h : a=b) (j : ℕ) (i : Fin (j+1) → κ) :
    formDegreeMap f p U h j ≫
      Pi.π (fun t : Fin (j+1) → κ => factor (E b) (∏ᶜ fun x : Fin (j+1) => U (t x))) i =
    Pi.π (fun t : Fin (j+1) → κ => factor (E a) (∏ᶜ fun x : Fin (j+1) => U (t x))) i ≫
      eqToHom (congrArg (fun q => factor (E q) (∏ᶜ fun x : Fin (j+1) => U (i x))) h) := by
  cases h
  let π : (complex (E a) U).X j ⟶ factor (E a) (∏ᶜ fun x : Fin (j+1) => U (i x)) :=
    Pi.π (fun t : Fin (j+1) → κ => factor (E a) (∏ᶜ fun x : Fin (j+1) => U (t x))) i
  have hm : formDegreeMap f p U (rfl : a=a) j = 𝟙 ((complex (E a) U).X j) :=
    congrArg (fun z : complex (E a) U ⟶ complex (E a) U => z.f j)
      ((complexFunctor U).map_id (E a))
  exact (congrArg (fun z => z ≫ π) hm).trans
    ((Category.id_comp π).trans (Category.comp_id π).symm)

private theorem tensorMap_cup_pi (q r j j' : ℕ) (i : Fin (j+j'+1) → κ)
    {A B : (Y).Modules} (a : A ⟶ (complex (E q) U).X j)
    (b : B ⟶ (complex (E r) U).X j') :
    (tensorMap a b ≫ orderedCup f p U q r j j') ≫
      Pi.π (fun t : Fin (j+j'+1) → κ =>
        factor (E (r+q)) (∏ᶜ fun x : Fin (j+j'+1) => U (t x))) i =
    factorWedgeAlong f p q r (∏ᶜ fun x : Fin (j+j'+1) => U (i x))
      (a ≫ prefixProjection f p U (E q) j j' i)
      (b ≫ suffixProjection f p U (E r) j j' i) := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => tensorMap a b ≫ z) (cup_pi f p U q r j j' i)).trans
      (factorWedgeAlong_tensorMap f p q r (∏ᶜ fun x : Fin (j+j'+1) => U (i x)) a b
        (prefixProjection f p U (E q) j j' i) (suffixProjection f p U (E r) j j' i)))

private theorem post_cast_projection {V : Type*} [Category V] {A B D P F : V}
    (x : A ⟶ B) (c : B ⟶ D) (πD : D ⟶ F) (πB : B ⟶ P) (e : P ⟶ F)
    (hc : c ≫ πD = πB ≫ e) :
    (x ≫ c) ≫ πD = (x ≫ πB) ≫ e := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => x ≫ z) hc).trans (Category.assoc _ _ _).symm)

private theorem postcomp_add_zsmul {V : Type*} [Category V] [Preadditive V]
    {A B D : V} (l r : A ⟶ B) (π : B ⟶ D) (z : ℤ) :
    (l + z • r) ≫ π = l ≫ π + z • (r ≫ π) := by
  rw [add_comp, zsmul_comp]

local notation "d" q => Cartier.SchemeRelativeFrobeniusBasisDifferential.differential f p n q

/-- The entire original ordered cup satisfies the actual pushed de Rham Leibniz rule. -/
theorem cup_derham_leibniz (q r j j' : ℕ) :
    orderedCup f p U q r j j' ≫ ((complexFunctor U).map (d (r+q))).f (j+j') =
    (show CanonicalGeometry.bundleTensor ((complex (E q) U).X j) ((complex (E r) U).X j') ⟶
        (complex (E (r+q+1)) U).X (j+j') from
      tensorMap (((complexFunctor U).map (d q)).f j) (𝟙 ((complex (E r) U).X j')) ≫
        orderedCup f p U (q+1) r j j') +
    (-1 : ℤ)^q •
      (show CanonicalGeometry.bundleTensor ((complex (E q) U).X j) ((complex (E r) U).X j') ⟶
          (complex (E (r+q+1)) U).X (j+j') from
        tensorMap (𝟙 ((complex (E q) U).X j)) (((complexFunctor U).map (d r)).f j') ≫
          orderedCup f p U q (r+1) j j' ≫
            formDegreeMap f p U (show (r+1)+q=r+q+1 by omega) (j+j')) := by
  apply Pi.hom_ext
  intro i
  change Fin (j+j'+1) → κ at i
  let V : (Y).Opens := ∏ᶜ fun x : Fin (j+j'+1) => U (i x)
  let P : (complex (E q) U).X j ⟶ factor (E q) V := prefixProjection f p U (E q) j j' i
  let S : (complex (E r) U).X j' ⟶ factor (E r) V := suffixProjection f p U (E r) j j' i
  let Hq : (complex (E q) U).X j ⟶ (complex (E (q+1)) U).X j :=
    ((complexFunctor U).map (d q)).f j
  let Hr : (complex (E r) U).X j' ⟶ (complex (E (r+1)) U).X j' :=
    ((complexFunctor U).map (d r)).f j'
  let π₀ : (complex (E (r+q)) U).X (j+j') ⟶ factor (E (r+q)) V :=
    Pi.π (fun t : Fin (j+j'+1) → κ =>
      factor (E (r+q)) (∏ᶜ fun x : Fin (j+j'+1) => U (t x))) i
  let π₁ : (complex (E (r+q+1)) U).X (j+j') ⟶ factor (E (r+q+1)) V :=
    Pi.π (fun t : Fin (j+j'+1) → κ =>
      factor (E (r+q+1)) (∏ᶜ fun x : Fin (j+j'+1) => U (t x))) i
  let π₂ : (complex (E ((r+1)+q)) U).X (j+j') ⟶ factor (E ((r+1)+q)) V :=
    Pi.π (fun t : Fin (j+j'+1) → κ =>
      factor (E ((r+1)+q)) (∏ᶜ fun x : Fin (j+j'+1) => U (t x))) i
  let hdeg : (r+1)+q=r+q+1 := by omega
  let e : factor (E ((r+1)+q)) V ⟶ factor (E (r+q+1)) V :=
    eqToHom (congrArg (fun s => factor (E s) V) hdeg)
  let L : CanonicalGeometry.bundleTensor ((complex (E q) U).X j) ((complex (E r) U).X j') ⟶
      (complex (E (r+q+1)) U).X (j+j') :=
    tensorMap Hq (𝟙 ((complex (E r) U).X j')) ≫ orderedCup f p U (q+1) r j j'
  let R : CanonicalGeometry.bundleTensor ((complex (E q) U).X j) ((complex (E r) U).X j') ⟶
      (complex (E (r+q+1)) U).X (j+j') :=
    tensorMap (𝟙 ((complex (E q) U).X j)) Hr ≫ orderedCup f p U q (r+1) j j' ≫
      formDegreeMap f p U hdeg (j+j')
  have hleft : (orderedCup f p U q r j j' ≫
      ((complexFunctor U).map (d (r+q))).f (j+j')) ≫ π₁ =
      factorWedgeAlong f p q r V P S ≫ (factorFunctor V).map (d (r+q)) :=
    (post_cast_projection (orderedCup f p U q r j j')
      (((complexFunctor U).map (d (r+q))).f (j+j')) π₁ π₀
      ((factorFunctor V).map (d (r+q))) (complexMap_pi U (d (r+q)) (j+j') i)).trans
        (congrArg (fun z => z ≫ (factorFunctor V).map (d (r+q))) (cup_pi f p U q r j j' i))
  have hfirst : L ≫ π₁ = factorWedgeAlong f p (q+1) r V
      (P ≫ (factorFunctor V).map (d q)) S :=
    (tensorMap_cup_pi f p U (q+1) r j j' i Hq (𝟙 ((complex (E r) U).X j'))).trans
      (congrArg₂ (fun a b => factorWedgeAlong f p (q+1) r V a b)
        (prefixProjection_naturality f p U (d q) j j' i) (Category.id_comp S))
  have hbase : (tensorMap (𝟙 ((complex (E q) U).X j)) Hr ≫
      orderedCup f p U q (r+1) j j') ≫ π₂ =
      factorWedgeAlong f p q (r+1) V P (S ≫ (factorFunctor V).map (d r)) :=
    (tensorMap_cup_pi f p U q (r+1) j j' i (𝟙 ((complex (E q) U).X j)) Hr).trans
      (congrArg₂ (fun a b => factorWedgeAlong f p q (r+1) V a b)
        (Category.id_comp P) (suffixProjection_naturality f p U (d r) j j' i))
  have hsecond : R ≫ π₁ =
      factorWedgeAlong f p q (r+1) V P (S ≫ (factorFunctor V).map (d r)) ≫ e :=
    (post_cast_projection
      (tensorMap (𝟙 ((complex (E q) U).X j)) Hr ≫ orderedCup f p U q (r+1) j j')
      (formDegreeMap f p U hdeg (j+j')) π₁ π₂ e (formDegreeMap_pi f p U hdeg (j+j') i)).trans
        (congrArg (fun z => z ≫ e) hbase)
  have hf := factorWedgeAlong_differential f p n q r V P S
  exact hleft.trans (hf.trans
    ((congrArg₂ (fun a b => a + (-1 : ℤ)^q • b) hfirst.symm hsecond.symm).trans
      (postcomp_add_zsmul L R π₁ ((-1 : ℤ)^q)).symm))

end EnvelopeProperty.DI.CechAlexanderWhitneyProduct
