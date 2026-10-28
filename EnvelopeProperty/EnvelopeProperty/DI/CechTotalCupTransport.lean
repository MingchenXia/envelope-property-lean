import EnvelopeProperty.DI.CechTotalCup
import EnvelopeProperty.DI.CechCupLeibniz
import EnvelopeProperty.DI.CechCupDeRhamLeibniz

/-! # Original differential and equality transports of native total inclusions -/
noncomputable section
namespace EnvelopeProperty.DI.CechTotalCup
open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.Preadditive
universe u
private theorem unitSign_smul {A : Type*} [AddCommGroup A] (q : ℕ) (x : A) :
    ((-1 : ℤˣ)^q) • x = ((-1 : ℤ)^q) • x :=
  (Units.smul_def ((-1 : ℤˣ)^q) x).trans
    (congrArg (fun z : ℤ => z • x) (Units.val_pow_eq_pow_val (a := (-1 : ℤˣ)) q))

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
variable (n : ℕ) [SmoothOfRelativeDimension n f]
variable {ι : Type u}
variable (U : ι → (Cartier.SchemeRelativeFrobenius.twist p f).Opens)
local notation "Y" => Cartier.SchemeRelativeFrobenius.twist p f
local notation "E" q => Cartier.SchemeRelativeFrobeniusDeRham.formModule f p q
local notation "K" => Cartier.SchemeRelativeFrobeniusBasisDifferential.complex f p n
local notation "C" => Cartier.DeligneIllusieLocalContinuationCechBicomplex.bicomplex U K
local notation "T" => Cartier.DeligneIllusieLocalContinuationCechTotalAugmentation.totalComplex U K

/-- The original total differential formula at every genuine input total index,
with the original native unit sign expressed as its same integer action. -/
theorem totalInclusion_d (q j a : ℕ) (ha : q+j=a) :
    HomologicalComplex₂.ιTotal (C) (.up ℕ) q j a ha ≫ (T).d a (a+1) =
    (show ((C).X q).X j ⟶ (T).X (a+1) from
      ((C).d q (q+1)).f j ≫
        HomologicalComplex₂.ιTotal (C) (.up ℕ) (q+1) j (a+1)
          (by change q+1+j=a+1; omega)) +
    ((-1 : ℤ)^q) •
      (show ((C).X q).X j ⟶ (T).X (a+1) from
        ((C).X q).d j (j+1) ≫
          HomologicalComplex₂.ιTotal (C) (.up ℕ) q (j+1) (a+1)
            (by change q+(j+1)=a+1; omega)) := by
  subst a
  let d₁ : ((C).X q).X j ⟶ (T).X (q+j+1) :=
    ((C).d q (q+1)).f j ≫
      HomologicalComplex₂.ιTotal (C) (.up ℕ) (q+1) j (q+j+1)
        (by change q+1+j=q+j+1; omega)
  let d₂ : ((C).X q).X j ⟶ (T).X (q+j+1) :=
    ((C).X q).d j (j+1) ≫
      HomologicalComplex₂.ιTotal (C) (.up ℕ) q (j+1) (q+j+1)
        (by change q+(j+1)=q+j+1; omega)
  exact (HomologicalComplex₂.ιTotal_d_upNat (C) q j).trans
    (congrArg (fun z => d₁ + z) (unitSign_smul q d₂))

/-- The original equality morphism on the original total-complex term family. -/
def totalDegreeMap {a b : ℕ} (h : a=b) : (T).X a ⟶ (T).X b :=
  eqToHom (congrArg (fun i => (T).X i) h)

/-- Native total inclusion followed by original total-degree transport is the original inclusion. -/
theorem totalDegreeMap_ιTotal (q j a b : ℕ) (ha : q+j=a) (h : a=b) :
    HomologicalComplex₂.ιTotal (C) (.up ℕ) q j a ha ≫ totalDegreeMap f p n U h =
      HomologicalComplex₂.ιTotal (C) (.up ℕ) q j b (ha.trans h) := by
  cases h
  exact Category.comp_id (HomologicalComplex₂.ιTotal (C) (.up ℕ) q j a ha)

/-- Original Cech-degree transport before native total inclusion retains the same summand. -/
theorem degreeMap_ιTotal (q a b N : ℕ) (h : a=b) (hb : q+b=N) :
    CechAlexanderWhitneyProduct.degreeMap U (E q) h ≫
      HomologicalComplex₂.ιTotal (C) (.up ℕ) q b N hb =
    HomologicalComplex₂.ιTotal (C) (.up ℕ) q a N ((congrArg (fun x => q+x) h).trans hb) := by
  cases h
  exact Category.id_comp (HomologicalComplex₂.ιTotal (C) (.up ℕ) q a N hb)

/-- Original form-degree transport before native total inclusion retains the same summand. -/
theorem formDegreeMap_ιTotal (q q' j N : ℕ) (h : q=q') (hN : q'+j=N) :
    CechAlexanderWhitneyProduct.formDegreeMap f p U h j ≫
      HomologicalComplex₂.ιTotal (C) (.up ℕ) q' j N hN =
    HomologicalComplex₂.ιTotal (C) (.up ℕ) q j N ((congrArg (fun x => x+j) h).trans hN) := by
  cases h
  have hm : CechAlexanderWhitneyProduct.formDegreeMap f p U (rfl : q=q) j =
      𝟙 ((Cartier.DeligneIllusieLocalContinuationCechModules.complex (E q) U).X j) :=
    congrArg (fun z : Cartier.DeligneIllusieLocalContinuationCechModules.complex (E q) U ⟶
      Cartier.DeligneIllusieLocalContinuationCechModules.complex (E q) U => z.f j)
      ((Cartier.DeligneIllusieLocalContinuationCechAugmentation.complexFunctor U).map_id (E q))
  exact (congrArg (fun z => z ≫ HomologicalComplex₂.ιTotal (C) (.up ℕ) q j N hN) hm).trans
    (Category.id_comp (HomologicalComplex₂.ιTotal (C) (.up ℕ) q j N hN))

end EnvelopeProperty.DI.CechTotalCup
