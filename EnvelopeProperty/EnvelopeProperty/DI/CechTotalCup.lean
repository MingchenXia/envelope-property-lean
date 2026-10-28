import EnvelopeProperty.DI.CechAlexanderWhitneyProduct
import EnvelopeProperty.DI.CechCupNaturality
import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusBasisDifferential
import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechTotalAugmentation
import ModularCurves.ForMathlib.TotalComplexUpNatDecomposition

/-! # Actual finite total cup and its whole original section pairing -/
noncomputable section
namespace EnvelopeProperty.DI.CechTotalCup
open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.Preadditive
open scoped BigOperators
universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
variable (n : ℕ) [SmoothOfRelativeDimension n f]
variable {ι : Type u}
variable (U : ι → (Cartier.SchemeRelativeFrobenius.twist p f).Opens)

local notation "Y" => Cartier.SchemeRelativeFrobenius.twist p f
local notation "K" => Cartier.SchemeRelativeFrobeniusBasisDifferential.complex f p n
local notation "C" => Cartier.DeligneIllusieLocalContinuationCechBicomplex.bicomplex U K
local notation "T" => Cartier.DeligneIllusieLocalContinuationCechTotalAugmentation.totalComplex U K

/-- A signed original bidegree component of the actual total cup. -/
def totalCupComponent {a b : ℕ} (s : _root_.Finset.HasAntidiagonal.antidiagonal a) (t : _root_.Finset.HasAntidiagonal.antidiagonal b) :
    CanonicalGeometry.bundleTensor ((T).X a) ((T).X b) ⟶ (T).X (a+b) :=
  ((-1 : ℤ) ^ (s.val.2 * t.val.1)) •
    (CechAlexanderWhitneyProduct.tensorMap
        (HomologicalComplex₂.πTotalUpNat (C) s.val.1 s.val.2 a)
        (HomologicalComplex₂.πTotalUpNat (C) t.val.1 t.val.2 b) ≫
      CechAlexanderWhitneyProduct.orderedCup f p U s.val.1 t.val.1 s.val.2 t.val.2 ≫
      HomologicalComplex₂.ιTotal (C) (.up ℕ) (t.val.1+s.val.1) (s.val.2+t.val.2) (a+b)
        (by
          have hs := _root_.Finset.HasAntidiagonal.mem_antidiagonal.mp s.property
          have ht := _root_.Finset.HasAntidiagonal.mem_antidiagonal.mp t.property
          change (t.val.1+s.val.1)+(s.val.2+t.val.2) = a+b
          omega))

/-- The finite signed sum of the actual ordered products on the original total complex. -/
def totalCup (a b : ℕ) :
    CanonicalGeometry.bundleTensor ((T).X a) ((T).X b) ⟶ (T).X (a+b) :=
  ∑ s : _root_.Finset.HasAntidiagonal.antidiagonal a, ∑ t : _root_.Finset.HasAntidiagonal.antidiagonal b,
    totalCupComponent f p n U s t

private def sectionPairing {Z : Scheme.{u}} {A B D : Z.Modules}
    (φ : CanonicalGeometry.bundleTensor A B ⟶ D) (W : Z.Opens) :
    Γ(A,W) →ₗ[Γ(Z,W)] Γ(B,W) →ₗ[Γ(Z,W)] Γ(D,W) := by
  refine LinearMap.mk₂ Γ(Z,W)
    (fun (x : Γ(A,W)) (y : Γ(B,W)) =>
      φ.val.app (op W) (CanonicalGeometry.tensorSection (X := Z) A B W x y)) ?_ ?_ ?_ ?_
  · intro x x' y
    exact (congrArg (φ.val.app (op W))
      (CanonicalGeometry.tensorSection_add_left A B W x x' y)).trans
        ((φ.val.app (op W)).hom.map_add _ _)
  · intro r x y
    exact (congrArg (φ.val.app (op W))
      (CanonicalGeometry.tensorSection_smul_left A B W r x y)).trans
        ((φ.val.app (op W)).hom.map_smul r _)
  · intro x y y'
    exact (congrArg (φ.val.app (op W))
      (CanonicalGeometry.tensorSection_add_right A B W x y y')).trans
        ((φ.val.app (op W)).hom.map_add _ _)
  · intro r x y
    exact (congrArg (φ.val.app (op W))
      (CanonicalGeometry.tensorSection_smul_right A B W r x y)).trans
        ((φ.val.app (op W)).hom.map_smul r _)

/-- The entire original section pairing induced by the actual total cup sheaf morphism. -/
def totalCupSection (a b : ℕ) (W : (Y).Opens) :
    Γ((T).X a,W) →ₗ[Γ(Y,W)] Γ((T).X b,W) →ₗ[Γ(Y,W)] Γ((T).X (a+b),W) :=
  sectionPairing (Z := Y) (totalCup f p n U a b) W

/-- This whole pairing uses the original tensor section on every section pair. -/
theorem totalCupSection_tensorSection (a b : ℕ) (W : (Y).Opens)
    (x : Γ((T).X a,W)) (y : Γ((T).X b,W)) :
    totalCupSection f p n U a b W x y =
      (totalCup f p n U a b).val.app (op W)
        (CanonicalGeometry.tensorSection (X := Y) ((T).X a) ((T).X b) W x y) := rfl

/-- The actual total cup pairing commutes with original restriction on all sections. -/
theorem totalCupSection_restrict (a b : ℕ) {V W : (Y).Opens} (i : V ⟶ W)
    (x : Γ((T).X a,W)) (y : Γ((T).X b,W)) :
    ((T).X (a+b)).val.map i.op (totalCupSection f p n U a b W x y) =
      totalCupSection f p n U a b V (((T).X a).val.map i.op x) (((T).X b).val.map i.op y) := by
  change ((T).X (a+b)).val.map i.op
      ((totalCup f p n U a b).val.app (op W)
        (CanonicalGeometry.tensorSection (X := Y) ((T).X a) ((T).X b) W x y)) =
    (totalCup f p n U a b).val.app (op V)
      (CanonicalGeometry.tensorSection (X := Y) ((T).X a) ((T).X b) V
        (((T).X a).val.map i.op x) (((T).X b).val.map i.op y))
  have h := PresheafOfModules.naturality_apply (totalCup f p n U a b).val i.op
    (CanonicalGeometry.tensorSection (X := Y) ((T).X a) ((T).X b) W x y)
  exact h.symm.trans (congrArg ((totalCup f p n U a b).val.app (op V))
    (CanonicalGeometry.tensorSection_restrict (X := Y) ((T).X a) ((T).X b) i x y))

end EnvelopeProperty.DI.CechTotalCup
