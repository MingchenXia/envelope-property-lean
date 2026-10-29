import EnvelopeProperty.DI.CechWholeSectionLeibniz
import EnvelopeProperty.DI.CechCupNaturality

/-!
# Čech Factor De Rham Leibniz

The actual whole-map de Rham rule on the original Cech factor. -/
noncomputable section
namespace EnvelopeProperty.DI.CechAlexanderWhitneyProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open CategoryTheory.Limits
open Cartier.DeligneIllusieLocalContinuationCechModules
open Cartier.DeligneIllusieLocalContinuationCechAugmentation
open Cartier.DeligneIllusieCechCupProduct

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem hom_zsmul_app {Z : Scheme.{u}} {M N : Z.Modules}
    (c : ℤ) (a : M ⟶ N) (W : Z.Opens) (s : Γ(M,W)) :
    (c • a).val.app (op W) s = c • a.val.app (op W) s := by
  have h : (c • a).val = c • a.val :=
    Functor.map_zsmul (SheafOfModules.forget Z.ringCatSheaf)
  rw [h, PresheafOfModules.zsmul_app]
  rfl

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Y" => Cartier.SchemeRelativeFrobenius.twist p f
local notation "E" q => Cartier.SchemeRelativeFrobeniusDeRham.formModule f p q

private theorem factorDegreeCast_app {a b : ℕ} (h : a = b)
    (V W : (Y).Opens) (s : Γ(factor (E a) V,W)) :
    (eqToHom (congrArg (fun q => factor (E q) V) h)).val.app (op W) s =
      CechWholeSectionLeibniz.degreeCast f p h (factorCut V W) s := by
  cases h
  rfl

variable (n : ℕ) [SmoothOfRelativeDimension n f]
local notation "d" q => Cartier.SchemeRelativeFrobeniusBasisDifferential.differential f p n q

/-- The entire original factor pairing satisfies the actual de Rham Leibniz rule. -/
theorem factorWedgeAlong_differential (q r : ℕ) (V : (Y).Opens)
    {A B : (Y).Modules} (a : A ⟶ factor (E q) V) (b : B ⟶ factor (E r) V) :
    factorWedgeAlong f p q r V a b ≫ (factorFunctor V).map (d (r+q)) =
      (show CanonicalGeometry.bundleTensor A B ⟶ factor (E (r+q+1)) V from
        factorWedgeAlong f p (q+1) r V (a ≫ (factorFunctor V).map (d q)) b) +
      (-1 : ℤ)^q •
        (factorWedgeAlong f p q (r+1) V a (b ≫ (factorFunctor V).map (d r)) ≫
          eqToHom (congrArg (fun s => factor (E s) V)
            (show (r+1)+q = r+q+1 by omega))) := by
  apply tensorSection_hom_ext
  intro W x y
  change (factorWedgeAlong f p q r V a b ≫ (factorFunctor V).map (d (r+q))).val.app
      (op W) (CanonicalGeometry.tensorSection A B W x y) =
    (factorWedgeAlong f p (q+1) r V (a ≫ (factorFunctor V).map (d q)) b).val.app
        (op W) (CanonicalGeometry.tensorSection A B W x y) +
      ((-1 : ℤ)^q •
        (factorWedgeAlong f p q (r+1) V a (b ≫ (factorFunctor V).map (d r)) ≫
          eqToHom (congrArg (fun s => factor (E s) V)
            (show (r+1)+q = r+q+1 by omega)))).val.app (op W)
              (CanonicalGeometry.tensorSection A B W x y)
  rw [hom_zsmul_app]
  change ((factorFunctor V).map (d (r+q))).val.app (op W)
      ((factorWedgeAlong f p q r V a b).val.app (op W)
        (CanonicalGeometry.tensorSection A B W x y)) =
    (factorWedgeAlong f p (q+1) r V (a ≫ (factorFunctor V).map (d q)) b).val.app (op W)
        (CanonicalGeometry.tensorSection A B W x y) +
      (-1 : ℤ)^q •
        (eqToHom (congrArg (fun s => factor (E s) V)
          (show (r+1)+q = r+q+1 by omega))).val.app (op W)
          ((factorWedgeAlong f p q (r+1) V a (b ≫ (factorFunctor V).map (d r))).val.app (op W)
            (CanonicalGeometry.tensorSection A B W x y))
  rw [factorWedgeAlong_tensorSection, factorWedgeAlong_tensorSection,
    factorWedgeAlong_tensorSection, factorDegreeCast_app]
  change (d (r+q)).val.app (op (factorCut V W))
      (formWedge f p q r (factorCut V W) (a.val.app (op W) x) (b.val.app (op W) y)) =
    (show Γ(E (r+q+1),factorCut V W) from
      formWedge f p (q+1) r (factorCut V W)
        ((d q).val.app (op (factorCut V W)) (a.val.app (op W) x)) (b.val.app (op W) y)) +
      (-1 : ℤ)^q • CechWholeSectionLeibniz.degreeCast f p
        (show (r+1)+q = r+q+1 by omega) (factorCut V W)
          (formWedge f p q (r+1) (factorCut V W) (a.val.app (op W) x)
            ((d r).val.app (op (factorCut V W)) (b.val.app (op W) y)))
  exact CechWholeSectionLeibniz.formWedge_differential f p n q r (factorCut V W)
    (a.val.app (op W) x) (b.val.app (op W) y)

end EnvelopeProperty.DI.CechAlexanderWhitneyProduct
