import EnvelopeProperty.DI.CechAlexanderWhitneyFactors

/-! # The actual ordered product on the original native sheaf Čech terms -/

noncomputable section
universe u
namespace EnvelopeProperty.DI.CechAlexanderWhitneyProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
open Cartier.DeligneIllusieLocalContinuationCechModules
open Cartier.DeligneIllusieCechCupProduct

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Y" => Cartier.SchemeRelativeFrobenius.twist p f
local notation "E" q => Cartier.SchemeRelativeFrobeniusDeRham.formModule f p q

variable {κ : Type u} (V : κ → Scheme.Opens (Cartier.SchemeRelativeFrobenius.twist p f))

/-- The actual native prefix projection followed by restriction to the full tuple. -/
def prefixProjection (M : (Y).Modules) (j j' : ℕ) (i : Fin (j+j'+1) → κ) :
    (complex M V).X j ⟶ factor M (∏ᶜ fun a : Fin (j+j'+1) => V (i a)) :=
  Pi.π (fun t : Fin (j+1) → κ => factor M (∏ᶜ fun a : Fin (j+1) => V (t a)))
    (i ∘ tuplePrefix j j') ≫ factorMap M (tupleOpen_le_prefix V j j' i)

/-- The actual native suffix projection followed by restriction to the full tuple. -/
def suffixProjection (M : (Y).Modules) (j j' : ℕ) (i : Fin (j+j'+1) → κ) :
    (complex M V).X j' ⟶ factor M (∏ᶜ fun a : Fin (j+j'+1) => V (i a)) :=
  Pi.π (fun t : Fin (j'+1) → κ => factor M (∏ᶜ fun a : Fin (j'+1) => V (t a)))
    (i ∘ tupleSuffix j j') ≫ factorMap M (tupleOpen_le_suffix V j j' i)

/-- The actual ordered Alexander--Whitney cup on the SAME published sheaf
Čech terms. Its two original tuples meet at their shared joining vertex. -/
def orderedCup (q r j j' : ℕ) :
    CanonicalGeometry.bundleTensor ((complex (E q) V).X j) ((complex (E r) V).X j') ⟶
      (complex (E (r+q)) V).X (j+j') := by
  exact Pi.lift (fun i : Fin (j+j'+1) → κ =>
    factorWedgeAlong f p q r (∏ᶜ fun a : Fin (j+j'+1) => V (i a))
      (prefixProjection f p V (E q) j j' i)
      (suffixProjection f p V (E r) j j' i))

/-- Every output tuple of the ACTUAL sheaf Čech cup has precisely the original
prefix/suffix restriction--wedge formula. -/
theorem cup_pi (q r j j' : ℕ) (i : Fin (j+j'+1) → κ) :
    orderedCup f p V q r j j' ≫
        Pi.π (fun t : Fin (j+j'+1) → κ =>
          factor (E (r+q)) (∏ᶜ fun a : Fin (j+j'+1) => V (t a))) i =
      factorWedgeAlong f p q r (∏ᶜ fun a : Fin (j+j'+1) => V (i a))
        (prefixProjection f p V (E q) j j' i)
        (suffixProjection f p V (E r) j j' i) :=
  Pi.lift_π _ i

/-- Every native cup projection on EVERY pair of whole original sections is
precisely the original exterior product after its actual prefix/suffix restrictions. -/
theorem cup_tensorSection_pi (q r j j' : ℕ) (i : Fin (j+j'+1) → κ) (W : (Y).Opens)
    (x : Γ((complex (E q) V).X j,W)) (y : Γ((complex (E r) V).X j',W)) :
    (Pi.π (fun t : Fin (j+j'+1) → κ =>
        factor (E (r+q)) (∏ᶜ fun a : Fin (j+j'+1) => V (t a))) i).val.app (op W)
      ((orderedCup f p V q r j j').val.app (op W)
        (CanonicalGeometry.tensorSection ((complex (E q) V).X j)
          ((complex (E r) V).X j') W x y)) =
      formWedge f p q r (factorCut (∏ᶜ fun a : Fin (j+j'+1) => V (i a)) W)
        ((prefixProjection f p V (E q) j j' i).val.app (op W) x)
        ((suffixProjection f p V (E r) j j' i).val.app (op W) y) := by
  have h := congrArg
    (fun z => z.val.app (op W)
      (CanonicalGeometry.tensorSection ((complex (E q) V).X j)
        ((complex (E r) V).X j') W x y)) (cup_pi f p V q r j j' i)
  exact h.trans ((factorWedgeAlong_tensorSection f p q r
    (∏ᶜ fun a : Fin (j+j'+1) => V (i a)) W
    (prefixProjection f p V (E q) j j' i) (suffixProjection f p V (E r) j j' i) x y).trans
      (factorWedge_apply f p q r (∏ᶜ fun a : Fin (j+j'+1) => V (i a)) W _ _))

end EnvelopeProperty.DI.CechAlexanderWhitneyProduct
