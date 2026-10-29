import EnvelopeProperty.Vanishing.NadelFiniteDualityTower
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! # Actual finite independent-root towers over the same original coefficient ring

Every stage and coefficient homomorphism is constructed from the original ring,
positive root degrees, and original coefficients.  The full coextension frame
and composite-coefficient counit are proved by finite induction.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelFiniteDualityTower

open CategoryTheory ModuleCat
open NadelFiniteDuality

universe u
variable {R : Type u} [CommRing R]

/-- The actual finite stages obtained by adjoining the original independent coefficients. -/
def independentRootStage (degree : ℕ → ℕ) (coefficient : ℕ → R) :
    ℕ → Under (CommRingCat.of R)
  | 0 => Under.mk (𝟙 (CommRingCat.of R))
  | k + 1 =>
    let B := independentRootStage degree coefficient k
    Under.mk (B.hom ≫ CommRingCat.ofHom
      (algebraMap B.right (Root (degree k) (B.hom (coefficient k)))))

/-- The literal ring at a constructed independent-root stage. -/
abbrev independentRootRing (degree : ℕ → ℕ) (coefficient : ℕ → R) (k : ℕ) : CommRingCat :=
  (independentRootStage degree coefficient k).right

/-- The actual original coefficient homomorphism into the constructed stage. -/
def independentRootStructure (degree : ℕ → ℕ) (coefficient : ℕ → R) (k : ℕ) :
    R →+* independentRootRing degree coefficient k :=
  (independentRootStage degree coefficient k).hom.hom

/-- The actual one-step coefficient homomorphism of the same constructed tower. -/
def independentRootStep (degree : ℕ → ℕ) (coefficient : ℕ → R) (k : ℕ) :
    independentRootRing degree coefficient k →+* independentRootRing degree coefficient (k + 1) :=
  algebraMap (independentRootRing degree coefficient k)
    (Root (degree k) (independentRootStructure degree coefficient k (coefficient k)))

/-- Each new original coefficient homomorphism is literally the composition of the old maps. -/
theorem independentRootStructure_succ (degree : ℕ → ℕ) (coefficient : ℕ → R) (k : ℕ) :
    independentRootStructure degree coefficient (k + 1) =
      (independentRootStep degree coefficient k).comp
        (independentRootStructure degree coefficient k) := rfl

variable [Nontrivial R]

/-- Nontriviality of every actual finite stage follows internally from its original monic bases. -/
theorem independentRootRing_nontrivial (degree : ℕ → ℕ) (coefficient : ℕ → R) :
    ∀ k, Nontrivial (independentRootRing degree coefficient k)
  | 0 => inferInstanceAs (Nontrivial R)
  | k + 1 =>
    letI := independentRootRing_nontrivial degree coefficient k
    root_nontrivial (degree k) (independentRootStructure degree coefficient k (coefficient k))

/-- The actual composite of the original successive top-coefficient functionals. -/
def independentTopCoefficient (degree : ℕ → ℕ) (coefficient : ℕ → R) :
    ∀ k, independentRootRing degree coefficient k → R
  | 0 => fun x => x
  | k + 1 =>
    letI := independentRootRing_nontrivial degree coefficient k
    fun x => independentTopCoefficient degree coefficient k
      (topCoefficient (degree k) (independentRootStructure degree coefficient k (coefficient k)) x)

/-- Every whole finite root stage is its actual coextension dual over the same original ring. -/
def independentRootIso (degree : ℕ → ℕ) (coefficient : ℕ → R) :
    ∀ k, ModuleCat.of (independentRootRing degree coefficient k)
        (independentRootRing degree coefficient k) ≅
      (coextendScalars (independentRootStructure degree coefficient k)).obj (ModuleCat.of R R)
  | 0 => (coextensionIdIso R).symm.app (ModuleCat.of R R)
  | k + 1 => by
    letI := independentRootRing_nontrivial degree coefficient k
    exact dualizingIso (degree k) (independentRootStructure degree coefficient k (coefficient k)) ≪≫
      (coextendScalars (independentRootStep degree coefficient k)).mapIso
        (independentRootIso degree coefficient k) ≪≫
      (coextensionCompIso (independentRootStructure degree coefficient k)
        (independentRootStep degree coefficient k)).app (ModuleCat.of R R)

/-- The whole actual finite-stage frame is multiplication against the original composite coefficient. -/
theorem independentRootIso_hom_apply (degree : ℕ → ℕ) (coefficient : ℕ → R)
    (k : ℕ) (x y : independentRootRing degree coefficient k) :
    (independentRootIso degree coefficient k).hom x y =
      independentTopCoefficient degree coefficient k (y * x) := by
  induction k with
  | zero =>
    change (coextensionIdIso R).inv.app (ModuleCat.of R R) x y = y * x
    exact coextensionIdIso_inv_apply (ModuleCat.of R R) x y
  | succ k ih =>
    let := independentRootRing_nontrivial degree coefficient k
    change (coextensionCompIso (independentRootStructure degree coefficient k)
      (independentRootStep degree coefficient k)).hom.app (ModuleCat.of R R)
        ((coextendScalars (independentRootStep degree coefficient k)).map
          (independentRootIso degree coefficient k).hom
          ((dualizingIso (degree k)
            (independentRootStructure degree coefficient k (coefficient k))).hom x)) y = _
    rw [coextensionCompIso_hom_apply]
    change (independentRootIso degree coefficient k).hom
      ((dualizingIso (degree k)
        (independentRootStructure degree coefficient k (coefficient k))).hom x y)
      (1 : independentRootRing degree coefficient k) = _
    rw [ih]
    change independentTopCoefficient degree coefficient k
      (1 * topCoefficient (degree k)
        (independentRootStructure degree coefficient k (coefficient k)) (x * y)) =
      independentTopCoefficient degree coefficient k
        (topCoefficient (degree k)
          (independentRootStructure degree coefficient k (coefficient k)) (y * x))
    rw [one_mul, mul_comm x y]

/-- The original native finite-stage counit is the same composite top coefficient. -/
theorem independentRootIso_counit (degree : ℕ → ℕ) (coefficient : ℕ → R)
    (k : ℕ) (x : independentRootRing degree coefficient k) :
    (restrictCoextendScalarsAdj (independentRootStructure degree coefficient k)).counit.app
        (ModuleCat.of R R) ((independentRootIso degree coefficient k).hom x) =
      independentTopCoefficient degree coefficient k x := by
  change (independentRootIso degree coefficient k).hom x
    (1 : independentRootRing degree coefficient k) = _
  rw [independentRootIso_hom_apply, one_mul]

end EnvelopeProperty.Vanishing.NadelFiniteDualityTower
