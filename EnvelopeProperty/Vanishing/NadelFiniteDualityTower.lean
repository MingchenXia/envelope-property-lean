import EnvelopeProperty.Vanishing.NadelFiniteDualityTowerCore

/-! # The actual native dual frame of two successive original monic roots

The second coefficient lies in the actual first root algebra.  Both native
single-root dual frames and the canonical coextension-composition comparison
are constructed internally.  No tower duality identification is an input.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelFiniteDualityTower

open CategoryTheory ModuleCat Module
open NadelFiniteDuality CyclicSectionPowerBasis

universe u
variable {R : Type u} [CommRing R] [Nontrivial R]

/-- The original positive-degree monic root algebra is nontrivial by its actual finite power basis. -/
theorem root_nontrivial (n : ℕ) (a : R) : Nontrivial (Root n a) :=
  (basis (n + 1) a (Nat.succ_pos n)).equivFun.toEquiv.nontrivial

attribute [local instance] root_nontrivial

/-- The literal composite of the original two monic-root coefficient homomorphisms. -/
def twoRootStructure (n : ℕ) (a : R) (m : ℕ) (b : Root n a) :
    R →+* Root m b :=
  (algebraMap (Root n a) (Root m b)).comp (algebraMap R (Root n a))

/-- The entire second root algebra is its actual native coextension dual over the original base. -/
def twoRootIso (n : ℕ) (a : R) (m : ℕ) (b : Root n a) :
    ModuleCat.of (Root m b) (Root m b) ≅
      (coextendScalars (twoRootStructure n a m b)).obj (ModuleCat.of R R) :=
  dualizingIso m b ≪≫
    (coextendScalars (algebraMap (Root n a) (Root m b))).mapIso (dualizingIso n a) ≪≫
      (coextensionCompIso (algebraMap R (Root n a))
        (algebraMap (Root n a) (Root m b))).app (ModuleCat.of R R)

/-- The whole native tower dual frame is multiplication against the original composite coefficients. -/
theorem twoRootIso_hom_apply (n : ℕ) (a : R) (m : ℕ) (b : Root n a)
    (x y : Root m b) :
    (twoRootIso n a m b).hom x y =
      topCoefficient n a (topCoefficient m b (y * x)) := by
  change (coextensionCompIso (algebraMap R (Root n a))
    (algebraMap (Root n a) (Root m b))).hom.app (ModuleCat.of R R)
      ((coextendScalars (algebraMap (Root n a) (Root m b))).map (dualizingIso n a).hom
        ((dualizingIso m b).hom x)) y = _
  rw [coextensionCompIso_hom_apply]
  change topCoefficient n a (topCoefficient m b (x * y) * 1) = _
  rw [mul_one, mul_comm x y]

/-- The native counit over the actual composite coefficient map is the composed top coefficient. -/
theorem twoRootIso_counit (n : ℕ) (a : R) (m : ℕ) (b : Root n a) (x : Root m b) :
    (restrictCoextendScalarsAdj (twoRootStructure n a m b)).counit.app (ModuleCat.of R R)
        ((twoRootIso n a m b).hom x) =
      topCoefficient n a (topCoefficient m b x) := by
  change (twoRootIso n a m b).hom x (1 : Root m b) = _
  rw [twoRootIso_hom_apply, one_mul]

end EnvelopeProperty.Vanishing.NadelFiniteDualityTower
