import EnvelopeProperty.Global.FibreInfinitesimalH0

/-!
# Genuine original ideal-power inclusions and coefficient multiplication

All morphisms act on the actual original whole ideal-module sections.
They retain the literal original underlying functions and coefficient
sections on every original open, with no comparison premise.
-/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace EnvelopeProperty.FibreIdealPowerTransitions

variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

private theorem inclusion_zero {n m : ℕ} (h : n ≤ m) :
    (FibreIdealPowers.extendedPower I f m).toModulesInclusion ≫
      FibreInfinitesimalModules.sectionMap I f n = 0 := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  apply (FibreInfinitesimalModules.projection_isLocallyMem_iff I f n W s.1).mp
  intro U hUW
  have hs := s.2 U hUW
  rw [FibreIdealPowers.extendedPower_ideal] at hs ⊢
  exact Ideal.pow_le_pow_right h hs

/-- The actual whole original module inclusion from EVERY higher ideal
power to EVERY lower ideal power, retaining its literal original sections. -/
def inclusion {n m : ℕ} (h : n ≤ m) :
    FibreIdealPowers.powerModule I f m ⟶ FibreIdealPowers.powerModule I f n :=
  FibreInfinitesimalModules.kernelLift I f n
    (FibreIdealPowers.extendedPower I f m).toModulesInclusion (inclusion_zero I f h)

/-- On EVERY original open the whole ideal-power inclusion retains
EVERY underlying original section. -/
theorem inclusion_app {n m : ℕ} (h : n ≤ m) (W : X.Opens)
    (s : Γ(FibreIdealPowers.powerModule I f m, W)) :
    ((inclusion I f h).app W s).1 = s.1 := rfl

/-- The original higher-to-lower inclusion followed by the actual lower
power inclusion is the ENTIRE original higher-power inclusion. -/
theorem inclusion_inclusion {n m : ℕ} (h : n ≤ m) :
    inclusion I f h ≫ (FibreIdealPowers.extendedPower I f n).toModulesInclusion =
      (FibreIdealPowers.extendedPower I f m).toModulesInclusion :=
  FibreInfinitesimalModules.kernelLift_inclusion I f n _ _

/-- The actual original equal-order ideal-power inclusion is the whole identity. -/
theorem inclusion_self (n : ℕ) : inclusion I f (le_refl n) = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  rfl

/-- All actual original ideal-power inclusions obey whole scheme-module composition. -/
theorem inclusion_comp {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) :
    inclusion I f hmk ≫ inclusion I f hnm = inclusion I f (hnm.trans hmk) := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  rfl

private theorem coefficient_restriction {U V : X.Opens} (h : U ≤ V) (r : R) :
    X.presheaf.map (homOfLE h).op (sectionsHom f V r) = sectionsHom f U r := by
  change X.presheaf.map (homOfLE h).op
    (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
      (ProperBirationalSections.coefficientMap f r)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Multiplication on the actual whole structure module by the SAME
original coefficient, on every original open and section. -/
def coefficientEnd (r : R) :
    SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf where
  val := PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom
        { toFun := fun s => sectionsHom f W.unop r * (show Γ(X, W.unop) from s)
          map_zero' := by
            change sectionsHom f W.unop r * (0 : Γ(X, W.unop)) = 0
            exact mul_zero _
          map_add' := by
            intro s t
            change sectionsHom f W.unop r *
                ((show Γ(X, W.unop) from s) + (show Γ(X, W.unop) from t)) = _
            exact mul_add _ _ _ }
      naturality {U V} h := by
        ext s
        change sectionsHom f V.unop r * X.presheaf.map h (show Γ(X, U.unop) from s) =
          X.presheaf.map h (sectionsHom f U.unop r * (show Γ(X, U.unop) from s))
        rw [map_mul]
        congr 1
        exact (coefficient_restriction f h.unop.le r).symm }
    (by
      intro W a s
      change sectionsHom f W.unop r *
          ((show Γ(X, W.unop) from a) * (show Γ(X, W.unop) from s)) =
        (show Γ(X, W.unop) from a) *
          (sectionsHom f W.unop r * (show Γ(X, W.unop) from s))
      exact mul_left_comm _ _ _)

/-- The original coefficient endomorphism is multiplication by its literal
original section on the ENTIRE original open. -/
theorem coefficientEnd_app (r : R) (W : X.Opens) (s : Γ(X, W)) :
    (show Γ(X, W) from (coefficientEnd f r).val.app (op W) s) =
      sectionsHom f W r * s := rfl

private theorem multiplication_zero {e : ℕ} (a : ↥(I^e)) (d : ℕ) :
    ((FibreIdealPowers.extendedPower I f d).toModulesInclusion ≫ coefficientEnd f a) ≫
      FibreInfinitesimalModules.sectionMap I f (e+d) = 0 := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  apply (FibreInfinitesimalModules.projection_isLocallyMem_iff I f (e+d) W _).mp
  intro U hUW
  rw [FibreIdealPowers.extendedPower_ideal, pow_add]
  change X.presheaf.map (homOfLE hUW).op
    (sectionsHom f W a * (show Γ(X, W) from s.1)) ∈ _
  rw [map_mul, coefficient_restriction]
  have ha := Ideal.mem_map_of_mem (sectionsHom f U.1) a.2
  rw [Ideal.map_pow] at ha
  apply Ideal.mul_mem_mul ha
  simpa only [FibreIdealPowers.extendedPower_ideal] using s.2 U hUW

/-- Every actual original homogeneous coefficient gives a genuine WHOLE
module-sheaf multiplication into its literal original higher ideal power. -/
def multiply {e : ℕ} (a : ↥(I^e)) (d : ℕ) :
    FibreIdealPowers.powerModule I f d ⟶ FibreIdealPowers.powerModule I f (e+d) :=
  FibreInfinitesimalModules.kernelLift I f (e+d)
    ((FibreIdealPowers.extendedPower I f d).toModulesInclusion ≫ coefficientEnd f a)
    (multiplication_zero I f a d)

/-- Genuine homogeneous multiplication retains EVERY original whole
section and its original coefficient on EVERY original open. -/
theorem multiply_app {e : ℕ} (a : ↥(I^e)) (d : ℕ) (W : X.Opens)
    (s : Γ(FibreIdealPowers.powerModule I f d, W)) :
    (show Γ(X, W) from ((multiply I f a d).app W s).1) =
      sectionsHom f W a * (show Γ(X, W) from s.1) := rfl

/-- The actual homogeneous multiplication lies over the SAME whole
original coefficient endomorphism of the original structure module. -/
theorem multiply_inclusion {e : ℕ} (a : ↥(I^e)) (d : ℕ) :
    multiply I f a d ≫ (FibreIdealPowers.extendedPower I f (e+d)).toModulesInclusion =
      (FibreIdealPowers.extendedPower I f d).toModulesInclusion ≫ coefficientEnd f a :=
  FibreInfinitesimalModules.kernelLift_inclusion I f (e+d) _ _

/-- EVERY actual higher-to-lower power inclusion commutes with the SAME
whole original homogeneous coefficient multiplication. -/
theorem multiply_inclusion_square {e : ℕ} (a : ↥(I^e)) {n m : ℕ} (h : n ≤ m) :
    inclusion I f h ≫ multiply I f a n =
      multiply I f a m ≫ inclusion I f (Nat.add_le_add_left h e) := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  rfl

end EnvelopeProperty.FibreIdealPowerTransitions
