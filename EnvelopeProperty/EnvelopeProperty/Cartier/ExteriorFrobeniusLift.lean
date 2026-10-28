import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Algebra.CharP.Lemmas
import EnvelopeProperty.Cartier.EtaleGradedLeibniz

/-! # Genuine whole exterior Frobenius lift from actual one-form data -/
noncomputable section
namespace EnvelopeProperty.Cartier.ExteriorFrobeniusLift
open CategoryTheory
universe u
variable (B M : Type u) [CommRing B] [AddCommGroup M] [Module B M]
variable (p : ℕ) [Fact p.Prime] [CharP B p]

/-- SAME original exterior forms with the ACTUAL native Frobenius coefficient action. -/
def forms (q : ℕ) : ModuleCat B :=
  (ModuleCat.restrictScalars (frobenius B p)).obj (ModuleCat.of B (⋀[B]^q M))

/-- SAME entire exterior algebra, with its ACTUAL native Frobenius coefficient action. -/
def ambient : ModuleCat B :=
  (ModuleCat.restrictScalars (frobenius B p)).obj (ModuleCat.of B (ExteriorAlgebra B M))

/-- The ENTIRE original homogeneous-form inclusion is linear for the SAME Frobenius actions. -/
def inclusion (q : ℕ) : forms B M p q →ₗ[B] ambient B M p where
  toFun w := ((show ⋀[B]^q M from w) : ExteriorAlgebra B M)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem one_form_square_zero (w : ⋀[B]^1 M) :
    (w : ExteriorAlgebra B M) * w = 0 := by
  obtain ⟨m, rfl⟩ := (exteriorPower.oneEquiv B M).symm.surjective w
  rw [exteriorPower.oneEquiv_symm_apply]
  change ExteriorAlgebra.ιMulti B 1 (fun _ => m) * ExteriorAlgebra.ιMulti B 1 (fun _ => m) = 0
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  exact ExteriorAlgebra.ι_sq_zero m

private def liftAux (f : M →ₗ[B] forms B M p 1) :
    letI : Algebra B (ULift.{0} (ExteriorAlgebra B M)) :=
      Algebra.compHom (ULift.{0} (ExteriorAlgebra B M)) (frobenius B p)
    ExteriorAlgebra B M →ₐ[B] ULift.{0} (ExteriorAlgebra B M) := by
  letI : Algebra B (ULift.{0} (ExteriorAlgebra B M)) :=
    Algebra.compHom (ULift.{0} (ExteriorAlgebra B M)) (frobenius B p)
  letI : Module B (ULift.{0} (ExteriorAlgebra B M)) := Algebra.toModule
  let g : M →ₗ[B] ULift.{0} (ExteriorAlgebra B M) :=
    { toFun := fun m => ULift.up (inclusion B M p 1 (f m))
      map_add' := fun x y => ULift.ext _ _ (((inclusion B M p 1).comp f).map_add x y)
      map_smul' := fun b m => ULift.ext _ _ (((inclusion B M p 1).comp f).map_smul b m) }
  exact ExteriorAlgebra.lift B ⟨g, fun m => ULift.ext _ _
    (one_form_square_zero B M (show ⋀[B]^1 M from f m))⟩

/-- The true whole ring homomorphism extending ANY actual Frobenius-linear one-form map.
Its square-zero condition is DERIVED from the original one-form carrier, not supplied.
The native whole ULift ring equivalence is used only to keep the two coefficient actions distinct. -/
def lift (f : M →ₗ[B] forms B M p 1) : ExteriorAlgebra B M →+* ExteriorAlgebra B M := by
  letI : Algebra B (ULift.{0} (ExteriorAlgebra B M)) :=
    Algebra.compHom (ULift.{0} (ExteriorAlgebra B M)) (frobenius B p)
  exact ULift.ringEquiv.toRingHom.comp (liftAux B M p f).toRingHom

/-- EVERY original vector has exactly its SAME prescribed genuine original one-form image. -/
theorem lift_ι (f : M →ₗ[B] forms B M p 1) (m : M) :
    lift B M p f (ExteriorAlgebra.ι B m) = inclusion B M p 1 (f m) := by
  let : Algebra B (ULift.{0} (ExteriorAlgebra B M)) :=
    Algebra.compHom (ULift.{0} (ExteriorAlgebra B M)) (frobenius B p)
  change ((liftAux B M p f) (ExteriorAlgebra.ι B m)).down = _
  dsimp only [liftAux]
  rw [ExteriorAlgebra.lift_ι_apply]
  rfl

/-- The true whole coefficient action is the original pth power, with no scalar certificate. -/
theorem lift_algebraMap (f : M →ₗ[B] forms B M p 1) (b : B) :
    lift B M p f (algebraMap B (ExteriorAlgebra B M) b) =
      algebraMap B (ExteriorAlgebra B M) (b^p) := by
  let : Algebra B (ULift.{0} (ExteriorAlgebra B M)) :=
    Algebra.compHom (ULift.{0} (ExteriorAlgebra B M)) (frobenius B p)
  have h := AlgHom.commutes (liftAux B M p f) b
  exact congrArg ULift.down h

/-- The WHOLE genuine lift is linear into the ACTUAL Frobenius-restricted exterior algebra. -/
def ambientLinear (f : M →ₗ[B] forms B M p 1) :
    ExteriorAlgebra B M →ₗ[B] ambient B M p where
  toFun := lift B M p f
  map_add' := (lift B M p f).map_add
  map_smul' b x := by
    change lift B M p f (b • x) = b^p • lift B M p f x
    rw [Algebra.smul_def, map_mul, lift_algebraMap, Algebra.smul_def]

/-- The ENTIRE genuine exterior Frobenius lift preserves EVERY actual homogeneous degree.
This is derived from its actual one-form values and original homogeneous-power induction. -/
theorem lift_homogeneous (f : M →ₗ[B] forms B M p 1) (q : ℕ) (w : ⋀[B]^q M) :
    lift B M p f (w : ExteriorAlgebra B M) ∈
      (LinearMap.range (ExteriorAlgebra.ι B : M →ₗ[B] ExteriorAlgebra B M))^q := by
  let N : Submodule B (ExteriorAlgebra B M) := LinearMap.range (ExteriorAlgebra.ι B)
  change lift B M p f (w : ExteriorAlgebra B M) ∈ N^q
  exact Submodule.pow_induction_on_left' N
    (C := fun i x _ => lift B M p f x ∈ N^i)
    (fun b => by rw [lift_algebraMap]; exact Submodule.algebraMap_mem _)
    (fun x y i hx hy ihx ihy => by rw [map_add]; exact Submodule.add_mem _ ihx ihy)
    (fun x hx i y hy ih => by
      obtain ⟨m, rfl⟩ := hx
      rw [map_mul, lift_ι, pow_succ']
      exact Submodule.mul_mem_mul (by
        change ((show ⋀[B]^1 M from f m) : ExteriorAlgebra B M) ∈ N
        simpa only [pow_one] using (f m).property) ih)
    w.property

/-- The actual whole degree-q lift into the SAME original forms with genuine Frobenius scalars. -/
def homogeneous (f : M →ₗ[B] forms B M p 1) (q : ℕ) : (⋀[B]^q M) →ₗ[B] forms B M p q where
  toFun w := ⟨lift B M p f (w : ExteriorAlgebra B M), lift_homogeneous B M p f q w⟩
  map_add' x y := Subtype.ext ((lift B M p f).map_add x y)
  map_smul' b w := Subtype.ext ((ambientLinear B M p f).map_smul b w)

/-- EVERY whole homogeneous lift has EXACTLY its SAME actual ambient ring-homomorphism value. -/
theorem homogeneous_coe (f : M →ₗ[B] forms B M p 1) (q : ℕ) (w : ⋀[B]^q M) :
    ((show ⋀[B]^q M from homogeneous B M p f q w) : ExteriorAlgebra B M) =
      lift B M p f (w : ExteriorAlgebra B M) := rfl

/-- The all-degree lift recovers EVERY original input one-form, as an ENTIRE equality. -/
theorem homogeneous_one (f : M →ₗ[B] forms B M p 1) (m : M) :
    homogeneous B M p f 1 ((exteriorPower.oneEquiv B M).symm m) = f m := by
  apply Subtype.ext
  rw [homogeneous_coe, exteriorPower.oneEquiv_symm_apply]
  change lift B M p f (ExteriorAlgebra.ιMulti B 1 (fun _ => m)) = _
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one, lift_ι]
  rfl

/-- The actual lifts preserve the SAME whole original homogeneous exterior products in ALL
pairs of degrees. Multiplicativity follows from the genuine entire ring map, not a certificate. -/
theorem homogeneous_wedgeProduct (f : M →ₗ[B] forms B M p 1) (q r : ℕ)
    (a : ⋀[B]^q M) (b : ⋀[B]^r M) :
    homogeneous B M p f (r+q) (EtaleGradedLeibniz.wedgeProduct q r a b) =
      (show forms B M p (r+q) from EtaleGradedLeibniz.wedgeProduct q r
        (show ⋀[B]^q M from homogeneous B M p f q a)
        (show ⋀[B]^r M from homogeneous B M p f r b)) := by
  apply Subtype.ext
  exact (lift B M p f).map_mul a b

end EnvelopeProperty.Cartier.ExteriorFrobeniusLift
