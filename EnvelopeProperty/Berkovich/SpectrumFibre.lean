/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumResidueField

/-!
# Fibres through actual completed residue-field tensor seminorms

For an arbitrary commutative algebra `B` over `A`, the fibre over a seminorm
`x` is equivalent to the prescribed-norm spectrum of `H(x) ⊗[A] B`.
The tensor valuation is constructed from the genuine completed-field map;
the inverse law uses density of the residue field in its completion.

The restriction map is continuous. This module's equivalence does not yet
assert inverse continuity or existence for an independent base extension.
-/

open scoped NNReal Topology
open Topology TensorProduct

noncomputable section

namespace EnvelopeProperty.Berkovich.Spectrum

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The actual point fibre over `x` under algebra-map pullback. An arbitrary
ring homomorphism is represented by its `RingHom.toAlgebra` structure. -/
abbrev Fibre (x : Spectrum A) := {y : Spectrum B // comap (algebraMap A B) y = x}

/-- The tensor algebra map induced by the genuine maps into the completed residue field. -/
def fibreHom {x : Spectrum A} {y : Spectrum B} (h : comap (algebraMap A B) y = x) :
    H x ⊗[A] B →+* H y :=
  letI : Algebra A (H y) := ((toH y).comp (algebraMap A B)).toAlgebra
  (Algebra.TensorProduct.productMap
    { H.map (algebraMap A B) h with commutes' := fun a => H.map_toH _ h a }
    { toH y with commutes' := fun _ => rfl }).toRingHom

@[simp]
theorem fibreHom_tmul {x : Spectrum A} {y : Spectrum B}
    (h : comap (algebraMap A B) y = x) (c : H x) (b : B) :
    fibreHom h (c ⊗ₜ[A] b) = H.map (algebraMap A B) h c * toH y b := rfl

@[simp]
theorem fibreHom_one_tmul {x : Spectrum A} {y : Spectrum B}
    (h : comap (algebraMap A B) y = x) (b : B) :
    fibreHom h (1 ⊗ₜ[A] b) = toH y b := by
  rw [fibreHom_tmul, map_one, one_mul]

@[simp]
theorem fibreHom_tmul_one {x : Spectrum A} {y : Spectrum B}
    (h : comap (algebraMap A B) y = x) (c : H x) :
    fibreHom h (c ⊗ₜ[A] (1 : B)) = H.map (algebraMap A B) h c := by
  rw [fibreHom_tmul, map_one, mul_one]

/-- The balancing relation for the original ring map inside the completed-field tensor algebra. -/
theorem algebraMap_tmul_one_eq (x : Spectrum A) (a : A) :
    (algebraMap A (H x) a ⊗ₜ[A] (1 : B)) = (1 : H x) ⊗ₜ[A] algebraMap A B a :=
  (Algebra.TensorProduct.algebraMap_apply a).symm.trans (Algebra.TensorProduct.algebraMap_apply' a)

/-- Pullback of the genuine completed residue-field norm defines the tensor fibre point. -/
def fibrePoint {x : Spectrum A} {y : Spectrum B} (h : comap (algebraMap A B) y = x) :
    RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] B) :=
  ⟨ofValuation ((NormedField.valuation (K := H y)).comap (fibreHom h)), fun c => by
    change ‖fibreHom h (c ⊗ₜ[A] (1 : B))‖₊ = ‖c‖₊
    rw [fibreHom_tmul_one]
    exact NNReal.eq (H.norm_map _ h c)⟩

@[simp]
theorem fibrePoint_val_tmul {x : Spectrum A} {y : Spectrum B}
    (h : comap (algebraMap A B) y = x) (c : H x) (b : B) :
    (fibrePoint h).1.val (c ⊗ₜ[A] b) = ‖c‖₊ * y.val b := by
  change ‖fibreHom h (c ⊗ₜ[A] b)‖₊ = _
  rw [fibreHom_tmul, nnnorm_mul, nnnorm_toH]
  exact congrArg (fun q : ℝ≥0 => q * y.val b) (NNReal.eq (H.norm_map _ h c))

/-- Restrict a prescribed-norm tensor point to the original algebra, landing in the actual fibre. -/
def fibreRestrict (x : Spectrum A)
    (z : RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] B)) : Fibre (B := B) x :=
  ⟨comap (Algebra.TensorProduct.includeRight (R := A) (A := H x)).toRingHom z.1, by
    refine ext_val fun a => ?_
    change z.1.val ((1 : H x) ⊗ₜ[A] algebraMap A B a) = x.val a
    rw [← algebraMap_tmul_one_eq]
    change z.1.val (algebraMap (H x) (H x ⊗[A] B) (toH x a)) = x.val a
    rw [z.2, NormedField.valuation_apply, nnnorm_toH]⟩

@[simp]
theorem fibreRestrict_val (x : Spectrum A)
    (z : RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] B)) (b : B) :
    (fibreRestrict x z).1.val b = z.1.val (1 ⊗ₜ[A] b) := rfl

/-- Tensor restriction is continuous in the pointwise seminorm topology. -/
@[fun_prop]
theorem continuous_fibreRestrict (x : Spectrum A) : Continuous (fibreRestrict (B := B) x) :=
  ((continuous_comap (Algebra.TensorProduct.includeRight (R := A) (A := H x)).toRingHom).comp
    continuous_subtype_val).subtype_mk _

/-- Restricting the constructed tensor point recovers the entire original fibre point. -/
@[simp]
theorem fibreRestrict_fibrePoint {x : Spectrum A} {y : Spectrum B}
    (h : comap (algebraMap A B) y = x) : fibreRestrict x (fibrePoint h) = ⟨y, h⟩ := by
  apply Subtype.ext
  refine ext_val fun b => ?_
  rw [fibreRestrict_val, fibrePoint_val_tmul, nnnorm_one, one_mul]

set_option maxHeartbeats 800000 in
/-- The completed-field comparison identifies the constructed tensor evaluation
with the canonical tensor-ring map into its completed residue field, on every element.
Density of `κ(x)` in `H(x)` is essential in the coefficient comparison. -/
theorem fibreHom_restrict_comp_toH (x : Spectrum A)
    (z : RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] B)) :
    (H.map (Algebra.TensorProduct.includeRight (R := A) (A := H x)).toRingHom
      (rfl : comap (Algebra.TensorProduct.includeRight (R := A) (A := H x)).toRingHom z.1 =
        (fibreRestrict x z).1)).comp (fibreHom (fibreRestrict x z).2) = toH z.1 := by
  let β := (Algebra.TensorProduct.includeRight (R := A) (A := H x) (B := B)).toRingHom
  let y := (fibreRestrict x z).1
  let ψ : H y →+* H z.1 := H.map β (rfl : comap β z.1 = y)
  let f : H x →+* H z.1 := ψ.comp (H.map (algebraMap A B) (fibreRestrict x z).2)
  let g : H x →+* H z.1 := (toH z.1).comp (algebraMap (H x) (H x ⊗[A] B))
  have hg : ∀ c, ‖g c‖ = ‖c‖ := by
    intro c
    change ‖toH z.1 (algebraMap (H x) (H x ⊗[A] B) c)‖ = ‖c‖
    rw [norm_toH, z.2, NormedField.valuation_apply]
    rfl
  have hfg : f = g := by
    apply H.ringHom_ext (x := x) (f := f) (g := g)
      ((H.isometry_map (x := y) (y := z.1) β rfl).continuous.comp
        (H.isometry_map (x := x) (y := y) (algebraMap A B) (fibreRestrict x z).2).continuous)
      (AddMonoidHomClass.isometry_of_norm g hg).continuous
    intro c
    have hκ : f.comp x.residueToH = g.comp x.residueToH := by
      apply Ideal.ResidueField.ringHom_ext
      refine RingHom.ext fun a => ?_
      change ψ (H.map (algebraMap A B) (fibreRestrict x z).2 (toH x a)) =
        toH z.1 (algebraMap (H x) (H x ⊗[A] B) (toH x a))
      rw [H.map_toH]
      have hmap : ψ (toH y (algebraMap A B a)) = toH z.1 (β (algebraMap A B a)) :=
        H.map_toH (x := y) (y := z.1) β (rfl : comap β z.1 = y) (algebraMap A B a)
      rw [hmap]
      change toH z.1 ((1 : H x) ⊗ₜ[A] algebraMap A B a) =
        toH z.1 ((algebraMap A (H x) a) ⊗ₜ[A] (1 : B))
      rw [algebraMap_tmul_one_eq]
    exact RingHom.congr_fun hκ c
  change ψ.comp (fibreHom (fibreRestrict x z).2) = toH z.1
  refine RingHom.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c b =>
    change ψ (fibreHom (fibreRestrict x z).2 (c ⊗ₜ[A] b)) = toH z.1 (c ⊗ₜ[A] b)
    rw [fibreHom_tmul, map_mul]
    have hc := RingHom.congr_fun hfg c
    change ψ (H.map (algebraMap A B) (fibreRestrict x z).2 c) =
      toH z.1 (c ⊗ₜ[A] (1 : B)) at hc
    have hb : ψ (toH y b) = toH z.1 ((1 : H x) ⊗ₜ[A] b) := H.map_toH β rfl b
    rw [hc, hb, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add t s ht hs => simp only [map_add, ht, hs]

/-- Tensor evaluation after restriction recovers the entire prescribed-norm tensor point. -/
@[simp]
theorem fibrePoint_fibreRestrict (x : Spectrum A)
    (z : RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] B)) :
    fibrePoint (fibreRestrict x z).2 = z := by
  apply Subtype.ext
  refine ext_val fun t => ?_
  change ‖fibreHom (fibreRestrict x z).2 t‖₊ = z.1.val t
  have he := RingHom.congr_fun (fibreHom_restrict_comp_toH x z) t
  have hn := H.norm_map
    (Algebra.TensorProduct.includeRight (R := A) (A := H x)).toRingHom
    (rfl : comap (Algebra.TensorProduct.includeRight (R := A) (A := H x)).toRingHom z.1 =
      (fibreRestrict x z).1) (fibreHom (fibreRestrict x z).2 t)
  apply NNReal.eq
  change ‖fibreHom (fibreRestrict x z).2 t‖ = (z.1.val t : ℝ)
  exact hn.symm.trans ((congrArg norm he).trans (norm_toH z.1 t))

/-- The genuine completed-residue-field tensor spectrum is equivalent to the original
seminorm fibre. Restriction is continuous; inverse continuity is not part of this equivalence. -/
def fibreEquiv (x : Spectrum A) :
    RelativeSpectrum (NormedField.valuation (K := H x)) (H x ⊗[A] B) ≃ Fibre (B := B) x where
  toFun := fibreRestrict x
  invFun y := fibrePoint y.2
  left_inv := fibrePoint_fibreRestrict x
  right_inv y := fibreRestrict_fibrePoint y.2

end EnvelopeProperty.Berkovich.Spectrum
