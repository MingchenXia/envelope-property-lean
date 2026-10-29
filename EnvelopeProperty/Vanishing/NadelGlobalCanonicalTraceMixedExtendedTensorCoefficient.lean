import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationSections

/-! # Whole tensor coefficients in the original mixed scalar extension

The original scalar-extension comparison preserves every coefficient of the
original mixed algebra. This is independent of the still-open canonical
differential square and counit normalization.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open scoped TensorProduct
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  let name := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationSections
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.actualTensorModuleIso_tmul
  unless (← Lean.getEnv).contains name do
    throwError "missing the original whole mixed tensor value"
  Lean.Elab.Command.modifyScope fun scope =>
    {scope with openDecls := Lean.OpenDecl.explicit `originalWholeTensorValue name :: scope.openDecls}

run_cmd
  let name := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceNative
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.actualTensorModuleIso
  unless (← Lean.getEnv).contains name do
    throwError "missing the original mixed tensor comparison"
  Lean.Elab.Command.modifyScope fun scope =>
    {scope with openDecls := Lean.OpenDecl.explicit `originalWholeTensorIso name :: scope.openDecls}

private theorem originalWholeTensorCoefficient
    {A S B : Type u} [CommRing A] [CommRing S] [CommRing B]
    [Algebra A S] [Algebra A B]
    (M : ModuleCat.{u} B) (P : ModuleCat.{u} (S ⊗[A] B))
    (e : (ModuleCat.extendScalars
      (R := CommRingCat.of B) (S := CommRingCat.of (S ⊗[A] B))
      (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := B)).toRingHom).obj M ≅ P)
    (s : S) (b : B) (w : M) :
    (originalWholeTensorIso (A := .of A) (S := .of S) (B := .of B) M P e).hom
        (s ⊗ₜ[A] (show (ModuleCat.restrictScalars (algebraMap A B)).obj M from b • w)) =
      (s ⊗ₜ[A] b) •
        (show P from
          (originalWholeTensorIso (A := .of A) (S := .of S) (B := .of B) M P e).hom
            ((1 : S) ⊗ₜ[A] (show (ModuleCat.restrictScalars (algebraMap A B)).obj M from w))) := by
  let : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have hs := originalWholeTensorValue M P e s
    (show (ModuleCat.restrictScalars (algebraMap A B)).obj M from b • w)
  have h1 := originalWholeTensorValue M P e (1 : S)
    (show (ModuleCat.restrictScalars (algebraMap A B)).obj M from w)
  rw [hs, h1]
  have ht :
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B) s ⊗ₜ[B] (b • w) =
        (s ⊗ₜ[A] b) •
          ((Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B) 1 ⊗ₜ[B] w) := by
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    congr 1
    change (1 ⊗ₜ[A] b) * (s ⊗ₜ[A] (1 : B)) =
      (s ⊗ₜ[A] b) * (1 ⊗ₜ[A] (1 : B))
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  exact (congrArg e.hom.hom.toFun ht).trans
    (e.hom.hom.map_smul (s ⊗ₜ[A] b) _)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
