import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureAffineNormalization
import EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniquenessCore
import EnvelopeProperty.AlgGeom.CyclicSectionStructuralUnitNaturality

/-! # Actual native affine sheaf traces commute with tensor base change

The equality is of the actual sheaf morphisms along the actual spectrum
square. Every original coefficient and every component is retained.
No caller supplies a trace-normalization or compatibility certificate.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
open AlgebraicGeometry CategoryTheory Scheme.Modules
open CyclicSectionGlobalCoverStructuralUnit CyclicSectionStructuralUnitNaturality
open scoped TensorProduct
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem affineHom_top_ext (A : CommRingCat.{u}) (M N : (Spec A).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f g : M ⟶ N)
    (h : ∀ x : Γ(M, ⊤), f.app ⊤ x = g.app ⊤ x) : f = g := by
  let MQ : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory :=
    ⟨M, inferInstance⟩
  let NQ : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory :=
    ⟨N, inferInstance⟩
  have he : ObjectProperty.homMk (X := MQ) (Y := NQ) f =
      ObjectProperty.homMk (X := MQ) (Y := NQ) g := by
    apply ((tildeEquiv (R := A)).inverse).map_injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact h x
  exact congrArg (fun k => k.hom) he

/-- The native affine sheaf trace evaluates on EVERY actual whole section
as the original algebra trace under the actual spectrum comparisons. -/
theorem affineStructureTrace_top (A B : CommRingCat.{u}) [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (x : Γ(Spec B, ⊤)) :
    (Scheme.ΓSpecIso A).hom ((affineStructureTrace A B).app ⊤ x) =
      Algebra.trace A B ((Scheme.ΓSpecIso B).hom x) := by
  let x' : (moduleSpecΓFunctor (R := A)).obj
      ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (unitObj (Spec B))) := x
  exact affineStructureTrace_apply A B x'

private theorem tensorSquare (A B S : CommRingCat.{u}) [Algebra A B] [Algebra A S] :
    Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[A] S ⊗[A] B).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B)) =
    Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[A] B))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A S)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  simp

/-- Native finite-free traces commute as ACTUAL SHEAF maps with the actual
tensor coefficient square, over an arbitrary base change algebra. -/
theorem affineStructureTrace_tensor_naturality
    (A B S : CommRingCat.{u}) [Algebra A B] [Algebra A S]
    [Module.Free A B] [Module.Finite A B] :
    unitSquareMap
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[A] B))))
        (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : B →ₐ[A] S ⊗[A] B).toRingHom))
        (Spec.map (CommRingCat.ofHom (algebraMap A S))) (tensorSquare A B S) ≫
      (pushforward (Spec.map (CommRingCat.ofHom (algebraMap A S)))).map
        (affineStructureTrace S (.of (S ⊗[A] B))) =
    affineStructureTrace A B ≫
      SheafOfModules.unitToPushforwardObjUnit
        (Spec.map (CommRingCat.ofHom (algebraMap A S))).toRingCatSheafHom := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let q := Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[A] B)))
  let g := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[A] S ⊗[A] B).toRingHom)
  let f := Spec.map (CommRingCat.ofHom (algebraMap A S))
  let h := tensorSquare A B S
  let : (unitObj (Spec B)).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : ((pushforward p).obj (unitObj (Spec B))).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom _
  let : (unitObj (Spec S)).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : ((pushforward f).obj (unitObj (Spec S))).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom _
  apply affineHom_top_ext A
  intro x
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).hom).1
  change (Scheme.ΓSpecIso S).hom
      ((affineStructureTrace S (.of (S ⊗[A] B))).app ⊤
        ((unitSquareMap p q g f h).app ⊤ x)) =
    (Scheme.ΓSpecIso S).hom (f.appTop ((affineStructureTrace A B).app ⊤ x))
  calc
    _ = Algebra.trace S (S ⊗[A] B)
        ((Scheme.ΓSpecIso (.of (S ⊗[A] B))).hom (g.appTop x)) :=
      (congrArg (fun z => (Scheme.ΓSpecIso S).hom
        ((affineStructureTrace S (.of (S ⊗[A] B))).app ⊤ z))
        (unitSquareMap_top p q g f h x)).trans
        (affineStructureTrace_top S (.of (S ⊗[A] B)) (g.appTop x))
    _ = Algebra.trace S (S ⊗[A] B)
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] S ⊗[A] B)
          ((Scheme.ΓSpecIso B).hom x)) :=
      congrArg (Algebra.trace S (S ⊗[A] B))
        (ConcreteCategory.congr_hom
          (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : B →ₐ[A] S ⊗[A] B).toRingHom)) x)
    _ = algebraMap A S (Algebra.trace A B ((Scheme.ΓSpecIso B).hom x)) :=
      NadelKummerTraceBaseChangeUniqueness.trace_one_tmul ((Scheme.ΓSpecIso B).hom x)
    _ = algebraMap A S
        ((Scheme.ΓSpecIso A).hom ((affineStructureTrace A B).app ⊤ x)) :=
      congrArg (algebraMap A S) (affineStructureTrace_top A B x).symm
    _ = _ := (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A S)))
      ((affineStructureTrace A B).app ⊤ x)).symm

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
