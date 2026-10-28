import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureChartTrace
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureAffineNormalization

/-! # The actual local structure trace has the entire original degree

The genuine basis supplies the degree even over a zero base ring. The
actual original structural unit is preserved by the actual cartesian
unit comparison; no normalization or matching certificate is assumed.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
open AlgebraicGeometry CategoryTheory Scheme.Modules Opposite
open CyclicSectionGlobalCoverStructuralUnit CyclicGlobalRoundedChartPushforward
universe u v
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

private theorem nsmul_id_app (X : Scheme.{u}) (M : X.Modules) (d : ℕ)
    (s : Γ(M, ⊤)) : (d • 𝟙 M).app ⊤ s = d • s := by
  change (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
    (d • 𝟙 M)).hom s) = _
  let F := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  have h₁ := congrArg (fun f => f.hom s) (F.map_nsmul (f := 𝟙 M) (n := d))
  have h₂ := congrArg (fun f => (d • f).hom s) (F.map_id M)
  exact h₁.trans h₂

private theorem conjugate_nsmul_id {E : Type*} [Category E] [Preadditive E]
    {M N : E} (e : M ≅ N) (d : ℕ) :
    e.hom ≫ (d • 𝟙 N) ≫ e.inv = d • 𝟙 M := by
  rw [Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul, Iso.hom_inv_id]

/-- The actual structural unit followed by the SAME actual native affine
sheaf trace is the entire finite-basis degree on the WHOLE structure sheaf. -/
theorem unit_comp_affineStructureTrace_of_basis
    (A B : CommRingCat.{u}) [Algebra A B] [Module.Free A B] [Module.Finite A B]
    {ι : Type v} [Fintype ι] (b : Module.Basis ι A B) :
    SheafOfModules.unitToPushforwardObjUnit
        (show Spec B ⟶ Spec A from
          Spec.map (CommRingCat.ofHom (algebraMap A B))).toRingCatSheafHom ≫
      affineStructureTrace A B = Fintype.card ι • 𝟙 (unitObj (Spec A)) := by
  let : (unitObj (Spec A)).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  apply affineHom_top_ext A
  intro x
  apply (unitSectionsEquiv A).injective
  have hu : pushforwardSectionsEquiv (R := A) (S := B)
      (((moduleSpecΓFunctor (R := A)).map
        (SheafOfModules.unitToPushforwardObjUnit
          (Spec.map (CommRingCat.ofHom (algebraMap A B))).toRingCatSheafHom)).hom.toFun x) =
      algebraMap A B (unitSectionsEquiv A x) :=
    ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))) x
  have hleft := (affineStructureTrace_apply A B _).trans
    ((congrArg (Algebra.trace A B) hu).trans
      (Algebra.trace_algebraMap_of_basis b (unitSectionsEquiv A x)))
  have hright := (congrArg (unitSectionsEquiv A)
    (nsmul_id_app (Spec A) (unitObj (Spec A)) (Fintype.card ι) x)).trans
      (map_nsmul (unitSectionsEquiv A) (Fintype.card ι) x)
  exact hleft.trans hright.symm

namespace WholeFreeChart
variable {X Y : Scheme.{u}} {π : Y ⟶ X} {D : ℕ} (C : WholeFreeChart π D)

/-- The SAME original structural unit is multiplied by the WHOLE original
degree under the actual local trace, not only under an auxiliary trace. -/
theorem unit_comp_traceOnSpec :
    (restrictFunctor C.base.2.fromSpec).map
        (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom) ≫
      C.traceOnSpec = D • 𝟙 ((restrictFunctor C.base.2.fromSpec).obj (unitObj X)) := by
  let _ := C.algebra
  let : Module.Free Γ(X, C.base.1) C.coeff := Module.Free.of_basis C.basis
  let : Module.Finite Γ(X, C.base.1) C.coeff := Module.Finite.of_basis C.basis
  let : IsOpenImmersion C.sourceMap := C.sourceMap_isOpenImmersion
  have hu : (restrictFunctor C.base.2.fromSpec).map
      (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom) ≫
      C.pushforwardIso.hom =
      (restrictUnitIso C.base.2.fromSpec).hom ≫
        SheafOfModules.unitToPushforwardObjUnit C.scalarMap.toRingCatSheafHom := by
    exact CyclicSectionStructuralUnitRestriction.restrictPushforwardUnit_triangle
      π C.scalarMap C.sourceMap C.base.2.fromSpec C.isPullback
  change _ ≫ (C.pushforwardIso.hom ≫ affineStructureTrace Γ(X, C.base.1) C.coeff ≫
    (restrictUnitIso C.base.2.fromSpec).inv) = _
  rw [← Category.assoc, hu]
  rw [Category.assoc, ← Category.assoc
    (SheafOfModules.unitToPushforwardObjUnit C.scalarMap.toRingCatSheafHom)]
  have ht : SheafOfModules.unitToPushforwardObjUnit C.scalarMap.toRingCatSheafHom ≫
      affineStructureTrace Γ(X, C.base.1) C.coeff =
        D • 𝟙 (unitObj (Spec Γ(X, C.base.1))) := by
    have hb := unit_comp_affineStructureTrace_of_basis
      Γ(X, C.base.1) C.coeff (ι := Fin D) C.basis
    exact hb.trans (congrArg (fun d => d • 𝟙 (unitObj (Spec Γ(X, C.base.1))))
      (Fintype.card_fin D))
  exact (congrArg (fun t => (restrictUnitIso C.base.2.fromSpec).hom ≫ t ≫
    (restrictUnitIso C.base.2.fromSpec).inv) ht).trans
      (conjugate_nsmul_id (restrictUnitIso C.base.2.fromSpec) D)

end WholeFreeChart
end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
