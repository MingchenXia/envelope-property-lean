import EnvelopeProperty.Vanishing.NadelBlowupCanonicalExceptionalSections
import EnvelopeProperty.Vanishing.NadelBlowupCanonicalGluingDescent

/-! # The SAME original principal generator multiplies an arbitrary actual ideal module -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealProductAffine
open SchemeLineSectionEvaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}}

def restrictTop (a : Γ(X, ⊤)) (W : X.Opens) : Γ(X, W) :=
  X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op a

theorem restrictTop_restriction (a : Γ(X, ⊤)) {U V : X.Opens} (h : U ≤ V) :
    X.presheaf.map (homOfLE h).op (restrictTop a V) = restrictTop a U := by
  rw [restrictTop, restrictTop, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private theorem multiply_mem (I J : X.IdealSheafData) (a : Γ(X, ⊤))
    (ha : I.IsLocallyMem ⊤ a) (W : X.Opens) (s : Γ(J.toModules, W)) :
    (I * J).IsLocallyMem W (restrictTop a W * (show Γ(X, W) from s.1)) := by
  intro V hVW
  change X.presheaf.map (homOfLE hVW).op
    (restrictTop a W * (show Γ(X, W) from s.1)) ∈ I.ideal V * J.ideal V
  rw [map_mul, restrictTop_restriction]
  exact Ideal.mul_mem_mul (ha V le_top) ((s : J.toSubmodule.obj (op W)).2 V hVW)

/-- Actual whole multiplication of the actual original J-module by the
SAME original included I-section, landing in the SAME original product ideal. -/
def multiplySection (I J : X.IdealSheafData) (a : Γ(X, ⊤)) (ha : I.IsLocallyMem ⊤ a) :
    J.toModules ⟶ (I * J).toModules where
  val :=
    { app W := ModuleCat.ofHom
        { toFun := fun s => ⟨restrictTop a W.unop * (show Γ(X, W.unop) from s.1), multiply_mem I J a ha W.unop s⟩
          map_add' := fun s t => by
            apply Subtype.ext
            change restrictTop a W.unop * ((show Γ(X, W.unop) from s.1) +
              (show Γ(X, W.unop) from t.1)) = _
            exact mul_add _ _ _
          map_smul' := fun r s => Subtype.ext (by
            change restrictTop a W.unop * ((show Γ(X, W.unop) from r) * (show Γ(X, W.unop) from s.1)) =
              (show Γ(X, W.unop) from r) * (restrictTop a W.unop * (show Γ(X, W.unop) from s.1))
            ring) }
      naturality := fun {U V} h => by
        apply ModuleCat.hom_ext
        ext s
        apply Subtype.ext
        let t : Γ(X, U.unop) := s.1
        change restrictTop a V.unop * X.presheaf.map h t =
          X.presheaf.map h (restrictTop a U.unop * t)
        rw [map_mul]
        have hr : X.presheaf.map h (restrictTop a U.unop) = restrictTop a V.unop := by
          simpa only [show (homOfLE h.unop.le).op = h from Subsingleton.elim _ _] using
            restrictTop_restriction a h.unop.le
        exact congrArg (fun z : Γ(X, V.unop) => z * X.presheaf.map h t) hr.symm }

/-- Its entire actual product-ideal inclusion is the SAME original J
inclusion followed by the SAME original whole structure scalar. -/
theorem multiplySection_inclusion (I J : X.IdealSheafData) (a : Γ(X, ⊤))
    (ha : I.IsLocallyMem ⊤ a) :
    multiplySection I J a ha ≫ (I * J).toModulesInclusion =
      J.toModulesInclusion ≫ ModularCurves.unitEndomorphismOfTopSection a := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  change restrictTop a W * (show Γ(X, W) from s.1) = (show Γ(X, W) from s.1) * restrictTop a W
  exact mul_comm _ _

/-- The original whole-open coefficient is exactly multiplication by the
SAME original a, under the native top section map. -/
theorem multiplySection_top (I J : X.IdealSheafData) (a : Γ(X, ⊤))
    (ha : I.IsLocallyMem ⊤ a) (s : Γ(J.toModules, ⊤)) :
    (show Γ(X, ⊤) from
      (show (I * J).toSubmodule.obj (op ⊤) from (multiplySection I J a ha).app ⊤ s).1) =
        a * (show Γ(X, ⊤) from s.1) := by
  change X.presheaf.map (𝟙 (op ⊤)) a * (show Γ(X, ⊤) from s.1) = _
  rw [X.presheaf.map_id]
  rfl

/-- Actual regularity of the actual affine original ideal generator makes
whole multiplication on ANY actual original ideal module an isomorphism. -/
theorem multiplySection_isIso [IsAffine X] (I J : X.IdealSheafData) (a : Γ(X, ⊤))
    (ha : a ∈ nonZeroDivisors Γ(X, ⊤))
    (hI : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {a}) :
    IsIso (multiplySection I J a ((I.isLocallyMem_iff ⟨⊤, isAffineOpen_top X⟩ a).mpr
      (hI.symm ▸ Ideal.mem_span_singleton_self a))) := by
  let hmem : I.IsLocallyMem ⊤ a := (I.isLocallyMem_iff ⟨⊤, isAffineOpen_top X⟩ a).mpr
    (hI.symm ▸ Ideal.mem_span_singleton_self a)
  let : J.toModules.IsQuasicoherent := J.isQuasicoherent_toModules
  let : (I * J).toModules.IsQuasicoherent := (I * J).isQuasicoherent_toModules
  apply Scheme.Modules.isIso_of_isQuasicoherent_of_isIso_app_top
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro x y hxy
    apply Subtype.ext
    have h : a * (show Γ(X, ⊤) from x.1) = a * (show Γ(X, ⊤) from y.1) :=
      (multiplySection_top I J a hmem x).symm.trans
        ((congrArg (fun z : Γ((I * J).toModules, ⊤) => (show Γ(X, ⊤) from z.1)) hxy).trans
          (multiplySection_top I J a hmem y))
    change (show Γ(X, ⊤) from x.1) = (show Γ(X, ⊤) from y.1)
    apply sub_eq_zero.mp
    apply (mul_left_mem_nonZeroDivisors_eq_zero_iff ha).mp
    rw [mul_sub, h, sub_self]
  · intro y
    have hy : (show Γ(X, ⊤) from y.1) ∈ Ideal.span {a} * J.ideal ⟨⊤, isAffineOpen_top X⟩ := by
      rw [← hI]
      exact (I * J).toModulesSectionsEquiv ⟨⊤, isAffineOpen_top X⟩ y |>.2
    obtain ⟨z, hz, he⟩ := Ideal.mem_span_singleton_mul.mp hy
    refine ⟨(J.toModulesSectionsEquiv ⟨⊤, isAffineOpen_top X⟩).symm ⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact (multiplySection_top I J a hmem _).trans he

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealProductAffine
