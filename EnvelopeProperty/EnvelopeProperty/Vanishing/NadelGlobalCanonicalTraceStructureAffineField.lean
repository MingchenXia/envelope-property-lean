import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureBaseChange
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureTensorNaturality
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureGenericFiber

/-! # The SAME actual free affine chart trace specializes to the field trace

The only free algebra is the displayed whole chart algebra. Its original
spectrum section isomorphism supplies freeness of its section algebra;
the actual affine scheme base-change trace theorem is then applicable.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
open AlgebraicGeometry CategoryTheory Scheme.Modules FlatGlobalSections
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original whole spectrum section comparison is an algebra
isomorphism for the SAME original structural scheme map. -/
def specSectionsAlgEquiv (A B : CommRingCat.{u}) [Algebra A B] :
    let p : Spec B ⟶ Spec A := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let _ := sectionsAlgebra p
    B ≃ₐ[A] Γ(Spec B, ⊤) := by
  let p : Spec B ⟶ Spec A := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let _ := sectionsAlgebra p
  refine { (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro a
  change (Scheme.ΓSpecIso B).inv (algebraMap A B a) =
    p.appTop ((Scheme.ΓSpecIso A).inv a)
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))) a

private instance algebraSpecMap_finite (A B : CommRingCat.{u}) [Algebra A B]
    [Module.Finite A B] : IsFinite
      (show Spec B ⟶ Spec A from Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The ACTUAL field trace of the actual first-projection image of EVERY
whole section equals the image of its SAME original affine sheaf trace. -/
theorem affineStructureTrace_fieldBaseChange_top
    (A B K : CommRingCat.{u}) (hK : IsField K) [Algebra A B] [Algebra A K]
    [Module.Free A B] [Module.Finite A B] (b : Γ(Spec B, ⊤)) :
    let p : Spec B ⟶ Spec A := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let q : baseChange (S := K) p ⟶ Spec K := structureMap (S := K) p
    (Scheme.ΓSpecIso K).hom
        ((fieldStructureTrace K hK q).app ⊤ ((firstProjection (S := K) p).appTop b)) =
      algebraMap A K ((Scheme.ΓSpecIso A).hom ((affineStructureTrace A B).app ⊤ b)) := by
  let p : Spec B ⟶ Spec A := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let q : baseChange (S := K) p ⟶ Spec K := structureMap (S := K) p
  let _ := sectionsAlgebra p
  let _ := sectionsAlgebra q
  let e := specSectionsAlgEquiv A B
  let : Module.Free A Γ(Spec B, ⊤) := Module.Free.of_equiv e.toLinearEquiv
  have hb := affine_trace_baseChange (S := K) p inferInstance b
  have heval : e ((Scheme.ΓSpecIso B).hom b) = b :=
    (Scheme.ΓSpecIso B).hom_inv_id_apply b
  have he := Algebra.trace_eq_of_algEquiv e ((Scheme.ΓSpecIso B).hom b)
  have hr : Algebra.trace A Γ(Spec B, ⊤) b =
      Algebra.trace A B ((Scheme.ΓSpecIso B).hom b) :=
    (congrArg (Algebra.trace A Γ(Spec B, ⊤)) heval).symm.trans he
  exact (fieldStructureTrace_top K hK q ((firstProjection (S := K) p).appTop b)).trans
    (hb.trans (congrArg (algebraMap A K)
      (hr.trans (affineStructureTrace_top A B b).symm)))

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
