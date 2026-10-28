import EnvelopeProperty.DeligneIllusie.WittTwoComplexMapNaturality
import Mathlib.RingTheory.RingHom.Etale

/-! # Actual chosen Frobenius lifts extend along genuine etale Witt restrictions -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoEtaleLiftRestriction
open scoped TensorProduct
universe u

private theorem nativeExtendLift
    {R C D E F : Type u} [CommRing R] [CommRing C] [CommRing D] [CommRing E] [CommRing F]
    [Algebra R C] [Algebra R D] [Algebra R E] [Algebra R F]
    (α : C →ₐ[R] D) (hα : α.toRingHom.FormallyEtale)
    (g : C →ₐ[R] E) (h : D →ₐ[R] F) (π : E →ₐ[R] F)
    (hπ : Function.Surjective π) (hnil : IsNilpotent (RingHom.ker π.toRingHom))
    (hsq : ∀ c, π (g c) = h (α c)) :
    ∃ l : D →ₐ[R] E, (∀ d, π (l d) = h d) ∧ (∀ c, l (α c) = g c) := by
  let : Algebra C D := α.toRingHom.toAlgebra
  let : Algebra C E := g.toRingHom.toAlgebra
  let : Algebra C F := (π.comp g).toRingHom.toAlgebra
  let : Algebra.FormallyEtale C D := hα
  let hh : D →ₐ[C] F := { h.toRingHom with commutes' := fun c => (hsq c).symm }
  let pp : E →ₐ[C] F := { π.toRingHom with commutes' := fun _ => rfl }
  let l := Algebra.FormallySmooth.liftOfSurjective hh pp hπ hnil
  let lR : D →ₐ[R] E :=
    { l.toRingHom with
      commutes' := fun r => by
        have hαr := α.commutes r
        change l (algebraMap R D r) = algebraMap R E r
        rw [← hαr]
        exact (l.commutes (algebraMap R C r)).trans (g.commutes r) }
  refine ⟨lR, ?_, ?_⟩
  · intro d
    exact Algebra.FormallySmooth.liftOfSurjective_apply hh pp hπ hnil d
  · intro c
    exact l.commutes c

private theorem nativeLiftUnique
    {R C D E F : Type u} [CommRing R] [CommRing C] [CommRing D] [CommRing E] [CommRing F]
    [Algebra R C] [Algebra R D] [Algebra R E] [Algebra R F]
    (α : C →ₐ[R] D) (hα : α.toRingHom.FormallyEtale)
    (g : C →ₐ[R] E) (π : E →ₐ[R] F)
    (hnil : IsNilpotent (RingHom.ker π.toRingHom))
    (l₁ l₂ : D →ₐ[R] E) (h₁ : ∀ c, l₁ (α c) = g c) (h₂ : ∀ c, l₂ (α c) = g c)
    (hr : ∀ d, π (l₁ d) = π (l₂ d)) : l₁ = l₂ := by
  let : Algebra C D := α.toRingHom.toAlgebra
  let : Algebra C E := g.toRingHom.toAlgebra
  let : Algebra.FormallyEtale C D := hα
  let ll₁ : D →ₐ[C] E := { l₁.toRingHom with commutes' := h₁ }
  let ll₂ : D →ₐ[C] E := { l₂.toRingHom with commutes' := h₂ }
  have he : ll₁ = ll₂ := Algebra.FormallyUnramified.ext' π.toRingHom hnil ll₁ ll₂ hr
  apply AlgHom.ext
  intro d
  exact AlgHom.congr_fun he d

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoSourceResidue.twistSMul WittTwoRelativeLift.residueCopyAlgebra
  WittTwoLiftDifference.frobeniusAlgebra
  WittTwoOriginalCotangentMaps.originalResidueRing WittTwoOriginalCotangentMaps.residueAlgebra
private abbrev W' := ULift.{0} (WittTwo.Ring p k)
private abbrev T (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A] :=
  WittTwoRelativeLift.TwistAlgebra p k A
private abbrev B (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A] :=
  WittTwoSmoothDifferentials.ResidueAlgebra p k A
variable {A A' : Type u} [CommRing A] [CommRing A']
  [Algebra (WittTwo.Ring p k) A] [Algebra (WittTwo.Ring p k) A']
  (β : A →ₐ[WittTwo.Ring p k] A')

private theorem untwist_naturality (t : T p k A) :
    WittTwoResidueUntwist.sourceUntwist p k A' (WittTwoLiftDifferenceNaturality.twistMap p k β t) =
      β (WittTwoResidueUntwist.sourceUntwist p k A t) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add t s ht hs => rw [map_add, map_add, map_add, map_add, ht, hs]
  | tmul c a =>
    rw [WittTwoLiftDifferenceNaturality.twistMap_tmul,
      WittTwoResidueUntwist.sourceUntwist_tmul,
      WittTwoResidueUntwist.sourceUntwist_tmul, map_mul, β.commutes]

/-- The SAME actual original tensor restriction is etale, genuinely derived from the actual map. -/
theorem twistMap_etale (hβ : β.toRingHom.Etale) :
    (WittTwoLiftDifferenceNaturality.twistMap p k β).toRingHom.Etale := by
  have h := RingHom.Etale.respectsIso.2 β.toRingHom
    (WittTwoResidueUntwist.sourceUntwist p k A).toRingEquiv hβ
  have hh := RingHom.Etale.respectsIso.1 _
    (WittTwoResidueUntwist.sourceUntwist p k A').symm.toRingEquiv h
  have he : (WittTwoResidueUntwist.sourceUntwist p k A').symm.toRingHom.comp
      (β.toRingHom.comp (WittTwoResidueUntwist.sourceUntwist p k A).toRingHom) =
      (WittTwoLiftDifferenceNaturality.twistMap p k β).toRingHom := by
    apply RingHom.ext
    intro t
    apply (WittTwoResidueUntwist.sourceUntwist p k A').injective
    exact ((WittTwoResidueUntwist.sourceUntwist p k A').apply_symm_apply _).trans
      (untwist_naturality p k β t).symm
  exact he ▸ hh

variable [Algebra.Smooth (WittTwo.Ring p k) A] [Algebra.Smooth (WittTwo.Ring p k) A']
variable (f : WittTwoLiftDifference.Lift p k A)
  (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)

include hf
omit [Algebra.Smooth (WittTwo.Ring p k) A] in
/-- A genuine target relative lift and its ENTIRE reduction/commuting equations are produced. -/
theorem exists_restrictedLift (hβ : β.toRingHom.Etale) :
    ∃ f' : WittTwoLiftDifference.Lift p k A',
      (∀ t, algebraMap A' (B p k A') (f' t) = WittTwoRelativeLift.residueFrobenius p k A' t) ∧
      (∀ t, β (f t) = f' (WittTwoLiftDifferenceNaturality.twistMap p k β t)) := by
  let := WittTwoRelativeLift.copyAlgebra p k A
  let := WittTwoRelativeLift.copyAlgebra p k A'
  let βc : A →ₐ[W' p k] A' :=
    { β.toRingHom with commutes' := fun c => β.commutes c.down }
  have he : (WittTwoLiftDifferenceNaturality.twistMap p k β).toRingHom.FormallyEtale :=
    (twistMap_etale p k β hβ).toAlgebra.formallyEtale
  have hsq (t : T p k A) : WittTwoRelativeLift.reductionMap p k A' (βc (f t)) =
      WittTwoRelativeLift.residueFrobenius p k A'
        (WittTwoLiftDifferenceNaturality.twistMap p k β t) := by
    change algebraMap A' (B p k A') (β (f t)) = _
    rw [← WittTwoAlgebraDivisionNaturality.residueMap_reduction, hf,
      WittTwoLiftDifferenceNaturality.residueFrobenius_naturality]
  obtain ⟨l, hl, hc⟩ := nativeExtendLift
    (WittTwoLiftDifferenceNaturality.twistMap p k β) he (βc.comp f)
    (WittTwoRelativeLift.residueFrobenius p k A') (WittTwoRelativeLift.reductionMap p k A')
    (WittTwoRelativeLift.reduction_surjective p k A')
    ⟨2, WittTwoRelativeLift.reduction_kernel_square_zero p k A'⟩ hsq
  exact ⟨l, hl, fun t => (hc t).symm⟩

omit hf [Algebra.Smooth (WittTwo.Ring p k) A] in
/-- Whole actual target lifts commuting with the prescribed source lift are genuinely unique. -/
theorem restrictedLift_unique (hβ : β.toRingHom.Etale)
    (f₁ f₂ : WittTwoLiftDifference.Lift p k A')
    (h₁ : ∀ t, algebraMap A' (B p k A') (f₁ t) = WittTwoRelativeLift.residueFrobenius p k A' t)
    (h₂ : ∀ t, algebraMap A' (B p k A') (f₂ t) = WittTwoRelativeLift.residueFrobenius p k A' t)
    (hc₁ : ∀ t, β (f t) = f₁ (WittTwoLiftDifferenceNaturality.twistMap p k β t))
    (hc₂ : ∀ t, β (f t) = f₂ (WittTwoLiftDifferenceNaturality.twistMap p k β t)) : f₁ = f₂ := by
  let := WittTwoRelativeLift.copyAlgebra p k A
  let := WittTwoRelativeLift.copyAlgebra p k A'
  let βc : A →ₐ[W' p k] A' :=
    { β.toRingHom with commutes' := fun c => β.commutes c.down }
  exact nativeLiftUnique (WittTwoLiftDifferenceNaturality.twistMap p k β)
    (twistMap_etale p k β hβ).toAlgebra.formallyEtale (βc.comp f)
    (WittTwoRelativeLift.reductionMap p k A')
    ⟨2, WittTwoRelativeLift.reduction_kernel_square_zero p k A'⟩
    f₁ f₂ (fun t => (hc₁ t).symm) (fun t => (hc₂ t).symm)
    (fun t => (h₁ t).trans (h₂ t).symm)

end EnvelopeProperty.DeligneIllusie.WittTwoEtaleLiftRestriction
