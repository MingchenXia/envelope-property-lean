/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierFlatParameterRestriction
import ModularCurves.Picard.InvertibleSheaf

/-! # Actual separation of invertible sheaves by the whole parameter open -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.CartierFlatParameter
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of R)) [Flat f]

/-- The genuine original invertible module sheaf restricts injectively to the
whole original parameter open on EVERY original open. -/
theorem invertibleModule_parameter_restriction_injective
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (V : X.Opens)
    (r : R) (hr : r ∈ nonZeroDivisors R) :
    Function.Injective (M.presheaf.map
      (homOfLE (inf_le_left : V ⊓ f ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ V)).op) := by
  obtain ⟨ι, C, hC, htriv⟩ := hM
  intro s t hst
  apply TopCat.Presheaf.IsSheaf.section_ext M.2
  intro x hx
  have hxC : x ∈ iSup C := by rw [hC]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxC
  obtain ⟨e⟩ := htriv i
  let W := V ⊓ C i
  let D := f ⁻¹ᵁ PrimeSpectrum.basicOpen r
  let a := Scheme.Modules.overTrivializationOfRestrictIso M (C i)
    (Scheme.Modules.restrictIsoOfPullbackIso M (C i) e)
  let OW : Over (C i) := Over.mk (homOfLE (inf_le_right : W ≤ C i))
  let OD : Over (C i) := Over.mk
    (homOfLE (inf_le_left.trans inf_le_right : W ⊓ D ≤ C i))
  let j : OD ⟶ OW := Over.homMk (homOfLE (inf_le_left : W ⊓ D ≤ W))
  refine ⟨W, inf_le_left, ⟨hx, hxi⟩, ?_⟩
  have hinj : Function.Injective (a.hom.val.app (op OW)) := by
    let ea := (PresheafOfModules.evaluation _ (op OW)).mapIso
      ((SheafOfModules.forget _).mapIso a)
    exact (ConcreteCategory.bijective_of_isIso ea.hom).injective
  apply hinj
  apply parameter_restriction_injective f W r hr
  have hnat (z : Γ(M, W)) :
      X.presheaf.map (homOfLE (inf_le_left : W ⊓ D ≤ W)).op
        (a.hom.val.app (op OW) z) =
      a.hom.val.app (op OD)
        (M.presheaf.map (homOfLE (inf_le_left : W ⊓ D ≤ W)).op z) := by
    exact (PresheafOfModules.naturality_apply a.hom.val j.op z).symm
  have he (z : Γ(M, V)) :
      M.presheaf.map (homOfLE (inf_le_left : W ⊓ D ≤ W)).op
        (M.presheaf.map (homOfLE (inf_le_left : W ≤ V)).op z) =
      M.presheaf.map (homOfLE (inf_le_inf inf_le_left le_rfl : W ⊓ D ≤ V ⊓ D)).op
        (M.presheaf.map (homOfLE (inf_le_left : V ⊓ D ≤ V)).op z) := by
    calc
      _ = M.presheaf.map ((homOfLE (inf_le_left : W ≤ V)).op ≫
          (homOfLE (inf_le_left : W ⊓ D ≤ W)).op) z := by
        rw [M.presheaf.map_comp]
        rfl
      _ = M.presheaf.map ((homOfLE (inf_le_left : V ⊓ D ≤ V)).op ≫
          (homOfLE (inf_le_inf inf_le_left le_rfl : W ⊓ D ≤ V ⊓ D)).op) z := by
        rfl
      _ = _ := by
        rw [M.presheaf.map_comp]
        rfl
  exact (hnat _).trans ((congrArg (fun z => a.hom.val.app (op OD) z)
    ((he s).trans ((congrArg (fun z => M.presheaf.map
      (homOfLE (inf_le_inf inf_le_left le_rfl : W ⊓ D ≤ V ⊓ D)).op z) hst).trans
        (he t).symm))).trans (hnat _).symm)

/-- On the whole original parameter open, genuine restriction detects
actual module-sheaf morphisms into the original invertible sheaf. -/
theorem hom_eq_of_parameter_restrict_eq
    {M N : X.Modules} (hN : Scheme.Modules.IsInvertible N)
    (a b : M ⟶ N) (r : R) (hr : r ∈ nonZeroDivisors R)
    (h : (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).map a =
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).map b) :
    a = b := by
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  apply invertibleModule_parameter_restriction_injective f N hN V r hr
  let D := f ⁻¹ᵁ PrimeSpectrum.basicOpen r
  have hV := congrArg (fun q => q.app (D.ι ⁻¹ᵁ V)) h
  change a.app (D.ι ''ᵁ (D.ι ⁻¹ᵁ V)) = b.app (D.ι ''ᵁ (D.ι ⁻¹ᵁ V)) at hV
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_comm D V] at hV
  exact (PresheafOfModules.naturality_apply a.val
    (homOfLE (inf_le_left : V ⊓ D ≤ V)).op s).symm.trans
      ((congrArg (fun q => q (M.presheaf.map
        (homOfLE (inf_le_left : V ⊓ D ≤ V)).op s)) hV).trans
          (PresheafOfModules.naturality_apply b.val
            (homOfLE (inf_le_left : V ⊓ D ≤ V)).op s))

/-- Equality after the true whole parameter-open pullback implies equality
of the actual original morphisms into an invertible module sheaf. -/
theorem hom_eq_of_parameter_pullback_eq
    {M N : X.Modules} (hN : Scheme.Modules.IsInvertible N)
    (a b : M ⟶ N) (r : R) (hr : r ∈ nonZeroDivisors R)
    (h : (Scheme.Modules.pullback (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).map a =
      (Scheme.Modules.pullback (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).map b) :
    a = b := by
  apply hom_eq_of_parameter_restrict_eq f hN a b r hr
  let e := Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι
  apply (cancel_mono (e.hom.app N)).mp
  rw [e.hom.naturality, e.hom.naturality, h]

end EnvelopeProperty.CartierFlatParameter
