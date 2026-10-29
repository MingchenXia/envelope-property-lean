import EnvelopeProperty.AlgGeom.Canonical.NativeLineSectionRatios
import EnvelopeProperty.Berkovich.SchemeLineLocalSectionEvaluation
import EnvelopeProperty.AlgGeom.Canonical.LineSectionRatioImage

/-! # SAME original local line coefficients are units along actual original unit lifts -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace EnvelopeProperty.ValuativeLineCoefficients
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalUnitEndCoefficientIsUnit {X : Scheme.{u}}
    (a : Scheme.Modules.unitObj X ⟶ Scheme.Modules.unitObj X) [IsIso a] :
    IsUnit (show Γ(X, ⊤) from a.val.app (.op ⊤) (show Γ(X, ⊤) from 1)) := by
  let b := inv a
  let r : Γ(X, ⊤) := a.val.app (.op ⊤) (show Γ(X, ⊤) from 1)
  let s : Γ(X, ⊤) := b.val.app (.op ⊤) (show Γ(X, ⊤) from 1)
  have h : s * r = 1 := by
    have he := congrArg (fun q : Scheme.Modules.unitObj X ⟶ Scheme.Modules.unitObj X =>
      q.val.app (.op ⊤) (show Γ(X, ⊤) from 1)) (IsIso.inv_hom_id a)
    change a.val.app (.op ⊤) s = (1 : Γ(X, ⊤)) at he
    have hs : a.val.app (.op ⊤) s = s * r := by
      have ht : a.val.app (.op ⊤) s = s *
          X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op
            (a.val.app (.op ⊤) (show Γ(X, ⊤) from 1)) :=
        CanonicalGeometry.originalUnitSection_apply a ⊤ s
      have hi : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op (⊤ : X.Opens)) :=
        Subsingleton.elim _ _
      have hres : X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op r = r :=
        (congrArg (fun i => X.presheaf.map i r) hi).trans
          (congrArg (fun q => q r) (X.presheaf.map_id (op (⊤ : X.Opens))))
      exact ht.trans (congrArg (fun z : Γ(X, ⊤) => s * z) hres)
    exact hs.symm.trans he
  exact ⟨⟨r, s, (mul_comm r s).trans h, h⟩, rfl⟩

private theorem originalSectionHomAtOne {X : Scheme.{u}} {M : X.Modules}
    (a : Scheme.Modules.unitObj X ⟶ M) :
    SchemeModuleGlobalSections.sectionHom M
      (a.val.app (.op ⊤) (show Γ(X, ⊤) from 1)) = a := by
  apply SheafOfModules.hom_ext
  ext U
  change (1 : Γ(X, U.unop)) •
      M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op
        (a.val.app (.op ⊤) (show Γ(X, ⊤) from 1)) =
    a.val.app U (show Γ(X, U.unop) from 1)
  rw [one_smul]
  have h := CanonicalGeometry.originalUnitSection_apply a U.unop (1 : Γ(X, U.unop))
  rw [one_smul] at h
  exact h.symm

private theorem originalAffineFrameAt {X : Scheme.{u}} (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (L.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme) := by
  obtain ⟨ι, O, hO, he⟩ := hL
  have hx : x ∈ ⨆ i, O i := by rw [hO]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUi⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hi (O i).isOpen
  obtain ⟨e⟩ := he i
  exact ⟨⟨U, hU⟩, hxU, ⟨Scheme.Modules.restrictIsoOfPullbackIso L U
    (Scheme.Modules.restrictTrivialization hUi e)⟩⟩

/-- Actual whole unitness after an original local-spectrum pullback DERIVES an actual
original affine line frame containing the entire lift, with SAME original generator's
native local coefficient a UNIT in the SAME original local ring. No frame/range/unit or
coefficient-matching data are supplied. -/
theorem exists_affineFrame_unit_coefficient {X : Scheme.{u}} (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (δ : Scheme.Modules.unitObj X ⟶ L)
    {V : Type u} [CommRing V] [IsLocalRing V] (l : Spec (.of V) ⟶ X)
    [IsIso ((Scheme.Modules.pullbackUnitIso l).inv ≫ (Scheme.Modules.pullback l).map δ)] :
    ∃ (U : X.affineOpens) (e : L.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme)
      (t : Spec (.of V) ⟶ U.1.toScheme),
      l (IsLocalRing.closedPoint V) ∈ U.1 ∧ t ≫ U.1.ι = l ∧
      IsUnit ((Scheme.ΓSpecIso (.of V)).hom.hom
        (t.appTop.hom (ModularCurves.affineOpenTopSection U
          (ModularCurves.localTrivializationCoefficient L U e
            (δ.val.app (.op ⊤) (show Γ(X, ⊤) from 1)))))) := by
  obtain ⟨U, hx, ⟨e⟩⟩ := originalAffineFrameAt L hL (l (IsLocalRing.closedPoint V))
  have hpre : l ⁻¹ᵁ U.1 = ⊤ :=
    (IsLocalRing.closedPoint_mem_iff (l ⁻¹ᵁ U.1)).mp hx
  have hrange : Set.range l ⊆ Set.range U.1.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change x ∈ l ⁻¹ᵁ U.1
    rw [hpre]
    trivial
  let t := IsOpenImmersion.lift U.1.ι l hrange
  have ht : t ≫ U.1.ι = l := IsOpenImmersion.lift_fac _ _ _
  let d := δ.val.app (.op ⊤) (show Γ(X, ⊤) from 1)
  let r := ModularCurves.affineOpenTopSection U (ModularCurves.localTrivializationCoefficient L U e d)
  have hδ : SchemeLineSectionEvaluation.pullbackSectionHom U.1.ι δ ≫
      (Scheme.Modules.pullbackIsoOfRestrictIso L U.1 e).hom =
        ModularCurves.unitEndomorphismOfTopSection r := by
    have h := SchemeLineSectionEvaluation.sectionHom_localScalar L U e d
    rw [originalSectionHomAtOne δ] at h
    exact h
  have hscalar := SchemeLineSectionEvaluation.frameViaFactor_sectionHom_scalar
    t U.1.ι l ht (Scheme.Modules.pullbackIsoOfRestrictIso L U.1 e) δ r hδ
  let : IsIso (SchemeLineSectionEvaluation.pullbackSectionHom l δ) := by
    change IsIso ((Scheme.Modules.pullbackUnitIso l).inv ≫ (Scheme.Modules.pullback l).map δ)
    infer_instance
  let : IsIso (ModularCurves.unitEndomorphismOfTopSection (t.appTop.hom r)) := by
    rw [← hscalar]
    infer_instance
  have hu := originalUnitEndCoefficientIsUnit
    (ModularCurves.unitEndomorphismOfTopSection (t.appTop.hom r))
  have hv : IsUnit (t.appTop.hom r) := by
    convert hu using 1
    rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
    simp only [homOfLE_refl, op_id, one_mul]
    erw [CategoryTheory.Functor.map_id]
    rfl
  exact ⟨U, e, t, hx, ht, hv.map (Scheme.ΓSpecIso (.of V)).hom.hom⟩

end EnvelopeProperty.ValuativeLineCoefficients
