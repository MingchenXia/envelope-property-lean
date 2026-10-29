import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionDimensionDrop
import Hironaka.Scheme.Modules.Sections
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import EnvelopeProperty.AlgGeom.Canonical.InvertibleLineAtlas
import EnvelopeProperty.AlgGeom.Canonical.GenericLineSections
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Actual projective coherent devissage foundations

Generic injectivity is transported to the original whole line sheaf by its
actual original local frames. No ampleness or numerical criterion is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion

theorem mono_of_genericStalk_injective {X : Scheme.{u}} [IsIntegral X]
    (T : X.Modules) (hT : IsInvertible T) {F : X.Modules} (v : T ⟶ F)
    (hv : Function.Injective
      ((Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (genericPoint X)).map v)) :
    Mono v := by
  let a := CanonicalGeometry.invertibleLineAtlas T hT
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U s t hst
  by_cases hU : Nonempty U.unop
  · let : Nonempty U.unop := hU
    have hη := CanonicalGeometry.genericPoint_mem_nonempty_open (X := X) U.unop
    have hs := TopCat.Presheaf.stalkFunctor_map_germ_apply U.unop (genericPoint X) hη
      ((Scheme.Modules.toPresheaf X).map v) s
    have ht := TopCat.Presheaf.stalkFunctor_map_germ_apply U.unop (genericPoint X) hη
      ((Scheme.Modules.toPresheaf X).map v) t
    have hg : T.presheaf.germ U.unop (genericPoint X) hη s =
        T.presheaf.germ U.unop (genericPoint X) hη t :=
      hv (hs.trans ((congrArg (F.presheaf.germ U.unop (genericPoint X) hη) hst).trans ht.symm))
    obtain ⟨V, hV, i, j, heq⟩ := T.presheaf.germ_eq _ _ _ _ _ hg
    cases Subsingleton.elim i j
    let : Nonempty V := ⟨⟨genericPoint X, hV⟩⟩
    exact a.restriction_injective i heq
  · apply TopCat.Presheaf.IsSheaf.section_ext (F := T.val.presheaf) T.isSheaf
    intro x hx
    exact (hU ⟨⟨x, hx⟩⟩).elim

theorem exists_affineBasis_zero_of_stalk_zero
    {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType]
    (x : X) (hx : Subsingleton (M.presheaf.stalk x)) :
    ∃ A : X.affineOpens, x ∈ A.1 ∧
      ∀ B : X.affineOpens, B.1 ≤ A.1 → Subsingleton Γ(M, B.1) := by
  classical
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := x) (show x ∈ (⊤ : X.Opens) from trivial)
  let : Module.Finite Γ(X, U) Γ(M, U) :=
    sections_module_finite_of_isFiniteType_of_isAffineOpen M ⟨U, hU⟩
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := Γ(X, U)) (M := Γ(M, U))
  have hlocal (i : Fin n) : ∃ V : X.Opens, ∃ hxV : x ∈ V,
      ∃ hVU : V ≤ U, M.presheaf.map (homOfLE hVU).op (s i) = 0 := by
    have hg : M.presheaf.germ U (x) hxU (s i) =
        M.presheaf.germ U (x) hxU 0 := hx.elim _ _
    obtain ⟨V, hxV, a, b, h⟩ := M.presheaf.germ_eq _ _ _ _ _ hg
    refine ⟨V, hxV, a.le, ?_⟩
    rw [show homOfLE a.le = a from Subsingleton.elim _ _]
    exact h.trans (map_zero _)
  choose V hxV hVU hzero using hlocal
  let W : X.Opens := U ⊓ ⨅ i : Fin n, V i
  have hxW : x ∈ W := by
    refine ⟨hxU, ?_⟩
    change x ∈ ((⨅ i : Fin n, V i : X.Opens) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxV
  obtain ⟨A, hA, hxA, hAW⟩ := exists_isAffineOpen_mem_and_subset hxW
  refine ⟨⟨A, hA⟩, hxA, ?_⟩
  intro B hBA
  let hBU : B.1 ≤ U := hBA.trans (hAW.trans inf_le_left)
  have hgen (i : Fin n) : M.presheaf.map (homOfLE hBU).op (s i) = 0 := by
    let hBV : B.1 ≤ V i := hBA.trans (hAW.trans (inf_le_right.trans (iInf_le V i)))
    have he : (homOfLE hBU).op = (homOfLE (hVU i)).op ≫ (homOfLE hBV).op :=
      Subsingleton.elim _ _
    rw [he, M.presheaf.map_comp_apply, hzero, map_zero]
  have hrestr (t : Γ(M, U)) : M.restrictionMap hBU t = 0 := by
    have ht : t ∈ Submodule.span Γ(X, U) (Set.range s) := by rw [hs]; trivial
    apply Submodule.span_induction (p := fun t _ => M.restrictionMap hBU t = 0) _ _ _ _ ht
    · rintro t ⟨i, rfl⟩
      exact hgen i
    · exact map_zero _
    · intro a b _ha _hb ha hb
      rw [map_add, ha, hb, add_zero]
    · intro r t _ht ht
      let : Module Γ(X, U) Γ(M, B.1) :=
        Module.compHom Γ(M, B.1) (X.presheaf.map (homOfLE hBU).op).hom
      have ht' : M.resₗ hBU t = 0 := ht
      exact ((M.resₗ hBU).map_smul r t).trans (by rw [ht', smul_zero])
  have hspan := M.span_range_restrictionMap_eq_top B.2 hU hBU
  have hzspan : Submodule.span Γ(X, B.1) (Set.range (M.restrictionMap hBU)) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact hrestr t
  have hBzero (t : Γ(M, B.1)) : t = 0 := by
    apply hzspan
    rw [hspan]
    trivial
  exact ⟨fun a b => (hBzero a).trans (hBzero b).symm⟩

/-- The support uses the actual original module stalk at every original point. -/
def moduleSupport {X : Scheme.{u}} (M : X.Modules) : Set X :=
  {x | ¬ Subsingleton (M.presheaf.stalk x)}

private theorem stalk_subsingleton_of_affineBasis_zero {X : Scheme.{u}}
    (M : X.Modules) (A : X.Opens)
    (hA : ∀ B : X.affineOpens, B.1 ≤ A → Subsingleton Γ(M, B.1))
    (y : X) (hy : y ∈ A) : Subsingleton (M.presheaf.stalk y) := by
  have hz (m : M.presheaf.stalk y) : m = 0 := by
    obtain ⟨U, hyU, s, hs⟩ := M.presheaf.exists_germ_eq m
    obtain ⟨B, hB, hyB, hBU⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (U := A ⊓ U) (x := y) ⟨hy, hyU⟩
    let : Subsingleton Γ(M, B) := hA ⟨B, hB⟩ (hBU.trans inf_le_left)
    let hle : B ≤ U := hBU.trans inf_le_right
    have ht : M.presheaf.map (homOfLE hle).op s = 0 := Subsingleton.elim _ _
    calc
      m = M.presheaf.germ U y hyU s := hs.symm
      _ = M.presheaf.germ B y hyB (M.presheaf.map (homOfLE hle).op s) :=
        (M.presheaf.germ_res_apply (homOfLE hle) y hyB s).symm
      _ = 0 := by rw [ht, map_zero]
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- Finite original affine generators and actual germ neighbourhoods derive
closedness of the actual original support, without a support certificate. -/
theorem moduleSupport_isClosed {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] : IsClosed (moduleSupport M) := by
  classical
  rw [← isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  change ¬ ¬ Subsingleton (M.presheaf.stalk x) at hx
  have hx0 : Subsingleton (M.presheaf.stalk x) := not_not.mp hx
  obtain ⟨A, hxA, hA⟩ := exists_affineBasis_zero_of_stalk_zero M x hx0
  refine ⟨(A.1 : Set X), ?_, A.1.isOpen, hxA⟩
  intro y hy
  change ¬ ¬ Subsingleton (M.presheaf.stalk y)
  exact not_not.mpr (stalk_subsingleton_of_affineBasis_zero M A.1 hA y hy)

/-- An actual generic-rank-zero coherent remainder has genuinely smaller
actual original support, derived internally from finite type and quasicoherence. -/
theorem moduleSupport_dimension_drop {X : Scheme.{u}} [IsIntegral X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (hη : Subsingleton (M.presheaf.stalk (genericPoint X)))
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ)) :
    topologicalKrullDim (moduleSupport M) ≤ d := by
  let Z : Closeds X := ⟨moduleSupport M, moduleSupport_isClosed M⟩
  have hZ : Z ≠ ⊤ := by
    intro htop
    have hmem : genericPoint X ∈ Z := by rw [htop]; trivial
    exact hmem hη
  exact properClosed_dimension_drop Z hZ d hdim

end EnvelopeProperty.SeshadriAmplenessCriterion
