import EnvelopeProperty.AlgGeom.SchemeModuleOpenCoverDetection
import EnvelopeProperty.AlgGeom.SchemeLineSectionFiberOpenFrame
import Mathlib.Topology.Separation.Basic

/-!
# Seshadri Ampleness Criterion Finite Generating Sections

Original pointwise sections construct finite whole generating sections. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.Modules
universe u v
namespace EnvelopeProperty.SeshadriAmplenessCriterion
open SchemeLineSectionEvaluation

/-- Actual compact T0 closed-point coverage is whole-space coverage. -/
theorem open_cover_of_closedPoint_cover {T : Type u} [TopologicalSpace T]
    [T0Space T] [CompactSpace T] {ι : Type v} (U : ι → Opens T)
    (hcover : ∀ x : T, IsClosed ({x} : Set T) → ∃ i : ι, x ∈ U i) :
    ∀ x : T, ∃ i : ι, x ∈ U i := by
  classical
  intro x
  by_contra hn
  have hxnot : x ∉ ⋃ i : ι, (U i : Set T) := by
    intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hn ⟨i, hi⟩
  have hclosed : IsClosed ((⋃ i : ι, (U i : Set T))ᶜ) :=
    (isOpen_iUnion (fun i => (U i).isOpen)).isClosed_compl
  obtain ⟨y, hy, hyclosed⟩ := hclosed.exists_closed_singleton ⟨x, hxnot⟩
  obtain ⟨i, hi⟩ := hcover y hyclosed
  exact hy (Set.mem_iUnion.mpr ⟨i, hi⟩)

/-- The original finite free evaluation is proved epic from the actual
same-section frame cover. No desired epimorphism or generators are supplied. -/
theorem exists_finite_generatingSections_of_finite_openSectionIsos
    {X : Scheme.{u}} (M : X.Modules) {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (t : ι → (unitObj X ⟶ M))
    (hcover : ∀ x : X, ∃ i : ι, x ∈ U i)
    (hIso : ∀ i : ι, IsIso (pullbackSectionHom (U i).ι (t i))) :
    ∃ G : M.GeneratingSections, G.IsFiniteType := by
  let π : SheafOfModules.free (R := X.ringCatSheaf) ι ⟶ M := Sigma.desc t
  have hpoints : ∀ x : X, ∃ (i : ι) (y : (U i).toScheme), (U i).ι y = x := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  have hπ : Epi π := by
    constructor
    intro N a b hab
    apply SchemeModuleOpenCoverDetection.hom_ext
      (fun i : ι => (U i).toScheme) (fun i => (U i).ι) hpoints
    intro i
    have ht : t i ≫ a = t i ≫ b := by
      have hh := congrArg (fun q => SheafOfModules.ιFree i ≫ q) hab
      have hπi : SheafOfModules.ιFree i ≫ π = t i := Sigma.ι_desc t i
      have hh' : (SheafOfModules.ιFree i ≫ π) ≫ a =
          (SheafOfModules.ιFree i ≫ π) ≫ b :=
        (Category.assoc (SheafOfModules.ιFree i) π a).trans
          (hh.trans (Category.assoc (SheafOfModules.ιFree i) π b).symm)
      exact (congrArg (fun q => q ≫ a) hπi).symm.trans
        (hh'.trans (congrArg (fun q => q ≫ b) hπi))
    let F := Scheme.Modules.pullback (U i).ι
    have hm : F.map (t i) ≫ F.map a = F.map (t i) ≫ F.map b :=
      (F.map_comp (t i) a).symm.trans
        ((congrArg (fun q => F.map q) ht).trans (F.map_comp (t i) b))
    let : IsIso (pullbackSectionHom (U i).ι (t i)) := hIso i
    apply (cancel_epi (pullbackSectionHom (U i).ι (t i))).mp
    have hm' := congrArg (fun q => (pullbackUnitIso (U i).ι).inv ≫ q) hm
    simpa only [pullbackSectionHom, Category.assoc] using hm'
  let G : M.GeneratingSections :=
    { I := ι
      s := M.freeHomEquiv π
      epi := by simpa only [Equiv.symm_apply_apply] using hπ }
  refine ⟨G, ?_⟩
  constructor
  change Finite ι
  infer_instance

/-- Compactness internally selects finitely many of the same original
whole sections and actual opens, then constructs actual finite generators. -/
theorem exists_finite_generatingSections_of_openSectionIsos
    {X : Scheme.{u}} [CompactSpace X] (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (t : ι → (unitObj X ⟶ M))
    (hcover : ∀ x : X, ∃ i : ι, x ∈ U i)
    (hIso : ∀ i : ι, IsIso (pullbackSectionHom (U i).ι (t i))) :
    ∃ G : M.GeneratingSections, G.IsFiniteType := by
  classical
  have hall : (Set.univ : Set X) ⊆ ⋃ i : ι, (U i : Set X) := by
    intro x _
    obtain ⟨i, hi⟩ := hcover x
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨a, ha⟩ := isCompact_univ.elim_finite_subcover
    (fun i : ι => (U i : Set X)) (fun i => (U i).isOpen) hall
  let κ := {i : ι // i ∈ a}
  have hfinitecover : ∀ x : X, ∃ i : κ, x ∈ U i.1 := by
    intro x
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp (ha (Set.mem_univ x))
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hx
    exact ⟨⟨i, hi⟩, hxi⟩
  exact exists_finite_generatingSections_of_finite_openSectionIsos M
    (fun i : κ => U i.1) (fun i => t i.1) hfinitecover (fun i => hIso i.1)

/-- Nonzero original fibers of internally chosen original whole sections
at each closed point construct actual finite whole generation of SAME M. -/
theorem exists_finite_generatingSections_of_closedPoint_fiber_nonzero
    {X : Scheme.{u}} [CompactSpace X] (M : X.Modules) (hM : IsInvertible M)
    (hpoint : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ t : unitObj X ⟶ M, pullbackSectionHom (X.fromSpecResidueField x) t ≠ 0) :
    ∃ G : M.GeneratingSections, G.IsFiniteType := by
  classical
  let ι := {x : X // IsClosed ({x} : Set X)}
  have hlocal (x : ι) : ∃ (t : unitObj X ⟶ M) (U : X.Opens),
      x.1 ∈ U ∧ IsIso (pullbackSectionHom U.ι t) := by
    obtain ⟨t, ht⟩ := hpoint x.1 x.2
    obtain ⟨U, hxU, hU⟩ :=
      SchemeLineSectionFiberOpenFrame.exists_open_isIso_of_pullbackSectionHom_ne_zero M hM t x.1 ht
    exact ⟨t, U, hxU, hU⟩
  choose t U hxU hIso using hlocal
  have hclosed : ∀ x : X, IsClosed ({x} : Set X) → ∃ i : ι, x ∈ U i := by
    intro x hx
    exact ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  exact exists_finite_generatingSections_of_openSectionIsos M U t
    (open_cover_of_closedPoint_cover U hclosed) hIso

#check @open_cover_of_closedPoint_cover
#print axioms open_cover_of_closedPoint_cover
#check @exists_finite_generatingSections_of_finite_openSectionIsos
#print axioms exists_finite_generatingSections_of_finite_openSectionIsos
#check @exists_finite_generatingSections_of_openSectionIsos
#print axioms exists_finite_generatingSections_of_openSectionIsos
#check @exists_finite_generatingSections_of_closedPoint_fiber_nonzero
#print axioms exists_finite_generatingSections_of_closedPoint_fiber_nonzero
end EnvelopeProperty.SeshadriAmplenessCriterion
