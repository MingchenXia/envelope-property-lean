import EnvelopeProperty.Potential.CurveAnalyticPieces

/-! # Genuine finite refinement of actual whole original analytic curve pieces -/

open scoped NNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology Filter
noncomputable section
namespace EnvelopeProperty

/-- Actual central clopen identities persist over a genuine base neighbourhood
under a genuine closed map. -/
theorem eventually_clopen_fibre_eq_of_central {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (hp : IsClosedMap p)
    (C D : Set X) (hC : IsClopen C) (hD : IsClopen D) (x : Y)
    (hcentral : ∀ z, p z = x → (z ∈ C ↔ z ∈ D)) :
    ∀ᶠ y in 𝓝 x, ∀ z, p z = y → (z ∈ C ↔ z ∈ D) := by
  let S := (C ∩ Dᶜ) ∪ (D ∩ Cᶜ)
  have hS : IsClosed S :=
    (hC.isClosed.inter hD.isOpen.isClosed_compl).union
      (hD.isClosed.inter hC.isOpen.isClosed_compl)
  have hx : x ∈ (p '' S)ᶜ := by
    rintro ⟨z,hz,hzx⟩
    rcases hz with hz | hz
    · exact hz.2 ((hcentral z hzx).mp hz.1)
    · exact hz.2 ((hcentral z hzx).mpr hz.1)
  filter_upwards [((hp S hS).isOpen_compl).mem_nhds hx] with y hy z hzy
  constructor
  · intro hzC
    by_contra hzD
    exact hy ⟨z,Or.inl ⟨hzC,hzD⟩,hzy⟩
  · intro hzD
    by_contra hzC
    exact hy ⟨z,Or.inr ⟨hzD,hzC⟩,hzy⟩

/-- A genuine finite central clopen partition persists on a base neighbourhood,
including the empty partition. -/
theorem eventually_clopen_fibre_partition_of_central {X Y ι : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
    (p : X → Y) (hp : IsClosedMap p) (C : Set X) (D : ι → Set X)
    (hC : IsClopen C) (hD : ∀ i, IsClopen (D i)) (x : Y)
    (hcover : ∀ z, p z = x → (z ∈ C ↔ ∃ i, z ∈ D i))
    (hdisj : ∀ i j, i ≠ j → ∀ z, p z = x → z ∈ D i → z ∈ D j → False) :
    ∀ᶠ y in 𝓝 x,
      (∀ z, p z = y → (z ∈ C ↔ ∃ i, z ∈ D i)) ∧
      (∀ i j, i ≠ j → ∀ z, p z = y → z ∈ D i → z ∈ D j → False) := by
  have hc := eventually_clopen_fibre_eq_of_central p hp C (⋃ i, D i) hC
    (isClopen_iUnion_of_finite hD) x (by simpa only [Set.mem_iUnion] using hcover)
  have hd (i j : ι) : ∀ᶠ y in 𝓝 x,
      i ≠ j → ∀ z, p z = y → z ∈ D i → z ∈ D j → False := by
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ hne => (hne hij).elim)
    · have hh := eventually_clopen_fibre_eq_of_central p hp (D i ∩ D j) ∅
        ((hD i).inter (hD j)) isClopen_empty x (by
          intro z hzx
          constructor
          · rintro ⟨hi,hj⟩
            exact (hdisj i j hij z hzx hi hj).elim
          · exact False.elim)
      filter_upwards [hh] with y hy _ z hzy hi hj
      exact (hy z hzy).mp ⟨hi,hj⟩
  filter_upwards [hc,Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hd i))]
    with y hy hpairs
  exact ⟨by simpa only [Set.mem_iUnion] using hy,hpairs⟩

namespace Berkovich.RelativeSpectrum

variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
variable [CommRing B] [Algebra K[X] B] [Algebra K B] [IsScalarTower K K[X] B] [Fintype ι]

namespace FCStandardAffinoid
variable {m : ℕ} (U : FCStandardAffinoid w m)

/-- The ACTUAL original central fibre points of a fixed whole analytic piece. -/
abbrev CurveCentralPiece (basis : Module.Basis ι K[X] B) (e : U.CurveAnalyticAlgebra basis)
    (x : RelativeSpectrum w K[X]) :=
  {y : RelativeSpectrum w B // y ∈ U.curveIdempotentAmbientPiece basis e ∧
    comap (IsScalarTower.toAlgHom K K[X] B) y = x}

/-- Finiteness is DERIVED from the original finite algebra, including empty central fibres. -/
theorem finite_curveCentralPiece (basis : Module.Basis ι K[X] B) (e : U.CurveAnalyticAlgebra basis)
    (x : RelativeSpectrum w K[X]) : Finite (U.CurveCentralPiece basis e x) := by
  let := Module.Finite.of_basis basis
  have hfinite := finite_preimage_comap_singleton (IsScalarTower.toAlgHom K K[X] B)
    (RingHom.finite_algebraMap.mpr inferInstance) x
  exact (hfinite.subset (fun y hy => hy.2)).to_subtype

end FCStandardAffinoid

/-- Every finite family of actual base neighbourhoods contains one genuine whole
standard-affinoid neighbourhood. The family may be empty. -/
theorem fc_exists_standardAffinoid_common_nhds {J : Type*} [Finite J]
    (x : RelativeSpectrum w K[X]) (N : J → Set (RelativeSpectrum w K[X]))
    (hN : ∀ j, N j ∈ 𝓝 x) :
    ∃ n : ℕ, ∃ U : FCStandardAffinoid w n, x ∈ interior U.carrier ∧
      ∀ j, U.carrier ⊆ N j := by
  have hall : {y | ∀ j, y ∈ N j} ∈ 𝓝 x := Filter.eventually_all.mpr hN
  obtain ⟨n,U,hx,hU⟩ := fc_exists_standardAffinoid_nhds x hall
  exact ⟨n,U,hx,fun j y hy => hU hy j⟩

namespace FCStandardAffinoid
variable {m : ℕ} (U : FCStandardAffinoid w m)

/-- A genuine finite central partition by actual analytic idempotents becomes an
ENTIRE literal disjoint partition after an actual base restriction. -/
theorem exists_standardAffinoid_restrict_piece_partition {J : Type*} [Finite J]
    (basis : Module.Basis ι K[X] B) {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (a : J → U.CurveAnalyticAlgebra basis) (ha : ∀ j, IsIdempotentElem (a j))
    (x : RelativeSpectrum w K[X]) (hx : x ∈ interior U.carrier)
    (hcover : ∀ y : RelativeSpectrum w B,
      comap (IsScalarTower.toAlgHom K K[X] B) y = x →
        (y ∈ U.curveIdempotentAmbientPiece basis e ↔ ∃ j, y ∈ U.curveIdempotentAmbientPiece basis (a j)))
    (hdisj : ∀ i j, i ≠ j → ∀ y : RelativeSpectrum w B,
      comap (IsScalarTower.toAlgHom K K[X] B) y = x →
        y ∈ U.curveIdempotentAmbientPiece basis (a i) →
        y ∈ U.curveIdempotentAmbientPiece basis (a j) → False) :
    ∃ n : ℕ, ∃ V : FCStandardAffinoid w n, ∃ _hxV : x ∈ interior V.carrier,
      ∃ hVU : V.carrier ⊆ U.carrier,
        V.curveIdempotentAmbientPiece basis (U.curveAnalyticNormedRestriction V hVU basis e) =
          ⋃ j, V.curveIdempotentAmbientPiece basis (U.curveAnalyticNormedRestriction V hVU basis (a j)) ∧
        Pairwise (fun i j => Disjoint
          (V.curveIdempotentAmbientPiece basis (U.curveAnalyticNormedRestriction V hVU basis (a i)))
          (V.curveIdempotentAmbientPiece basis (U.curveAnalyticNormedRestriction V hVU basis (a j)))) := by
  let := Module.Finite.of_basis basis
  let φ := IsScalarTower.toAlgHom K K[X] B
  let p : U.CurvePreimage (B := B) → RelativeSpectrum w K[X] := fun y => comap φ y.1
  have hp : IsClosedMap p :=
    (isClosedMap_comap_of_isIntegral φ (RingHom.finite_algebraMap.mpr inferInstance).to_isIntegral).domRestrict
      (U.isClosed_carrier.preimage (continuous_comap φ))
  have hnear := eventually_clopen_fibre_partition_of_central p hp
    (U.curveIdempotentOriginalPiece basis e) (fun j => U.curveIdempotentOriginalPiece basis (a j))
    (U.isClopen_curveIdempotentOriginalPiece basis he)
    (fun j => U.isClopen_curveIdempotentOriginalPiece basis (ha j)) x
    (by
      intro y hy
      simpa only [U.mem_curveIdempotentAmbientPiece_iff basis e y.1 y.2,
        U.mem_curveIdempotentAmbientPiece_iff basis (a _) y.1 y.2] using hcover y.1 hy)
    (by
      intro i j hij y hy hi hj
      exact hdisj i j hij y.1 hy
        ((U.mem_curveIdempotentAmbientPiece_iff basis (a i) y.1 y.2).mpr hi)
        ((U.mem_curveIdempotentAmbientPiece_iff basis (a j) y.1 y.2).mpr hj))
  obtain ⟨n,V,hxV,hV⟩ := fc_exists_standardAffinoid_nhds x
    (Filter.inter_mem hnear (isOpen_interior.mem_nhds hx))
  let hVU : V.carrier ⊆ U.carrier := fun y hy => interior_subset (hV hy).2
  have hpiece (c : U.CurveAnalyticAlgebra basis) :
      V.curveIdempotentAmbientPiece basis (U.curveAnalyticNormedRestriction V hVU basis c) =
        U.curveIdempotentAmbientPiece basis c ∩ comap φ ⁻¹' V.carrier :=
    U.curveIdempotentAmbientPiece_restriction V hVU basis c
  refine ⟨n,V,hxV,hVU,?_,?_⟩
  · ext y
    rw [hpiece]
    constructor
    · rintro ⟨hyC,hyV⟩
      have hyU := hVU hyV
      have hyC' := (U.mem_curveIdempotentAmbientPiece_iff basis e y hyU).mp hyC
      obtain ⟨j,hj⟩ := ((hV hyV).1.1 ⟨y,hyU⟩ rfl).mp hyC'
      apply Set.mem_iUnion.mpr
      refine ⟨j,?_⟩
      rw [hpiece]
      exact ⟨(U.mem_curveIdempotentAmbientPiece_iff basis (a j) y hyU).mpr hj,hyV⟩
    · intro hy
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hy
      rw [hpiece] at hj
      have hyU := hVU hj.2
      have hj' := (U.mem_curveIdempotentAmbientPiece_iff basis (a j) y hyU).mp hj.1
      exact ⟨(U.mem_curveIdempotentAmbientPiece_iff basis e y hyU).mpr
        (((hV hj.2).1.1 ⟨y,hyU⟩ rfl).mpr ⟨j,hj'⟩),hj.2⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro y hi hj
    rw [hpiece] at hi hj
    have hyU := hVU hi.2
    exact (hV hi.2).1.2 i j hij ⟨y,hyU⟩ rfl
      ((U.mem_curveIdempotentAmbientPiece_iff basis (a i) y hyU).mp hi.1)
      ((U.mem_curveIdempotentAmbientPiece_iff basis (a j) y hyU).mp hj.1)

end FCStandardAffinoid

namespace FCStandardAffinoid
variable {m n : ℕ} (U : FCStandardAffinoid w m) (V : FCStandardAffinoid w n)

omit [Fintype ι] in
/-- Restriction through an actual central carrier point preserves its ENTIRE central piece. -/
theorem curveIdempotentAmbientPiece_central_restriction (hVU : V.carrier ⊆ U.carrier)
    (basis : Module.Basis ι K[X] B) (e : U.CurveAnalyticAlgebra basis)
    (x : RelativeSpectrum w K[X]) (hx : x ∈ V.carrier) :
    V.curveIdempotentAmbientPiece basis (U.curveAnalyticNormedRestriction V hVU basis e) ∩
        comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' {x} =
      U.curveIdempotentAmbientPiece basis e ∩ comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' {x} := by
  rw [U.curveIdempotentAmbientPiece_restriction V hVU basis e]
  ext y
  constructor
  · exact fun hy => ⟨hy.1.1,hy.2⟩
  · rintro ⟨hy,hyx⟩
    have hyV : comap (IsScalarTower.toAlgHom K K[X] B) y ∈ V.carrier := by
      rw [show comap (IsScalarTower.toAlgHom K K[X] B) y = x from hyx]
      exact hx
    exact ⟨⟨hy,hyV⟩,hyx⟩

end FCStandardAffinoid

namespace FCStandardAffinoid
variable {m : ℕ} (U : FCStandardAffinoid w m)

/-- Every fixed genuine original analytic piece has a CONSTRUCTED finite singleton
refinement subordinate to ANY original point neighbourhoods on its actual central fibre. -/
theorem exists_standardAffinoid_piece_refinement
    (basis : Module.Basis ι K[X] B) {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (x : RelativeSpectrum w K[X]) (hx : x ∈ interior U.carrier)
    (N : U.CurveCentralPiece basis e x → Set (RelativeSpectrum w B))
    (hN : ∀ i, N i ∈ 𝓝 i.1) :
    ∃ n : ℕ, ∃ V : FCStandardAffinoid w n, ∃ _hxV : x ∈ interior V.carrier,
      ∃ hVU : V.carrier ⊆ U.carrier,
        ∃ a : U.CurveCentralPiece basis e x → V.CurveAnalyticAlgebra basis,
          (∀ i, IsIdempotentElem (a i)) ∧
          (∀ i, V.curveIdempotentAmbientPiece basis (a i) ⊆ N i ∧
            V.curveIdempotentAmbientPiece basis (a i) ∩
              comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' {x} = {i.1}) ∧
          V.curveIdempotentAmbientPiece basis (U.curveAnalyticNormedRestriction V hVU basis e) =
            ⋃ i, V.curveIdempotentAmbientPiece basis (a i) ∧
          Pairwise (fun i j => Disjoint (V.curveIdempotentAmbientPiece basis (a i))
            (V.curveIdempotentAmbientPiece basis (a j))) := by
  let I := U.CurveCentralPiece basis e x
  let : Finite I := U.finite_curveCentralPiece basis e x
  have hpieces (i : I) :
      ∃ k : ℕ, ∃ V : FCStandardAffinoid w k, ∃ _hxV : x ∈ interior V.carrier,
        ∃ a : V.CurveAnalyticAlgebra basis, IsIdempotentElem a ∧
          V.curveIdempotentAmbientPiece basis a ⊆ N i ∧
          V.curveIdempotentAmbientPiece basis a ∩
            comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' {x} = {i.1} := by
    have hsub : {i.1} ⊆ comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' {x} := by
      rintro z (rfl : z = i.1)
      exact i.2.2
    have hNi : N i ∈ 𝓝ˢ ({i.1} : Set (RelativeSpectrum w B)) := by
      simpa only [nhdsSet_singleton] using hN i
    obtain ⟨k,V,hxV,a,ha,hVN,hcl,hcentral⟩ :=
      exists_standardAffinoid_analytic_piece_subset x basis {i.1} hsub (N i) hNi
    exact ⟨k,V,hxV,a,ha,hVN,hcentral⟩
  choose k Vi hxVi ai hai hiN hicentral using hpieces
  let Base : Option I → Set (RelativeSpectrum w K[X]) :=
    fun o => o.elim (interior U.carrier) (fun i => interior (Vi i).carrier)
  have hBase (o : Option I) : Base o ∈ 𝓝 x := by
    cases o with
    | none => exact isOpen_interior.mem_nhds hx
    | some i => exact isOpen_interior.mem_nhds (hxVi i)
  obtain ⟨n,V,hxV,hV⟩ := fc_exists_standardAffinoid_common_nhds x Base hBase
  let hVU : V.carrier ⊆ U.carrier := fun z hz => interior_subset (hV none hz)
  let hVVi (i : I) : V.carrier ⊆ (Vi i).carrier := fun z hz => interior_subset (hV (some i) hz)
  let er := U.curveAnalyticNormedRestriction V hVU basis e
  let ar : I → V.CurveAnalyticAlgebra basis :=
    fun i => (Vi i).curveAnalyticNormedRestriction V (hVVi i) basis (ai i)
  have her : IsIdempotentElem er := he.map _
  have har (i : I) : IsIdempotentElem (ar i) := (hai i).map _
  have hcent (i : I) : V.curveIdempotentAmbientPiece basis (ar i) ∩
      comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' {x} = {i.1} :=
    ((Vi i).curveIdempotentAmbientPiece_central_restriction V (hVVi i) basis (ai i) x
      (interior_subset hxV)).trans (hicentral i)
  have hcentR : V.curveIdempotentAmbientPiece basis er ∩
      comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' {x} =
        U.curveIdempotentAmbientPiece basis e ∩ comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' {x} :=
    U.curveIdempotentAmbientPiece_central_restriction V hVU basis e x (interior_subset hxV)
  have hiiff (i : I) (y : RelativeSpectrum w B)
      (hy : comap (IsScalarTower.toAlgHom K K[X] B) y = x) :
      y ∈ V.curveIdempotentAmbientPiece basis (ar i) ↔ y = i.1 := by
    simpa only [Set.mem_inter_iff,hy,Set.mem_preimage,Set.mem_singleton_iff,and_true] using
      Set.ext_iff.mp (hcent i) y
  obtain ⟨l,W,hxW,hWV,hpartition,hpair⟩ :=
    V.exists_standardAffinoid_restrict_piece_partition basis her ar har x hxV
      (by
        intro y hy
        constructor
        · intro hyR
          have hyU := (Set.ext_iff.mp hcentR y).mp ⟨hyR,hy⟩
          let i : I := ⟨y,hyU.1,hy⟩
          exact ⟨i,(hiiff i y hy).mpr rfl⟩
        · rintro ⟨i,hi⟩
          have hiy := (hiiff i y hy).mp hi
          subst y
          exact ((Set.ext_iff.mp hcentR i.1).mpr ⟨i.2.1,i.2.2⟩).1)
      (by
        intro i j hij y hy hi hj
        apply hij
        apply Subtype.ext
        exact ((hiiff i y hy).mp hi).symm.trans ((hiiff j y hy).mp hj))
  let a : I → W.CurveAnalyticAlgebra basis :=
    fun i => V.curveAnalyticNormedRestriction W hWV basis (ar i)
  have hWU : W.carrier ⊆ U.carrier := hWV.trans hVU
  have hrestriction : V.curveAnalyticNormedRestriction W hWV basis er =
      U.curveAnalyticNormedRestriction W hWU basis e := by
    apply (W.curveAnalyticOriginalEquiv basis).injective
    change (V.curveAnalyticRestriction W hWV)
      (U.curveAnalyticRestriction V hVU (U.curveAnalyticOriginalEquiv basis e)) =
        U.curveAnalyticRestriction W hWU (U.curveAnalyticOriginalEquiv basis e)
    induction U.curveAnalyticOriginalEquiv basis e using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add r s hr hs => simp only [map_add,hr,hs]
    | tmul r b =>
      rw [U.curveAnalyticRestriction_tmul,V.curveAnalyticRestriction_tmul,U.curveAnalyticRestriction_tmul]
      exact congrArg (fun r : W.AnalyticFunctions => r ⊗ₜ[K[X]] b)
        (RingHom.congr_fun (U.analyticRestriction_comp V hVU W hWV) r)
  refine ⟨l,W,hxW,hWU,a,fun i => (har i).map _,?_,?_,hpair⟩
  · intro i
    constructor
    · intro y hy
      have hyV := (V.curveIdempotentAmbientPiece_restriction W hWV basis (ar i)) ▸ hy
      have hyVi := ((Vi i).curveIdempotentAmbientPiece_restriction V (hVVi i) basis (ai i)) ▸ hyV.1
      exact hiN i hyVi.1
    · exact (V.curveIdempotentAmbientPiece_central_restriction W hWV basis (ar i) x
        (interior_subset hxW)).trans (hcent i)
  · rw [hrestriction] at hpartition
    exact hpartition

end FCStandardAffinoid

end Berkovich.RelativeSpectrum
end EnvelopeProperty
