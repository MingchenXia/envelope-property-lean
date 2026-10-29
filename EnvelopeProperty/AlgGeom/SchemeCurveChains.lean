import EnvelopeProperty.AlgGeom.AffineCurveChains
import EnvelopeProperty.AlgGeom.SchemeCurveDimensions
import Mathlib.AlgebraicGeometry.Noetherian
import Hironaka.Scheme.Defs

/-!
# Actual closed integral curve chains in finite-type schemes

A step is witnessed by an actual dimension-one integral scheme and an actual
closed immersion into the ORIGINAL scheme. Affine curve closures and actual
component inclusions therefore give scheme curves with their original points,
not merely chains in auxiliary coordinate rings.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
universe u

namespace EnvelopeProperty.FcSchemeCurveChains

variable {X Y : Scheme.{u}}

/-- Two original scheme points lie on one actual closed integral curve. -/
def CurveStep (x y : X) : Prop :=
  ∃ (C : Scheme.{u}) (i : C ⟶ X), IsClosedImmersion i ∧ IsIntegral C ∧
    topologicalKrullDim C = 1 ∧ x ∈ Set.range i ∧ y ∈ Set.range i

/-- A finite chain of actual closed integral curves in the original scheme,
allowing the empty chain at equal points. -/
def CurveChain (x y : X) : Prop := Relation.ReflTransGen CurveStep x y

theorem CurveStep.symm {x y : X} (h : CurveStep x y) : CurveStep y x := by
  obtain ⟨C, i, hi, hC, hd, hx, hy⟩ := h
  exact ⟨C, i, hi, hC, hd, hy, hx⟩

theorem CurveChain.refl (x : X) : CurveChain x x := Relation.ReflTransGen.refl

theorem CurveChain.trans {x y z : X} (hxy : CurveChain x y) (hyz : CurveChain y z) :
    CurveChain x z := Relation.ReflTransGen.trans hxy hyz

theorem CurveStep.curveChain {x y : X} (h : CurveStep x y) : CurveChain x y :=
  Relation.ReflTransGen.single h

theorem CurveChain.symm {x y : X} (h : CurveChain x y) : CurveChain y x := by
  induction h with
  | refl => exact CurveChain.refl _
  | tail _hxy hyz ih => exact hyz.symm.curveChain.trans ih

/-- Actual component inclusions transport actual scheme curves by composition
of closed immersions, retaining the actual source curve and its dimension. -/
theorem curveStep_map_closedImmersion (f : X ⟶ Y) [IsClosedImmersion f]
    {x y : X} (hxy : CurveStep x y) : CurveStep (f x) (f y) := by
  obtain ⟨C, i, hi, hC, hd, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hxy
  have : IsClosedImmersion i := hi
  refine ⟨C, i ≫ f, inferInstance, hC, hd, ⟨a, ?_⟩, ⟨b, ?_⟩⟩
  · change f (i a) = f x
    rw [ha]
  · change f (i b) = f y
    rw [hb]

theorem curveChain_map_closedImmersion (f : X ⟶ Y) [IsClosedImmersion f]
    {x y : X} (hxy : CurveChain x y) : CurveChain (f x) (f y) := by
  induction hxy with
  | refl => exact CurveChain.refl _
  | tail _hxy hyz ih => exact ih.trans (curveStep_map_closedImmersion f hyz).curveChain

variable {F : Type u} [Field F]

/-- An actual affine prime quotient step closes to an actual integral closed
curve of dimension one in the ORIGINAL scheme. -/
theorem curveStep_of_affine (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f]
    {U : X.Opens} (hU : IsAffineOpen U) {x y : PrimeSpectrum Γ(X, U)}
    (hxy : FcCurveChains.CurveStep x y) :
    CurveStep (hU.fromSpec x) (hU.fromSpec y) := by
  obtain ⟨P, hP, hd, hx, hy⟩ := hxy
  obtain ⟨I, hI, hId, hpre⟩ :=
    FcSchemeCurveDimensions.exists_closed_integral_curve_of_affine_prime f hU P hP hd
  let ι : PrimeSpectrum Γ(X, U) → X := hU.fromSpec
  have hpre' : ι ⁻¹' (I.support : Set X) = PrimeSpectrum.zeroLocus (P : Set Γ(X, U)) := hpre
  refine ⟨I.subscheme, I.subschemeι, inferInstance, hI, hId, ?_, ?_⟩
  · rw [I.range_subschemeι]
    change x ∈ ι ⁻¹' (I.support : Set X)
    rw [hpre']
    exact hx
  · rw [I.range_subschemeι]
    change y ∈ ι ⁻¹' (I.support : Set X)
    rw [hpre']
    exact hy

theorem curveChain_of_affine (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f]
    {U : X.Opens} (hU : IsAffineOpen U) {x y : PrimeSpectrum Γ(X, U)}
    (hxy : FcCurveChains.CurveChain x y) :
    CurveChain (hU.fromSpec x) (hU.fromSpec y) := by
  induction hxy with
  | refl => exact CurveChain.refl _
  | tail _hxy hyz ih => exact ih.trans (curveStep_of_affine f hU hyz).curveChain

variable [IsAlgClosed F]

/-- Original closed points in a common affine open of an integral scheme are
joined by genuine CLOSED curves in the whole original scheme. -/
theorem curveChain_of_common_affine (f : X ⟶ Spec (CommRingCat.of F))
    [LocallyOfFiniteType f] [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)
    (x y : X) (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set X))
    (hxU : x ∈ U) (hyU : y ∈ U) : CurveChain x y := by
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : Algebra F Γ(X, U) := (FiniteTypePoint.affineBaseMap f hU).toAlgebra
  have : Algebra.FiniteType F Γ(X, U) := FiniteTypePoint.affineBaseMap_finiteType f hU
  let a := hU.primeIdealOf ⟨x, hxU⟩
  let b := hU.primeIdealOf ⟨y, hyU⟩
  let ι : PrimeSpectrum Γ(X, U) → X := hU.fromSpec
  have hι : Topology.IsOpenEmbedding ι := hU.fromSpec.isOpenEmbedding
  have ha : ι a = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hb : ι b = y := hU.fromSpec_primeIdealOf ⟨y, hyU⟩
  have hac : IsClosed ({a} : Set (PrimeSpectrum Γ(X, U))) :=
    preimage_closedPoints_subset hι.injective hι.continuous (by
      change IsClosed ({ι a} : Set X)
      rwa [ha])
  have hbc : IsClosed ({b} : Set (PrimeSpectrum Γ(X, U))) :=
    preimage_closedPoints_subset hι.injective hι.continuous (by
      change IsClosed ({ι b} : Set X)
      rwa [hb])
  have hlocal := FcAffineCurveChains.curveChain_of_isClosed (F := F) a b hac hbc
  have hglobal := curveChain_of_affine f hU hlocal
  change CurveChain (ι a) (ι b) at hglobal
  simpa only [ha, hb] using hglobal

/-- Every two closed points of an actual integral scheme locally of finite
type over an algebraically closed field are joined by actual closed integral
curves. A closed point in a constructed affine intersection glues both chains. -/
theorem curveChain_of_integral (f : X ⟶ Spec (CommRingCat.of F))
    [LocallyOfFiniteType f] [IsIntegral X] (x y : X)
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set X)) : CurveChain x y := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : X.Opens) from trivial)
  have hUV : ((U : Set X) ∩ V).Nonempty :=
    nonempty_preirreducible_inter U.isOpen V.isOpen ⟨x, hxU⟩ ⟨y, hyV⟩
  obtain ⟨z, ⟨hzU, hzV⟩, hzc⟩ := nonempty_inter_closedPoints hUV
    (U.isOpen.inter V.isOpen).isLocallyClosed
  exact (curveChain_of_common_affine f hU x z hx hzc hxU hzU).trans
    (curveChain_of_common_affine f hV z y hzc hy hzV hyV)

/-- Two original closed points in any actual irreducible closed subset are
joined by actual closed curves in the ORIGINAL scheme. The integral reduced
component scheme and both endpoint lifts are constructed. -/
theorem curveChain_of_common_irreducible_closed
    (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f]
    (Z : Closeds X) (hZ : IsIrreducible (Z : Set X)) (x y : X)
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set X))
    (hxZ : x ∈ Z) (hyZ : y ∈ Z) : CurveChain x y := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have : IsIntegral I.subscheme := FcSchemeCurveDimensions.isIntegral_vanishingIdeal_subscheme Z hZ
  have hxrange : x ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hxZ
  have hyrange : y ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hyZ
  obtain ⟨a, ha⟩ := hxrange
  obtain ⟨b, hb⟩ := hyrange
  have hac : IsClosed ({a} : Set I.subscheme) :=
    preimage_closedPoints_subset I.subschemeι.isClosedEmbedding.injective I.subschemeι.continuous (by
      change IsClosed ({I.subschemeι a} : Set X)
      rwa [ha])
  have hbc : IsClosed ({b} : Set I.subscheme) :=
    preimage_closedPoints_subset I.subschemeι.isClosedEmbedding.injective I.subschemeι.continuous (by
      change IsClosed ({I.subschemeι b} : Set X)
      rwa [hb])
  have hlocal := curveChain_of_integral (I.subschemeι ≫ f) a b hac hbc
  simpa only [ha, hb] using curveChain_map_closedImmersion I.subschemeι hlocal

/-- The source curve-chain theorem for arbitrary connected finite-type
schemes over an algebraically closed field. All curves are actual integral
closed subschemes of the ORIGINAL X of global dimension one. No reducedness,
irreducibility, separatedness, cover, lifting or class-count assumption occurs. -/
theorem curveChain_of_connected_finiteType
    (f : X ⟶ Spec (CommRingCat.of F)) [FiniteType f] [PreconnectedSpace X]
    (x y : X) (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set X)) :
    CurveChain x y := by
  classical
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  let S : Set (Set X) := {Z | ∃ z : X, IsClosed ({z} : Set X) ∧ z ∈ Z ∧ CurveChain x z}
  let U : Set X := ⋃ Z ∈ irreducibleComponents X ∩ S, Z
  let V : Set X := ⋃ Z ∈ irreducibleComponents X \ S, Z
  have hfinite := NoetherianSpace.finite_irreducibleComponents (α := X)
  have hUc : IsClosed U :=
    (hfinite.inter_of_left S).isClosed_biUnion fun Z hZ =>
      isClosed_of_mem_irreducibleComponents Z hZ.1
  have hVc : IsClosed V :=
    hfinite.sdiff.isClosed_biUnion fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  have hcover (z : X) : z ∈ U ∨ z ∈ V := by
    have hZ := irreducibleComponent_mem_irreducibleComponents z
    by_cases hZS : irreducibleComponent z ∈ S
    · exact Or.inl (Set.mem_iUnion₂.mpr
        ⟨irreducibleComponent z, ⟨hZ, hZS⟩, mem_irreducibleComponent⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr
        ⟨irreducibleComponent z, ⟨hZ, hZS⟩, mem_irreducibleComponent⟩)
  have hdisjoint : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro z hzU hzV
    obtain ⟨Z, ⟨hZ, hZS⟩, hzZ⟩ := Set.mem_iUnion₂.mp hzU
    obtain ⟨W, ⟨hW, hWS⟩, hzW⟩ := Set.mem_iUnion₂.mp hzV
    obtain ⟨w, hw, hwZ, hxw⟩ := hZS
    have hZc := isClosed_of_mem_irreducibleComponents Z hZ
    have hWc := isClosed_of_mem_irreducibleComponents W hW
    obtain ⟨m, ⟨hmZ, hmW⟩, hmc⟩ := nonempty_inter_closedPoints
      (show (Z ∩ W).Nonempty from ⟨z, hzZ, hzW⟩) (hZc.inter hWc).isLocallyClosed
    have hwm : CurveChain w m := curveChain_of_common_irreducible_closed f ⟨Z, hZc⟩ hZ.1
      w m hw hmc hwZ hmZ
    exact hWS ⟨m, hmc, hmW, hxw.trans hwm⟩
  have hcomp : Uᶜ = V := by
    ext z
    constructor
    · exact fun hz => (hcover z).resolve_left hz
    · exact fun hzV hzU => Set.disjoint_left.mp hdisjoint hzU hzV
  have hUopen : IsOpen U := by
    rw [← isClosed_compl_iff, hcomp]
    exact hVc
  have hxU : x ∈ U := Set.mem_iUnion₂.mpr ⟨irreducibleComponent x,
    ⟨irreducibleComponent_mem_irreducibleComponents x,
      ⟨x, hx, mem_irreducibleComponent, CurveChain.refl x⟩⟩, mem_irreducibleComponent⟩
  have hUall : U = Set.univ := IsClopen.eq_univ ⟨hUc, hUopen⟩ ⟨x, hxU⟩
  have hyU : y ∈ U := hUall ▸ Set.mem_univ y
  obtain ⟨Z, ⟨hZ, hZS⟩, hyZ⟩ := Set.mem_iUnion₂.mp hyU
  obtain ⟨w, hw, hwZ, hxw⟩ := hZS
  exact hxw.trans (curveChain_of_common_irreducible_closed f
    ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩ hZ.1 w y hw hy hwZ hyZ)

end EnvelopeProperty.FcSchemeCurveChains
