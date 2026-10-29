import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechStalkTotal
import ModularCurves.ForMathlib.TotalComplexUpNatHorizontalEdgeHigher

/-! # The SAME original module total Cech augmentation is a genuine quasi-isomorphism -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechTotalQuasiIso
open CategoryTheory Category Limits AlgebraicGeometry TopologicalSpace
open DeligneIllusieLocalContinuationCechModules DeligneIllusieLocalContinuationCechAugmentation
open DeligneIllusieLocalContinuationCechBicomplex DeligneIllusieLocalContinuationCechTotalAugmentation
open DeligneIllusieLocalContinuationCechResolution DeligneIllusieLocalContinuationCechTotalDegreeZero
open DeligneIllusieLocalContinuationCechStalkTotal
universe u
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (E : CochainComplex X.Modules ℕ)

private theorem stalkAxis_exact (x : X) (hU : ⨆ i, U i = ⊤) (q : ℕ) :
    ((ShortComplex.mk (augmentation U (E.X q)) ((complex (E.X q) U).d 0 1)
      (augmentation_comp_d U (E.X q))).map (stalkFunctor X x)).Exact :=
  (augmentation_exact (E.X q) U hU).map (stalkFunctor X x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stalkPositive_exact (x : X) (hU : ⨆ i, U i = ⊤) (q p : ℕ) (hp : 0 < p) :
    ((ShortComplex.mk ((complex (E.X q) U).d (p-1) p) ((complex (E.X q) U).d p (p+1))
      ((complex (E.X q) U).d_comp_d (p-1) p (p+1))).map (stalkFunctor X x)).Exact := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have h := complex_exactAt_positive (E.X q) U hU r
  rw [HomologicalComplex.exactAt_iff' _ r (r+1) (r+2) (by simp) (by simp)] at h
  exact h.map (stalkFunctor X x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- ALL positive degrees of the actual native stalk edge; the honest cover supplies every row internally. -/
theorem stalkAugmentation_quasiIsoAt_succ (x : X) (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    QuasiIsoAt (stalkAugmentation U E x) (n+1) := by
  let (q : ℕ) : Mono ((stalkFunctor X x).map (augmentation U (E.X q))) := by
    let := augmentation_mono (E.X q) U hU
    exact Functor.map_mono (stalkFunctor X x) _
  unfold stalkAugmentation
  apply HomologicalComplex₂.totalUpNatHorizontalEdge_quasiIsoAt_succ
  · exact stalkAxis_exact U E x hU n
  · exact stalkAxis_exact U E x hU (n+1)
  · intro q p _ hp
    exact stalkPositive_exact U E x hU q p hp
  · intro q p _ hp
    exact stalkPositive_exact U E x hU q p hp

/-- The SAME original augmentation mapped to the actual stalk is a quasi-isomorphism in every positive degree. -/
theorem totalAugmentation_stalk_quasiIsoAt_succ (x : X) (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    QuasiIsoAt (((stalkFunctor X x).mapHomologicalComplex (.up ℕ)).map
      (totalAugmentation U E)) (n+1) := by
  apply (quasiIsoAt_iff_comp_right _ (totalStalkIso U E x).hom (n+1)).mp
  rw [totalAugmentation_stalk_square U E x]
  exact stalkAugmentation_quasiIsoAt_succ U E x hU n

private theorem original_isIso_of_stalks {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, IsIso ((stalkFunctor X x).map φ)) : IsIso φ := by
  have : IsIso ((Scheme.Modules.toSheaf X).map φ) := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
    intro x
    exact h x
  exact isIso_of_reflects_iso φ (Scheme.Modules.toSheaf X)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homology_isIso_of_stalks {A B : CochainComplex X.Modules ℕ} (φ : A ⟶ B) (n : ℕ)
    (h : ∀ x : X,
      QuasiIsoAt (((stalkFunctor X x).mapHomologicalComplex (.up ℕ)).map φ) n) :
    IsIso (HomologicalComplex.homologyMap φ n) := by
  apply original_isIso_of_stalks
  intro x
  let G := stalkFunctor X x
  let ψ := (HomologicalComplex.shortComplexFunctor X.Modules (.up ℕ) n).map φ
  have hψ : ShortComplex.QuasiIso (G.mapShortComplex.map ψ) := (h x).quasiIso
  have : IsIso (ShortComplex.homologyMap (G.mapShortComplex.map ψ)) :=
    (ShortComplex.quasiIso_iff _).mp hψ
  have : IsIso (((A.sc n).mapHomologyIso G).hom ≫ G.map (ShortComplex.homologyMap ψ)) := by
    rw [← ShortComplex.mapHomologyIso_hom_naturality ψ G]
    infer_instance
  change IsIso (G.map (ShortComplex.homologyMap ψ))
  exact IsIso.of_isIso_comp_left ((A.sc n).mapHomologyIso G).hom _

/-- ALL positive degrees of the SAME original X.Modules total augmentation, reflected from actual stalks. -/
theorem totalAugmentation_quasiIsoAt_succ (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    QuasiIsoAt (totalAugmentation U E) (n+1) := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact homology_isIso_of_stalks (totalAugmentation U E) (n+1)
    (fun x => totalAugmentation_stalk_quasiIsoAt_succ U E x hU n)

/-- The ENTIRE SAME original module Cech total augmentation is a native quasi-isomorphism. -/
theorem totalAugmentation_quasiIso (hU : ⨆ i, U i = ⊤) :
    QuasiIso (totalAugmentation U E) := by
  rw [quasiIso_iff]
  rintro (_ | n)
  · exact totalAugmentation_quasiIsoAt_zero U E hU
  · exact totalAugmentation_quasiIsoAt_succ U E hU n

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechTotalQuasiIso
