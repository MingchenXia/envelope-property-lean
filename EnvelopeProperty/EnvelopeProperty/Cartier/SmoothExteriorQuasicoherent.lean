import EnvelopeProperty.Cartier.SmoothEtaleAffineCover
import EnvelopeProperty.Cartier.SmoothSchemeDeRham
import EnvelopeProperty.Cartier.SchemeFrobenius
import EnvelopeProperty.AlgGeom.Canonical.CanonicalLineSheaf
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent

/-! # Quasicoherence of ALL SAME original smooth exterior cotangent sheaves -/
noncomputable section
namespace EnvelopeProperty.Cartier.SmoothExteriorQuasicoherent
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The SAME genuine original affine-chart exterior comparison in EVERY degree. -/
def affineChartIso {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (v : Fin n → Γ(X, V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V
    (Scheme.Modules.restrictFunctor hV.fromSpec).obj
      (CanonicalGeometry.exteriorCotangentSheaf f q) ≅
      AlgebraicGeometry.tilde (CanonicalGeometry.affineExteriorCotangentModule k Γ(X, V) q) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f V
  exact CanonicalGeometry.exteriorCotangentSheafOpenImmersionIso f hV.fromSpec q ≪≫
    eqToIso (congrArg (fun h => CanonicalGeometry.exteriorCotangentSheaf h q)
      (CanonicalGeometry.affineChartStructuralMap_eq_affineStructuralMap f hV)) ≪≫
    CanonicalGeometry.affineExteriorCotangentSheafIso k Γ(X, V)
      (Char0.etaleDifferentialBasis v hv) q

private theorem affineOver_isQuasicoherent {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (v : Fin n → Γ(X, V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (q : ℕ) :
    ((CanonicalGeometry.exteriorCotangentSheaf f q).over V).IsQuasicoherent := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let M := CanonicalGeometry.exteriorCotangentSheaf f q
  have hSpec : (M.restrict hV.fromSpec).IsQuasicoherent :=
    (Scheme.Modules.isQuasicoherent (Spec Γ(X, V))).prop_of_iso
      (affineChartIso f hV v hv q).symm inferInstance
  have hRestrict : ((M.restrict V.ι).restrict hV.isoSpec.inv).IsQuasicoherent :=
    (Scheme.Modules.isQuasicoherent (Spec Γ(X, V))).prop_of_iso
      ((Scheme.Modules.restrictFunctorComp hV.isoSpec.inv V.ι).app M) hSpec
  let : (M.restrict V.ι).IsQuasicoherent :=
    (Scheme.Modules.isQuasicoherent_restrictFunctor_iff hV.isoSpec.symm).mp hRestrict
  let : IsAffine V := hV
  exact Scheme.Modules.isQuasicoherent_over_of_restrict_of_isAffineOpen M V

/-- Original smooth geometry DERIVES actual quasicoherence of EVERY original exterior degree. -/
theorem exterior_isQuasicoherent (n : ℕ) [SmoothOfRelativeDimension n f] (q : ℕ) :
    (CanonicalGeometry.exteriorCotangentSheaf f q).IsQuasicoherent := by
  obtain ⟨U, hU, _, hcover, he⟩ := SmoothEtaleAffineCover.exists_affine_etale_cover f n
  have hlocal (x : X) : ((CanonicalGeometry.exteriorCotangentSheaf f q).over (U x)).IsQuasicoherent := by
    obtain ⟨v, hv⟩ := he x
    exact affineOver_isQuasicoherent f (hU x) v hv q
  have hc : (Opens.grothendieckTopology X).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact hcover
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ (CanonicalGeometry.exteriorCotangentSheaf f q) _ U hc hlocal

/-- The SAME actual Frobenius exterior modules are genuinely quasicoherent, in ALL degrees. -/
theorem frobeniusForm_isQuasicoherent (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) [SmoothOfRelativeDimension n f] (q : ℕ) :
    (SmoothSchemeDeRham.formModule f p q).IsQuasicoherent := by
  let : (CanonicalGeometry.exteriorCotangentSheaf f q).IsQuasicoherent :=
    exterior_isQuasicoherent f n q
  let : IsAffineHom (SchemeFrobenius.map f p) := SchemeFrobenius.isAffineHom_map f p
  exact Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom (SchemeFrobenius.map f p)

end EnvelopeProperty.Cartier.SmoothExteriorQuasicoherent
