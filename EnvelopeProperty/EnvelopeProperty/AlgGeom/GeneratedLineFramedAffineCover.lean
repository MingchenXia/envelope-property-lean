import EnvelopeProperty.AlgGeom.GeneratedLineProjectiveAffineMap
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.AlgebraicGeometry.Cover.Directed

/-! # The genuine locally directed affine cover of SAME original line frames -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.GeneratedLineFramedAffineCover
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} (L : X.Modules)

/-- All actual original affine-site opens with a genuine original whole line frame. -/
def FramedAffineSite := {U : X.AffineZariskiSite //
  Nonempty ((Scheme.Modules.pullback U.1.ι).obj L ≅ unitObj U.1.toScheme)}

instance framedAffineSite_partialOrder : PartialOrder (FramedAffineSite L) :=
  inferInstanceAs (PartialOrder {U : X.AffineZariskiSite //
    Nonempty ((Scheme.Modules.pullback U.1.ι).obj L ≅ unitObj U.1.toScheme)})

/-- Actual invertibility internally produces an actual framed affine neighborhood of EVERY original point. -/
theorem exists_framed_affine (hL : IsInvertible L) (x : X) :
    ∃ U : X.AffineZariskiSite, x ∈ U.1 ∧
      Nonempty ((Scheme.Modules.pullback U.1.ι).obj L ≅ unitObj U.1.toScheme) := by
  obtain ⟨ι, V, hV, e⟩ := hL
  have hx : x ∈ ⨆ i, V i := by rw [hV]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  obtain ⟨W, hWa, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hi
  exact ⟨⟨W, hWa⟩, hxW, ⟨restrictTrivialization hWV (e i).some⟩⟩

/-- The genuine whole original-source cover by ALL actual framed affine opens. -/
def framedCover (hL : IsInvertible L) : X.OpenCover :=
  Scheme.Cover.mkOfCovers (FramedAffineSite L)
    (fun U => U.1.1.toScheme) (fun U => U.1.1.ι) (by
      intro x
      obtain ⟨U, hxU, e⟩ := exists_framed_affine L hL x
      exact ⟨⟨U, e⟩, ⟨x, hxU⟩, rfl⟩)

instance framedCover_partialOrder (hL : IsInvertible L) : PartialOrder (framedCover L hL).I₀ :=
  inferInstanceAs (PartialOrder (FramedAffineSite L))

/-- TRUE native affine intersection refinements with restricted actual
frames derive the original cover's local directedness. -/
instance framedCover_locallyDirected (hL : IsInvertible L) :
    (framedCover L hL).LocallyDirected where
  trans {U V} h := (Scheme.AffineZariskiSite.directedCover X).trans (homOfLE h.le)
  trans_id U := (Scheme.AffineZariskiSite.directedCover X).trans_id U.1
  trans_comp h k := (Scheme.AffineZariskiSite.directedCover X).trans_comp (homOfLE h.le) (homOfLE k.le)
  w h := (Scheme.AffineZariskiSite.directedCover X).trans_map (homOfLE h.le)
  directed {U V} x := by
    obtain ⟨W, hWU, hWV, y, hy⟩ :=
      (Scheme.AffineZariskiSite.directedCover X).exists_lift_trans_eq x
    let W' : FramedAffineSite L := ⟨W, ⟨restrictTrivialization
      (Scheme.AffineZariskiSite.toOpens_mono hWU.le) U.2.some⟩⟩
    exact ⟨W', homOfLE hWU.le, homOfLE hWV.le, y, hy⟩
  property_trans h := Scheme.Cover.LocallyDirected.property_trans
    (𝒰 := Scheme.AffineZariskiSite.directedCover X) (homOfLE h.le)

/-- A true original whole frame on each actual framed affine open, selected from its actual property. -/
def frame (U : FramedAffineSite L) :
    (Scheme.Modules.pullback U.1.1.ι).obj L ≅ unitObj U.1.1.toScheme := U.2.some

end EnvelopeProperty.GeneratedLineFramedAffineCover
