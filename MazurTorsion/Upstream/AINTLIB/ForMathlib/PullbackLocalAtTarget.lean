/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Cartesianness is Zariski-local at the target

A commutative square of schemes

    A ──f──▶ B
    │        │
    g        h
    ▼        ▼
    C ──k──▶ D

is **cartesian** as soon as its restrictions over an open cover `{Uᵢ}` of `B` are cartesian.
Mathlib knows that *morphism properties* can be checked on an open cover of the target
(`IsZariskiLocalAtTarget`) but has no such statement for `IsPullback`; this file supplies it,
by applying `IsZariskiLocalAtTarget (isomorphisms Scheme)` to the comparison morphism
`A ⟶ B ×_D C`.

The consumer is leaf `[a3-ii]` of `[T-E5c-ROUTE-A]`: the square

    E ────▶ E/G
    │        │
    π        π'
    ▼        ▼
    X ────▶ X/G

is cartesian because it is so over each affine chart of `E/G`, where it is `Spec` of the
Galois-descent pushout `Γ(W) ≅ Γ(X) ⊗_{Γ(X)ᴳ} Γ(W)ᴳ`.
-/

universe u v

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory

/-- A morphism between the apexes of two pullback squares over the same cospan, commuting with
both projections, is an isomorphism. -/
theorem IsPullback.isIso_of_isPullback {C : Type*} [Category C] {P P' X Y Z : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {fst' : P' ⟶ X} {snd' : P' ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g)
    (m : P ⟶ P') (hm₁ : m ≫ fst' = fst) (hm₂ : m ≫ snd' = snd) : IsIso m := by
  have hm : m = (h.isoIsPullback X Y h').hom :=
    h'.hom_ext (by rw [hm₁, IsPullback.isoIsPullback_hom_fst])
      (by rw [hm₂, IsPullback.isoIsPullback_hom_snd])
  rw [hm]
  infer_instance

end CategoryTheory

namespace AlgebraicGeometry

/-- **Cartesianness is Zariski-local at the target.** If the square `(f, g, h, k)` commutes and
its restriction over each member of an open cover `{Uᵢ}` of `B` is cartesian, then the square is
cartesian.

The restricted square over `Uᵢ` has apex `f ⁻¹ᵁ Uᵢ`, projections `f ∣_ Uᵢ` and
`(f ⁻¹ᵁ Uᵢ).ι ≫ g`, and cospan `(Uᵢ).ι ≫ h`, `k`. -/
theorem isPullback_of_iSup_eq_top {A B C D : Scheme.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {h : B ⟶ D} {k : C ⟶ D} (w : f ≫ h = g ≫ k)
    {ι : Type v} (U : ι → B.Opens) (hU : iSup U = ⊤)
    (H : ∀ i, IsPullback (f ∣_ U i) ((f ⁻¹ᵁ U i).ι ≫ g) ((U i).ι ≫ h) k) :
    IsPullback f g h k := by
  have hsq : CommSq f g h k := ⟨w⟩
  set q₁ := pullback.fst h k with hq₁
  set q₂ := pullback.snd h k with hq₂
  set u : A ⟶ pullback h k := pullback.lift f g w with hu
  have hu₁ : u ≫ q₁ = f := pullback.lift_fst _ _ _
  have hu₂ : u ≫ q₂ = g := pullback.lift_snd _ _ _
  have hcover : ⨆ i, q₁ ⁻¹ᵁ U i = ⊤ := Scheme.Hom.iSup_preimage_eq_top _ hU
  have hiso : IsIso u := by
    have hloc : (isomorphisms Scheme) u := by
      refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := isomorphisms Scheme)
        (fun i => q₁ ⁻¹ᵁ U i) hcover fun i => ?_
      -- the restricted square over `Uᵢ`, on the pullback side
      have s : IsPullback ((q₁ ⁻¹ᵁ U i).ι) (q₁ ∣_ U i) q₁ ((U i).ι) :=
        (isPullback_morphismRestrict q₁ (U i)).flip
      have t : IsPullback q₂ q₁ k h := (IsPullback.of_hasPullback h k).flip
      have pasted : IsPullback ((q₁ ⁻¹ᵁ U i).ι ≫ q₂) (q₁ ∣_ U i) k
        ((U i).ι ≫ h) :=
        IsPullback.paste_horiz s t
      -- the two apexes agree as opens of `A`
      have hpre : u ⁻¹ᵁ (q₁ ⁻¹ᵁ U i) = f ⁻¹ᵁ U i := by
        rw [← Scheme.Hom.comp_preimage, hu₁]
      set m : (f ⁻¹ᵁ U i : Scheme.{u}) ⟶ (q₁ ⁻¹ᵁ U i : Scheme.{u}) :=
        (A.isoOfEq hpre).inv ≫ (u ∣_ (q₁ ⁻¹ᵁ U i)) with hm
      have hm₁ : m ≫ ((q₁ ⁻¹ᵁ U i).ι ≫ q₂) = (f ⁻¹ᵁ U i).ι ≫ g := by
        rw [hm, Category.assoc, ← Category.assoc (u ∣_ (q₁ ⁻¹ᵁ U i)),
          morphismRestrict_ι, Category.assoc, hu₂, ← Category.assoc, Scheme.isoOfEq_inv_ι]
      have hm₂ : m ≫ (q₁ ∣_ U i) = f ∣_ U i := by
        rw [← cancel_mono (U i).ι, Category.assoc, morphismRestrict_ι, morphismRestrict_ι, hm,
          Category.assoc, ← Category.assoc (u ∣_ (q₁ ⁻¹ᵁ U i)), morphismRestrict_ι,
          Category.assoc, hu₁, ← Category.assoc, Scheme.isoOfEq_inv_ι]
      have hmiso : IsIso m := (H i).flip.isIso_of_isPullback pasted m hm₁ hm₂
      have hrestrict : u ∣_ (q₁ ⁻¹ᵁ U i) = (A.isoOfEq hpre).hom ≫ m := by
        rw [hm, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      show IsIso (u ∣_ (q₁ ⁻¹ᵁ U i))
      rw [hrestrict]
      infer_instance
    exact hloc
  exact IsPullback.of_iso_pullback hsq (asIso u) hu₁ hu₂

/-- **Isomorphisms descend along an fppf base change** (stacks 02L4, applied): if in a cartesian
square the morphism `f` opposite `g` is surjective + flat + quasi-compact and the base-changed
morphism `fst` is an isomorphism, then `g` is an isomorphism. This is the workhorse of the
`[a5-P-fppf]` comparison: an iso after pulling back along the (finite étale, hence fppf) quotient
cover is an iso downstairs. -/
theorem isIso_of_isPullback_of_fppf {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    [Surjective f] [Flat f] [QuasiCompact f] [IsIso fst] : IsIso g := by
  have hg : (isomorphisms Scheme.{u}) g := by
    refine MorphismProperty.of_isPullback_of_descendsAlong
      (P := isomorphisms Scheme.{u}) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ ?_
    exact inferInstanceAs (IsIso fst)
  exact hg

end AlgebraicGeometry
