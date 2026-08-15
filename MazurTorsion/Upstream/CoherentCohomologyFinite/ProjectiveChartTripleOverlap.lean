/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartRatioTransition

/-!
# Triple-overlap transport for standard projective charts

This file records the open-set and section-transport identities needed to
compare independently extended sections on three standard charts.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

variable (k : Type) [CommRing k] (d : ℕ)

theorem module_presheaf_map_eqToIso_apply
    {X : Scheme.{0}}
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{0})
    {A B A' B' : X.Opens}
    (eA : A = A') (eB : B = B')
    (h : A ≤ B) (h' : A' ≤ B')
    (x : F.obj (.op B)) :
    (eqToIso (congrArg (fun U => F.obj (.op U)) eA)).hom
        (F.map (homOfLE h).op x) =
      F.map (homOfLE h').op
        ((eqToIso
          (congrArg (fun U => F.obj (.op U)) eB)).hom x) := by
  subst A'
  subst B'
  rfl

theorem eqToIso_smul_apply
    {X : Scheme.{0}} (M : X.Modules)
    {U V : X.Opens} (e : U = V)
    (r : Γ(X, U)) (x : Γ(M, U)) :
    (eqToIso (congrArg (fun W => Γ(M, W)) e)).hom
        (r • x) =
      (eqToIso (congrArg (fun W => Γ(X, W)) e)).hom r •
        (eqToIso (congrArg (fun W => Γ(M, W)) e)).hom x := by
  subst V
  rfl

theorem Γ_eqToIso_hom_eq_presheaf_map
    {X : Scheme.{0}} {U V : X.Opens} (h : U = V) :
    (eqToIso (congrArg (fun W => Γ(X, W)) h)).hom =
      X.presheaf.map (eqToHom h.symm).op := by
  subst V
  simp

theorem Γ_eqToIso_inv_eq_presheaf_map
    {X : Scheme.{0}} {U V : X.Opens} (h : U = V) :
    (eqToIso (congrArg (fun W => Γ(X, W)) h)).inv =
      X.presheaf.map (eqToHom h).op := by
  subst V
  simp

theorem presheaf_mapIso_op_inv_eq_Γ_eqToIso_hom
    {X : Scheme.{0}} {U V : X.Opens} (h : U = V) :
    (X.presheaf.mapIso (eqToIso h).op).inv =
      (eqToIso (congrArg (fun W => Γ(X, W)) h)).hom := by
  subst V
  simp

theorem Γ_eqToIso_hom_trans
    {X : Scheme.{0}} {U V W : X.Opens}
    (hUV : U = V) (hVW : V = W) :
    (eqToIso (congrArg (fun T => Γ(X, T)) hUV)).hom ≫
        (eqToIso (congrArg (fun T => Γ(X, T)) hVW)).hom =
      (eqToIso
        (congrArg (fun T => Γ(X, T)) (hUV.trans hVW))).hom := by
  subst V
  subst W
  simp

theorem appIso_inv_eqToIso_transport
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
    {U V : X.Opens} (h : U = V) (s : Γ(X, V)) :
    (eqToIso (congrArg (fun W => Γ(Y, W))
      (congrArg (fun W => f ''ᵁ W) h))).hom
        ((f.appIso U).inv
          ((eqToIso (congrArg
            (fun W => Γ(X, W)) h)).inv s)) =
      (f.appIso V).inv s := by
  subst V
  simp

private theorem image_top_comp_iso_eq
    {A B X : Scheme.{0}} (e : A ≅ B)
    (g : B ⟶ X) [IsOpenImmersion g] :
    (e.hom ≫ g) ''ᵁ (⊤ : A.Opens) =
      g ''ᵁ (⊤ : B.Opens) := by
  rw [Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.opensRange_comp_of_isIso]

theorem appIso_inv_natural_iso_over
    {A B X : Scheme.{0}} (e : A ≅ B)
    (g : B ⟶ X) [IsOpenImmersion g]
    (s : Γ(B, ⊤)) :
    (eqToIso (congrArg (fun U => Γ(X, U))
      (image_top_comp_iso_eq e g))).hom
        (((e.hom ≫ g).appIso ⊤).inv
          (e.hom.appTop s)) =
      (g.appIso ⊤).inv s := by
  let he : e.hom ''ᵁ (⊤ : A.Opens) = (⊤ : B.Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.opensRange_of_isIso]
  let hc :
      g ''ᵁ (e.hom ''ᵁ (⊤ : A.Opens)) =
        (e.hom ≫ g) ''ᵁ (⊤ : A.Opens) :=
    (Scheme.Hom.comp_image e.hom g ⊤).symm
  let ho :
      (e.hom ≫ g) ''ᵁ (⊤ : A.Opens) =
        g ''ᵁ (⊤ : B.Opens) :=
    image_top_comp_iso_eq e g
  have htop :
      e.hom.appTop =
        (eqToIso (congrArg (fun U => Γ(B, U)) he)).inv ≫
          (e.hom.appIso ⊤).hom := by
    rw [Γ_eqToIso_inv_eq_presheaf_map he]
    rw [Scheme.Hom.appIso_hom, ← Category.assoc]
    rw [e.hom.naturality]
    rw [Category.assoc]
    rw [← Functor.map_comp]
    calc
      e.hom.appTop =
          e.hom.appTop ≫ 𝟙 _ := (Category.comp_id _).symm
      _ = e.hom.appTop ≫ A.presheaf.map (𝟙 _) := by
        exact congrArg
          (fun q => e.hom.appTop ≫ q)
          (A.presheaf.map_id _).symm
      _ = _ := by
        congr 1
  rw [htop]
  simp only [ConcreteCategory.comp_apply,
    Scheme.Hom.comp_appIso, Iso.trans_inv,
    Iso.hom_inv_id_apply]
  change
    (eqToIso (congrArg (fun U => Γ(X, U)) ho)).hom
        ((X.presheaf.mapIso (eqToIso hc).op).inv
          ((g.appIso (e.hom ''ᵁ (⊤ : A.Opens))).inv
            ((eqToIso (congrArg
              (fun U => Γ(B, U)) he)).inv s))) =
      (g.appIso ⊤).inv s
  rw [presheaf_mapIso_op_inv_eq_Γ_eqToIso_hom hc]
  rw [← ConcreteCategory.comp_apply,
    Γ_eqToIso_hom_trans hc ho]
  rw [show hc.trans ho =
      congrArg (fun U => g ''ᵁ U) he from
    Subsingleton.elim _ _]
  exact appIso_inv_eqToIso_transport g he s

/-- The product ratio basic open in chart `j` maps to the intersection of
the `j`, `i`, and `l` standard opens. -/
lemma standardAffineCover_image_chartRatio_mul
    (i l j : Fin (d + 1)) :
    standardChartMap k d j ''ᵁ
        chartRatioProductOpen k d i l j =
      standardChart k j ⊓
        (standardChart k i ⊓ standardChart k l) := by
  have hpre_i :
      standardChartMap k d j ⁻¹ᵁ standardChart k i =
        chartRatioOpen k d i j := by
    change
      (standardAffineOpenCover k d).f j ⁻¹ᵁ standardChart k i =
        PrimeSpectrum.basicOpen (chartRatio k d i j)
    exact standardAffineCover_preimage_standardChart k d i j
  have hpre_l :
      standardChartMap k d j ⁻¹ᵁ standardChart k l =
        chartRatioOpen k d l j := by
    change
      (standardAffineOpenCover k d).f j ⁻¹ᵁ standardChart k l =
        PrimeSpectrum.basicOpen (chartRatio k d l j)
    exact standardAffineCover_preimage_standardChart k d l j
  have hpre :
      standardChartMap k d j ⁻¹ᵁ
          (standardChart k i ⊓ standardChart k l) =
        chartRatioOpen k d i j ⊓ chartRatioOpen k d l j := by
    rw [Scheme.Hom.preimage_inf, hpre_i, hpre_l]
  calc
    _ = standardChartMap k d j ''ᵁ
          (chartRatioOpen k d i j ⊓ chartRatioOpen k d l j) := by
      exact congrArg
        (fun U => standardChartMap k d j ''ᵁ U)
        (PrimeSpectrum.basicOpen_mul _ _)
    _ = standardChartMap k d j ''ᵁ
          (standardChartMap k d j ⁻¹ᵁ
            (standardChart k i ⊓ standardChart k l)) := by
      rw [hpre]
    _ = (standardChartMap k d j).opensRange ⊓
          (standardChart k i ⊓ standardChart k l) :=
      Scheme.Hom.image_preimage_eq_opensRange_inf _ _
    _ = _ := by
      have hrange :
          (standardChartMap k d j).opensRange =
            standardChart k j := by
        rw [← Scheme.Hom.image_top_eq_opensRange]
        exact standardAffineCover_image_top k d j
      rw [hrange]

/-- Sections on the product ratio basic open, identified with sections on
the corresponding ambient triple intersection. -/
def chartTripleSectionsIso
    (M : (scheme k d).Modules)
    (i l j : Fin (d + 1)) :
    Γ(chartModule k d M j,
        chartRatioProductOpen k d i l j) ≅
      Γ(M, standardChart k j ⊓
        (standardChart k i ⊓ standardChart k l)) :=
  M.restrictAppIso (standardChartMap k d j)
      (chartRatioProductOpen k d i l j) ≪≫
    eqToIso (congrArg (fun U => Γ(M, U))
      (standardAffineCover_image_chartRatio_mul k d i l j))

/-- A chart-ring scalar restricted to the product ratio basic open and
transported to the corresponding ambient triple intersection. -/
def chartScalarOnTriple
    (i l j : Fin (d + 1))
    (r : chartRing k d j) :
    Γ(scheme k d, standardChart k j ⊓
      (standardChart k i ⊓ standardChart k l)) :=
  let U : (Spec (chartRing k d j)).Opens :=
    chartRatioProductOpen k d i l j
  let q : Γ(Spec (chartRing k d j), U) :=
    (Spec (chartRing k d j)).presheaf.map U.leTop.op
      ((Scheme.ΓSpecIso (chartRing k d j)).inv r)
  (eqToIso (congrArg
    (fun V => Γ(scheme k d, V))
    (standardAffineCover_image_chartRatio_mul
      k d i l j))).hom
    ((ConcreteCategory.hom
      ((standardChartMap k d j).appIso U).inv) q)

/-- Transport from a chart to the ambient triple intersection is
semilinear for the transported chart scalar. -/
theorem chartTripleSectionsIso_hom_smul
    (M : (scheme k d).Modules)
    (i l j : Fin (d + 1))
    (r : chartRing k d j)
    (s : Γ(chartModule k d M j,
      chartRatioProductOpen k d i l j)) :
    (chartTripleSectionsIso k d M i l j).hom (r • s) =
      chartScalarOnTriple k d i l j r •
        (chartTripleSectionsIso k d M i l j).hom s := by
  rw [AlgebraicGeometry.Scheme.Modules.smul_Spec_def]
  dsimp only [chartTripleSectionsIso, chartScalarOnTriple]
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  let U : (Spec (chartRing k d j)).Opens :=
    chartRatioProductOpen k d i l j
  let q : Γ(Spec (chartRing k d j), U) :=
    (Spec (chartRing k d j)).presheaf.map U.leTop.op
      ((Scheme.ΓSpecIso (chartRing k d j)).inv r)
  have hsmul :
      (M.restrictAppIso
          (standardChartMap k d j) U).hom
          (q • s) =
        ((standardChartMap k d j).appIso U).inv q •
          (M.restrictAppIso
            (standardChartMap k d j) U).hom s := by
    exact congrArg
      (fun (φ : _ ⟶ _) => (ConcreteCategory.hom φ) s)
      (AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom
        (standardChartMap k d j) M U q)
  refine (congrArg
    (eqToIso (congrArg (fun V => Γ(M, V))
      (standardAffineCover_image_chartRatio_mul
        k d i l j))).hom hsmul).trans ?_
  exact eqToIso_smul_apply M
    (standardAffineCover_image_chartRatio_mul k d i l j) _ _

/-- Unpacking `chartSectionOnOverlap`: after transport to the ambient
intersection it is simply restriction of the original chart section. -/
@[simp]
theorem chartOverlapSectionsIso_hom_chartSectionOnOverlap
    (M : (scheme k d).Modules)
    (i j : Fin (d + 1))
    (s : Γ(chartModule k d M i, ⊤)) :
    (chartOverlapSectionsIso k d M i j).hom
        (chartSectionOnOverlap k d M i j s) =
      M.presheaf.map (homOfLE inf_le_right).op
        ((chartTopSectionsIso k d M i).hom s) := by
  let x :
      Γ(M, standardChart k j ⊓ standardChart k i) :=
    M.presheaf.map (homOfLE inf_le_right).op
      ((chartTopSectionsIso k d M i).hom s)
  change
    (chartOverlapSectionsIso k d M i j).hom
        ((chartOverlapSectionsIso k d M i j).inv x) = x
  exact
    (chartOverlapSectionsIso k d M i j).inv_hom_id_apply x

/-- Restriction of a chart top section, transported to the ambient
pairwise intersection, is ordinary restriction from that standard open. -/
theorem chartOverlapSectionsIso_hom_restrict_top
    (M : (scheme k d).Modules)
    (i j : Fin (d + 1))
    (s : Γ(chartModule k d M j, ⊤)) :
    (chartOverlapSectionsIso k d M i j).hom
        ((chartModule k d M j).presheaf.map
          (homOfLE
            (show chartRatioOpen k d i j ≤ ⊤ from le_top)).op s) =
      M.presheaf.map (homOfLE inf_le_left).op
        ((chartTopSectionsIso k d M j).hom s) := by
  dsimp only [chartOverlapSectionsIso, chartTopSectionsIso]
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  have hnat :
      (M.restrictAppIso (standardChartMap k d j)
          (chartRatioOpen k d i j)).hom
          ((chartModule k d M j).presheaf.map
            (homOfLE
              (show chartRatioOpen k d i j ≤ ⊤ from le_top)).op s) =
        M.presheaf.map
          (homOfLE
            (Scheme.Hom.image_mono
              (standardChartMap k d j)
              (show chartRatioOpen k d i j ≤ ⊤ from le_top))).op
          ((M.restrictAppIso
            (standardChartMap k d j) ⊤).hom s) := by
    exact congrArg
      (fun (φ : _ ⟶ _) => (ConcreteCategory.hom φ) s)
      (Scheme.Modules.map_restrictAppIso_hom
        (standardChartMap k d j) M
        (homOfLE
          (show chartRatioOpen k d i j ≤ ⊤ from le_top)).op)
  refine (congrArg
    (eqToIso (congrArg (fun U => Γ(M, U))
      (standardAffineCover_image_chartRatio k d i j))).hom
        hnat).trans ?_
  exact
    module_presheaf_map_eqToIso_apply M.presheaf
      (standardAffineCover_image_chartRatio k d i j)
      (standardAffineCover_image_top k d j)
      _ inf_le_left
      ((M.restrictAppIso
        (standardChartMap k d j) ⊤).hom s)

/-- Inclusion of the ambient triple intersection into the `j,l`
pairwise intersection. -/
lemma chartTriple_le_pairJL
    (i l j : Fin (d + 1)) :
    standardChart k j ⊓
          (standardChart k i ⊓ standardChart k l) ≤
      standardChart k j ⊓ standardChart k l :=
  le_inf inf_le_left (inf_le_right.trans inf_le_right)

/-- Inclusion of the ambient triple intersection into the `j,i`
pairwise intersection. -/
lemma chartTriple_le_pairJI
    (i l j : Fin (d + 1)) :
    standardChart k j ⊓
          (standardChart k i ⊓ standardChart k l) ≤
      standardChart k j ⊓ standardChart k i :=
  le_inf inf_le_left (inf_le_right.trans inf_le_left)

/-- Restricting in the affine-chart model and then transporting to the
ambient triple overlap agrees with transporting to the ambient pairwise
overlap and restricting there. -/
theorem chartTripleSectionsIso_hom_restrict_pairJL
    (M : (scheme k d).Modules)
    (i l j : Fin (d + 1))
    (s : Γ(chartModule k d M j,
      chartRatioOpen k d l j)) :
    (chartTripleSectionsIso k d M i l j).hom
        ((chartModule k d M j).presheaf.map
          (homOfLE
            (PrimeSpectrum.basicOpen_mul_le_right
              (chartRatioElement k d i j)
              (chartRatioElement k d l j))).op s) =
      M.presheaf.map
        (homOfLE (chartTriple_le_pairJL k d i l j)).op
        ((chartOverlapSectionsIso k d M l j).hom s) := by
  dsimp only [chartTripleSectionsIso, chartOverlapSectionsIso]
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  have hnat :
      (M.restrictAppIso (standardChartMap k d j)
          (chartRatioProductOpen k d i l j)).hom
          ((chartModule k d M j).presheaf.map
            (homOfLE
              (PrimeSpectrum.basicOpen_mul_le_right
                (chartRatio k d i j)
                (chartRatio k d l j))).op s) =
        M.presheaf.map
          (homOfLE
            (Scheme.Hom.image_mono
              (standardChartMap k d j)
              (PrimeSpectrum.basicOpen_mul_le_right
                (chartRatio k d i j)
                (chartRatio k d l j)))).op
          ((M.restrictAppIso
            (standardChartMap k d j)
            (chartRatioOpen k d l j)).hom s) := by
    exact congrArg
      (fun (φ : _ ⟶ _) => (ConcreteCategory.hom φ) s)
      (Scheme.Modules.map_restrictAppIso_hom
        (standardChartMap k d j) M
        (homOfLE
          (PrimeSpectrum.basicOpen_mul_le_right
            (chartRatio k d i j)
            (chartRatio k d l j))).op)
  refine (congrArg
    (eqToIso (congrArg (fun U => Γ(M, U))
      (standardAffineCover_image_chartRatio_mul
        k d i l j))).hom hnat).trans ?_
  exact
    module_presheaf_map_eqToIso_apply M.presheaf
      (standardAffineCover_image_chartRatio_mul k d i l j)
      (standardAffineCover_image_chartRatio k d l j)
      _ (chartTriple_le_pairJL k d i l j)
      ((M.restrictAppIso
        (standardChartMap k d j)
        (chartRatioOpen k d l j)).hom s)

/-- The analogous restriction identity through the `j,i` pairwise
intersection. -/
theorem chartTripleSectionsIso_hom_restrict_pairJI
    (M : (scheme k d).Modules)
    (i l j : Fin (d + 1))
    (s : Γ(chartModule k d M j,
      chartRatioOpen k d i j)) :
    (chartTripleSectionsIso k d M i l j).hom
        ((chartModule k d M j).presheaf.map
          (homOfLE
            (PrimeSpectrum.basicOpen_mul_le_left
              (chartRatioElement k d i j)
              (chartRatioElement k d l j))).op s) =
      M.presheaf.map
        (homOfLE (chartTriple_le_pairJI k d i l j)).op
        ((chartOverlapSectionsIso k d M i j).hom s) := by
  dsimp only [chartTripleSectionsIso, chartOverlapSectionsIso]
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  have hnat :
      (M.restrictAppIso (standardChartMap k d j)
          (chartRatioProductOpen k d i l j)).hom
          ((chartModule k d M j).presheaf.map
            (homOfLE
              (PrimeSpectrum.basicOpen_mul_le_left
                (chartRatio k d i j)
                (chartRatio k d l j))).op s) =
        M.presheaf.map
          (homOfLE
            (Scheme.Hom.image_mono
              (standardChartMap k d j)
              (PrimeSpectrum.basicOpen_mul_le_left
                (chartRatio k d i j)
                (chartRatio k d l j)))).op
          ((M.restrictAppIso
            (standardChartMap k d j)
            (chartRatioOpen k d i j)).hom s) := by
    exact congrArg
      (fun (φ : _ ⟶ _) => (ConcreteCategory.hom φ) s)
      (Scheme.Modules.map_restrictAppIso_hom
        (standardChartMap k d j) M
        (homOfLE
          (PrimeSpectrum.basicOpen_mul_le_left
            (chartRatio k d i j)
            (chartRatio k d l j))).op)
  refine (congrArg
    (eqToIso (congrArg (fun U => Γ(M, U))
      (standardAffineCover_image_chartRatio_mul
        k d i l j))).hom hnat).trans ?_
  exact
    module_presheaf_map_eqToIso_apply M.presheaf
      (standardAffineCover_image_chartRatio_mul k d i l j)
      (standardAffineCover_image_chartRatio k d i j)
      _ (chartTriple_le_pairJI k d i l j)
      ((M.restrictAppIso
        (standardChartMap k d j)
        (chartRatioOpen k d i j)).hom s)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
