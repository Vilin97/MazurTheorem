/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts

/-!
# Degree-zero exactness of the Cech complex

For a sheaf valued in an abelian category, the restriction map from sections on the
union of a family of opens is the kernel of the first Cech restriction-difference map.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u

namespace TopCat.Sheaf

open Presheaf.SheafConditionEqualizerProducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasProducts C]
variable {X : TopCat.{w}} {ι : Type w} (F : X.Sheaf C) (U : ι → Opens X)

/-- The equalizer fork from the sheaf condition, viewed as the kernel of the first
Cech restriction-difference map. -/
private noncomputable def cechResSubKernelFork :
    KernelFork (leftRes F.presheaf U - rightRes F.presheaf U) :=
  Preadditive.kernelForkOfFork (fork F.presheaf U)

/-- Sections on the union of the opens are the kernel of the first Cech differential. -/
private noncomputable def isLimitCechResSub : IsLimit (cechResSubKernelFork F U) :=
  Preadditive.isLimitKernelForkOfFork
    ((F.presheaf.isSheaf_iff_isSheafEqualizerProducts.mp F.2 U).some)

/-- The augmentation and first restriction-difference map of the Cech complex. -/
noncomputable def cechZeroShortComplex : ShortComplex C :=
  ShortComplex.mk (res F.presheaf U) (leftRes F.presheaf U - rightRes F.presheaf U)
    (by rw [Preadditive.comp_sub, w, sub_self])

/-- The Cech complex of a sheaf is exact at degree zero. -/
theorem cechZeroShortComplex_exact : (cechZeroShortComplex F U).Exact := by
  apply ShortComplex.exact_of_f_is_kernel
  refine IsLimit.ofIsoLimit (isLimitCechResSub F U) ?_
  apply Fork.ext (Iso.refl _)

end TopCat.Sheaf
