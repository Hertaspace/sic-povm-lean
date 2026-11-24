/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified for this repository: the two theorems below are copied verbatim from the files
`Nyll/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayClassSubgroupExistence.lean` and
`.../RayClassSubgroupRealizationEq.lean` of n-yamaguchi-0729/ClassFieldTheory at commit
fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565. At that commit these two files are not yet written as
Lean `module`s, and a `module` cannot import a non-`module` file, so this file restates them as a
`module`. Everything they import is already a `module` upstream. Names and proofs are unchanged.
-/
module

public import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
public import Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassSubgroupFieldAntitone

/-!
# Existence and uniqueness of the class field of a ray-class subgroup

Every subgroup of an ideal-theoretic ray class group is the kernel of the
Frobenius-normalized Artin map of a finite abelian extension, and the class field
is independent of the realization as an actual intermediate field.
-/

@[expose] public section

open scoped NumberField

noncomputable section

universe u

namespace ClassFieldTheory

/-- Every ray-class subgroup has a finite abelian class-field realization. -/
theorem rayClassSubgroup_existence
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m)) :
    Nonempty (RayClassSubgroupRealization K m H) := by
  exact GlobalClassFieldComparison.rayClassSubgroup_existence K m H

/-- Two realizations for the same modulus and subgroup have the same
intermediate field in the chosen separable closure. -/
theorem rayClassSubgroupRealizations_eq
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m))
    (R₁ R₂ : RayClassSubgroupRealization K m H) :
    R₁.extension.1 = R₂.extension.1 := by
  apply le_antisymm
  · exact rayClassSubgroupField_antitone K m (le_refl H) R₂ R₁
  · exact rayClassSubgroupField_antitone K m (le_refl H) R₁ R₂

end ClassFieldTheory
