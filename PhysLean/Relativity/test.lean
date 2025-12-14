import Mathlib.Geometry.Manifold.Algebra.LieGroup
import PhysLean.Relativity.MinkowskiMatrix
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Analysis.Matrix.Normed

open minkowskiMatrix Matrix GeneralLinearGroup


def LorentzGroup (d) : Subgroup (GL (Fin 1 ⊕ Fin d) ℝ) where
  carrier := {Λ | (dual Λ.val) * Λ = 1}
  one_mem' := by simp
  mul_mem' := by
    simp only [Set.mem_setOf_eq, Units.val_mul, dual_mul]
    grind
  inv_mem' := by
    intro a h
    apply Matrix.inv_inj
    . replace h := congr_arg (· * a.val⁻¹) h
      simp only [mul_inv_cancel_right_of_invertible, one_mul] at h
      simp only [coe_units_inv, Matrix.mul_inv_rev, inv_inv_of_invertible, inv_one]
      rw [←h, dual_dual]
      simp
    . simp [det_ne_zero a]


namespace LorentzGroup

variable {d}

scoped[LorentzGroup] notation (name := lorentzGroup_notation) "𝓛" => LorentzGroup

instance : Coe (𝓛 d) (Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) where
  coe a := a.val.val

variable (Λ : 𝓛 d)

abbrev toMatrix := Λ.val.val

scoped[LorentzGroup] postfix:max "ᵐ" => LorentzGroup.toMatrix

lemma det_ne_zero : Λᵐ.det ≠ 0 := GeneralLinearGroup.det_ne_zero Λ.val

noncomputable def transpose : 𝓛 d :=
  ⟨GeneralLinearGroup.mkOfDetNeZero Λᵐᵀ (by simp [det_ne_zero]), sorry⟩

open Manifold
open scoped Manifold

open scoped Matrix.Norms.Operator

open scoped Manifold



instance (n : Type*) [Fintype n] [DecidableEq n] :
    LieGroup 𝓘(ℝ, Matrix n n ℝ) ⊤
      (GeneralLinearGroup n ℝ) := by
infer_instance
