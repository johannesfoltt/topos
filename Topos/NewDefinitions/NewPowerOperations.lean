import Topos.NewDefinitions.NewPower

namespace CategoryTheory

open Category MonoidalCategory CartesianMonoidalCategory Classifier PowerObject

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [Classifier C]

namespace PowerObject

variable (op : (Ω : C) ⊗ (Ω : C) ⟶ (Ω : C)) (X : C) [PowerObject X]

-- The morphism duplicating the first component
abbrev PowBraiding : X ⊗ ((pow X) ⊗ (pow X) : C) ⟶ (X ⊗ pow X) ⊗ (X ⊗ pow X) :=
  lift ((𝟙 X) ⊗ (fst _ _)) ((𝟙 X) ⊗ (snd _ _))

def PowOperation : (pow X) ⊗ (pow X) ⟶ (pow X) :=
  ((PowBraiding X) ≫ (in_ ⊗ in_) ≫ op)^

variable {X} {Y : C}

theorem PowOperation_transpose_ClassifierOperation (s₀ s₁ : X ⊗ Y ⟶ Ω) : (lift s₀ s₁ ≫ op)^ = (lift (s₀^) (s₁^)) ≫ PowOperation op X  := by {
  apply uniq
  have comm_UL : ((𝟙 X) ⊗ (lift (s₀^) (s₁^))) ≫ PowBraiding X = diag (X ⊗ Y) ≫ (((𝟙 X) ⊗ (s₀^)) ⊗ ((𝟙 X) ⊗ (s₁^))) := by aesop_cat
  have comm_UM : (((𝟙 X) ⊗ (s₀^)) ⊗ ((𝟙 X) ⊗ (s₁^))) ≫ (in_ ⊗ in_) = s₀ ⊗ s₁ := by {
    refine hom_ext (((𝟙 X ⊗ s₀^) ⊗ 𝟙 X ⊗ s₁^) ≫ (in_ ⊗ in_)) (s₀ ⊗ s₁) ?_ ?_
    · rw [tensorHom_fst, ← tensor_comp, tensorHom_fst, comm]
    · rw [tensorHom_snd, ← tensor_comp, tensorHom_snd, comm]
  }
  have comm_UML : ((𝟙 X) ⊗ (lift (s₀^) (s₁^))) ≫ PowBraiding X ≫ (in_ ⊗ in_) = diag (X ⊗ Y) ≫ (s₀ ⊗ s₁) := by rw [← assoc, comm_UL, assoc, comm_UM]
  have comm_L : ((𝟙 X) ⊗ (PowOperation op X)) ≫ in_ = PowBraiding X ≫ (in_ ⊗ in_) ≫ op := comm (PowBraiding X ≫ (in_ ⊗ in_) ≫ op)
  nth_rewrite 2 [← id_comp s₀, ← id_comp s₁]
  rw [← comp_id (𝟙 X), tensor_comp, ← lift_map, ← comm_UML, assoc, comm_L, assoc, assoc]
}

lemma PowOperation_nameClassifierOperation (s₀ s₁ : X ⟶ Ω) : ⌜(lift s₀ s₁ ≫ op)⌝ = lift ⌜s₀⌝ ⌜s₁⌝ ≫ PowOperation op X := by {
  unfold name
  rw [comp_lift_assoc]
  exact PowOperation_transpose_ClassifierOperation op (fst X (𝟙_ C) ≫ s₀) (fst X (𝟙_ C) ≫ s₁)
}

theorem PowOperation_transposeInv_ClassifierOperation (s₀ s₁ : Y ⟶ pow X) : (lift s₀ s₁ ≫ PowOperation op X)^ = (lift (s₀^) (s₁^)) ≫ op := by {
  nth_rw 1 [← transpose_right_inv s₀, ← transpose_right_inv s₁, ← PowOperation_transpose_ClassifierOperation, transpose_left_inv]
}
