import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

namespace CategoryTheory

open Category Limits

universe u v
variable {C}
variable [Category.{v, u} C] [CartesianMonoidalCategory C]
variable (L : C)

structure LatticeObject where
  bot : ⊤_ C ⟶ L
  top : ⊤_ C ⟶ L
  meet : L ⨯ L ⟶ L
  join : L ⨯ L ⟶ L
  meet_assoc : (prod.map meet (𝟙 L)) ≫ meet = (prod.associator L L L).hom ≫ (prod.map (𝟙 L) meet) ≫ meet := by aesop_cat
  meet_comm : (prod.braiding L L).hom ≫ meet = meet := by aesop_cat
  meet_idem : (diag L) ≫ meet = 𝟙 L := by aesop_cat
  meet_top : (Limits.prod.leftUnitor L).inv ≫ (prod.map top (𝟙 L)) ≫ meet = 𝟙 L := by aesop_cat
  join_assoc : (prod.map join (𝟙 L)) ≫ join = (prod.associator L L L).hom ≫ (prod.map (𝟙 L) join) ≫ join := by aesop_cat
  join_comm : (prod.braiding L L).hom ≫ join = join := by aesop_cat
  join_idem : (diag L) ≫ join = 𝟙 L := by aesop_cat
  join_bot : (Limits.prod.leftUnitor L).inv ≫ (prod.map bot (𝟙 L)) ≫ join = 𝟙 L := by aesop_cat
  absorp_meet_join : (prod.map (diag L) (𝟙 L)) ≫ (prod.associator L L L).hom ≫ (prod.map (𝟙 L) ((prod.braiding L L).hom ≫ join)) ≫ meet = prod.fst := by aesop_cat
  absorp_join_meet : (prod.map (diag L) (𝟙 L)) ≫ (prod.associator L L L).hom ≫ (prod.map (𝟙 L) (prod.braiding L L).hom) ≫ (prod.associator L L L).inv ≫ (prod.map meet (𝟙 L)) ≫ join = prod.fst := by aesop_cat

structure HeytingAlgebraObject extends LatticeObject L where
  imp : L ⨯ L ⟶ L
  imp_refl : (diag L) ≫ imp = (terminal.from L) ≫ top
  meet_fst_imp : (prod.map (diag L) (𝟙 L)) ≫ (prod.associator L L L).hom ≫ (prod.map (𝟙 L) imp) ≫ meet = meet
  meet_snd_imp : (prod.map (diag L) (𝟙 L)) ≫ (prod.associator L L L).hom ≫ (prod.map (𝟙 L) ((prod.braiding L L).hom ≫ imp)) ≫ meet = prod.fst
  imp_meet : (prod.map (𝟙 L) meet) ≫ imp = (prod.lift ((prod.map (𝟙 L) prod.fst) ≫ imp) ((prod.map (𝟙 L) prod.snd) ≫ imp)) ≫ meet

variable [HasPullbacks C]

structure PosetObject where
  graph : C
  graph_inc : graph ⟶ L ⨯ L
  graph_inc_mono : Mono graph_inc
  refl : ∃ (d : L ⟶ graph), d ≫ graph_inc = diag L
  trans : sorry
  antisymm : ∃ (i : (pullback (graph_inc) (graph_inc ≫ (prod.braiding L L).hom)) ⟶ L), i ≫ (diag L) = pullback.fst (graph_inc) (graph_inc ≫ (prod.braiding L L).hom) ≫ graph_inc
