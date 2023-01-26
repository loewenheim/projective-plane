import Mathlib.Logic.Basic

variable {P L : Type}

class Geometry (P : Type _) where
  line : Type _
  incidence : Membership P line

attribute [instance] Geometry.incidence

namespace Geometry
variable {p q r s: P}


def collinear [Geometry P] (p q r : P) : Prop :=
  ∃ l : line P, p ∈ l ∧ q ∈ l ∧ r ∈ l 

def isQuadrangle [Geometry P] (p q r s : P) : Prop :=
    ¬ collinear p q r
  ∧ ¬ collinear p q s
  ∧ ¬ collinear p r s
  ∧ ¬ collinear q r s

instance dual [Geometry P] : Geometry (line P) where
  line := P
  incidence := ⟨fun l p => p ∈ l⟩

theorem triangle_rotate [Geometry P] : ¬ collinear p q r -> ¬ collinear q r p := by
  simp[collinear]
  intro triangle_pqr l hq hr hp
  apply triangle_pqr <;> assumption

theorem quadrangle_rotate [Geometry P] : isQuadrangle p q r s -> isQuadrangle q r s p := by
  intro ⟨triangle_pqr, triangle_pqs, triangle_prs, triangle_qrs⟩
  exact ⟨triangle_qrs, triangle_rotate triangle_pqr, triangle_rotate triangle_pqs, triangle_rotate triangle_prs⟩

end Geometry

class ProjectivePlane (P : Type _) extends Geometry P :=
  exists_connecting_line : ∀ p q : P, ∃ l : line, p ∈ l ∧ q ∈ l
  exists_intersection_point : ∀ l m : line, ∃ p : P, p ∈ l ∧ p ∈ m
  point_line_uniq : ∀ {p q : P} {l m : line}, p ∈ l → q ∈ l → p ∈ m → q ∈ m → p = q ∨ l = m
  exists_quadrangle : ∃ (p q r s : P), Geometry.isQuadrangle p q r s

namespace ProjectivePlane
open Geometry

variable {p q : P}

noncomputable def connectingLine [ProjectivePlane P] (p q : P) : line P := Exists.choose <| exists_connecting_line p q

infix:75 " ⊔ " => connectingLine

theorem connectingLine_left [ProjectivePlane P] : ∀ p q : P,  p ∈ p ⊔ q :=
    λ p q => (Exists.choose_spec (exists_connecting_line p q)).left

theorem connectingLine_right [ProjectivePlane P] : ∀ p q : P,  q ∈ p ⊔ q :=
    λ p q => (Exists.choose_spec (exists_connecting_line p q)).right

theorem connectingLine_uniq [ProjectivePlane P] : ∀ (p q : P) (l : line P), p ≠ q → p ∈ l → q ∈ l → l = p ⊔ q :=
by intro p q l hpq hpl hql
   have hpm : p ∈ p ⊔ q := connectingLine_left p q
   have hqm : q ∈ p ⊔ q := connectingLine_right p q 
   have h : p = q ∨ l = p ⊔ q := point_line_uniq hpl hql hpm hqm
   cases h with
    | inl hpq' => contradiction
    | inr h' => exact h'

theorem connectingLine_comm [ProjectivePlane P] : ∀ (p q : P), p ≠ q -> p ⊔ q = q ⊔ p := by
  intro p q hpq
  have hpm : p ∈ q ⊔ p := connectingLine_right q p
  have hqm : q ∈ q ⊔ p := connectingLine_left q p
  exact Eq.symm (connectingLine_uniq p q (q ⊔ p) hpq hpm hqm)
@[simp] theorem connectingLine_left [ProjectivePlane P] : ∀ (p q : P),  p ∈ p ⊔ q := by
    intro p q
    exact (Exists.choose_spec (exists_connecting_line p q)).left

@[simp] theorem connectingLine_right [ProjectivePlane P] : ∀ (p q : P),  q ∈ p ⊔ q := by
    intro p q
    exact (Exists.choose_spec (exists_connecting_line p q)).right
noncomputable def intersectionPoint [ProjectivePlane P] (l m : line P) : P := Exists.choose <| exists_intersection_point l m

infix:75 " ⊓ " => intersectionPoint

theorem intersectionPoint_left [ProjectivePlane P] : ∀ l m : line P,  l ⊓ m ∈ l :=
    λ l m => (Exists.choose_spec (exists_intersection_point l m)).left

theorem intersectionPoint_right [ProjectivePlane P] : ∀ l m : line P,  l ⊓ m ∈ m :=
    λ l m => (Exists.choose_spec (exists_intersection_point l m)).right

theorem intersectionPoint_uniq [ProjectivePlane P] : ∀ (l m : line P) (p : P), l ≠ m → p ∈ l → p ∈ m → p = l ⊓ m :=
by intro l m p hlm hpl hpm
   have hql : l ⊓ m ∈ l:= intersectionPoint_left l m
   have hqm : l ⊓ m ∈ m:= intersectionPoint_right l m 
   have h : p = l ⊓ m ∨ l = m := point_line_uniq hpl hql hpm hqm
   cases h with
    | inl h' => exact h'
    | inr hlm' => contradiction
@[simp] theorem intersectionPoint_left [ProjectivePlane P] : ∀ (l m : line P),  l ⊓ m ∈ l := by
    intro l m
    exact (Exists.choose_spec (exists_intersection_point l m)).left

@[simp] theorem intersectionPoint_right [ProjectivePlane P] : ∀ (l m : line P),  l ⊓ m ∈ m := by
  intro l m
  exact (Exists.choose_spec (exists_intersection_point l m)).right

end ProjectivePlane

namespace Fano
open Geometry

inductive Points where
  | p1
  | p2
  | p3 
  | p4
  | p5
  | p6
  | p7
deriving DecidableEq, Repr

inductive Lines where
  | l1
  | l2
  | l3 
  | l4
  | l5
  | l6
  | l7
deriving DecidableEq, Repr

def Lines.points : Lines → List Points
  | .l1 => [.p1, .p2, .p4]
  | .l2 => [.p2, .p3, .p5]
  | .l3 => [.p3, .p4, .p6]
  | .l4 => [.p4, .p5, .p7]
  | .l5 => [.p5, .p6, .p1]
  | .l6 => [.p6, .p7, .p2]
  | .l7 => [.p7, .p1, .p3]

instance FanoMembership : Membership Points Lines where
  mem p l := p ∈ l.points

instance FanoGeometry : Geometry Points where
line := Lines
incidence := FanoMembership

attribute [local simp] line

instance (p : Points) (l : Lines) : Decidable (p ∈ l) := by
  cases l <;> rw [FanoMembership] <;> simp <;> infer_instance

instance (P : Points → Prop) [∀ p, Decidable (P p)] : Decidable (∀ p, P p) :=
  if h : P .p1 ∧ P .p2 ∧ P .p3 ∧ P .p4 ∧ P .p5 ∧ P .p6 ∧ P .p7 then
    isTrue <| by
      repeat
        try rename_i h
        cases h
      intro p
      cases p <;> assumption
  else
    isFalse <| by
      intro H
      apply h
      repeat
        try constructor <;> try apply H

instance (P : Points → Prop) [∀ p, Decidable (P p)] : Decidable (∃ p, P p) :=
  if h : ∀ p, ¬ P p then
    isFalse <| by simp [not_exists, h]
  else
    isTrue <| by
      simp [not_forall, not_not] at h
      exact h

instance (P : Lines → Prop) [∀ l, Decidable (P l)] : Decidable (∀ l, P l) :=
  if h : P .l1 ∧ P .l2 ∧ P .l3 ∧ P .l4 ∧ P .l5 ∧ P .l6 ∧ P .l7 then
    isTrue <| by
      repeat
        try rename_i h
        cases h
      intro l
      cases l <;> assumption
  else
    isFalse <| by
      intro H
      apply h
      repeat
        try constructor <;> try apply H

instance (P : Lines → Prop) [∀ l, Decidable (P l)] : Decidable (∃ l, P l) :=
  if h : ∀ l, ¬ P l then
    isFalse <| by simp [not_exists, h]
  else
    isTrue <| by
      simp [not_forall, not_not] at h
      exact h


def Fano.exists_connecting_line : ∀ (p q : Points), ∃ l : Lines, p ∈ l ∧ q ∈ l := by
  decide

def Fano.exists_intersection_point : ∀ (l m : Lines), ∃ p : Points, p ∈ l ∧ p ∈ m := by
  decide
 
theorem Fano.quadrangle1236 : Geometry.isQuadrangle Points.p1 Points.p2 Points.p3 Points.p6 :=
  ⟨by simp[collinear], by simp[collinear], by simp[collinear], by simp[collinear]⟩

theorem Fano.point_line_uniq : ∀ {p q : Points} {l m : Lines}, p ∈ l -> q ∈ l -> p ∈ m -> q ∈ m -> p = q ∨ l = m := by
  decide
    
instance : ProjectivePlane Points where
  exists_connecting_line := Fano.exists_connecting_line  
  exists_intersection_point := Fano.exists_intersection_point
  exists_quadrangle := ⟨.p1, .p2, .p3, .p6, Fano.quadrangle1236⟩
  point_line_uniq := Fano.point_line_uniq
