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
open Classical

variable {p q r s : P}

noncomputable def connectingLine [ProjectivePlane P] (p q : P) : line P := Exists.choose <| exists_connecting_line p q

infix:75 " ⊔ " => connectingLine

@[simp] theorem connectingLine_left [ProjectivePlane P] : ∀ (p q : P),  p ∈ p ⊔ q := by
    intro p q
    exact (Exists.choose_spec (exists_connecting_line p q)).left

@[simp] theorem connectingLine_right [ProjectivePlane P] : ∀ (p q : P),  q ∈ p ⊔ q := by
    intro p q
    exact (Exists.choose_spec (exists_connecting_line p q)).right

theorem connectingLine_uniq [ProjectivePlane P] : ∀ {p q : P} {l : line P}, p ≠ q → p ∈ l → q ∈ l → l = p ⊔ q := by
  intro p q l hpq hpl hql
  let m := p ⊔ q
  have hpm : p ∈ m := by simp
  have hqm : q ∈ m := by simp 
  have h : p = q ∨ l = m := point_line_uniq hpl hql hpm hqm 
  cases h with
  | inl hpq' => contradiction
  | inr h' => assumption

theorem connectingLine_comm [ProjectivePlane P] : ∀ (p q: P), p ⊔ q = q ⊔ p := fun p q =>
  byCases
    (fun h : q = p => by rw[h])
    (fun hpq : q ≠ p => by
      apply connectingLine_uniq <;> (simp ; try assumption)
    )

noncomputable def intersectionPoint [ProjectivePlane P] (l m : line P) : P := Exists.choose <| exists_intersection_point l m

infix:75 " ⊓ " => intersectionPoint

@[simp] theorem intersectionPoint_left [ProjectivePlane P] : ∀ (l m : line P),  l ⊓ m ∈ l := by
    intro l m
    exact (Exists.choose_spec (exists_intersection_point l m)).left

@[simp] theorem intersectionPoint_right [ProjectivePlane P] : ∀ (l m : line P),  l ⊓ m ∈ m := by
  intro l m
  exact (Exists.choose_spec (exists_intersection_point l m)).right

theorem intersectionPoint_uniq [ProjectivePlane P] : ∀ {l m : line P} {p : P}, l ≠ m → p ∈ l → p ∈ m → p = l ⊓ m := by
  intro l m p hlm hpl hpm
  let q :=  l ⊓ m
  have hql : q ∈ l := by simp
  have hqm : q ∈ m := by simp 
  have h : p = q ∨ l = m := point_line_uniq hpl hql hpm hqm
  cases h with
  | inl h' => exact h'
  | inr hlm' => contradiction

theorem intersectionPoint_comm [ProjectivePlane P] : ∀ (l m : line P), l ⊓ m = m ⊓ l := fun l m =>
  byCases
    (fun h : m = l => by rw[h])
    (fun hpq : m ≠ l => by
      apply intersectionPoint_uniq <;> (simp ; try assumption)
    )

theorem triangle_lines_unequal [ProjectivePlane P] : ¬ collinear p q r -> (p ⊔ q) ≠ (q ⊔ r) ∧ (p ⊔ q) ≠ (r ⊔ p) ∧ (q ⊔ r) ≠ (r ⊔ p) := by
  intro hnc
  apply And.intro
  . intro h
    simp[collinear] at hnc
    apply hnc (p ⊔ q)
    . simp
    . simp
    . simp[h]
  . apply And.intro
    . intro h
      simp[collinear] at hnc
      apply (hnc (p ⊔ q))
      . simp
      . simp
      . simp[h]
    . intro h
      simp[collinear] at hnc
      apply (hnc (q ⊔ r))
      . simp[h]
      . simp
      . simp[h]

theorem dual_triangle [ProjectivePlane P] : ¬ collinear p q r -> ¬ collinear (p ⊔ q) (q ⊔ r) (r ⊔ p) := by
  let a := p ⊔ q
  let b := q ⊔ r
  intro hnc
  simp[collinear]
  -- assume there is a point s such on all three lines
  intro s hpq hqr hrp

  -- s must be equal to q because it is on a and b
  have hsq : s = q := by
    have diff_lines : a ≠ b := (triangle_lines_unequal hnc).left
    have hsq': s = q ∨ a = b := by
      apply point_line_uniq <;> (simp ; try assumption)
    cases hsq' with
    | inl it => exact it
    | inr not_it => contradiction

  -- that means p q r are collinear -> contradiction
  have c : collinear p q r := by
   exists (r ⊔ p)
   rw[hsq] at hrp
   simp
   assumption

  contradiction


theorem dual_quadrangle_part [ProjectivePlane P] : isQuadrangle p q r s -> ¬ collinear (p ⊔ q) (q ⊔ r) (r ⊔ s) := by
  intro ⟨triangle_pqr, _, _, triangle_qrs⟩
  let a := p ⊔ q
  let b := q ⊔ r
  let c := r ⊔ s

  let t := a ⊓ c

  have t_is_not_q : q ≠ t := by
      intro h
      -- if q = t = (p ⊔ q) ⊓ (r ⊔ s), then r ⊔ s contains q and hence q, r, s are collinear
      have : collinear q r s := by
        simp[collinear]
        rw[h]
        exists c
        apply And.intro
        . simp
        . apply And.intro
          . simp
          . simp
      contradiction

  have t_is_not_r : r ≠ t := by
    intro h
    have : collinear p q r := by
     simp[collinear]
     rw[h]
     exists a
     apply And.intro
     . simp
     . apply And.intro
       . simp
       . simp
    contradiction

  have a_is_q_t : a = q ⊔ t := by
      apply connectingLine_uniq
      . assumption
      . simp
      . simp

  have c_is_r_t : c = r ⊔ t := by
    apply connectingLine_uniq
    . assumption
    . simp
    . simp

  have triangle_tqr :  ¬ collinear t q r := by
    simp[collinear]
    -- assume there is a line l containing q, r, t
    intro l htl hql hrl

    -- l = a because l contains both q and t
    have l_is_a : l = a := by
      rw[a_is_q_t]
      apply connectingLine_uniq <;> assumption
    rw[l_is_a] at hrl
    -- a = l contains p, q, r
    have : collinear p q r := by
      simp[collinear]
      exists a
      apply And.intro
      . simp
      . apply And.intro
        . simp
        . assumption
    contradiction

  have : ¬ collinear a b c := by
    rw[a_is_q_t, c_is_r_t, connectingLine_comm]
    apply dual_triangle
    assumption

  assumption

theorem dual_quadrangle [ProjectivePlane P] : isQuadrangle p q r s -> isQuadrangle (p ⊔ q) (q ⊔ r) (r ⊔ s) (s ⊔ p) := by
  intro ⟨triangle_pqr, triangle_pqs, triangle_prs, triangle_qrs⟩
  let a := p ⊔ q
  let b := q ⊔ r
  let c := r ⊔ s
  let d := s ⊔ p

  have triangle_abc : ¬ collinear a b c := by
    apply dual_quadrangle_part
    exact ⟨triangle_pqr, triangle_pqs, triangle_prs, triangle_qrs⟩

  have triangle_abd : ¬ collinear a b d := by
    apply triangle_rotate
    apply dual_quadrangle_part
    apply quadrangle_rotate
    apply quadrangle_rotate
    apply quadrangle_rotate
    exact ⟨triangle_pqr, triangle_pqs, triangle_prs, triangle_qrs⟩

  have triangle_acd : ¬ collinear a c d := by
    apply triangle_rotate
    apply triangle_rotate
    apply dual_quadrangle_part
    apply quadrangle_rotate
    apply quadrangle_rotate
    exact ⟨triangle_pqr, triangle_pqs, triangle_prs, triangle_qrs⟩

  have triangle_bcd : ¬ collinear b c d := by
    apply dual_quadrangle_part
    apply quadrangle_rotate
    exact ⟨triangle_pqr, triangle_pqs, triangle_prs, triangle_qrs⟩

  exact ⟨triangle_abc, triangle_abd, triangle_acd, triangle_bcd⟩  

instance dual [inst : ProjectivePlane P] : ProjectivePlane (line P) where
  line := P
  incidence := ⟨fun l p => p ∈ l⟩
  exists_connecting_line := inst.exists_intersection_point
  exists_intersection_point := inst.exists_connecting_line
  point_line_uniq := by
    intros
    rw[or_comm]
    apply inst.point_line_uniq <;> assumption
  exists_quadrangle := 
    match inst.exists_quadrangle with
    | ⟨p, q, r, s, prf⟩ => ⟨ (p ⊔ q), (q ⊔ r), (r ⊔ s), (s ⊔ p), dual_quadrangle prf⟩
    
theorem dual_involution [h : ProjectivePlane P] :
  let h' : ProjectivePlane (line (line P)) := inferInstance
  h' = h := by rfl
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
