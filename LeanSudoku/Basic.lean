/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ported from Markus Himmel's Lean 3 version by Jeremy Avigad
-/
import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set

def row (i : Fin 9) : Set (Fin 9 × Fin 9) := { p | p.1 = i }
def col (i : Fin 9) : Set (Fin 9 × Fin 9) := { p | p.2 = i }
def box (i j : Fin 3) : Set (Fin 9 × Fin 9) := { p | p.1.1 / 3 = i.1 ∧ p.2.1 / 3 = j.1 }

lemma mem_row (i j k : Fin 9) : (j, k) ∈ row i ↔ j = i := Iff.rfl
lemma mem_col (i j k : Fin 9) : (j, k) ∈ col i ↔ k = i := Iff.rfl
lemma mem_box (i j : Fin 9) (k l : Fin 3) : (i, j) ∈ box k l ↔ i.1 / 3 = k.1 ∧ j.1 / 3 = l.1 := Iff.rfl


structure Sudoku :=
(f : Fin 9 × Fin 9 → Fin 9)
(h_row : ∀ i : Fin 9, Set.BijOn f (row i) Set.univ)
(h_col : ∀ i : Fin 9, Set.BijOn f (col i) Set.univ)
(h_box : ∀ i j : Fin 3, Set.BijOn f (box i j) Set.univ)

namespace Sudoku

lemma cell_cases (s : Sudoku) (i j : Fin 9) :
    s.f (i, j) = 9 ∨ s.f (i, j) = 1 ∨ s.f (i, j) = 2 ∨ s.f (i, j) = 3 ∨ s.f (i, j) = 4 ∨ s.f (i, j) = 5 ∨ s.f (i, j) = 6 ∨ s.f (i, j) = 7 ∨ s.f (i, j) = 8 := by
  cases' s.f (i, j) with v hv
  interval_cases v <;> tauto

lemma row_cases (s : Sudoku) (i j : Fin 9) :
    s.f (i, 0) = j ∨ s.f (i, 1) = j ∨ s.f (i, 2) = j ∨ s.f (i, 3) = j ∨ s.f (i, 4) = j ∨ s.f (i, 5) = j ∨ s.f (i, 6) = j ∨ s.f (i, 7) = j ∨ s.f (i, 8) = j := by
  obtain ⟨⟨x, ⟨y, hy⟩⟩, ⟨h, h'⟩⟩ : j ∈ s.f '' row i := (s.h_row i).surjOn trivial
  rw [mem_row] at h
  subst h
  interval_cases y <;> tauto

lemma col_cases (s : Sudoku) (i j : Fin 9) :
    s.f (0, i) = j ∨ s.f (1, i) = j ∨ s.f (2, i) = j ∨ s.f (3, i) = j ∨ s.f (4, i) = j ∨ s.f (5, i) = j ∨ s.f (6, i) = j ∨ s.f (7, i) = j ∨ s.f (8, i) = j := by
  obtain ⟨⟨⟨x, hx⟩, y⟩, ⟨h, h'⟩⟩ : j ∈ s.f '' col i := (s.h_col i).surjOn trivial
  rw [mem_col] at h
  subst h
  interval_cases x <;> tauto

lemma box_cases (s : Sudoku) (i j : Fin 3) (k : Fin 9) :
    s.f ((3 * i.1 : ℕ), (3 * j.1 : ℕ)) = k ∨
    s.f ((3 * i.1 : ℕ), (3 * j.1 + 1 : ℕ)) = k ∨
    s.f ((3 * i.1 : ℕ), (3 * j.1 + 2 : ℕ)) = k ∨
    s.f ((3 * i.1 + 1 : ℕ), (3 * j.1 : ℕ)) = k ∨
    s.f ((3 * i.1 + 1 : ℕ), (3 * j.1 + 1 : ℕ)) = k ∨
    s.f ((3 * i.1 + 1 : ℕ), (3 * j.1 + 2 : ℕ)) = k ∨
    s.f ((3 * i.1 + 2 : ℕ), (3 * j.1 : ℕ)) = k ∨
    s.f ((3 * i.1 + 2 : ℕ), (3 * j.1 + 1 : ℕ)) = k ∨
    s.f ((3 * i.1 + 2 : ℕ), (3 * j.1 + 2 : ℕ)) = k := by
  obtain ⟨⟨x, y⟩, ⟨h, h'⟩⟩ : k ∈ s.f '' box i j := (s.h_box i j).surjOn trivial
  rw [mem_box] at h
  cases' h with h₀ h₁
  have hx : x.1 = 3 * i.val + (x.1 % 3)
  · rw [add_comm, ←h₀, Nat.mod_add_div]
  have hy : y.1 = 3 * j.val + (y.1 % 3)
  · rw [add_comm, ←h₁, Nat.mod_add_div]
  have := Nat.mod_lt x.val (show 3 > 0 by decide)
  have := Nat.mod_lt y.val (show 3 > 0 by decide)
  interval_cases (x.1 % 3) <;>
    (try rw [add_zero] at hx) <;>
    rw [←hx] <;>
    interval_cases (y.val % 3) <;>
    (try rw [add_zero] at hy) <;>
    simp only [←hy, Fin.cast_val_eq_self] <;>
    tauto

lemma cell_conflict (s : Sudoku) {i j k l : Fin 9} (h₀ : s.f (i, j) = k) (h₁ : s.f (i, j) = l)
    (h₂ : k ≠ l) : False := by
  apply h₂
  rw [←h₀, ←h₁]

lemma row_conflict (s : Sudoku) {i j k l : Fin 9} (h₀ : s.f (i, j) = l) (h₁ : s.f (i, k) = l)
    (h₂ : j ≠ k) : False := by
  apply h₂
  suffices : (i, j) = (i, k)
  · cases' this; rfl
  refine (s.h_row i).injOn ?_ ?_ (h₀.trans h₁.symm) <;>
  rw [mem_row]

lemma col_conflict (s : Sudoku) {i j k l : Fin 9} (h₀ : s.f (i, k) = l) (h₁ : s.f (j, k) = l)
    (h₂ : i ≠ j) : False := by
  apply h₂
  suffices : (i, k) = (j, k)
  · rcases this; rfl
  refine (s.h_col k).injOn ?_ ?_ (h₀.trans h₁.symm) <;>
  rw [mem_col]


lemma bloop {i : ℕ} (hi : i < 9) : i / 3 < 3 := by interval_cases i <;> decide

lemma box_conflict (s : Sudoku) {i j k l m : Fin 9} (h₀ : s.f (i, j) = m) (h₁ : s.f (k, l) = m)
    (h₂ : i.1 / 3 = k.1 / 3) (h₃ : j.1 / 3 = l.1 / 3) (h₄ : i ≠ k ∨ j ≠ l) : False := by
  contrapose h₄
  push_neg
  clear h₄
  suffices : (i, j) = (k, l)
  · cases' this; exact ⟨rfl, rfl⟩
  refine (s.h_box (i.1 / 3 : ℕ) (j.1 / 3 : ℕ)).injOn ?_ ?_ (h₀.trans h₁.symm)
  · rw [mem_box]
    constructor
    · rw [Fin.val_cast_of_lt]
      exact bloop i.2
    . rw [Fin.val_cast_of_lt]
      exact bloop j.2
  · rw [mem_box]
    constructor
    · rw [Fin.val_cast_of_lt]
      · exact h₂.symm
      · exact bloop i.2
    · rw [Fin.val_cast_of_lt]
      · exact h₃.symm
      · exact bloop j.2

/-- Outer pencil marks capture the fact that a certain number appears in one of two places. -/
def snyder (s : Sudoku) (i j k l m : Fin 9) : Prop :=
  s.f (i, j) = m ∨ s.f (k, l) = m

def snyder₃ (s : Sudoku) (i j k l m n o : Fin 9) : Prop :=
  s.f (i, j) = o ∨ s.f (k, l) = o ∨ s.f (m, n) = o

/-- Inner pencil marks capture the fact that a certain cell contains one of two numbers. -/
def double (s : Sudoku) (i j k l : Fin 9) : Prop :=
  s.f (i, j) = k ∨ s.f (i, j) = l

/-- Inner pencil marks capture the fact that a certain cell contains one of three numbers. -/
def triple (s : Sudoku) (i j k l m : Fin 9) : Prop :=
  s.f (i, j) = k ∨ s.f (i, j) = l ∨ s.f (i, j) = m

lemma triple_perm₁ {s : Sudoku} {i j k l m : Fin 9} : s.triple i j k l m → s.triple i j l k m := by
  unfold triple; tauto

lemma triple_perm₂ {s : Sudoku} {i j k l m : Fin 9} : s.triple i j k l m → s.triple i j m l k := by
  unfold triple; tauto

/-- The first (trivial) piece of Sudoku theory: If there are two outer pencil marks relating two
    cells, then we get an inner pencil mark for those two numbers in both cells. -/
lemma double_left_of_snyder {s : Sudoku} {i j k l m n : Fin 9} (h₀ : snyder s i j k l m)
    (h₁ : snyder s i j k l n) (h₂ : m ≠ n) : double s i j m n := by
  unfold double; cases' h₀ with h₀ h₀ <;> cases' h₁ with h₁ h₁ <;> (try tauto);
    exact absurd (h₀.symm.trans h₁) h₂

/-- The first (trivial) piece of Sudoku theory: If there are two outer pencil marks relating two
    cells, then we get an inner pencil mark for those two numbers in both cells. -/
lemma double_right_of_snyder {s : Sudoku} {i j k l m n : Fin 9} (h₀ : snyder s i j k l m)
    (h₁ : snyder s i j k l n) (h₂ : m ≠ n) : double s k l m n := by
  unfold double; cases' h₀ with h₀ h₀ <;> cases' h₁ with h₁ h₁ <;> (try tauto);
    exact absurd (h₀.symm.trans h₁) h₂

lemma triple_of_double₁ {s : Sudoku} {i j k l m : Fin 9} : s.double i j k l → s.triple i j m k l := by
  unfold triple; tauto

lemma triple_of_double₂ {s : Sudoku} {i j k l m : Fin 9} : s.double i j k l → s.triple i j k m l := by
  unfold double triple; tauto

lemma triple_of_double₃ {s : Sudoku} {i j k l m : Fin 9} : s.double i j k l → s.triple i j k l m := by
  unfold double triple; tauto


/-- Two cells are in contention if they "see each other", i.e., cannot contain the same number. -/
def contention (s : Sudoku) (i j k l : Fin 9) : Prop :=
  ∀ (m : Fin 9), s.f (i, j) = m → s.f (k, l) = m → False

lemma row_contention {s : Sudoku} {i j k : Fin 9} (h : j ≠ k) : s.contention i j i k :=
  fun _ h₀ h₁ => s.row_conflict h₀ h₁ h

lemma col_contention {s : Sudoku} {i j k : Fin 9} (h : i ≠ j) : s.contention i k j k :=
  fun _ h₀ h₁ => s.col_conflict h₀ h₁ h

lemma box_contention {s : Sudoku} {i j k l : Fin 9} (h : i.1 / 3 = k.1 / 3)
  (h' : j.1 / 3 = l.1 / 3) (h'' : i ≠ k ∨ j ≠ l) : s.contention i j k l :=
  fun _ h₀ h₁ => s.box_conflict h₀ h₁ h h' h''

lemma snyder₃_of_triple₁ {s : Sudoku} {i j k l m n o p q : Fin 9}
    (h₀ : s.triple i j o p q) (h₁ : s.triple k l o p q) (h₂ : s.triple m n o p q)
    (h : s.contention i j k l) (h' : s.contention i j m n) (h'' : s.contention k l m n) :
  s.snyder₃ i j k l m n o := by
  unfold snyder₃
  rcases h₀ with h₀|h₀|h₀
  · left; exact h₀
  · rcases h₁ with h₁|h₁|h₁
    · right; left; exact h₁
    · exfalso; exact h _ h₀ h₁
    rcases h₂ with h₂|h₂|h₂
    · right; right; exact h₂
    · exfalso; exact h' _ h₀ h₂
    · exfalso; exact h'' _ h₁ h₂
  · rcases h₁ with h₁|h₁|h₁
    · right; left; exact h₁
    swap; exfalso; exact h _ h₀ h₁
    rcases h₂ with h₂|h₂|h₂
    · right; right; exact h₂
    · exfalso; exact h'' _ h₁ h₂
    · exfalso; exact h' _ h₀ h₂

lemma snyder₃_of_triple₂ {s : Sudoku} {i j k l m n o p q : Fin 9}
  (h₀ : s.triple i j o p q) (h₁ : s.triple k l o p q) (h₂ : s.triple m n o p q)
  (h : s.contention i j k l) (h' : s.contention i j m n) (h'' : s.contention k l m n) :
  s.snyder₃ i j k l m n p :=
snyder₃_of_triple₁ (triple_perm₁ h₀) (triple_perm₁ h₁) (triple_perm₁ h₂) h h' h''

lemma snyder₃_of_triple₃ {s : Sudoku} {i j k l m n o p q : Fin 9}
  (h₀ : s.triple i j o p q) (h₁ : s.triple k l o p q) (h₂ : s.triple m n o p q)
  (h : s.contention i j k l) (h' : s.contention i j m n) (h'' : s.contention k l m n) :
  s.snyder₃ i j k l m n q :=
snyder₃_of_triple₁ (triple_perm₂ h₀) (triple_perm₂ h₁) (triple_perm₂ h₂) h h' h''

lemma snyder₃_of_triple_row₁ {s : Sudoku} {i j k l m n o : Fin 9}
  (hj : s.triple i j m n o) (hk : s.triple i k m n o) (hl : s.triple i l m n o)
  (hjk : j ≠ k) (hkl : k ≠ l) (hjl : j ≠ l) : s.snyder₃ i j i k i l m :=
snyder₃_of_triple₁ hj hk hl (row_contention hjk) (row_contention hjl) (row_contention hkl)

lemma snyder₃_of_triple_row₂ {s : Sudoku} {i j k l m n o : Fin 9}
  (hj : s.triple i j m n o) (hk : s.triple i k m n o) (hl : s.triple i l m n o)
  (hjk : j ≠ k) (hkl : k ≠ l) (hjl : j ≠ l) : s.snyder₃ i j i k i l n :=
snyder₃_of_triple₂ hj hk hl (row_contention hjk) (row_contention hjl) (row_contention hkl)

lemma snyder₃_of_triple_row₃ {s : Sudoku} {i j k l m n o : Fin 9}
  (hj : s.triple i j m n o) (hk : s.triple i k m n o) (hl : s.triple i l m n o)
  (hjk : j ≠ k) (hkl : k ≠ l) (hjl : j ≠ l) : s.snyder₃ i j i k i l o :=
snyder₃_of_triple₃ hj hk hl (row_contention hjk) (row_contention hjl) (row_contention hkl)

end Sudoku
