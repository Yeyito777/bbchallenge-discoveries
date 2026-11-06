/-
Bridge from the corrected A(a,b) rule map to the certified `highLevelNext` of google-deepmind/cryptids (commit c86f158).
Images: J(0,w) is A(6,w+1); J(u,w), u>=1, is A(2u,w+4). One T step is 0, 1 or 2 applications of the A map.
Conclusion: if the A map iterated from (6,1) reaches its halt form, the Turing machine halts from the blank tape.
-/
import BusyBeaver.BB6.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
import Mathlib.Tactic.SplitIfs

namespace BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.AMap

open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

def aNext : ℕ × ℕ → Option (ℕ × ℕ)
  | (a, b) =>
    if b = a + 3 then none
    else if b > a + 3 then some (2 * a + 6, b - a - 3)
    else if b = 1 then (if a % 4 = 2 then some (6, a + 7) else some (22, a - 2))
    else if b = 3 then (if a % 4 = 2 then some (6, a + 13) else some (a + 8, 2))
    else if b % 2 = 1 then
      (if b = a + 1 then some (6, a + b + 2)
       else if (a + 5 - b) % 4 = 2 then some (a + 11 - b, 2 * b - 4)
       else some (a + 19 - b, 2 * b - 8))
    else if (a + 2 - b) % 4 = 0 then some (6, a + b + 7) else some (22, a + b - 2)

def img : HighLevelState → ℕ × ℕ
  | .J u w => if u = 0 then (6, w + 1) else (2 * u, w + 4)

def aIter (n : ℕ) (s : ℕ × ℕ) : Option (ℕ × ℕ) := (Option.bind · aNext)^[n] (some s)

theorem iter_none (n : ℕ) : (Option.bind · aNext)^[n] (none : Option (ℕ × ℕ)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [Function.iterate_succ_apply] using ih

theorem aIter_add (m n : ℕ) (s t : ℕ × ℕ) (h : aIter m s = some t) :
    aIter (m + n) s = aIter n t := by
  unfold aIter at *
  rw [Nat.add_comm, Function.iterate_add_apply, h]

theorem aIter_split {N k : ℕ} {s t : ℕ × ℕ} (hN : aIter N s = none) (hk : aIter k s = some t) :
    ∃ j, N = k + j ∧ aIter j t = none := by
  rcases Nat.le_total k N with hle | hle
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact ⟨j, rfl, by rw [← aIter_add k j s t hk]; exact hN⟩
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hle
    have : aIter (N + r) s = none := by
      unfold aIter at *
      rw [Nat.add_comm, Function.iterate_add_apply, hN, iter_none]
    rw [this] at hk; cases hk

theorem aIter_one (s : ℕ × ℕ) : aIter 1 s = aNext s := rfl
theorem aIter_two {s t : ℕ × ℕ} (h : aNext s = some t) : aIter 2 s = aNext t := by
  have : aIter 2 s = aIter 1 t := aIter_add 1 1 s t (by rw [aIter_one, h])
  rw [this, aIter_one]

macro "anext" : tactic => `(tactic| (simp only [aNext]; split_ifs <;> first | rfl | omega | (refine congrArg some (Prod.ext ?_ ?_) <;> dsimp only <;> omega)))
macro "tnext" : tactic => `(tactic| (simp only [highLevelNext]; split_ifs <;> first | rfl | omega))

theorem img_zero (w : ℕ) : img (.J 0 w) = (6, w + 1) := rfl
theorem img_pos (u w : ℕ) (hu : u ≠ 0) : img (.J u w) = (2 * u, w + 4) := by simp [img, hu]

/-! T on each guard region, and the A-map applications it stands for. Here a = 2u, b = w+4. -/
section
variable (u w : ℕ)

theorem T1 (c : w ≥ 2 * u + 3) : highLevelNext (.J u w) = some (.J (2 * u + 3) (w - 2 * u - 3)) := by tnext
theorem T2 (c : w = 2 * u + 2) : highLevelNext (.J u w) = some (.J 0 (4 * u + 18)) := by tnext
theorem T3 (c : w = 2 * u + 1) : highLevelNext (.J u w) = some (.J 11 (4 * u + 2)) := by tnext
theorem T4 (c : w = 2 * u) : highLevelNext (.J u w) = some (.J 0 (4 * u + 12)) := by tnext
theorem T5 (c : w < 2 * u) (e : w % 2 = 0) (d : u - w / 2 = 1) :
    highLevelNext (.J u w) = some (.J 0 (2 * w + 12)) := by tnext
theorem T6 (c : w < 2 * u) (e : w % 2 = 0) (d : u - w / 2 ≠ 1) (d2 : (u - w / 2) % 2 = 0) :
    highLevelNext (.J u w) = some (.J 11 (2 * u + w - 2)) := by tnext
theorem T7 (c : w < 2 * u) (e : w % 2 = 0) (d : u - w / 2 ≠ 1) (d2 : (u - w / 2) % 2 ≠ 0) :
    highLevelNext (.J u w) = some (.J 0 (2 * u + w + 10)) := by tnext
theorem T8 (c : w < 2 * u) (e : w % 2 ≠ 0) (d : u - w / 2 = 2) :
    highLevelNext (.J u w) = some (.J 0 (2 * w + 8)) := by tnext
theorem T9 (c : w < 2 * u) (e : w % 2 ≠ 0) (d : u - w / 2 ≠ 2) (d1 : u - w / 2 ≠ 1) (d2 : (u - w / 2) % 2 = 0) (w1 : w = 1) :
    highLevelNext (.J u w) = some (.J 11 (2 * u + 10)) := by tnext
theorem T10 (c : w < 2 * u) (e : w % 2 ≠ 0) (d : u - w / 2 ≠ 2) (d1 : u - w / 2 ≠ 1) (d2 : (u - w / 2) % 2 = 0) (w1 : w ≠ 1) :
    highLevelNext (.J u w) = some (.J (u - w / 2 + 7) (2 * w - 4)) := by tnext
theorem T11 (c : w < 2 * u) (e : w % 2 ≠ 0) (d : u - w / 2 ≠ 2) (d1 : u - w / 2 ≠ 1) (d2 : (u - w / 2) % 2 ≠ 0) :
    highLevelNext (.J u w) = some (.J (u - w / 2 + 3) (2 * w)) := by tnext
theorem T12 (c : w < 2 * u) (e : w % 2 ≠ 0) (d1 : u - w / 2 = 1) : highLevelNext (.J u w) = none := by tnext

theorem A1 (hu : u ≠ 0) (c : w ≥ 2 * u + 3) : aNext (2 * u, w + 4) = some (2 * (2 * u + 3), w - 2 * u - 3 + 4) := by anext
theorem A2a (c : w = 2 * u + 2) : aNext (2 * u, w + 4) = some (2 * (2 * u) + 6, 3) := by anext
theorem A2b : aNext (2 * (2 * u) + 6, 3) = some (6, 4 * u + 18 + 1) := by anext
theorem A3a (c : w = 2 * u + 1) : aNext (2 * u, w + 4) = some (2 * (2 * u) + 6, 2) := by anext
theorem A_x (a b : ℕ) (h0 : b < a + 3) (h1 : b ≠ 1) (h3 : b ≠ 3) (e : b % 2 = 0) (m : (a + 2 - b) % 4 ≠ 0) :
    aNext (a, b) = some (22, a + b - 2) := by anext
theorem A3b : aNext (2 * (2 * u) + 6, 2) = some (2 * 11, 4 * u + 2 + 4) := by
  rw [A_x _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
  exact congrArg some (Prod.ext rfl (by dsimp only; omega))
theorem A4a (c : w = 2 * u) : aNext (2 * u, w + 4) = some (2 * (2 * u) + 6, 1) := by anext
theorem A4b : aNext (2 * (2 * u) + 6, 1) = some (6, 4 * u + 12 + 1) := by anext
theorem A5 (c : w < 2 * u) (e : w % 2 = 0) (d : u - w / 2 = 1) : aNext (2 * u, w + 4) = some (6, 2 * w + 12 + 1) := by anext
theorem A6 (c : w < 2 * u) (e : w % 2 = 0) (d : u - w / 2 ≠ 1) (d2 : (u - w / 2) % 2 = 0) :
    aNext (2 * u, w + 4) = some (2 * 11, 2 * u + w - 2 + 4) := by anext
theorem A7 (c : w < 2 * u) (e : w % 2 = 0) (d : u - w / 2 ≠ 1) (d2 : (u - w / 2) % 2 ≠ 0) :
    aNext (2 * u, w + 4) = some (6, 2 * u + w + 10 + 1) := by anext
theorem A8 (c : w < 2 * u) (e : w % 2 ≠ 0) (d : u - w / 2 = 2) : aNext (2 * u, w + 4) = some (6, 2 * w + 8 + 1) := by anext
theorem A9a (hu : u ≠ 0) (h2 : u ≠ 2) (d2 : u % 2 = 0) : aNext (2 * u, 5) = some (2 * u + 14, 2) := by anext
theorem A9b (d2 : u % 2 = 0) : aNext (2 * u + 14, 2) = some (2 * 11, 2 * u + 10 + 4) := by
  rw [A_x _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
  exact congrArg some (Prod.ext rfl (by dsimp only; omega))
theorem A10 (c : w < 2 * u) (e : w % 2 ≠ 0) (d : u - w / 2 ≠ 2) (d1 : u - w / 2 ≠ 1) (d2 : (u - w / 2) % 2 = 0) (w1 : w ≠ 1) :
    aNext (2 * u, w + 4) = some (2 * (u - w / 2 + 7), 2 * w - 4 + 4) := by anext
theorem A11 (c : w < 2 * u) (e : w % 2 ≠ 0) (d : u - w / 2 ≠ 2) (d1 : u - w / 2 ≠ 1) (d2 : (u - w / 2) % 2 ≠ 0) :
    aNext (2 * u, w + 4) = some (2 * (u - w / 2 + 3), 2 * w + 4) := by anext
theorem A12 (c : w < 2 * u) (e : w % 2 ≠ 0) (d1 : u - w / 2 = 1) : aNext (2 * u, w + 4) = none := by anext
end

/-- The T halt case is the A halt form. -/
theorem sim_none (u w : ℕ) (hu : u ≠ 0) (h : highLevelNext (.J u w) = none) :
    aNext (img (.J u w)) = none := by
  rw [img_pos u w hu]
  by_cases c : w < 2 * u
  · by_cases e : w % 2 = 0
    · by_cases d : u - w / 2 = 1
      · rw [T5 u w c e d] at h; cases h
      · by_cases d2 : (u - w / 2) % 2 = 0
        · rw [T6 u w c e d d2] at h; cases h
        · rw [T7 u w c e d d2] at h; cases h
    · by_cases d1 : u - w / 2 = 1
      · exact A12 u w c e d1
      · by_cases d : u - w / 2 = 2
        · rw [T8 u w c e d] at h; cases h
        · by_cases d2 : (u - w / 2) % 2 = 0
          · by_cases w1 : w = 1
            · rw [T9 u w c e d d1 d2 w1] at h; cases h
            · rw [T10 u w c e d d1 d2 w1] at h; cases h
          · rw [T11 u w c e d d1 d2] at h; cases h
  · by_cases c1 : w ≥ 2 * u + 3
    · rw [T1 u w c1] at h; cases h
    · by_cases c2 : w = 2 * u + 2
      · rw [T2 u w c2] at h; cases h
      · by_cases c3 : w = 2 * u + 1
        · rw [T3 u w c3] at h; cases h
        · rw [T4 u w (by omega)] at h; cases h

/-- One T step, as A-map applications. `k = 0` only for `J 0 w ↦ J 3 (w-3)`, the same A state. -/
theorem sim_some (u w : ℕ) (s' : HighLevelState) (h : highLevelNext (.J u w) = some s') :
    ∃ k ≤ 2, aIter k (img (.J u w)) = some (img s') ∧ (k = 0 → u = 0 ∧ ∃ w', s' = .J 3 w') := by
  by_cases hu : u = 0
  · subst hu
    by_cases c1 : w ≥ 3
    · rw [T1 0 w c1] at h; cases h
      refine ⟨0, by decide, ?_, fun _ => ⟨rfl, _, rfl⟩⟩
      rw [img_zero, img_pos (2 * 0 + 3) (w - 2 * 0 - 3) (by decide)]
      exact congrArg some (Prod.ext rfl (by dsimp only; omega))
    · have : w = 0 ∨ w = 1 ∨ w = 2 := by omega
      rcases this with rfl | rfl | rfl
      · rw [T4 0 0 rfl] at h; cases h
        exact ⟨1, by decide, by rw [aIter_one]; rfl, fun z => absurd z (by decide)⟩
      · rw [T3 0 1 rfl] at h; cases h
        exact ⟨1, by decide, by rw [aIter_one]; rfl, fun z => absurd z (by decide)⟩
      · rw [T2 0 2 rfl] at h; cases h
        exact ⟨1, by decide, by rw [aIter_one]; rfl, fun z => absurd z (by decide)⟩
  · rw [img_pos u w hu]
    by_cases c : w < 2 * u
    · by_cases e : w % 2 = 0
      · by_cases d : u - w / 2 = 1
        · rw [T5 u w c e d] at h; cases h
          exact ⟨1, by decide, by rw [aIter_one, img_zero]; exact A5 u w c e d, fun z => absurd z (by decide)⟩
        · by_cases d2 : (u - w / 2) % 2 = 0
          · rw [T6 u w c e d d2] at h; cases h
            exact ⟨1, by decide, by rw [aIter_one, img_pos 11 _ (by decide)]; exact A6 u w c e d d2, fun z => absurd z (by decide)⟩
          · rw [T7 u w c e d d2] at h; cases h
            exact ⟨1, by decide, by rw [aIter_one, img_zero]; exact A7 u w c e d d2, fun z => absurd z (by decide)⟩
      · by_cases d1 : u - w / 2 = 1
        · rw [T12 u w c e d1] at h; cases h
        · by_cases d : u - w / 2 = 2
          · rw [T8 u w c e d] at h; cases h
            exact ⟨1, by decide, by rw [aIter_one, img_zero]; exact A8 u w c e d, fun z => absurd z (by decide)⟩
          · by_cases d2 : (u - w / 2) % 2 = 0
            · by_cases w1 : w = 1
              · have hw := T9 u w c e d d1 d2 w1
                subst w1
                rw [hw] at h; cases h
                have d3 : u % 2 = 0 := by omega
                exact ⟨2, by decide, by rw [aIter_two (A9a u hu (by omega) d3), img_pos 11 _ (by decide)]; exact A9b u d3, fun z => absurd z (by decide)⟩
              · rw [T10 u w c e d d1 d2 w1] at h; cases h
                exact ⟨1, by decide, by rw [aIter_one, img_pos _ _ (by omega)]; exact A10 u w c e d d1 d2 w1, fun z => absurd z (by decide)⟩
            · rw [T11 u w c e d d1 d2] at h; cases h
              exact ⟨1, by decide, by rw [aIter_one, img_pos _ _ (by omega)]; exact A11 u w c e d d1 d2, fun z => absurd z (by decide)⟩
    · by_cases c1 : w ≥ 2 * u + 3
      · rw [T1 u w c1] at h; cases h
        exact ⟨1, by decide, by rw [aIter_one, img_pos _ _ (by omega)]; exact A1 u w hu c1, fun z => absurd z (by decide)⟩
      · by_cases c2 : w = 2 * u + 2
        · rw [T2 u w c2] at h; cases h
          exact ⟨2, by decide, by rw [aIter_two (A2a u w c2), img_zero]; exact A2b u, fun z => absurd z (by decide)⟩
        · by_cases c3 : w = 2 * u + 1
          · rw [T3 u w c3] at h; cases h
            exact ⟨2, by decide, by rw [aIter_two (A3a u w c3), img_pos 11 _ (by decide)]; exact A3b u, fun z => absurd z (by decide)⟩
          · have c4 : w = 2 * u := by omega
            rw [T4 u w c4] at h; cases h
            exact ⟨2, by decide, by rw [aIter_two (A4a u w c4), img_zero]; exact A4b u, fun z => absurd z (by decide)⟩

def flag : HighLevelState → ℕ
  | .J u _ => if u = 0 then 1 else 0

theorem halts_of_aHalts : ∀ (M : ℕ) (s : HighLevelState) (N : ℕ),
    2 * N + flag s ≤ M → aIter N (img s) = none → CollatzHalts highLevelNext s := by
  intro M
  induction M with
  | zero =>
    intro s N hM hN
    have : N = 0 := by omega
    subst this; simp [aIter] at hN
  | succ M ih =>
    intro s N hM hN
    cases hT : highLevelNext s with
    | none => exact ⟨1, by simp [hT]⟩
    | some s' =>
      obtain ⟨u, w⟩ := s
      obtain ⟨k, hk, hit, hz⟩ := sim_some u w s' hT
      obtain ⟨j, rfl, hj⟩ := aIter_split hN hit
      have hs' : CollatzHalts highLevelNext s' := by
        refine ih s' j ?_ hj
        by_cases h0 : k = 0
        · obtain ⟨rfl, w', rfl⟩ := hz h0
          subst h0
          simp [flag] at hM ⊢; omega
        · have : flag s' ≤ 1 := by cases s'; simp only [flag]; split_ifs <;> omega
          omega
      obtain ⟨n, hn⟩ := hs'
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      simpa [hT] using hn

/-- If the A map from A(6,1) reaches its halt form, the machine halts from the blank tape. -/
theorem isHalt_of_aMap (h : ∃ N, aIter N (6, 1) = none) : IsHalt target := by
  obtain ⟨N, hN⟩ := h
  rw [isHalt_iff_highLevel_acceleration]
  exact halts_of_aHalts _ highLevelStart N le_rfl (by simpa [highLevelStart, img] using hN)

end BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.AMap

#print axioms BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.AMap.isHalt_of_aMap
