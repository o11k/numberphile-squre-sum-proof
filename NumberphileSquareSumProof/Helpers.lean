import NumberphileSquareSumProof.Basic

import Init.Data.List.Lemmas
import Mathlib.Data.List.Perm.Subperm

/-- Perfect square via integer sqrt — O(1)-ish, no search. -/
def isPerfSq (n : ℕ) : Bool :=
  let r := n.sqrt
  r * r == n

theorem isPerfSq_correct (n : ℕ) : isPerfSq n = true → IsPerfectSquare n := by
  unfold isPerfSq IsPerfectSquare
  simp only [beq_iff_eq]
  intro h
  exact ⟨n.sqrt, h⟩

/-- Regular check, single pass, with fast square test. -/
def checkRegular : List ℕ → Bool
  | []           => true
  | [_]          => true
  | a :: b :: t  => isPerfSq (a + b) && checkRegular (b :: t)

theorem checkRegular_correct : ∀ l : List ℕ, checkRegular l = true → RegularList l := by
  intro l
  induction l with
  | nil => simp [RegularList]
  | cons a t ih =>
    cases t with
    | nil => simp [RegularList]
    | cons b rest =>
      simp only [checkRegular, Bool.and_eq_true]
      intro ⟨hsq, hrec⟩
      exact ⟨isPerfSq_correct _ hsq, ih hrec⟩

/-- Cyclical: regular + last-to-first wraps to a square. -/
def checkCyclical (l : List ℕ) : Bool :=
  match l with
  | []        => true
  | a :: rest => checkRegular (a :: rest) && isPerfSq ((a :: rest).getLast (by simp) + a)

theorem checkCyclical_correct (l : List ℕ) : checkCyclical l = true → CyclicalRegularList l := by
  cases l with
  | nil => simp [CyclicalRegularList]
  | cons a rest =>
    simp only [checkCyclical, Bool.and_eq_true]
    intro ⟨hreg, hsq⟩
    exact ⟨checkRegular_correct _ hreg, isPerfSq_correct _ hsq⟩


private def makeSeenArrayAux : (lst : List ℕ) → (arr : Array Bool)
    → (∀ x, lst.contains x → x < arr.size) → Array Bool
  | [],        m, _ => m
  | x :: rest, m, h =>
    have hx : x < m.size := h x (by simp)
    have hset_size : (m.set x true hx).size = m.size := Array.size_set hx
    have hn : ∀ y, rest.contains y → y < (m.set x true hx).size := by
      intro y hy
      rw [hset_size]
      exact h y (by simp [List.mem_cons, List.contains_iff_mem.mp hy])
    makeSeenArrayAux rest (m.set x true hx) hn


private def makeSeenArray : List ℕ → Array Bool
  | []          => #[]
  | fst :: rest =>
    let l := fst :: rest
    have hne : l ≠ [] := List.cons_ne_nil _ _
    let max := l.toArray.max (by simp [hne])
    let seen := Array.replicate (max + 1) false
    have hm : ∀ x, l.contains x → x < seen.size := by
      intro x hx
      simp only [seen, Array.size_replicate]
      have hmem : x ∈ l := List.contains_iff_mem.mp hx
      have hle : x ≤ max := by
        apply Array.le_max_of_mem (xs := l.toArray)
        simp [hmem]
      omega
    makeSeenArrayAux l seen hm

-- Size is preserved by makeSeenArrayAux
private theorem makeSeenArrayAux_size (lst : List ℕ) (m : Array Bool)
    (h : ∀ x, lst.contains x → x < m.size)
    : (makeSeenArrayAux lst m h).size = m.size := by
  induction lst generalizing m with
  | nil => simp [makeSeenArrayAux]
  | cons x rest ih =>
    simp only [makeSeenArrayAux]
    have hx : x < m.size := h x (by simp)
    have hsize : (m.set x true hx).size = m.size := Array.size_set hx
    have hbound' : ∀ z, rest.contains z → z < (m.set x true hx).size := fun z hz => by
      rw [hsize]; exact h z (by simp [List.mem_cons, List.contains_iff_mem.mp hz])
    rw [ih _ hbound', hsize]

-- After makeSeenArrayAux, slot y is true iff it was already true OR y ∈ lst
private theorem makeSeenArrayAux_getElem (lst : List ℕ) (m : Array Bool)
    (hbound : ∀ x, lst.contains x → x < m.size) (y : ℕ) (hy : y < m.size) :
    (makeSeenArrayAux lst m hbound)[y]'(makeSeenArrayAux_size lst m hbound ▸ hy) =
    true ↔ m[y]'hy = true ∨ y ∈ lst := by
  induction lst generalizing m with
  | nil => simp [makeSeenArrayAux]
  | cons x rest ih =>
    simp only [makeSeenArrayAux, List.mem_cons]
    have hx : x < m.size := hbound x (by simp)
    have hsize : (m.set x true hx).size = m.size := Array.size_set hx
    have hbound' : ∀ z, rest.contains z → z < (m.set x true hx).size := fun z hz => by
      rw [hsize]; exact hbound z (by simp [List.mem_cons, List.contains_iff_mem.mp hz])
    have hy' : y < (m.set x true hx).size := hsize.symm ▸ hy
    rw [ih (m.set x true hx) hbound' hy']
    by_cases hxy : x = y
    · subst hxy; simp [Array.getElem_set (h' := hx)]
    · simp [Array.getElem_set (h' := hx), hxy, Ne.symm hxy]

-- seen[x] = true ↔ x ∈ lst, for x in bounds
private theorem makeSeenArray_getElem_iff (lst : List ℕ) (x : ℕ)
    (hx : x < (makeSeenArray lst).size) :
    (makeSeenArray lst)[x]'hx = true ↔ x ∈ lst := by
  match lst with
  | [] => simp [makeSeenArray] at hx
  | fst :: rest =>
    simp only [makeSeenArray]
    have hne : (fst :: rest) ≠ [] := List.cons_ne_nil _ _
    have hm : ∀ z, (fst :: rest).contains z → z <
        (Array.replicate ((fst :: rest).toArray.max (by simp [hne]) + 1) false).size :=
      fun z hz => by
        simp only [Array.size_replicate]
        exact Nat.lt_succ_of_le (Array.le_max_of_mem (by simp [List.contains_iff_mem.mp hz]))
    have hsize : (makeSeenArrayAux (fst :: rest)
        (Array.replicate ((fst :: rest).toArray.max (by simp [hne]) + 1) false) hm).size =
        (Array.replicate ((fst :: rest).toArray.max (by simp [hne]) + 1) false).size :=
      makeSeenArrayAux_size _ _ hm
    have hx' : x < (Array.replicate ((fst :: rest).toArray.max (by simp [hne]) + 1) false).size :=
      hsize ▸ hx
    rw [makeSeenArrayAux_getElem _ _ hm x hx']
    simp [Array.getElem_replicate]

private theorem makeSeenArray_getElem (lst : List ℕ) (x : ℕ) (hin : x ∈ lst) :
    (makeSeenArray lst)[x]'(by
      match lst with
      | [] => simp at hin
      | fst :: rest =>
        simp only [makeSeenArray]
        have hne : (fst :: rest) ≠ [] := List.cons_ne_nil _ _
        have hm : ∀ z, (fst :: rest).contains z → z <
            (Array.replicate ((fst :: rest).toArray.max (by simp [hne]) + 1) false).size :=
          fun z hz => by
            simp only [Array.size_replicate]
            exact Nat.lt_succ_of_le
              (Array.le_max_of_mem (by simp [List.contains_iff_mem.mp hz]))
        rw [makeSeenArrayAux_size _ _ hm, Array.size_replicate]
        exact Nat.lt_succ_of_le (Array.le_max_of_mem (by simp [List.mem_toArray, hin]))) = true :=
  (makeSeenArray_getElem_iff lst x _).mpr hin

/-- O(n) permutation check: build seen array, verify size, then check slots 1..n. -/
def checkPermRange (l : List ℕ) : Bool :=
  let n := l.length
  let seen := makeSeenArray l
  (seen.size == n + 1) &&
  (List.range' 1 n).all (fun i => seen.getD i false)

private theorem length_range'_one (n : ℕ) : (List.range' 1 n).length = n := by
  induction n with
  | zero => simp
  | succ n _ => simp [List.range'_succ]

-- if checkPermRange passes, every x in range' 1 n is in l
private theorem checkPermRange_mem (l : List ℕ) (h : checkPermRange l = true) :
    ∀ x ∈ List.range' 1 l.length, x ∈ l := by
  simp only [checkPermRange, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hsize, hall⟩ := h
  intro x hx
  have hxi : x < (makeSeenArray l).size := by
    rw [hsize]; simp only [List.mem_range'_1] at hx; omega
  have htrue : (makeSeenArray l)[x]'hxi = true := by
    have := hall x hx
    simp only [Array.getD, hxi, ↓reduceDIte] at this
    exact this
  exact (makeSeenArray_getElem_iff l x hxi).mp htrue

theorem checkPermRange_correct (l : List ℕ) (h : checkPermRange l = true) :
    l.Perm (List.range' 1 l.length) := by
  set n := l.length
  set r := List.range' 1 n
  have hmem : r ⊆ l := checkPermRange_mem l h
  have hnd  : r.Nodup := List.nodup_range'
  -- r <+~ l means ∃ l', l' ~ l ∧ r <+ l'
  have hsp : List.Subperm r l := hnd.subperm hmem
  obtain ⟨l', hperm, hsub⟩ := List.subperm_iff.mp hsp
  -- lengths: r.length = n = l.length = l'.length
  have hlen_r  : r.length = n          := length_range'_one n
  have hlen_l' : l'.length = n         := hperm.length_eq
  -- r <+ l' with equal lengths → r = l'
  have heq : r = l' := hsub.eq_of_length (hlen_r.trans hlen_l'.symm)
  exact (heq ▸ hperm).symm

-- Recursive worker: maps value → its index in L.
-- Bound proof ensures every (x, i) in pairs has x < m.size, so we use set not set!
private def indexMapAux : (pairs : List (ℕ × ℕ)) → (m : Array (Option ℕ))
    → (∀ p ∈ pairs, p.1 < m.size) → Array (Option ℕ)
  | [],             m, _ => m
  | (x, i) :: rest, m, h =>
    have hx : x < m.size := h _ (List.mem_cons.mpr (Or.inl rfl))
    have hsize : (m.set x (some i) hx).size = m.size := Array.size_set hx
    have hrest : ∀ p ∈ rest, p.1 < (m.set x (some i) hx).size := fun p hp => by
      rw [hsize]; exact h _ (List.mem_cons.mpr (Or.inr hp))
    indexMapAux rest (m.set x (some i) hx) hrest

-- Size is preserved
private theorem indexMapAux_size (pairs : List (ℕ × ℕ)) (m : Array (Option ℕ))
    (hb : ∀ p ∈ pairs, p.1 < m.size) :
    (indexMapAux pairs m hb).size = m.size := by
  induction pairs generalizing m with
  | nil => simp [indexMapAux]
  | cons p rest ih =>
    simp only [indexMapAux]
    have hx : p.1 < m.size := hb _ (List.mem_cons.mpr (Or.inl rfl))
    have hsize : (m.set p.1 (some p.2) hx).size = m.size := Array.size_set hx
    have hrest : ∀ q ∈ rest, q.1 < (m.set p.1 (some p.2) hx).size := fun q hq => by
      rw [hsize]; exact hb _ (List.mem_cons.mpr (Or.inr hq))
    rw [ih _ hrest, hsize]

-- if slot a holds some j after indexMapAux, then (a, j) was in pairs or in the initial array
private theorem indexMapAux_getElem (pairs : List (ℕ × ℕ)) (m : Array (Option ℕ))
    (hb : ∀ p ∈ pairs, p.1 < m.size) (a : ℕ) (ha : a < m.size) :
    (indexMapAux pairs m hb)[a]'(indexMapAux_size pairs m hb ▸ ha) = some j →
    (a, j) ∈ pairs ∨ m[a]'ha = some j := by
  induction pairs generalizing m with
  | nil => simp [indexMapAux]
  | cons p rest ih =>
    simp only [indexMapAux]
    obtain ⟨x, i⟩ := p
    have hx : x < m.size := hb _ (List.mem_cons.mpr (Or.inl rfl))
    have hsize : (m.set x (some i) hx).size = m.size := Array.size_set hx
    have hrest : ∀ q ∈ rest, q.1 < (m.set x (some i) hx).size := fun q hq => by
      rw [hsize]; exact hb _ (List.mem_cons.mpr (Or.inr hq))
    have ha' : a < (m.set x (some i) hx).size := hsize.symm ▸ ha
    intro hval
    rcases ih _ hrest ha' hval with hmem | hinit
    · exact Or.inl (List.mem_cons.mpr (Or.inr hmem))
    · by_cases hxa : x = a
      · subst hxa
        rw [Array.getElem_set (h' := hx)] at hinit
        simp only [↓reduceIte, Option.some.injEq] at hinit
        subst hinit
        exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
      · rw [Array.getElem_set (h' := hx), if_neg hxa] at hinit
        exact Or.inr hinit

private def indexMap (L : List ℕ) (hval : ∀ x ∈ L, x < L.length + 1) : Array (Option ℕ) :=
  let m := Array.replicate (L.length + 1) (none : Option ℕ)
  have hb : ∀ p ∈ L.zipIdx, p.1 < m.size := by
    intro ⟨x, i⟩ hmem
    simp only [m, Array.size_replicate]
    exact hval x (List.fst_mem_of_mem_zipIdx hmem)
  indexMapAux L.zipIdx m hb

private theorem indexMap_size (L : List ℕ) (hval : ∀ x ∈ L, x < L.length + 1) :
    (indexMap L hval).size = L.length + 1 := by
  simp only [indexMap, indexMapAux_size, Array.size_replicate]

-- Backward: if slot x holds some j, then L[j] = x
private theorem indexMap_getElem (L : List ℕ) (hval : ∀ x ∈ L, x < L.length + 1)
    (x j : ℕ) (hx : x < (indexMap L hval).size)
    (hlookup : (indexMap L hval)[x]'hx = some j) : L[j]? = some x := by
  simp only [indexMap] at hx hlookup
  set m := Array.replicate (L.length + 1) (none : Option ℕ)
  have hb : ∀ p ∈ L.zipIdx, p.1 < m.size := by
    intro ⟨v, i⟩ hmem
    simp only [m, Array.size_replicate]
    exact hval v (List.fst_mem_of_mem_zipIdx hmem)
  have ha : x < m.size := indexMapAux_size _ _ hb ▸ hx
  rcases indexMapAux_getElem _ _ hb x ha hlookup with hmem | hinitial
  · exact List.mk_mem_zipIdx_iff_getElem?.mp hmem
  · simp [m] at hinitial

-- Elements of a perm of range' 1 n are all in 1..n
private theorem mem_lt_succ_of_perm_range' (l : List ℕ) (hp : l.Perm (List.range' 1 l.length))
    (x : ℕ) (hx : x ∈ l) : x < l.length + 1 := by
  have := hp.mem_iff.mp hx
  simp only [List.mem_range'_1] at this; omega

-- Build value→index map using getD-style safe writes; no proof required.
private def indexMapSafe (L : List ℕ) : Array (Option ℕ) :=
  let m := Array.replicate (L.length + 1) (none : Option ℕ)
  L.zipIdx.foldl (fun acc (xi : ℕ × ℕ) =>
    if h : xi.1 < acc.size then acc.set xi.1 (some xi.2) h else acc) m

-- When the perm bound holds, indexMapSafe equals indexMap.
private theorem indexMapSafe_eq (L : List ℕ) (hval : ∀ x ∈ L, x < L.length + 1) :
    indexMapSafe L = indexMap L hval := by
  simp only [indexMapSafe, indexMap]
  set m := Array.replicate (L.length + 1) (none : Option ℕ)
  have hb : ∀ p ∈ L.zipIdx, p.1 < m.size := fun ⟨x, _⟩ hp => by
    simp only [m, Array.size_replicate]
    exact hval x (List.fst_mem_of_mem_zipIdx hp)
  -- show the foldl agrees with indexMapAux by induction
  suffices h : ∀ (pairs : List (ℕ × ℕ)) (acc : Array (Option ℕ))
      (hb2 : ∀ p ∈ pairs, p.1 < acc.size),
      pairs.foldl (fun a xi => if hh : xi.1 < a.size then a.set xi.1 (some xi.2) hh else a) acc =
      indexMapAux pairs acc hb2 from h L.zipIdx m hb
  intro pairs
  induction pairs with
  | nil => simp [indexMapAux]
  | cons p rest ih =>
    intro acc hb2
    simp only [List.foldl_cons, indexMapAux]
    have hx : p.1 < acc.size := hb2 _ (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ q ∈ rest, q.1 < (acc.set p.1 (some p.2) hx).size := fun q hq => by
      rw [Array.size_set]; exact hb2 _ (List.mem_cons.mpr (Or.inr hq))
    rw [dif_pos hx]
    exact ih _ hrest

def checkSameParity (S L : List ℕ) : Bool :=
  let idx_l := indexMapSafe L
  S.zipIdx.all fun (x, i) =>
    match idx_l[x]? with
    | some (some j) => i % 2 == j % 2
    | _ => false

theorem checkSameParity_correct (S L : List ℕ) (hL : ∀ x ∈ L, x < L.length + 1)
    (h : checkSameParity S L = true) : sameIndexParity S L := by
  simp only [checkSameParity, List.all_eq_true, indexMapSafe_eq L hL] at h
  intro x _ i hSi
  have hcheck := h (x, i) (List.mem_zipIdx_iff_getElem?.mpr hSi)
  simp only at hcheck
  rcases hq : (indexMap L hL)[x]? with _ | (_ | j)
  · simp [hq] at hcheck
  · simp [hq] at hcheck
  · simp only [hq] at hcheck
    obtain ⟨hx, hv⟩ := Array.getElem?_eq_some_iff.mp hq
    exact ⟨j, indexMap_getElem L hL x j hx hv, by simpa [beq_iff_eq] using hcheck⟩

def checkNinjaPair (S L : List ℕ) : Bool :=
  (L.length == S.length + 1) &&
  checkPermRange S &&
  checkPermRange L &&
  checkCyclical S &&
  checkCyclical L &&
  (S.head? == some 1) &&
  (L.head? == some 1) &&
  (if S.length % 2 == 1 then S.getLast? == some 3 else S.getLast? == some 8) &&
  (if L.length % 2 == 1 then L.getLast? == some 3 else L.getLast? == some 8) &&
  checkSameParity S L

theorem checkNinjaPair_correct (S L : List ℕ) (h : checkNinjaPair S L = true) :
    NinjaPair S L := by
  simp only [checkNinjaPair, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hlen, hpS⟩, hpL⟩, hcS⟩, hcL⟩, hhS⟩, hhL⟩, htS⟩, htL⟩, hsp⟩ := h
  have hpermS := checkPermRange_correct S hpS
  have hpermL := checkPermRange_correct L hpL
  have hbL : ∀ x ∈ L, x < L.length + 1 := mem_lt_succ_of_perm_range' L hpermL
  -- decode the conditional tail checks using split_ifs
  have htS_odd : S.length % 2 = 1 → S.getLast? = some 3 := by
    intro hodd
    simp only [if_pos hodd, beq_iff_eq] at htS; exact htS
  have htS_even : S.length % 2 = 0 → S.getLast? = some 8 := by
    intro heven
    simp only [if_neg (by omega : ¬ S.length % 2 = 1), beq_iff_eq] at htS; exact htS
  have htL_odd : L.length % 2 = 1 → L.getLast? = some 3 := by
    intro hodd
    simp only [if_pos hodd, beq_iff_eq] at htL; exact htL
  have htL_even : L.length % 2 = 0 → L.getLast? = some 8 := by
    intro heven
    simp only [if_neg (by omega : ¬ L.length % 2 = 1), beq_iff_eq] at htL; exact htL
  exact ⟨hlen, hpermL, hpermS,
    checkCyclical_correct S hcS, checkCyclical_correct L hcL,
    hhS, hhL,
    htS_odd, htS_even, htL_odd, htL_even,
    checkSameParity_correct S L hbL hsp⟩
