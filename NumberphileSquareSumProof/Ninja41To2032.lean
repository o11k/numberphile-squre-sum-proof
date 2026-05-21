import NumberphileSquareSumProof.Basic
import NumberphileSquareSumProof.Helpers

/-- Parse "1,2,3" into [1,2,3]. -/
def parseList (s : String) : List ℕ :=
  (s.splitOn ",").filterMap (·.trimAscii.toNat?)

def parseNinjaTable (s : String) : List (ℕ × (List ℕ) × (List ℕ)) :=
  (s.splitOn "\n").filterMap (fun line =>
    if line.trimAscii.isEmpty then none else
    match line.splitOn ";" with
    | [nStr, slStr] =>
      match slStr.splitOn "|" with
      | [sCsv, lCsv] =>
        (nStr.trimAscii.toNat?).map fun n => (n, parseList sCsv, parseList lCsv)
      | _ => none
    | _ => none)

def TABLE_START := 41
def TABLE_END := 2032
def TABLE_LEN := TABLE_END - TABLE_START + 1

/-- One line per entry: "n;S_csv|L_csv". -/
def ninjaTableRaw : String := include_str "ninja_pairs.txt"
def ninjaTable : List (ℕ × (List ℕ) × (List ℕ)) := parseNinjaTable ninjaTableRaw

def ninjaTableOk : Bool :=
  (ninjaTable.map (·.1)) == List.range' TABLE_START TABLE_LEN
  && ninjaTable.all (fun (n, s, l) => (s.length == n) && checkNinjaPair s l)

theorem ninjaTableOk_true : ninjaTableOk = true := by native_decide

theorem ninja_number_of_ge_41_le_2032 :
∀ n : ℕ, n ≥ 41 → n ≤ 2032 → NinjaNumber n := by
  intro n hlo hhi
  have htok := ninjaTableOk_true
  simp only [ninjaTableOk, TABLE_START, TABLE_LEN, TABLE_END,
    Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at htok
  obtain ⟨hkeys, hvalid⟩ := htok
  -- find the entry for n
  have hmem : n ∈ ninjaTable.map (·.1) := by
    rw [hkeys]
    simp only [List.mem_range'_1]
    omega
  obtain ⟨⟨m, s, l⟩, hmem_entry, rfl⟩ := List.mem_map.mp hmem
  obtain ⟨hlen, hcheck⟩ := hvalid _ hmem_entry
  exact ⟨s, l, hlen, checkNinjaPair_correct s l hcheck⟩
