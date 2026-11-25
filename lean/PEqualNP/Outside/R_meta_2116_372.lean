import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

-- The three OR gates follow the order in which their distinguished inputs are first read.
-- The four lists contain the remaining gates. Each bit mask in the search represents an edge.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_2116_372
    (canonical : ∀ (C : Circuit) (τ : Fin 9 → Fin 9),
      let wire := fun (j : ℕ) => if h : j < 9 then (τ ⟨j,h⟩).val else j
      let gate := fun (g : Gate) => {g with inputs := (g.inputs.map wire).mergeSort}
      FanInTwo C → (∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1) →
      ∀ x : Fin 9 → Bool, (Circuit.mk (C.gates.map gate) (wire C.output)).eval (List.ofFn x) =
        C.eval (List.ofFn (x ∘ τ)))
    (enumerate : ∀ (p q r s : List Gate) (i j k o : ℕ),
      let reader := fun (a b : ℕ) => Gate.mk .or [a,b]
      let C := Circuit.mk (p ++ reader 4 i :: (q ++ reader 6 j :: (r ++ reader 7 k :: s))) o
      let free := p ++ q ++ r ++ s
      free.length ≤ 12 → (∀ w ∈ [i,j,k], 9 ≤ w) → FanInTwo C → ReadsBack 9 C →
      o + 1 = 9 + C.gates.length →
      (∀ t, t+1 < C.gates.length → ∃ g ∈ C.gates.drop (t+1), 9+t ∈ g.inputs) →
      (∀ g ∈ free, g.inputs.Pairwise (· < ·) ∧
        ((g.op = .not ∧ g.inputs.length = 1) ∨ (g.op ≠ .not ∧ g.inputs.length = 2)) ∧
        ∀ w ∈ g.inputs, w ∉ ([4,6,7] : List ℕ)) →
      ∃ z : ℕ, z < 512 ∧
        C.eval (List.ofFn (fun v : Fin 9 => z.testBit v.val)) ≠
          ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any (fun e => z &&& e == e)) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x6).card = (1 : ℕ) ∧ ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  let edge (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5

  let extend (l : List Bool) (g : Gate) : List Bool :=
    l ++ [g.op.eval (g.inputs.map fun k => l.getD k false)]

  have prefixValue (xs ys : List Bool) (i : ℕ) (d : Bool) (h : i < xs.length) :
      (xs ++ ys).getD i d = xs.getD i d := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

  have absentValue (xs : List Bool) (i : ℕ) (h : xs.length ≤ i) : xs.getD i false = false := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

  have preserve_input (gs : List Gate) (l : List Bool) (i : ℕ) (hi : i < l.length) :
      (gs.foldl extend l).getD i false = l.getD i false := by
    induction gs generalizing l with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl extend (extend l g)).getD i false = _
      rw [ih (extend l g) (by simp [extend]; omega)]
      exact prefixValue _ _ _ _ hi

  have snoc_agree (l l' : List Bool) (b : Bool) (v : ℕ) (len : l.length = l'.length)
      (eq : ∀ k, k ≠ v → l.getD k false = l'.getD k false) :
      ∀ k, k ≠ v → (l ++ [b]).getD k false = (l' ++ [b]).getD k false := by
    intro k hv
    by_cases h : k < l.length
    · rw [prefixValue _ _ _ _ h, prefixValue _ _ _ _ (by omega : k < l'.length)]
      exact eq k hv
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : l.length ≤ k),
        List.getElem?_append_right (by omega : l'.length ≤ k), len]

  have propagate (gs : List Gate) (v w : ℕ)
      (read : ∀ g ∈ gs, v ∈ g.inputs → g.op = .or ∧ (g.inputs = [v,w] ∨ g.inputs = [w,v]))
      (l l' : List Bool) (len : l.length = l'.length) (hw : w < l.length)
      (bit : l.getD w false = true) (bit' : l'.getD w false = true)
      (eq : ∀ k, k ≠ v → l.getD k false = l'.getD k false) :
      ∀ k, k ≠ v → (gs.foldl extend l).getD k false = (gs.foldl extend l').getD k false := by
    induction gs generalizing l l' with
    | nil => exact eq
    | cons g gs ih =>
      have val : g.op.eval (g.inputs.map fun k => l.getD k false) =
          g.op.eval (g.inputs.map fun k => l'.getD k false) := by
        by_cases hv : v ∈ g.inputs
        · obtain ⟨op, pins⟩ := read g (by simp) hv
          have evalOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
          rcases pins with p | p <;>
            simp only [op, p, evalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id, bit, bit', Bool.true_or, Bool.or_true]
        · congr 1
          apply List.map_congr_left
          intro k hk
          exact eq k (fun e => hv (e ▸ hk))
      apply ih (fun h hh => read h (List.mem_cons_of_mem _ hh)) (extend l g) (extend l' g)
      · simp [extend, len]
      · simp [extend]; omega
      · exact (prefixValue _ _ _ _ hw).trans bit
      · exact (prefixValue _ _ _ _ (by omega : w < l'.length)).trans bit'
      · unfold extend
        rw [val]
        exact snoc_agree _ _ _ _ len eq

  -- Holding the other input true masks the private input. A pair of graph assignments detects this.
  have raw_companion (C : Circuit) (hf : circuitFun 9 C = edge) (v w : Fin 9)
      (hv : v ∈ ([4,6,7] : List (Fin 9))) (diff : w ≠ v)
      (read : ∀ g ∈ C.gates, v.val ∈ g.inputs → g.op = .or ∧
        (g.inputs = [v.val,w.val] ∨ g.inputs = [w.val,v.val])) : False := by
    let pair (w t j : Fin 9) : Bool := decide (j = w ∨ j = t)
    let triple (v w t j : Fin 9) : Bool := decide (j = v ∨ j = w ∨ j = t)
    have wit : ∀ a ∈ ([4,6,7] : List (Fin 9)), ∀ b : Fin 9, b ≠ a → ∃ t : Fin 9,
        edge (pair b t) = false ∧ edge (triple a b t) = true := by decide
    obtain ⟨t,hx,hy⟩ := wit v hv w diff
    let x := pair w t
    let y := triple v w t
    have ofFn (a : Fin 9 → Bool) (j : ℕ) (hj : j < 9) :
        (List.ofFn a).getD j false = a ⟨j,hj⟩ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hj)]
      simp only [Option.getD_some, List.getElem_ofFn]
    have eq : ∀ k, k ≠ v.val → (List.ofFn x).getD k false = (List.ofFn y).getD k false := by
      intro k hk
      by_cases h : k < 9
      · rw [ofFn x k h, ofFn y k h]
        have ne : (⟨k,h⟩ : Fin 9) ≠ v := fun e => hk (congrArg Fin.val e)
        simp [x, y, pair, triple, ne]
      · rw [absentValue _ _ (by simpa using Nat.le_of_not_gt h : (List.ofFn x).length ≤ k),
            absentValue _ _ (by simpa using Nat.le_of_not_gt h : (List.ofFn y).length ≤ k)]
    by_cases out : C.output = v.val
    · let z : Fin 9 → Bool := fun j => decide (j = v)
      have singleton : ∀ i : Fin 9, edge (fun j => decide (j = i)) = false := by decide
      have hz := congrFun hf z
      change (C.gates.foldl extend (List.ofFn z)).getD C.output false = edge z at hz
      rw [out, preserve_input _ _ _ (by simp), ofFn z _ v.isLt, singleton v] at hz
      simp [z] at hz
    · have all := propagate C.gates v.val w.val read (List.ofFn x) (List.ofFn y) (by simp)
          (by simp) (by rw [ofFn x _ w.isLt]; simp [x,pair])
          (by rw [ofFn y _ w.isLt]; simp [y,triple]) eq C.output out
      change circuitFun 9 C x = circuitFun 9 C y at all
      rw [hf] at all
      change edge (pair w t) = edge (triple v w t) at all
      rw [hx,hy] at all
      exact Bool.noConfusion all

  have raw_companion_indexed (C : Circuit) (hf : circuitFun 9 C = edge) (v : Fin 9)
      (hv : v ∈ ([4,6,7] : List (Fin 9))) (w : ℕ) (diff : w ≠ v.val) (i : Fin C.size)
      (op : (C.gates.get i).op = .or)
      (pins : (C.gates.get i).inputs = [v.val,w] ∨ (C.gates.get i).inputs = [w,v.val])
      (privateRead : ∀ k : Fin C.size, k ≠ i → v.val ∉ (C.gates.get k).inputs) : 9 ≤ w := by
    apply Nat.le_of_not_gt
    intro hw
    apply raw_companion C hf v ⟨w,hw⟩ hv (fun e => diff (congrArg Fin.val e))
    intro g hg hvg
    obtain ⟨k,rfl⟩ := List.mem_iff_get.mp hg
    have ki : k = i := by
      exact Classical.byContradiction (fun h => privateRead k h hvg)
    subst k
    exact ⟨op,pins⟩

  dsimp only
  intro C model unique
  obtain ⟨minimal, budget, computes, shape, _⟩ := model
  change circuitFun 9 C = edge at computes
  let Mark (v : Nat) (g : Gate) : Prop :=
    g.op = .or ∧ ∃ w, 9 ≤ w ∧ (g.inputs = [v,w] ∨ g.inputs = [w,v])

  let Segmented (C : Circuit) : Prop :=
    ∃ (a b c : Nat) (p q r s : List Gate) (u v w : Gate),
      [a,b,c].Perm [4,6,7] ∧
      C.gates = p ++ u :: (q ++ v :: (r ++ w :: s)) ∧
      Mark a u ∧ Mark b v ∧ Mark c w ∧
      (∀ g ∈ p ++ q ++ r ++ s, ∀ x ∈ ([4,6,7] : List Nat), x ∉ g.inputs) ∧
      p.length + q.length + r.length + s.length ≤ 12

  have decompose (C : Circuit) (budget : C.size ≤ 15)
      (chosen : ∀ x ∈ ([4,6,7] : List Nat),
        ∃ i : Fin C.size, Mark x (C.gates.get i) ∧
          (∀ j : Fin C.size, x ∈ (C.gates.get j).inputs ↔ j = i)) : Segmented C := by
    let slice (lo hi : Nat) := (C.gates.drop lo).take (hi - lo)
    have atSlice {lo hi : Nat} {g : Gate} (h : g ∈ slice lo hi) :
        ∃ k : Fin C.size, lo ≤ k.val ∧ k.val < hi ∧ C.gates.get k = g := by
      obtain ⟨t,ht,hg⟩ := List.mem_iff_getElem.mp h
      have ht' : t < min (hi-lo) (C.gates.length-lo) := by simpa [slice] using ht
      refine ⟨⟨lo+t, by change lo+t < C.gates.length; omega⟩, Nat.le_add_right _ _, ?_, ?_⟩
      · change lo+t < hi; omega
      change C.gates[lo+t] = g
      simpa [slice, List.get_eq_getElem, List.getElem_take, List.getElem_drop] using hg
    have form (lo hi : Nat) (hle : lo ≤ hi) (hlt : hi < C.gates.length) :
        C.gates.drop lo = slice lo hi ++ C.gates[hi] :: C.gates.drop (hi+1) := by
      rw [← List.drop_eq_getElem_cons hlt]
      have hz : hi-lo+lo = hi := by omega
      simpa [slice, List.drop_drop, hz, Nat.add_comm lo] using
        (List.take_append_drop (hi-lo) (C.gates.drop lo)).symm
    have sorted (a b c : Nat) (i j k : Fin C.size) (hp : [a,b,c].Perm [4,6,7])
        (hij : i.val < j.val) (hjk : j.val < k.val)
        (ma : Mark a (C.gates.get i)) (mb : Mark b (C.gates.get j)) (mc : Mark c (C.gates.get k))
        (ha : ∀ t : Fin C.size, a ∈ (C.gates.get t).inputs ↔ t = i)
        (hb : ∀ t : Fin C.size, b ∈ (C.gates.get t).inputs ↔ t = j)
        (hc : ∀ t : Fin C.size, c ∈ (C.gates.get t).inputs ↔ t = k) : Segmented C := by
      let p := slice 0 i.val
      let q := slice (i.val+1) j.val
      let r := slice (j.val+1) k.val
      let s := slice (k.val+1) C.size
      have he : C.gates.drop (k.val+1) = s := by
        change _ = (C.gates.drop (k.val+1)).take (C.gates.length - (k.val+1))
        rw [← List.length_drop, List.take_length]
      have eq : C.gates = p ++ C.gates.get i :: (q ++ C.gates.get j :: (r ++ C.gates.get k :: s)) := by
        have h := form 0 i.val (Nat.zero_le _) i.isLt
        rw [form (i.val+1) j.val (by omega) j.isLt, form (j.val+1) k.val (by omega) k.isLt, he] at h
        change C.gates = p ++ C.gates[i.val]'i.isLt :: (q ++ C.gates[j.val]'j.isLt :: (r ++ C.gates[k.val]'k.isLt :: s))
        simpa [p,q,r] using h
      refine ⟨a,b,c,p,q,r,s,C.gates.get i,C.gates.get j,C.gates.get k,hp,eq,ma,mb,mc,?_,?_⟩
      · intro g hg x hx hit
        have clean (t : Fin C.size) (ht : C.gates.get t = g)
            (ni : t.val ≠ i.val) (nj : t.val ≠ j.val) (nk : t.val ≠ k.val) : False := by
          have hm := hp.mem_iff.mpr hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rw [← ht] at hit
          rcases hm with rfl | rfl | rfl
          · exact ni (congrArg Fin.val ((ha t).mp hit))
          · exact nj (congrArg Fin.val ((hb t).mp hit))
          · exact nk (congrArg Fin.val ((hc t).mp hit))
        simp only [List.mem_append] at hg
        rcases hg with ((h | h) | h) | h
        all_goals
          obtain ⟨t,hlo,hhi,ht⟩ := atSlice h
          exact clean t ht (by omega) (by omega) (by omega)
      · have sz := congrArg List.length eq
        simp only [List.length_append, List.length_cons] at sz
        change C.gates.length ≤ 15 at budget
        omega
    obtain ⟨i, mi, ui⟩ := chosen 4 (by decide)
    obtain ⟨j, mj, uj⟩ := chosen 6 (by decide)
    obtain ⟨k, mk, uk⟩ := chosen 7 (by decide)
    have apart {a b : Nat} {i j : Fin C.size} (ma : Mark a (C.gates.get i))
        (mb : Mark b (C.gates.get j)) (hab : a ≠ b) (ha : a < 9) : i.val ≠ j.val := by
      intro e
      have e' := Fin.ext e
      subst j
      obtain ⟨_, w, hw, ea⟩ := ma
      obtain ⟨_, z, hz, eb⟩ := mb
      rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea] at eb <;> simp at eb <;> omega
    have ij := apart mi mj (by decide) (by decide)
    have jk := apart mj mk (by decide) (by decide)
    have ik := apart mi mk (by decide) (by decide)
    by_cases h1 : i.val < j.val
    · by_cases h2 : j.val < k.val
      · exact sorted 4 6 7 i j k (by decide) h1 h2 mi mj mk ui uj uk
      · by_cases h3 : i.val < k.val
        · exact sorted 4 7 6 i k j (by decide) h3 (by omega) mi mk mj ui uk uj
        · exact sorted 7 4 6 k i j (by decide) (by omega) h1 mk mi mj uk ui uj
    · by_cases h2 : i.val < k.val
      · exact sorted 6 4 7 j i k (by decide) (by omega) h2 mj mi mk uj ui uk
      · by_cases h3 : j.val < k.val
        · exact sorted 6 7 4 j k i (by decide) h3 (by omega) mj mk mi uj uk ui
        · exact sorted 7 6 4 k j i (by decide) (by omega) (by omega) mk mj mi uk uj ui
  have chosen : ∀ x ∈ ([4,6,7] : List Nat), ∃ i : Fin C.size, Mark x (C.gates.get i) ∧
      (∀ j : Fin C.size, x ∈ (C.gates.get j).inputs ↔ j = i) := by
    intro x hx
    have hx9 : x < 9 := by simp at hx; omega
    let v : Fin 9 := ⟨x,hx9⟩
    have hv : v ∈ ([4,6,7] : List (Fin 9)) := by
      simp at hx ⊢
      rcases hx with h | h | h <;> simp [v,h]
    obtain ⟨cardinality, ops⟩ := unique v hv
    let readers : Finset (Fin C.size) := Finset.univ.filter fun i => x ∈ (C.gates.get i).inputs
    change readers.card = 1 at cardinality
    obtain ⟨i, eqlist⟩ := Finset.card_eq_one.mp cardinality
    have hit (k : Fin C.size) : x ∈ (C.gates.get k).inputs ↔ k = i := by
      have equal : k ∈ readers ↔ k = i := by rw [eqlist, Finset.mem_singleton]
      simpa [readers] using equal
    have atI := (hit i).mpr rfl
    have isOR : (C.gates.get i).op = .or := ops i (by
      change i ∈ readers
      rw [eqlist]
      exact Finset.mem_singleton_self i)
    have pins2 : (C.gates.get i).inputs.length = 2 := by
      rcases (shape i).2.2 with hn | ha
      · rw [isOR] at hn
        cases hn.1
      · exact ha.2
    have only (k : Fin C.size) (hne : k ≠ i) : x ∉ (C.gates.get k).inputs :=
      fun h => hne ((hit k).mp h)
    obtain ⟨a,b,pins⟩ := List.length_eq_two.mp pins2
    have ab : a ≠ b := by simpa [pins] using (shape i).2.1
    have own : x = a ∨ x = b := by simpa [pins] using atI
    refine ⟨i, ⟨isOR, ?_⟩, hit⟩
    rcases own with ea | eb
    · subst a
      exact ⟨b,raw_companion_indexed C computes v hv b (Ne.symm ab) i isOR (Or.inl pins) only,
        Or.inl pins⟩
    · subst b
      exact ⟨a,raw_companion_indexed C computes v hv a ab i isOR (Or.inr pins) only,Or.inr pins⟩
  -- Permuting the three pairs of opposite vertices preserves the six-cycle and its attachments.
  have symmetry : ∀ a b c : Nat, [a,b,c].Perm [4,6,7] →
      ∃ t : Fin 9 → Fin 9,
        let ρ := fun j : Nat => if h : j < 9 then (t ⟨j,h⟩).val else j
        ρ a = 4 ∧ ρ b = 6 ∧ ρ c = 7 ∧
        (∀ j, ρ j ∈ ([4,6,7] : List Nat) ↔ j ∈ ([4,6,7] : List Nat)) ∧
        Function.Injective t ∧ (∀ x, edge (x ∘ t) = edge x) := by
    let A : Fin 6 → Fin 9 → Fin 9 :=
      ![![0, 1, 2, 3, 4, 5, 6, 7, 8], ![0, 5, 8, 3, 4, 1, 7, 6, 2],
        ![1, 0, 5, 8, 6, 2, 4, 7, 3], ![1, 2, 3, 8, 6, 0, 7, 4, 5],
        ![2, 1, 0, 5, 7, 3, 6, 4, 8], ![2, 3, 8, 5, 7, 1, 4, 6, 0]]
    have cover : ∀ a b c : Fin 9, [a.val,b.val,c.val].Perm [4,6,7] →
        ∃ k : Fin 6, (A k a).val = 4 ∧ (A k b).val = 6 ∧ (A k c).val = 7 := by
      dsimp only [A]
      decide
    have pres : ∀ k : Fin 6, ∀ j : Fin 9,
        (A k j).val ∈ ([4,6,7] : List Nat) ↔ j.val ∈ ([4,6,7] : List Nat) := by
      dsimp only [A]
      decide
    have fixed : ∀ k : Fin 6, ∀ x : Fin 9 → Bool, edge (x ∘ A k) = edge x := by
      intro k x
      fin_cases k <;> simp [edge, A, Function.comp_def, Bool.and_comm, Bool.or_comm,
        Bool.or_left_comm, Bool.or_assoc]
    have inject : ∀ k : Fin 6, Function.Injective (A k) := by
      change ∀ (k : Fin 6) (i j : Fin 9), A k i = A k j → i = j
      dsimp only [A]
      decide
    intro a b c h
    have hbnd : ∀ j ∈ [a,b,c], j < 9 := by
      intro j hj
      have hh : j ∈ [4,6,7] := h.mem_iff.mp hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      omega
    have ha := hbnd a (by simp)
    have hb := hbnd b (by simp)
    have hc := hbnd c (by simp)
    obtain ⟨k,h1,h2,h3⟩ := cover ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ h
    refine ⟨A k, ?_, ?_, ?_, ?_, inject k, fixed k⟩
    · simpa [ha] using h1
    · simpa [hb] using h2
    · simpa [hc] using h3
    · intro j
      by_cases hj : j < 9
      · simpa [hj] using pres k ⟨j,hj⟩
      · simp [hj]
  obtain ⟨a,b,c,p,q,r,s,ga,gb,gc,hperm,hcut,ma,mb,mc,hclean,hcount⟩ :=
    decompose C budget chosen
  obtain ⟨τ, ha, hb, hc, hspecial, hinject, hinv⟩ := symmetry a b c hperm
  let wire := fun (j : ℕ) => if h : j < 9 then (τ ⟨j,h⟩).val else j
  let gate := fun (g : Gate) => {g with inputs := (g.inputs.map wire).mergeSort}
  let D : Circuit := ⟨C.gates.map gate, wire C.output⟩
  have renameLarge (j : ℕ) (hj : 9 ≤ j) : wire j = j := by simp [wire, Nat.not_lt.mpr hj]
  have rewire {a' : ℕ} {g : Gate} (small : a' < 9) (h : Mark a' g) :
      ∃ w, 9 ≤ w ∧ gate g = ⟨.or, [wire a', w]⟩ := by
    obtain ⟨hop,w,hw,pins⟩ := h
    refine ⟨w,hw,?_⟩
    have hle : wire a' ≤ w := by
      have : wire a' < 9 := by simp [wire, small]
      omega
    cases g with
    | mk op ins =>
      change op = .or at hop
      subst op
      rcases pins with pins | pins <;> change ins = _ at pins <;> subst ins <;>
        simp [gate, renameLarge w hw, List.mergeSort_pair, hle, show ¬ w ≤ wire a' from by
          have : wire a' < 9 := by simp [wire, small]
          omega]
  have below (v : ℕ) (h : v ∈ [a,b,c]) : v < 9 := by
    have hh := hperm.mem_iff.mp h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    omega
  obtain ⟨i,hi,egi⟩ := rewire (below a (by simp)) ma
  obtain ⟨j,hj,egj⟩ := rewire (below b (by simp)) mb
  obtain ⟨k,hk,egk⟩ := rewire (below c (by simp)) mc
  change wire a = 4 at ha
  change wire b = 6 at hb
  change wire c = 7 at hc
  rw [ha] at egi
  rw [hb] at egj
  rw [hc] at egk
  have layout : D.gates = p.map gate ++ (Gate.mk .or [4,i]) ::
      (q.map gate ++ (Gate.mk .or [6,j]) :: (r.map gate ++ (Gate.mk .or [7,k]) :: s.map gate)) := by
    change C.gates.map gate = _
    simp only [hcut,List.map_append,List.map_cons,egi,egj,egk]
  have fan : FanInTwo D := by
    intro g hg
    obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
    have H := minimal.1 g' hg'
    exact ⟨H.1, by simpa [gate] using H.2⟩
  have reads : ReadsBack 9 D := by
    intro n hn w hw
    change n < (C.gates.map gate).length at hn
    have hn' : n < C.size := by change n < C.gates.length; simpa using hn
    have gat : gateAt D n = gate (C.gates.get ⟨n,hn'⟩) := by
      change (C.gates.map gate).getD n _ = _
      rw [List.getD_eq_getElem _ _ hn]
      simp
    rw [gat] at hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ((List.mergeSort_perm _ _).mem_iff.mp hw)
    have orig := (shape ⟨n,hn'⟩).1 v hv
    by_cases small : v < 9
    · have : wire v < 9 := by simp [wire,small]
      omega
    · simpa [wire,small] using orig
  have wireInj : Function.Injective wire := by
    intro x y eq
    by_cases hx : x < 9 <;> by_cases hy : y < 9
    · have he : τ ⟨x,hx⟩ = τ ⟨y,hy⟩ := Fin.ext (by simpa [wire,hx,hy] using eq)
      exact congrArg Fin.val (hinject he)
    · have h := (τ ⟨x,hx⟩).isLt
      simp [wire,hx,hy] at eq
      omega
    · have h := (τ ⟨y,hy⟩).isLt
      simp [wire,hx,hy] at eq
      omega
    · simpa [wire,hx,hy] using eq
  have clean : ∀ g ∈ (p ++ q ++ r ++ s).map gate, g.inputs.Pairwise (· < ·) ∧
      ((g.op = .not ∧ g.inputs.length = 1) ∨ (g.op ≠ .not ∧ g.inputs.length = 2)) ∧
      ∀ w ∈ g.inputs, w ∉ ([4,6,7] : List ℕ) := by
    intro g hg
    obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
    have member : g' ∈ C.gates := by
      rw [hcut]
      simp only [List.mem_append,List.mem_cons] at hg' ⊢
      tauto
    obtain ⟨n,hn⟩ := List.mem_iff_get.mp member
    have norm := (shape n).2
    rw [hn] at norm
    refine ⟨?_,?_,?_⟩
    · have weak : (gate g').inputs.Pairwise (· ≤ ·) := List.pairwise_mergeSort' _ _
      have distinct : (gate g').inputs.Nodup :=
        (List.mergeSort_perm _ _).nodup_iff.mpr (norm.1.map wireInj)
      exact (weak.and distinct).imp (fun h => lt_of_le_of_ne h.1 h.2)
    · simpa [gate] using norm.2
    · intro w hw hs
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ((List.mergeSort_perm _ _).mem_iff.mp hw)
      exact hclean g' hg' v ((hspecial _).mp hs) hv
  have unary : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1 := by
    intro g hg hop
    obtain ⟨n,rfl⟩ := List.mem_iff_get.mp hg
    rcases (shape n).2.2 with h | h
    · exact h.2.le
    · exact (h.1 hop).elim
  have lastout (C : Circuit) (minimal : IsMinimalCircuit 9 C)
      (correct : circuitFun 9 C = edge) : C.output + 1 = 9 + C.gates.length := by
    let F := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
    have flen (gs : List Gate) (w : List Bool) :
        (gs.foldl F w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp [F]
        omega
    have fpre (gs : List Gate) (w : List Bool) (k : Nat) (hk : k < w.length) :
        (gs.foldl F w).getD k false = w.getD k false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih (F w g) (by simp [F]; omega)]
        exact List.getD_append _ _ _ _ hk
    have hout : C.output < 9 + C.gates.length := by
      by_contra! h
      have hh := congrFun correct (fun _ => true)
      change (C.gates.foldl F (List.ofFn (fun _ : Fin 9 => true))).getD C.output false = true at hh
      rw [List.getD_eq_default _ _ (by simpa [flen] using h)] at hh
      contradiction
    have hfirst : 9 ≤ C.output := by
      by_contra! h
      let i : Fin 9 := ⟨C.output,h⟩
      let x : Fin 9 → Bool := fun j => decide (j = i)
      have hsingle : ∀ i : Fin 9, edge (fun j => decide (j = i)) = false := by
        dsimp only [edge]
        decide
      have hh := (congrFun correct x).trans (hsingle i)
      change (C.gates.foldl F (List.ofFn x)).getD C.output false = false at hh
      have hb : C.output < (List.ofFn x).length := by simpa using h
      rw [fpre _ _ _ hb, List.getD_eq_getElem _ _ hb] at hh
      rw [List.getElem_ofFn] at hh
      simp [x,i] at hh
    let m := C.output + 1 - 9
    have hm : m ≤ C.gates.length := by dsimp [m]; omega
    let D : Circuit := ⟨C.gates.take m,C.output⟩
    have hfan : FanInTwo D := by
      intro g hg
      exact minimal.1 g (List.mem_of_mem_take hg)
    have equiv : circuitFun 9 D = circuitFun 9 C := by
      funext x
      change ((C.gates.take m).foldl F (List.ofFn x)).getD C.output false =
        (C.gates.foldl F (List.ofFn x)).getD C.output false
      conv_rhs => rw [← List.take_append_drop m C.gates, List.foldl_append]
      symm
      apply fpre
      simp [flen, List.length_take, m]
      omega
    have hs := minimal.2 D hfan equiv
    change C.gates.length ≤ (C.gates.take m).length at hs
    rw [List.length_take, Nat.min_eq_left hm] at hs
    dsimp [m] at hs
    omega

  -- Every retained gate feeds a later one unless it is the output.
  have usedLater (C : Circuit) (minimal : IsMinimalCircuit 9 C)
      (pre post : List Gate) (g : Gate) (decomp : C.gates = pre ++ g :: post)
      (notOut : C.output ≠ 9 + pre.length) :
      ∃ q ∈ post, 9 + pre.length ∈ q.inputs := by
    by_contra! absent
    let w := 9 + pre.length
    let shift := fun (i : Nat) => if i < w then i else i - 1
    let rename := fun (q : Gate) => Gate.mk q.op (q.inputs.map shift)
    let D : Circuit := ⟨pre ++ post.map rename, shift C.output⟩
    have fan : FanInTwo D := by
      intro q hq
      change q ∈ pre ++ post.map rename at hq
      rcases List.mem_append.mp hq with h | h
      · exact minimal.1 q (by rw [decomp]; exact List.mem_append_left _ h)
      · obtain ⟨q',h',rfl⟩ := List.mem_map.mp h
        have hq' := minimal.1 q' (by rw [decomp]; simp [h'])
        simpa [rename] using hq'
    let F := fun (l : List Bool) (q : Gate) =>
      l ++ [q.op.eval (q.inputs.map (fun i => l.getD i false))]
    have len (qs : List Gate) (l : List Bool) : (qs.foldl F l).length = l.length + qs.length := by
      induction qs generalizing l with
      | nil => simp
      | cons q qs ih =>
        rw [List.foldl_cons, ih]
        simp [F]
        omega
    have reader (L R : List Bool) (b : Bool) (i : Nat) (hw : L.length = w) (hne : i ≠ w) :
        (L ++ R).getD (shift i) false = (L ++ b :: R).getD i false := by
      by_cases hlt : i < w
      · have hi : i < L.length := by omega
        simp only [shift,hlt,ite_true]
        rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ hi]
      · have hgt : w < i := by omega
        simp only [shift,hlt,ite_false]
        rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega)]
        have heq : i - L.length = (i - 1 - L.length) + 1 := by omega
        rw [heq]
        rfl
    have sim (L : List Bool) (hw : L.length = w) (b : Bool) (qs : List Gate)
        (hn : ∀ q ∈ qs, w ∉ q.inputs) (R : List Bool) :
        ∃ R', (qs.map rename).foldl F (L ++ R) = L ++ R' ∧
          qs.foldl F (L ++ b :: R) = L ++ b :: R' := by
      induction qs generalizing R with
      | nil => exact ⟨R,rfl,rfl⟩
      | cons q qs ih =>
        have he : (rename q).inputs.map (fun i => (L ++ R).getD i false) =
            q.inputs.map (fun i => (L ++ b :: R).getD i false) := by
          change (q.inputs.map shift).map _ = _
          rw [List.map_map]
          apply List.map_congr_left
          intro i hi
          exact reader L R b i hw (by rintro rfl; exact hn q (by simp) hi)
        let v := q.op.eval (q.inputs.map (fun i => (L ++ b :: R).getD i false))
        have h1 : F (L ++ R) (rename q) = L ++ (R ++ [v]) := by
          simp only [F, he, List.append_assoc]
          rfl
        have h2 : F (L ++ b :: R) q = L ++ b :: (R ++ [v]) := by
          simp [F, v, List.append_assoc]
        simp only [List.map_cons, List.foldl_cons, h1, h2]
        exact ih (fun q' hq => hn q' (List.mem_cons_of_mem _ hq)) (R ++ [v])
    have equiv : circuitFun 9 D = circuitFun 9 C := by
      funext x
      let L := pre.foldl F (List.ofFn x)
      let b := g.op.eval (g.inputs.map (fun i => L.getD i false))
      have hw : L.length = w := by simp [L, len, w]
      obtain ⟨R,h1,h2⟩ := sim L hw b post absent []
      change ((pre ++ post.map rename).foldl F (List.ofFn x)).getD (shift C.output) false =
        (C.gates.foldl F (List.ofFn x)).getD C.output false
      rw [decomp,List.foldl_append,List.foldl_append,List.foldl_cons]
      change ((post.map rename).foldl F L).getD (shift C.output) false =
        (post.foldl F (L ++ [b])).getD C.output false
      simp only [List.append_nil] at h1
      rw [h1,h2]
      exact reader _ _ _ _ hw notOut
    have hs := minimal.2 D fan equiv
    change C.gates.length ≤ (pre ++ post.map rename).length at hs
    simp [decomp] at hs
  have live : ∀ t, t+1 < D.gates.length → ∃ g ∈ D.gates.drop (t+1), 9+t ∈ g.inputs := by
    intro t ht
    change t + 1 < (C.gates.map gate).length at ht
    have ht' : t+1 < C.gates.length := by simpa using ht
    have ht0 : t < C.gates.length := by omega
    have pref : (C.gates.take t).length = t := by simp [List.length_take, Nat.min_eq_left ht0.le]
    have decomp : C.gates = C.gates.take t ++ C.gates[t] :: C.gates.drop (t+1) := by
      rw [← List.drop_eq_getElem_cons ht0, List.take_append_drop]
    have hout := lastout C minimal computes
    obtain ⟨g,hg,hpin⟩ := usedLater C minimal (C.gates.take t) (C.gates.drop (t+1)) C.gates[t] decomp
      (by rw [pref]; omega)
    refine ⟨gate g, ?_, ?_⟩
    · change gate g ∈ (C.gates.map gate).drop (t+1)
      rw [← List.map_drop]
      exact List.mem_map_of_mem hg
    · rw [pref] at hpin
      apply (List.mergeSort_perm _ _).mem_iff.mpr
      exact List.mem_map.mpr ⟨9+t,hpin,renameLarge _ (by omega)⟩
  have run (x : Fin 9 → Bool) : D.eval (List.ofFn x) = edge x := by
    calc D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ τ)) := canonical C τ minimal.1 unary x
         _ = edge (x ∘ τ) := congrFun computes _
         _ = edge x := hinv x
  have bad := enumerate (p.map gate) (q.map gate) (r.map gate) (s.map gate) i j k D.output
  change (p.map gate ++ q.map gate ++ r.map gate ++ s.map gate).length ≤ 12 →
    (∀ w ∈ [i,j,k], 9 ≤ w) → _ at bad
  have deq : Circuit.mk (p.map gate ++ Gate.mk .or [4,i] ::
      (q.map gate ++ Gate.mk .or [6,j] :: (r.map gate ++ Gate.mk .or [7,k] :: s.map gate)))
      D.output = D := by rw [← layout]
  dsimp only at bad
  rw [deq] at bad
  obtain ⟨z,hz,wrong⟩ := bad (by simpa [Nat.add_assoc] using hcount)
    (by intro w hw; simp at hw; rcases hw with rfl|rfl|rfl <;> assumption)
    fan reads (by
      have ho := lastout C minimal computes
      have hl : C.gates.length ≥ 1 := by
        rw [hcut]
        simp only [List.length_append, List.length_cons]
        omega
      have low : 9 ≤ C.output := by omega
      rw [← layout]
      change wire C.output + 1 = 9 + (C.gates.map gate).length
      simpa [renameLarge _ low] using ho) (by
      rw [← layout]
      exact live) (by simpa only [List.map_append] using clean)
  apply wrong
  rw [run]
  have rows : ∀ t : Fin 512, edge (fun v : Fin 9 => t.val.testBit v.val) =
    ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any (fun e => t.val &&& e == e) := by decide
  exact rows ⟨z,hz⟩
