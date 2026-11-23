import Mathlib
import PEqualNP.Defs

namespace LMeta572

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

theorem plug {m r s : ℕ} (f : (Fin m → Bool) → Bool) (H : (Fin (m+1) → Bool) → Bool)
    (hf : HasCircuitSize m f r) (hh : HasCircuitSize (m+1) H s)
    (live : ∃ x, f x = true) :
    HasCircuitSize m (fun x => H (Fin.snoc x (f x))) (r+s) := by
  obtain ⟨D,okD,szD,evD⟩ := hf
  let M := m + D.gates.length
  have len (x : Fin m → Bool) : (D.wires (List.ofFn x)).length = M := by
    have aux (gs : List Gate) (W : List Bool) :
        (gs.foldl step W).length = W.length + gs.length := by
      induction gs generalizing W with
      | nil => simp
      | cons h t ih => simp [List.foldl,ih,step]; omega
    change (D.gates.foldl step _).length = _
    rw [aux]; simp [M]
  have valid : D.output < M := by
    obtain ⟨x,hx⟩ := live
    by_contra! hx'
    have h := evD x
    unfold Circuit.eval at h
    rw [List.getD_eq_default _ _ (by rw [len]; exact hx'), hx] at h
    contradiction
  let π : Fin (m+1) → Fin M := Fin.snoc (fun i : Fin m => (⟨i.val, by dsimp [M]; omega⟩ : Fin M)) ⟨D.output,valid⟩
  obtain ⟨C,okC,szC,evC⟩ := relabel_size π H s hh
  refine ⟨⟨D.gates ++ C.gates,C.output⟩,?_,?_,?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact okD g h
    · exact okC g h
  · change (D.gates++C.gates).length ≤ _
    change D.gates.length ≤ _ at szD
    change C.gates.length ≤ _ at szC
    simp; omega
  · intro x
    let W := D.wires (List.ofFn x)
    let z : Fin M → Bool := fun i => W.getD i.val false
    have ofz : List.ofFn z = W := by
      apply List.ext_getElem <;> simp [z,W,len]
    have hz : z ∘ π = Fin.snoc x (f x) := by
      funext i; refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [z,π,W,Circuit.eval] using evD x
      · have keep (gs : List Gate) (w : List Bool) (j : Nat) (hj : j < w.length) :
            (gs.foldl step w).getD j false = w.getD j false := by
          induction gs generalizing w with
          | nil => rfl
          | cons h t ih =>
            rw [List.foldl_cons,ih (step w h) (by simp [step]; omega)]
            exact List.getD_append _ _ _ _ hj
        simp only [Function.comp_apply,π,Fin.snoc_castSucc]
        change (D.gates.foldl step (List.ofFn x)).getD j.val false = x j
        rw [keep _ _ _ (by simp)]
        simp [List.getD_eq_getElem]
    have h : C.eval (List.ofFn z) = H (z ∘ π) := evC z
    rw [hz] at h
    change ((D.gates ++ C.gates).foldl step _).getD C.output false = _
    rw [List.foldl_append]
    change (C.gates.foldl step W).getD C.output false = _
    change (C.gates.foldl step (List.ofFn z)).getD C.output false = _ at h
    rw [ofz] at h
    exact h
theorem weaken {m s t : ℕ} {f : (Fin m → Bool) → Bool}
    (h : HasCircuitSize m f s) (hle : s ≤ t) : HasCircuitSize m f t := by
  obtain ⟨C, ok, sz, ev⟩ := h
  exact ⟨C,ok,sz.trans hle,ev⟩
theorem input {m : ℕ} (i : Fin m) : HasCircuitSize m (fun x => x i) 0 := by
  refine ⟨⟨[],i.val⟩,by simp [FanInTwo],by simp [Circuit.size],?_⟩
  intro x; simp [Circuit.eval,Circuit.wires,List.getD_eq_getElem]
theorem addWire {m : ℕ} (a b : Fin m) (op : GateOp) (ho : op = .and ∨ op = .or) :
    HasCircuitSize m (fun x => op.eval [x a,x b]) 1 := by
  refine ⟨⟨[⟨op,[a,b]⟩],m⟩,?_,by simp [Circuit.size],?_⟩
  · intro g hg; simp at hg; subst g
    obtain rfl|rfl := ho <;> simp
  · intro x
    simp [Circuit.eval,Circuit.wires,List.getD_eq_getElem]
theorem binary {m s t : ℕ} {f g : (Fin m → Bool) → Bool}
    (hf : HasCircuitSize m f s) (hg : HasCircuitSize m g t)
    (lf : ∃ x, f x = true) (lg : ∃ x, g x = true)
    (op : GateOp) (ho : op = .and ∨ op = .or) :
    HasCircuitSize m (fun x => op.eval [f x,g x]) (s+t+1) := by
  let G : (Fin (m+1) → Bool) → Bool := fun z => g (fun i => z i.castSucc)
  have hG : HasCircuitSize (m+1) G t := relabel_size Fin.castSucc g t hg
  have lG : ∃ x, G x = true := by
    obtain ⟨x,hx⟩ := lg
    exact ⟨Fin.snoc x false, by simpa [G] using hx⟩
  have h1 := addWire (Fin.last m).castSucc (Fin.last (m+1)) op ho
  have h2 := plug G _ hG h1 lG
  have h3 := plug f _ hf h2 lf
  simpa [G,Nat.add_assoc] using h3
theorem orSize {m s t : ℕ} {f g : (Fin m → Bool) → Bool}
    (hf : HasCircuitSize m f s) (hg : HasCircuitSize m g t) :
    HasCircuitSize m (fun x => f x || g x) (s+t+1) := by
  by_cases lf : ∃ x, f x = true
  · by_cases lg : ∃ x, g x = true
    · simpa [GateOp.eval] using binary hf hg lf lg .or (Or.inr rfl)
    · have h x : g x = false := by cases he : g x <;> simp_all
      simpa [h] using weaken hf (show s ≤ s+t+1 by omega)
  · have h x : f x = false := by cases he : f x <;> simp_all
    simpa [h] using weaken hg (show t ≤ s+t+1 by omega)
theorem andLive {m s t : ℕ} {f g : (Fin m → Bool) → Bool}
    (hf : HasCircuitSize m f s) (hg : HasCircuitSize m g t)
    (lf : ∃ x, f x = true) (lg : ∃ x, g x = true) :
    HasCircuitSize m (fun x => f x && g x) (s+t+1) := by
  simpa [GateOp.eval] using binary hf hg lf lg .and (Or.inl rfl)


theorem congrSize {M : ℕ} {f f' : (Fin M → Bool) → Bool} {s : ℕ}
    (h : HasCircuitSize M f' s) (e : ∀ x, f x = f' x) : HasCircuitSize M f s := by
  have e' : f = f' := funext e
  rw [e']
  exact h

theorem qcast {Q : ℕ → Prop} {a b : ℕ} (h : Q a) (e : a = b) : Q b := by
  rw [← e]
  exact h

def inp (M i : ℕ) (x : Fin M → Bool) : Bool := if hi : i < M then x ⟨i, hi⟩ else false

theorem inp_size (M i : ℕ) (hi : i < M) : HasCircuitSize M (inp M i) 0 := by
  refine congrSize (input (⟨i, hi⟩ : Fin M)) (fun x => ?_)
  unfold inp
  rw [dif_pos hi]

theorem inp_live (M i : ℕ) (hi : i < M) : inp M i (fun _ => true) = true := by
  unfold inp
  rw [dif_pos hi]

theorem inp_natAdd (N K : ℕ) (x : Fin (N + K) → Bool) (i : Fin K) :
    inp (N + K) (N + i.val) x = x (Fin.natAdd N i) := by
  have hi : N + i.val < N + K := by
    have := i.isLt
    omega
  unfold inp
  rw [dif_pos hi]
  rfl

theorem inp_castAdd (N K : ℕ) (x : Fin (N + K) → Bool) (w : Fin N) :
    inp (N + K) w.val x = x (Fin.castAdd K w) := by
  have hw : w.val < N + K := by
    have := w.isLt
    omega
  unfold inp
  rw [dif_pos hw]
  rfl

def term (M a b c : ℕ) (x : Fin M → Bool) : Bool := inp M c x && (inp M a x || inp M b x)

theorem term_true (M a b c : ℕ) (x : Fin M → Bool) :
    term M a b c x = true ↔ inp M c x = true ∧ (inp M a x = true ∨ inp M b x = true) := by
  unfold term
  rw [Bool.and_eq_true, Bool.or_eq_true]

theorem term_size (M a b c : ℕ) (ha : a < M) (hb : b < M) (hc : c < M) :
    HasCircuitSize M (term M a b c) 2 := by
  have h1 := orSize (inp_size M a ha) (inp_size M b hb)
  have l1 : ∃ x : Fin M → Bool, (inp M a x || inp M b x) = true :=
    ⟨fun _ => true, by rw [inp_live M a ha]; rfl⟩
  have h2 := andLive (inp_size M c hc) h1 ⟨fun _ => true, inp_live M c hc⟩ l1
  exact congrSize (weaken h2 (by omega)) (fun x => rfl)

def orUpTo {α : Type} (t : ℕ → α → Bool) : ℕ → α → Bool
  | 0, _ => false
  | (m + 1), x => orUpTo t m x || t m x

theorem orUpTo_zero {α : Type} (t : ℕ → α → Bool) (x : α) : orUpTo t 0 x = false := rfl

theorem orUpTo_succ {α : Type} (t : ℕ → α → Bool) (m : ℕ) (x : α) :
    orUpTo t (m + 1) x = (orUpTo t m x || t m x) := rfl

theorem orUpTo_true {α : Type} (t : ℕ → α → Bool) (m : ℕ) (x : α) :
    orUpTo t m x = true ↔ ∃ k, k < m ∧ t k x = true := by
  induction m with
  | zero =>
    rw [orUpTo_zero]
    constructor
    · intro h
      exact absurd h (by decide)
    · rintro ⟨k, hk, _⟩
      omega
  | succ m ih =>
    rw [orUpTo_succ, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨k, hk, hkt⟩ | h)
      · exact ⟨k, Nat.lt_succ_of_lt hk, hkt⟩
      · exact ⟨m, Nat.lt_succ_self m, h⟩
    · rintro ⟨k, hk, hkt⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · exact Or.inl ⟨k, hk', hkt⟩
      · exact Or.inr hkt

theorem bigOr {M : ℕ} (f : (Fin M → Bool) → Bool) (t : ℕ → (Fin M → Bool) → Bool) (s : ℕ)
    (hf : HasCircuitSize M f s) :
    ∀ m : ℕ, (∀ k, k < m → HasCircuitSize M (t k) 2) →
      HasCircuitSize M (fun x => f x || orUpTo t m x) (s + 3 * m) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine congrSize (weaken hf (by omega)) (fun x => ?_)
    show (f x || orUpTo t 0 x) = f x
    rw [orUpTo_zero, Bool.or_false]
  | succ m ih =>
    intro ht
    have h1 := ih (fun k hk => ht k (Nat.lt_succ_of_lt hk))
    have h2 := orSize h1 (ht m (Nat.lt_succ_self m))
    refine congrSize (weaken h2 (by omega)) (fun x => ?_)
    show (f x || orUpTo t (m + 1) x) = ((f x || orUpTo t m x) || t m x)
    rw [orUpTo_succ, Bool.or_assoc]

theorem pathE_iff (N K : ℕ) (u v : Fin N) (x : Fin (N + K) → Bool) :
    (∃ i : Fin K, x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd K u) = true) ∨
      (i.val + 1 = K ∧ x (Fin.castAdd K v) = true) ∨
      ∃ j : Fin K, j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true)) ↔
    ∃ i : ℕ, i < K ∧ inp (N + K) (N + i) x = true ∧ ((i = 0 ∧ inp (N + K) u.val x = true) ∨
      (i + 1 = K ∧ inp (N + K) v.val x = true) ∨
      (i + 1 < K ∧ inp (N + K) (N + (i + 1)) x = true)) := by
  constructor
  · rintro ⟨i, hp, hr⟩
    refine ⟨i.val, i.isLt, ?_, ?_⟩
    · rw [inp_natAdd N K x]
      exact hp
    · rcases hr with ⟨h0, hu⟩ | ⟨hl, hv⟩ | ⟨j, hj, hpj⟩
      · refine Or.inl ⟨h0, ?_⟩
        rw [inp_castAdd N K x]
        exact hu
      · refine Or.inr (Or.inl ⟨hl, ?_⟩)
        rw [inp_castAdd N K x]
        exact hv
      · have hjlt := j.isLt
        refine Or.inr (Or.inr ⟨by omega, ?_⟩)
        rw [← hj, inp_natAdd N K x]
        exact hpj
  · rintro ⟨i, hi, hp, hr⟩
    refine ⟨⟨i, hi⟩, ?_, ?_⟩
    · rw [← inp_natAdd N K x]
      exact hp
    · rcases hr with ⟨h0, hu⟩ | ⟨hl, hv⟩ | ⟨hlt, hpj⟩
      · refine Or.inl ⟨h0, ?_⟩
        rw [← inp_castAdd N K x]
        exact hu
      · refine Or.inr (Or.inl ⟨hl, ?_⟩)
        rw [← inp_castAdd N K x]
        exact hv
      · refine Or.inr (Or.inr ⟨⟨i + 1, hlt⟩, rfl, ?_⟩)
        rw [← inp_natAdd N K x]
        exact hpj

theorem combA (Q : ℕ → Prop) (N h uu vv : ℕ) :
    (∃ i : ℕ, i < 2 * h + 1 ∧ Q (N + i) ∧ ((i = 0 ∧ Q uu) ∨ (i + 1 = 2 * h + 1 ∧ Q vv) ∨
      (i + 1 < 2 * h + 1 ∧ Q (N + (i + 1))))) ↔
    ∃ k : ℕ, k < h + 1 ∧ Q (N + 2 * k) ∧
      (Q (if k = 0 then uu else N + 2 * k - 1) ∨ Q (if k = h then vv else N + 2 * k + 1)) := by
  constructor
  · rintro ⟨i, hi, hq, hr⟩
    rcases Nat.even_or_odd' i with ⟨k, rfl | rfl⟩
    · refine ⟨k, by omega, hq, ?_⟩
      rcases hr with ⟨h0, hu⟩ | ⟨hl, hv⟩ | ⟨hlt, hn⟩
      · left
        rw [if_pos (by omega : k = 0)]
        exact hu
      · right
        rw [if_pos (by omega : k = h)]
        exact hv
      · right
        rw [if_neg (by omega : ¬ k = h)]
        exact qcast hn (by omega)
    · rcases hr with ⟨h0, _⟩ | ⟨hl, _⟩ | ⟨hlt, hn⟩
      · omega
      · omega
      · refine ⟨k + 1, by omega, qcast hn (by omega), Or.inl ?_⟩
        rw [if_neg (by omega : ¬ k + 1 = 0)]
        exact qcast hq (by omega)
  · rintro ⟨k, hk, hq, hl | hr⟩
    · by_cases h0 : k = 0
      · rw [if_pos h0] at hl
        exact ⟨0, by omega, qcast hq (by omega), Or.inl ⟨rfl, hl⟩⟩
      · rw [if_neg h0] at hl
        exact ⟨2 * k - 1, by omega, qcast hl (by omega),
          Or.inr (Or.inr ⟨by omega, qcast hq (by omega)⟩)⟩
    · by_cases hkh : k = h
      · rw [if_pos hkh] at hr
        exact ⟨2 * k, by omega, hq, Or.inr (Or.inl ⟨by omega, hr⟩)⟩
      · rw [if_neg hkh] at hr
        exact ⟨2 * k, by omega, hq, Or.inr (Or.inr ⟨by omega, qcast hr (by omega)⟩)⟩

theorem combB (Q : ℕ → Prop) (N h uu vv : ℕ) :
    (∃ i : ℕ, i < 2 * h + 1 ∧ Q (N + i) ∧ ((i = 0 ∧ Q uu) ∨ (i + 1 = 2 * h + 1 ∧ Q vv) ∨
      (i + 1 < 2 * h + 1 ∧ Q (N + (i + 1))))) ↔
    ((Q uu ∧ Q N) ∨ (Q vv ∧ Q (N + 2 * h))) ∨
      ∃ k : ℕ, k < h ∧ Q (N + (2 * k + 1)) ∧ (Q (N + 2 * k) ∨ Q (N + (2 * k + 2))) := by
  constructor
  · rintro ⟨i, hi, hq, hr⟩
    rcases hr with ⟨h0, hu⟩ | ⟨hl, hv⟩ | ⟨hlt, hn⟩
    · exact Or.inl (Or.inl ⟨hu, qcast hq (by omega)⟩)
    · exact Or.inl (Or.inr ⟨hv, qcast hq (by omega)⟩)
    · rcases Nat.even_or_odd' i with ⟨k, rfl | rfl⟩
      · exact Or.inr ⟨k, by omega, qcast hn (by omega), Or.inl hq⟩
      · exact Or.inr ⟨k, by omega, hq, Or.inr (qcast hn (by omega))⟩
  · rintro ((⟨hu, hN⟩ | ⟨hv, hNh⟩) | ⟨k, hk, hq, hl | hr⟩)
    · exact ⟨0, by omega, qcast hN (by omega), Or.inl ⟨rfl, hu⟩⟩
    · exact ⟨2 * h, by omega, hNh, Or.inr (Or.inl ⟨rfl, hv⟩)⟩
    · exact ⟨2 * k, by omega, hl, Or.inr (Or.inr ⟨by omega, hq⟩)⟩
    · exact ⟨2 * k + 1, by omega, hq, Or.inr (Or.inr ⟨by omega, qcast hr (by omega)⟩)⟩

def tA (N h uu vv k : ℕ) : (Fin (N + (2 * h + 1)) → Bool) → Bool :=
  term (N + (2 * h + 1)) (if k = 0 then uu else N + 2 * k - 1)
    (if k = h then vv else N + 2 * k + 1) (N + 2 * k)

def tB (N h k : ℕ) : (Fin (N + (2 * h + 1)) → Bool) → Bool :=
  term (N + (2 * h + 1)) (N + 2 * k) (N + (2 * k + 2)) (N + (2 * k + 1))

theorem tA_size (N h : ℕ) (u v : Fin N) (k : ℕ) (hk : k < h + 1) :
    HasCircuitSize (N + (2 * h + 1)) (tA N h u.val v.val k) 2 := by
  have hu := u.isLt
  have hv := v.isLt
  refine term_size _ _ _ _ ?_ ?_ ?_
  · split_ifs <;> omega
  · split_ifs <;> omega
  · omega

theorem tB_size (N h k : ℕ) (hk : k < h) :
    HasCircuitSize (N + (2 * h + 1)) (tB N h k) 2 := by
  refine term_size _ _ _ _ ?_ ?_ ?_ <;> omega

def pos (N h j : ℕ) : ℕ := if j < N then j else if j = N then N else N + 2 * h

theorem pos_lt (N h j : ℕ) (hj : j < N + 2) : pos N h j < N + (2 * h + 1) := by
  unfold pos
  split_ifs <;> omega

def pmap (N h : ℕ) (j : Fin (N + 2)) : Fin (N + (2 * h + 1)) :=
  ⟨pos N h j.val, pos_lt N h j.val j.isLt⟩

theorem x_pmap (N h : ℕ) (x : Fin (N + (2 * h + 1)) → Bool) (j : Fin (N + 2)) :
    x (pmap N h j) = inp (N + (2 * h + 1)) (pos N h j.val) x := by
  unfold inp
  rw [dif_pos (pos_lt N h j.val j.isLt)]
  rfl

theorem pos_cast (N h : ℕ) (i : Fin N) : pos N h (Fin.castAdd 2 i).val = i.val := by
  show pos N h i.val = i.val
  unfold pos
  rw [if_pos i.isLt]

theorem pos_zero (N h : ℕ) : pos N h (Fin.natAdd N (0 : Fin 2)).val = N := by
  have e : (Fin.natAdd N (0 : Fin 2)).val = N := by simp
  rw [e]
  unfold pos
  rw [if_neg (by omega), if_pos rfl]

theorem pos_one (N h : ℕ) : pos N h (Fin.natAdd N (1 : Fin 2)).val = N + 2 * h := by
  have e : (Fin.natAdd N (1 : Fin 2)).val = N + 1 := by simp
  rw [e]
  unfold pos
  rw [if_neg (by omega), if_neg (by omega)]

theorem partA (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool) (s : ℕ)
    (hs : HasCircuitSize N g s) (F : (Fin (N + (2 * h + 1)) → Bool) → Bool)
    (hF : ∀ x : Fin (N + (2 * h + 1)) → Bool, ∃ (p : Prop) (d : Decidable p),
      F x = (g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) || @decide p d) ∧
      (p ↔ ∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧
        ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨
        (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨
        ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) :
    HasCircuitSize (N + (2 * h + 1)) F (3 * h + s + 3) := by
  have hb : HasCircuitSize (N + (2 * h + 1))
      (fun x : Fin (N + (2 * h + 1)) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i))) s :=
    relabel_size (Fin.castAdd (2 * h + 1)) g s hs
  have hc := bigOr _ (tA N h u.val v.val) s hb (h + 1) (fun k hk => tA_size N h u v k hk)
  refine congrSize (weaken hc (by omega)) (fun x => ?_)
  obtain ⟨p, d, hFx, hp⟩ := hF x
  rw [hFx]
  show (g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) || @decide p d) =
    (g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) || orUpTo (tA N h u.val v.val) (h + 1) x)
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_eq, orUpTo_true]
  refine hp.trans ((pathE_iff N (2 * h + 1) u v x).trans
    ((combA (fun q => inp (N + (2 * h + 1)) q x = true) N h u.val v.val).trans ?_))
  refine exists_congr (fun k => and_congr_right (fun _ => ?_))
  exact (term_true _ _ _ _ x).symm

theorem partB (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool) (s : ℕ)
    (hs : HasCircuitSize (N + 2) (fun x : Fin (N + 2) → Bool =>
      g (fun i : Fin N => x (Fin.castAdd 2 i)) ||
        (x (Fin.castAdd 2 u) && x (Fin.natAdd N (0 : Fin 2))) ||
        (x (Fin.castAdd 2 v) && x (Fin.natAdd N (1 : Fin 2)))) s)
    (F : (Fin (N + (2 * h + 1)) → Bool) → Bool)
    (hF : ∀ x : Fin (N + (2 * h + 1)) → Bool, ∃ (p : Prop) (d : Decidable p),
      F x = (g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) || @decide p d) ∧
      (p ↔ ∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧
        ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨
        (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨
        ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) :
    HasCircuitSize (N + (2 * h + 1)) F (3 * h + s) := by
  have hb := relabel_size (pmap N h) _ s hs
  have hc := bigOr _ (tB N h) s hb h (fun k hk => tB_size N h k hk)
  refine congrSize (weaken hc (by omega)) (fun x => ?_)
  obtain ⟨p, d, hFx, hp⟩ := hF x
  rw [hFx]
  have hG : g (fun i : Fin N => (x ∘ pmap N h) (Fin.castAdd 2 i)) =
      g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) := by
    congr 1
    funext i
    show x (pmap N h (Fin.castAdd 2 i)) = x (Fin.castAdd (2 * h + 1) i)
    rw [x_pmap N h x, pos_cast, inp_castAdd N (2 * h + 1) x]
  have hU : (x ∘ pmap N h) (Fin.castAdd 2 u) = inp (N + (2 * h + 1)) u.val x := by
    show x (pmap N h (Fin.castAdd 2 u)) = _
    rw [x_pmap N h x, pos_cast]
  have hV : (x ∘ pmap N h) (Fin.castAdd 2 v) = inp (N + (2 * h + 1)) v.val x := by
    show x (pmap N h (Fin.castAdd 2 v)) = _
    rw [x_pmap N h x, pos_cast]
  have hA : (x ∘ pmap N h) (Fin.natAdd N (0 : Fin 2)) = inp (N + (2 * h + 1)) N x := by
    show x (pmap N h (Fin.natAdd N (0 : Fin 2))) = _
    rw [x_pmap N h x, pos_zero]
  have hB : (x ∘ pmap N h) (Fin.natAdd N (1 : Fin 2)) = inp (N + (2 * h + 1)) (N + 2 * h) x := by
    show x (pmap N h (Fin.natAdd N (1 : Fin 2))) = _
    rw [x_pmap N h x, pos_one]
  show (g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) || @decide p d) =
    (((g (fun i : Fin N => (x ∘ pmap N h) (Fin.castAdd 2 i)) ||
        ((x ∘ pmap N h) (Fin.castAdd 2 u) && (x ∘ pmap N h) (Fin.natAdd N (0 : Fin 2)))) ||
        ((x ∘ pmap N h) (Fin.castAdd 2 v) && (x ∘ pmap N h) (Fin.natAdd N (1 : Fin 2)))) ||
      orUpTo (tB N h) h x)
  rw [hG, hU, hV, hA, hB, Bool.or_assoc, Bool.or_assoc]
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_eq, Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, orUpTo_true]
  refine hp.trans ((pathE_iff N (2 * h + 1) u v x).trans
    ((combB (fun q => inp (N + (2 * h + 1)) q x = true) N h u.val v.val).trans ?_))
  refine or_assoc.trans (or_congr Iff.rfl (or_congr Iff.rfl ?_))
  refine exists_congr (fun k => and_congr_right (fun _ => ?_))
  exact (term_true _ _ _ _ x).symm

end LMeta572

theorem PEqualNP.Outside.L_meta_572 : ∀ (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool), u ≠ v → 3 ≤ h → g (fun _ : Fin N => false) = false → (∃ x : Fin N → Bool, x u = true ∧ g x = false) → (∃ x : Fin N → Bool, x v = true ∧ g x = false) → ∀ s : ℕ, (PEqualNP.MetaComplexity.HasCircuitSize N g s → PEqualNP.MetaComplexity.HasCircuitSize (N + (2 * h + 1)) (fun x : Fin (N + 2 * h + 1) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) || decide (∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨ (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨ ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s + 3)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize (N + 2) (fun x : Fin (N + 2) → Bool => g (fun i : Fin N => x (Fin.castAdd 2 i)) || (x (Fin.castAdd 2 u) && x (Fin.natAdd N (0 : Fin 2))) || (x (Fin.castAdd 2 v) && x (Fin.natAdd N (1 : Fin 2)))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + (2 * h + 1)) (fun x : Fin (N + 2 * h + 1) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) || decide (∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨ (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨ ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) := by
  intro N h u v g _ _ _ _ _ s
  constructor
  · intro hs
    exact LMeta572.partA N h u v g s hs _ (fun x => ⟨_, _, rfl, Iff.rfl⟩)
  · intro hs
    exact LMeta572.partB N h u v g s hs _ (fun x => ⟨_, _, rfl, Iff.rfl⟩)
