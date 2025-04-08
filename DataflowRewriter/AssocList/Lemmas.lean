import DataflowRewriter.AssocList.Basic
import Mathlib.Logic.Function.Basic

namespace Batteries.AssocList

theorem append_eq {α β} {a b : AssocList α β} :
  (a.append b).toList = a.toList ++ b.toList := by
  induction a generalizing b <;> simp [*, append]

theorem append_eq2 {α β} {a b : AssocList α β} :
  a.append b = (a.toList ++ b.toList).toAssocList := by
  induction a generalizing b <;> simp [*, append]

theorem append_find? {α β} [DecidableEq α] (a b : AssocList α β) (i) :
  (a.append b).find? i = a.find? i
  ∨ (a.append b).find? i = b.find? i := by
  induction a with
  | nil => simp [append]
  | cons k v t ih =>
    by_cases h : k = i
    <;> simp_all [append, List.find?_cons_of_pos, List.find?_cons_of_neg]

theorem append_find?2 {α β} [DecidableEq α] {a b : AssocList α β} {i x} :
  (a.append b).find? i = some x →
  a.find? i = some x ∨ (a.find? i = none ∧ b.find? i = some x) := by
  induction a with
  | nil => simp [append]
  | cons k v t ih =>
    by_cases h : k = i
    <;> simp_all [append, List.find?_cons_of_pos, List.find?_cons_of_neg]

theorem find?_mapVal {α β γ} [DecidableEq α] {a : AssocList α β} {f : α → β → γ} {i}:
  (a.mapVal f).find? i = (a.find? i).map (f i) := by
  induction a with
  | nil => simp
  | cons k v a ih => dsimp [find?]; split <;> simp_all

theorem disjoint_cons_left {α β γ} [DecidableEq α] {t : AssocList α β} {b : AssocList α γ} {a y} :
  (cons a y t).disjoint_keys b = true → t.disjoint_keys b = true := by
  unfold disjoint_keys; intros; simp [*]
  simp [List.inter.eq_1] at *
  rename_i h
  intro el hin; apply h
  simp_all [keysList]

theorem disjoint_keys_symm {α β γ} [DecidableEq α] {a : AssocList α β} {b : AssocList α γ} :
  a.disjoint_keys b → b.disjoint_keys a := by
  unfold disjoint_keys
  simp; intro H
  simp [List.inter.eq_1] at *
  unfold Not at *; intros
  solve_by_elim

theorem append_find_left {α β} [DecidableEq α] {a b : AssocList α β} {i x} :
  a.find? i = some x →
  (a.append b).find? i = some x := by
  induction a with
  | nil => simp
  | cons a y t ih =>
    intro hfind
    simp only [append]
    rw [Batteries.AssocList.find?.eq_2] at hfind ⊢
    split <;> rename_i _ heq
    · simp_all
    · simp only [heq] at hfind; solve_by_elim

theorem append_find_right {α β} [DecidableEq α] (a b : AssocList α β) {i} :
  a.find? i = none →
  (a.append b).find? i = b.find? i := by
  induction a with
  | nil => simp [append]
  | cons a y t ih =>
    intro hfind
    simp only [append]
    rw [Batteries.AssocList.find?.eq_2] at hfind ⊢
    split <;> rename_i _ heq
    · simp_all
    · simp only [heq] at hfind; solve_by_elim

private theorem map_keys_list' {α β γ} [DecidableEq α] {f : α → β → γ} {l : List (α × β)} {ident val} :
  List.find? (fun x => x.fst == ident) l = some val →
  List.find? ((fun x => x.fst == ident) ∘ fun x => (x.fst, f x.fst x.snd)) l = some (ident, val.snd) := by
  induction l generalizing ident val <;> simp_all
  rename_i head tail iH
  intro Hfirst
  rcases Hfirst with ⟨ h1, h2 ⟩ | ⟨ h1, h2 ⟩
  subst_vars; left; simp
  right; and_intros; assumption
  apply iH
  assumption

theorem map_keys_list {α β γ} [DecidableEq α] {ident} {l : AssocList α β} {f : α → β → γ} :
    (l.mapVal f).find? ident = (l.find? ident).map (f ident) := by
  simp [find?_eq]
  cases h : List.find? (fun x => x.fst == ident) l.toList <;> simp_all
  · assumption
  · rename_i val
    refine ⟨ ident, val.snd, ?_ ⟩
    and_intros <;> try rfl
    apply map_keys_list'; assumption

theorem mapKey_toList {α β} {l : AssocList α β} {f : α → α} :
  l.mapKey f = (l.toList.map (λ | (a, b) => (f a, b))).toAssocList := by
  induction l <;> simp [*]

theorem mapKey_toList2 {α β} {l : AssocList α β} {f : α → α} :
  (l.mapKey f).toList = (l.toList.map (λ | (a, b) => (f a, b))) := by
  induction l <;> simp [*]

theorem contains_none {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    ¬ m.contains ident →
    m.find? ident = none := by
  intros H; rw [Batteries.AssocList.contains_eq] at H
  rw [Batteries.AssocList.find?_eq]
  rw [Option.map_eq_none', List.find?_eq_none]; intros x H
  rcases x with ⟨ a, b⟩
  simp at *; unfold Not; intros; apply H
  subst_vars; assumption

theorem contains_some {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    m.contains ident →
    (m.find? ident).isSome := by
  intros H; rw [Batteries.AssocList.contains_eq] at H; simp at H; rcases H with ⟨ a, H ⟩
  simp [*]; constructor; assumption

theorem contains_some2 {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    (m.find? ident).isSome →
    m.contains ident := by
  intro; by_cases contains ident m = true; assumption
  rename_i a b; have := contains_none b
  rw [this] at a; contradiction

theorem contains_some3 {α β} [DecidableEq α] {m : AssocList α β} {ident x} :
    m.find? ident = some x →
    m.contains ident := by
  intro h; apply contains_some2; rw [h]; rfl

theorem contains_find?_iff {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    (∃ x, m.find? ident = some x) ↔ m.contains ident := by
  constructor
  · intro h; cases h; solve_by_elim [contains_some3]
  · intro h; rw [← Option.isSome_iff_exists]; solve_by_elim [contains_some]

theorem contains_find?_isSome_iff {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    (m.find? ident).isSome ↔ m.contains ident := by
  rw [Option.isSome_iff_exists]; apply contains_find?_iff

theorem keysList_find {α β} [DecidableEq α] {m : AssocList α β} {ident} :
  (m.find? ident).isSome → ident ∈ m.keysList := by simp_all [keysList]

theorem keysList_find2 {α β} [DecidableEq α] {m : AssocList α β} {ident} :
  ident ∈ m.keysList → (m.find? ident).isSome := by simp_all [keysList]

theorem notkeysList_find2 {α β} [DecidableEq α] {m : AssocList α β} {ident} :
  ident ∉ m.keysList → m.find? ident = none := by
  have : ¬ (m.find? ident).isSome → m.find? ident = none := by
    intro h; simp at h; simp
    skip; intros; unfold Not; intros; apply h; subst_vars; assumption
  intro; apply this; unfold Not; intros; simp_all [keysList]

theorem append_find_right_disjoint {α β} [DecidableEq α] {a b : AssocList α β} {i x} :
  a.disjoint_keys b →
  b.find? i = some x →
  (a.append b).find? i = some x := by
  induction a with
  | nil => simp [append]
  | cons a y t ih =>
    intro hdisj hfind
    simp only [append]
    rw [Batteries.AssocList.find?.eq_2]
    split <;> rename_i _ heq
    · exfalso; clear ih;
      simp_all only [disjoint_keys]
      simp [Inter.inter, List.instInterOfBEq_batteries, List.inter.eq_1] at hdisj
      apply hdisj; constructor; simp at heq; subst_vars
      apply keysList_find; rw [Option.isSome_iff_exists]
      solve_by_elim
    · solve_by_elim [disjoint_cons_left]

-- @[simp] theorem erase_map_comm {α β γ} [DecidableEq α] {a : AssocList α β} ident (f : α → β → γ) :
--   (a.erase ident).mapVal f = (a.mapVal f).erase ident := by sorry

@[simp] axiom eraseAll_map_comm {α β γ} [DecidableEq α] {a : AssocList α β} ident (f : α → β → γ) :
  (a.eraseAll ident).mapVal f = (a.mapVal f).eraseAll ident

@[simp] axiom find?_map_comm {α β γ} [DecidableEq α] {a : AssocList α β} ident (f : β → γ) :
  (a.find? ident).map f = (a.mapVal (λ _ => f)).find? ident

axiom erase_equiv {α β} [DecidableEq α] {a b : AssocList α β} ident ident' :
  a.find? ident = b.find? ident →
  (a.erase ident').find? ident = (b.erase ident').find? ident

@[simp] axiom find?_eraseAll_eq {α β} [DecidableEq α] (a : AssocList α β) i :
  (a.eraseAll i).find? i = none

@[simp] axiom find?_eraseAll_list {α β} { T : α} [DecidableEq α] (a : AssocList α β):
  List.find? (fun x => x.1 == T) (AssocList.eraseAllP (fun k x => decide (k = T)) a).toList = none

@[simp] axiom in_eraseAll_list {α β} {Ta : α} {elem : (α × β)} [DecidableEq α] (a : AssocList α β):
  elem ∈ (AssocList.eraseAllP (fun k x => decide (k = Ta)) a).toList -> elem ∈ a.toList

@[simp] axiom not_in_eraseAll_list {α β} {Ta : α} {elem : (α × β)} [DecidableEq α] (a : AssocList α β):
  elem ∈ (AssocList.eraseAllP (fun k x => decide (k = Ta)) a).toList -> elem.1 = Ta -> False


axiom in_eraseAll_noDup {α β γ δ} {l : List ((α × β) × γ × δ)} (Ta : α) [DecidableEq α](a : AssocList α (β × γ × δ)):
  (List.map Prod.fst ( List.map Prod.fst (l ++ (List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) a.toList)))).Nodup ->
  (List.map Prod.fst ( List.map Prod.fst (l ++ List.map (fun x => ((x.1, x.2.1), x.2.2.1, x.2.2.2)) (AssocList.eraseAllP (fun k x => decide (k = Ta)) a).toList))).Nodup


@[simp] axiom in_eraseAll_map_comm {α β} (Ta : α) [DecidableEq α] (a : AssocList α β):
  (a.toList).Nodup -> ((AssocList.eraseAllP (fun k x => decide (k = Ta)) a).toList).Nodup

@[simp] axiom find?_eraseAll_neg {α β} { T : α} { T' : α} [DecidableEq α] (a : AssocList α β) (i : β):
Batteries.AssocList.find? T (AssocList.eraseAllP (fun k x => decide (k = T')) a) = some i -> ¬ (T = T') -> (Batteries.AssocList.find? T a = some i)

@[simp] axiom find?_eraseAll_neq {α β} [DecidableEq α] (a : AssocList α β) i i' :
  i ≠ i' →
  (a.eraseAll i).find? i' = a.find? i'

theorem find?_eraseAll {α β} [DecidableEq α] {a : AssocList α β} {i i' v} :
  (a.eraseAll i').find? i = some v → a.find? i = some v := by
  intro h; by_cases heq : i = i'
  · subst i'; rw [find?_eraseAll_eq] at h; contradiction
  . rw [find?_eraseAll_neq] at h; assumption; symm; assumption

theorem contains_eraseAll {α β} [DecidableEq α] {a : AssocList α β} {i i'} :
  (a.eraseAll i').contains i → a.contains i := by
  simp only [←contains_find?_iff]; intro ⟨_, _⟩; solve_by_elim [find?_eraseAll]

@[simp] theorem any_map {α β} {f : α → β} {l : List α} {p : β → Bool} : (l.map f).any p = l.any (p ∘ f) := by
  induction l <;> simp

theorem keysInMap {α β} [DecidableEq α] {m : AssocList α β} {k} : m.contains k → k ∈ m.keysList := by
  unfold Batteries.AssocList.contains Batteries.AssocList.keysList
  intro Hk; simp_all

theorem keysNotInMap {α β} [DecidableEq α] {m : AssocList α β} {k} : ¬ m.contains k → k ∉ m.keysList := by
  unfold Batteries.AssocList.contains Batteries.AssocList.keysList
  intro Hk; simp_all

axiom disjoint_keys_mapVal {α β γ μ} [DecidableEq α] {a : AssocList α β} {b : AssocList α γ} {f : α → γ → μ} :
  a.disjoint_keys b → a.disjoint_keys (b.mapVal f)

theorem disjoint_keys_mapVal_both {α β γ μ η} [DecidableEq α] {a : AssocList α β} {b : AssocList α γ} {f : α → γ → μ} {g : α → β → η} :
  a.disjoint_keys b → (a.mapVal g).disjoint_keys (b.mapVal f) := by
  intros; solve_by_elim [disjoint_keys_mapVal, disjoint_keys_symm]

theorem mapKey_find? {α β γ} [DecidableEq α] [DecidableEq γ] {a : AssocList α β} {f : α → γ} {i} (hinj : Function.Injective f) :
  (a.mapKey f).find? (f i) = a.find? i := by
  induction a with
  | nil => simp
  | cons k v xs ih =>
    dsimp
    by_cases h : f k = f i
    · have h' := hinj h; rw [h']; simp
    · have h' := hinj.ne_iff.mp h;
      rw [Batteries.AssocList.find?.eq_2]
      rw [Batteries.AssocList.find?.eq_2]; rw [ih]
      have t1 : (f k == f i) = false := by simp [*]
      have t2 : (k == i) = false := by simp [*]
      rw [t1, t2]

axiom keysList_EqExt {α β} [DecidableEq α] [DecidableEq β] (a b : AssocList α β) :
  a.EqExt b → a.wf → b.wf → a.keysList.Perm b.keysList

/-
These are needed because ExprLow currently only checks equality and uniqueness against the map
-/

axiom filterId_wf {α} [DecidableEq α] (p : AssocList α α) : p.wf → p.filterId.wf

axiom filderId_Nodup {α} [DecidableEq α] (p : AssocList α α) : p.keysList.Nodup → p.filterId.keysList.Nodup

-- theorem filterId_EqExt {α} [DecidableEq α] (p : AssocList α α) := sorry

axiom mapVal_mapKey {α β γ σ} {f : α → γ} {g : β → σ} {m : AssocList α β}:
  (m.mapKey f).mapVal (λ _ => g) = (m.mapVal (λ _ => g)).mapKey f

axiom mapKey_append {α β γ} {f : α → γ} {m n : AssocList α β}:
  (m.mapKey f).append (n.mapKey f) = (m.append n).mapKey f

axiom eraseAll_comm_mapKey {α β γ} [DecidableEq α] [DecidableEq γ] {f : α → γ} {i} {m : AssocList α β} :
  (m.mapKey f).eraseAll (f i) = (m.eraseAll i).mapKey f

theorem bijectivePortRenaming_bijective {α} [DecidableEq α] {p : AssocList α α} :
  Function.Bijective p.bijectivePortRenaming := by
  rw [Function.bijective_iff_existsUnique]
  intro b
  by_cases h : p.filterId.keysList.inter p.inverse.filterId.keysList = ∅ && p.keysList.Nodup && p.inverse.keysList.Nodup
  · cases h' : (p.filterId.append p.inverse.filterId).find? b
    · refine ⟨b, ?_, ?_⟩
      unfold bijectivePortRenaming; simp [*, -AssocList.find?_eq]
      unfold bijectivePortRenaming; simp [*, -AssocList.find?_eq]
      intro y Hy; simp at h; simp [h, -AssocList.find?_eq] at Hy
      cases h'' : AssocList.find? y (p.filterId.append p.inverse.filterId)
      · rw [h''] at Hy; dsimp at Hy; assumption
      · rw [h''] at Hy; dsimp at Hy; subst b
        have := invertibleMap (by unfold invertible; simp [*]) h''
        rw [this] at h'; injection h'
    · rename_i val
      refine ⟨val, ?_, ?_⟩
      · unfold bijectivePortRenaming; simp [*, -AssocList.find?_eq];
        simp at h; simp [h, -AssocList.find?_eq]
        rw [invertibleMap]; rfl; simp [invertible, *]; assumption
      · unfold bijectivePortRenaming; simp [*, -AssocList.find?_eq]; intros y hY
        simp at h; simp [h, -AssocList.find?_eq] at hY
        cases h'' : AssocList.find? y (p.filterId.append p.inverse.filterId)
        · rw [h''] at hY; dsimp at hY; subst y; rw [h''] at h'; injection h'
        · rename_i val'; rw [h''] at hY; dsimp at *; subst b
          have := invertibleMap (by simp [invertible, *]) h''; rw [this] at h'; injection h'
  · refine ⟨b, ?_, ?_⟩
    unfold bijectivePortRenaming; simp [*]; intro a b c; exfalso; apply h; simp [*]
    unfold bijectivePortRenaming; simp [*]; split; exfalso; apply h; simp [*]
    simp

theorem bijectivePortRenaming_id {α} [DecidableEq α] : @bijectivePortRenaming α _ ∅ = id := by rfl

@[simp]
theorem find?_gss : ∀ {α} [DecidableEq α] {β x v} {pm: AssocList α β},
  (AssocList.find? x (AssocList.cons x v pm)) = .some v := by simpa

@[simp]
theorem find?_gso : ∀ {α} [DecidableEq α] {β x' x v} {pm: AssocList α β},
  x ≠ x' → AssocList.find? x' (AssocList.cons x v pm) = AssocList.find? x' pm := by simp_all

@[simp] theorem find?_ge : ∀ {α} [DecidableEq α] {β x},
  AssocList.find? x (.nil : AssocList α β) = .none := by simpa

end Batteries.AssocList
