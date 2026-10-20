(** AVL maps from integers to integers, as immutable HeapLang values, with
    a Gallina model [AVL].  [AVL.to_list] is the in-order association list,
    determined by [AVL.to_map] alone, so programs that publish it do not
    reveal the shape of the tree. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import sorting gmap.
From iris.heap_lang Require Import lang notation proofmode.
From cryptis Require Import lib.

Module AVL.

#[local] Open Scope Z_scope.

Inductive tree := Leaf | Node (l : tree) (k v h : Z) (r : tree).

Definition height t : Z := match t with Leaf => 0 | Node _ _ _ h _ => h end.

Definition zmax a b : Z := if bool_decide (a < b) then b else a.

Lemma zmax_eq a b : zmax a b = Z.max a b.
Proof. rewrite /zmax; case: bool_decide_reflect; lia. Qed.

Definition node l k v r := Node l k v (1 + zmax (height l) (height r)) r.

Definition bal l k v r :=
  if bool_decide (height r + 1 < height l) then
    match l with
    | Node ll lk lv _ lr =>
      if bool_decide (height lr ≤ height ll) then node ll lk lv (node lr k v r)
      else match lr with
           | Node lrl lrk lrv _ lrr =>
             node (node ll lk lv lrl) lrk lrv (node lrr k v r)
           | Leaf => node l k v r
           end
    | Leaf => node l k v r
    end
  else if bool_decide (height l + 1 < height r) then
    match r with
    | Node rl rk rv _ rr =>
      if bool_decide (height rl ≤ height rr) then node (node l k v rl) rk rv rr
      else match rl with
           | Node rll rlk rlv _ rlr =>
             node (node l k v rll) rlk rlv (node rlr rk rv rr)
           | Leaf => node l k v r
           end
    | Leaf => node l k v r
    end
  else node l k v r.

Fixpoint insert k v t :=
  match t with
  | Leaf => Node Leaf k v 1 Leaf
  | Node l k' v' h r =>
    if bool_decide (k < k') then bal (insert k v l) k' v' r
    else if bool_decide (k' < k) then bal l k' v' (insert k v r)
    else Node l k v h r
  end.

Fixpoint lookup k t :=
  match t with
  | Leaf => None
  | Node l k' v' _ r =>
    if bool_decide (k < k') then lookup k l
    else if bool_decide (k' < k) then lookup k r
    else Some v'
  end.

Fixpoint to_list_acc t acc :=
  match t with
  | Leaf => acc
  | Node l k v _ r => to_list_acc l ((k, v) :: to_list_acc r acc)
  end.

Definition to_list t := to_list_acc t [].

Definition key_lt (p q : Z * Z) := p.1 < q.1.
Arguments key_lt _ _ /.

Definition bst t := StronglySorted key_lt (to_list t).

Definition to_map t : gmap Z Z := list_to_map (to_list t).

Fixpoint balanced t :=
  match t with
  | Leaf => True
  | Node l _ _ h r =>
    balanced l ∧ balanced r ∧
    h = 1 + Z.max (height l) (height r) ∧
    -1 ≤ height l - height r ≤ 1
  end.

(** * In-order lists *)

Lemma to_list_acc_app t acc : to_list_acc t acc = to_list t ++ acc.
Proof.
elim: t acc => [|l IHl k v h r IHr] acc //=.
by rewrite /to_list /= !IHl !IHr app_nil_r -app_assoc.
Qed.

Lemma to_list_node l k v h r :
  to_list (Node l k v h r) = to_list l ++ (k, v) :: to_list r.
Proof. by rewrite {1}/to_list /= to_list_acc_app. Qed.

Lemma to_list_acc_bal l k v r acc :
  to_list_acc (bal l k v r) acc = to_list_acc l ((k, v) :: to_list_acc r acc).
Proof.
rewrite /bal; case: bool_decide_reflect => _.
{ case: l => [|ll lk lv lh lr] //=.
  case: bool_decide_reflect => _ //=.
  by case: lr => [|lrl lrk lrv lrh lrr] /=. }
case: bool_decide_reflect => _ //=.
case: r => [|rl rk rv rh rr] //=.
case: bool_decide_reflect => _ //=.
by case: rl => [|rll rlk rlv rlh rlr] /=.
Qed.

Lemma to_list_bal l k v r :
  to_list (bal l k v r) = to_list l ++ (k, v) :: to_list r.
Proof. by rewrite /to_list to_list_acc_bal to_list_acc_app. Qed.

Lemma bst_node l k v h r :
  bst (Node l k v h r) ↔
  bst l ∧ bst r ∧
  Forall (λ p, p.1 < k) (to_list l) ∧ Forall (λ p, k < p.1) (to_list r).
Proof.
rewrite /bst to_list_node StronglySorted_app StronglySorted_cons.
split.
- move=> [Hlr [Hl [/Forall_forall Hr' Hr]]].
  split; first done. split; first done. split; apply/Forall_forall.
  + move=> p Hp. apply: (Hlr p (k, v) Hp). apply/elem_of_cons. by left.
  + by move=> q /Hr'.
- move=> [Hl [Hr [/Forall_forall Hlk /Forall_forall Hkr]]].
  split; last (split; last split) => //.
  + move=> p q /Hlk /= Hp /elem_of_cons [->|/Hkr /= Hq]; rewrite /key_lt /=; lia.
  + by apply/Forall_forall => q /Hkr.
Qed.

Lemma keys_lt_notin k (l : list (Z * Z)) :
  Forall (λ p, p.1 < k) l → k ∉ l.*1.
Proof. move/Forall_forall => H /list_elem_of_fmap [[k' v'] [/= e /H /=]]. lia. Qed.

Lemma keys_gt_notin k (l : list (Z * Z)) :
  Forall (λ p, k < p.1) l → k ∉ l.*1.
Proof. move/Forall_forall => H /list_elem_of_fmap [[k' v'] [/= e /H /=]]. lia. Qed.

(** * Lookup *)

Lemma lookup_to_map k t : bst t → lookup k t = to_map t !! k.
Proof.
elim: t => [|l IHl k' v' h r IHr] //= /bst_node [Hl [Hr [Hlk Hkr]]].
rewrite /to_map to_list_node list_to_map_app list_to_map_cons.
have Hnl : (list_to_map (to_list l) : gmap Z Z) !! k' = None.
{ apply: not_elem_of_list_to_map_1. exact: keys_lt_notin. }
case: bool_decide_reflect => [Hkk'|Hkk'].
- have Hnone : (<[k':=v']> (list_to_map (to_list r)) : gmap Z Z) !! k = None.
  { rewrite lookup_insert_ne; last lia.
    apply: not_elem_of_list_to_map_1. apply: keys_gt_notin.
    apply: (Forall_impl _ _ _ Hkr) => p /= ?. lia. }
  by rewrite IHl // (lookup_union_l _ _ _ Hnone).
- case: bool_decide_reflect => [Hk'k|Hk'k].
  + have Hnone : (list_to_map (to_list l) : gmap Z Z) !! k = None.
    { apply: not_elem_of_list_to_map_1. apply: keys_lt_notin.
      apply: (Forall_impl _ _ _ Hlk) => p /= ?. lia. }
    rewrite IHr // (lookup_union_r _ _ _ Hnone) lookup_insert_ne //. lia.
  + have -> : k = k' by lia.
    by rewrite (lookup_union_r _ _ _ Hnl) lookup_insert_eq.
Qed.

(** * Insertion *)

Fixpoint ins k v (l : list (Z * Z)) :=
  match l with
  | [] => [(k, v)]
  | (k', v') :: l =>
    if bool_decide (k < k') then (k, v) :: (k', v') :: l
    else if bool_decide (k' < k) then (k', v') :: ins k v l
    else (k, v) :: l
  end.

Lemma ins_app_l k v l1 l2 :
  Forall (λ p, k < p.1) l2 → ins k v (l1 ++ l2) = ins k v l1 ++ l2.
Proof.
elim: l1 => [|[k' v'] l1 IH] /= Hl2.
- case: l2 Hl2 => //= - [k2 v2] l2 /Forall_cons [/= Hk _].
  by rewrite bool_decide_eq_true_2.
- by do 2![case: bool_decide_reflect => //= _]; rewrite IH.
Qed.

Lemma ins_app_r k v l1 l2 :
  Forall (λ p, p.1 < k) l1 → ins k v (l1 ++ l2) = l1 ++ ins k v l2.
Proof.
elim: l1 => [|[k' v'] l1 IH] //= /Forall_cons [/= Hk' Hl1].
rewrite bool_decide_eq_false_2; last lia.
rewrite bool_decide_eq_true_2; last lia.
by rewrite IH.
Qed.

Lemma list_to_map_ins k v l :
  (list_to_map (ins k v l) : gmap Z Z) = <[k:=v]> (list_to_map l).
Proof.
elim: l => [|[k' v'] l IH] //=.
case: bool_decide_reflect => [Hkk'|Hkk'] //.
case: bool_decide_reflect => [Hk'k|Hk'k].
- rewrite !list_to_map_cons IH (insert_insert _ k' k).
  by rewrite decide_False; last lia.
- have -> : k' = k by lia.
  by rewrite !list_to_map_cons (insert_insert _ k k) decide_True.
Qed.

Lemma ins_elem k v l p : p ∈ ins k v l → p.1 = k ∨ p ∈ l.
Proof.
elim: l => [|[k' v'] l IH] /=.
{ rewrite list_elem_of_singleton => ->. by left. }
case: bool_decide_reflect => _.
{ rewrite !elem_of_cons => - [->|?]; [by left | by right]. }
case: bool_decide_reflect => _; rewrite !elem_of_cons.
- move=> [->|/IH [?|?]]; [by right; left | by left | by right; right].
- move=> [->|?]; [by left | by right; right].
Qed.

Lemma StronglySorted_ins k v l :
  StronglySorted key_lt l → StronglySorted key_lt (ins k v l).
Proof.
elim: l => [|[k' v'] l IH] /= Hs; first by repeat constructor.
move: (Hs) => /StronglySorted_cons [/Forall_forall Hk' Hl].
case: bool_decide_reflect => [Hkk'|Hkk'].
- apply/StronglySorted_cons; split; last done.
  apply/Forall_forall => p /elem_of_cons [->|/Hk' /= ?] /=; lia.
- case: bool_decide_reflect => [Hk'k|Hk'k].
  + apply/StronglySorted_cons; split; last exact: IH.
    apply/Forall_forall => p /ins_elem [/= e | /Hk' /= ?] /=; lia.
  + apply/StronglySorted_cons; split; last done.
    apply/Forall_forall => p /Hk' /= ?. rewrite /=. lia.
Qed.

Lemma to_list_insert k v t :
  bst t → to_list (insert k v t) = ins k v (to_list t).
Proof.
elim: t => [|l IHl k' v' h r IHr] //= /bst_node [Hl [Hr [Hlk Hkr]]].
rewrite to_list_node.
case: bool_decide_reflect => [Hkk'|Hkk'].
- rewrite to_list_bal IHl // ins_app_l //.
  apply/Forall_cons; split; first done.
  apply: (Forall_impl _ _ _ Hkr) => p /= ?. lia.
- have Hlk' : Forall (λ p : Z * Z, p.1 < k) (to_list l).
  { apply: (Forall_impl _ _ _ Hlk) => p /= ?. lia. }
  case: bool_decide_reflect => [Hk'k|Hk'k].
  + rewrite to_list_bal IHr // ins_app_r //=.
    rewrite bool_decide_eq_false_2; last lia.
    by rewrite bool_decide_eq_true_2.
  + have -> : k' = k by lia.
    rewrite to_list_node ins_app_r //=.
    by rewrite bool_decide_eq_false_2; last lia.
Qed.

Lemma bst_leaf : bst Leaf.
Proof. constructor. Qed.

Lemma bst_insert k v t : bst t → bst (insert k v t).
Proof. move=> Hb. rewrite /bst to_list_insert //. exact: StronglySorted_ins. Qed.

Lemma to_map_leaf : to_map Leaf = ∅.
Proof. by []. Qed.

Lemma to_map_insert k v t :
  bst t → to_map (insert k v t) = <[k:=v]> (to_map t).
Proof. move=> Hb. by rewrite /to_map to_list_insert // list_to_map_ins. Qed.

(** * The in-order list is a function of the map *)

#[local] Instance key_lt_antisymm : AntiSymm (=@{Z * Z}) key_lt.
Proof. move=> [k v] [k' v'] /=. lia. Qed.

Lemma StronglySorted_key_lt_NoDup (l : list (Z * Z)) :
  StronglySorted key_lt l → NoDup l.*1.
Proof.
elim: l => [|[k v] l IH] /= Hs; first by constructor.
move/StronglySorted_cons: Hs => [/Forall_forall Hk Hl].
apply/NoDup_cons; split; last exact: IH.
move=> /list_elem_of_fmap [[k' v'] [/= e /Hk /=]]. lia.
Qed.

Lemma sorted_assoc_unique (l1 l2 : list (Z * Z)) :
  StronglySorted key_lt l1 → StronglySorted key_lt l2 →
  (list_to_map l1 : gmap Z Z) = list_to_map l2 → l1 = l2.
Proof.
move=> Hs1 Hs2 Hm. apply: StronglySorted_unique => //.
have Hn1 := StronglySorted_key_lt_NoDup _ Hs1.
have Hn2 := StronglySorted_key_lt_NoDup _ Hs2.
apply: NoDup_Permutation; try by apply: NoDup_fmap_1.
move=> [k v].
by rewrite (elem_of_list_to_map (M:=gmap Z) _ _ _ Hn1)
           (elem_of_list_to_map (M:=gmap Z) _ _ _ Hn2) Hm.
Qed.

Lemma to_list_to_map t1 t2 :
  bst t1 → bst t2 → to_map t1 = to_map t2 → to_list t1 = to_list t2.
Proof. exact: sorted_assoc_unique. Qed.

(** * Balance *)

Lemma height_node l k v r :
  height (node l k v r) = 1 + Z.max (height l) (height r).
Proof. by rewrite /node /= zmax_eq. Qed.

Lemma balanced_height t : balanced t → 0 ≤ height t.
Proof. elim: t => [|l IHl k v h r IHr] //= [/IHl ? [/IHr ? [-> _]]]. lia. Qed.

Lemma balanced_node l k v r :
  balanced l → balanced r → -1 ≤ height l - height r ≤ 1 →
  balanced (node l k v r).
Proof. move=> ???. rewrite /node /= zmax_eq. do !split; try done; lia. Qed.

Ltac balanced_tac := do !split; try done; lia.

Lemma bal_spec l k v r :
  balanced l → balanced r → -2 ≤ height l - height r ≤ 2 →
  balanced (bal l k v r) ∧
  ((-1 ≤ height l - height r ≤ 1 ∧
    height (bal l k v r) = 1 + Z.max (height l) (height r)) ∨
   ((height l - height r = 2 ∨ height l - height r = -2) ∧
    Z.max (height l) (height r) ≤ height (bal l k v r) ≤
    1 + Z.max (height l) (height r))).
Proof.
move=> Hl Hr Hd.
have Hhl := balanced_height _ Hl. have Hhr := balanced_height _ Hr.
rewrite /bal. case: bool_decide_reflect => H1.
{ case: l Hl Hhl Hd H1 => [|ll lk lv lh lr] /= Hl Hhl Hd H1; first lia.
  move: Hl => [Hll [Hlr [E Hb]]].
  have Hhll := balanced_height _ Hll. have Hhlr := balanced_height _ Hlr.
  case: bool_decide_reflect => H2.
  - rewrite /node /= !zmax_eq. split; [balanced_tac | right].
    split; lia.
  - case: lr Hlr Hhlr Hb Hd H1 H2 E => [|lrl lrk lrv lrh lrr] /= Hlr Hhlr Hb Hd H1 H2 E;
      first lia.
    move: Hlr => [Hlrl [Hlrr [E' Hb']]].
    have Hhlrl := balanced_height _ Hlrl. have Hhlrr := balanced_height _ Hlrr.
    rewrite /node /= !zmax_eq. split; [balanced_tac | right].
    split; lia. }
case: bool_decide_reflect => H2; last first.
{ rewrite height_node. split; last by left; split; lia.
  apply: balanced_node => //. lia. }
case: r Hr Hhr Hd H1 H2 => [|rl rk rv rh rr] /= Hr Hhr Hd H1 H2; first lia.
move: Hr => [Hrl [Hrr [E Hb]]].
have Hhrl := balanced_height _ Hrl. have Hhrr := balanced_height _ Hrr.
case: bool_decide_reflect => H3.
- rewrite /node /= !zmax_eq. split; [balanced_tac | right].
  split; lia.
- case: rl Hrl Hhrl Hb Hd H1 H2 H3 E => [|rll rlk rlv rlh rlr] /= Hrl Hhrl Hb Hd H1 H2 H3 E;
    first lia.
  move: Hrl => [Hrll [Hrlr [E' Hb']]].
  have Hhrll := balanced_height _ Hrll. have Hhrlr := balanced_height _ Hrlr.
  rewrite /node /= !zmax_eq. split; [balanced_tac | right].
  split; lia.
Qed.

Lemma balanced_leaf : balanced Leaf.
Proof. by []. Qed.

Lemma insert_spec k v t :
  balanced t →
  balanced (insert k v t) ∧
  height t ≤ height (insert k v t) ≤ height t + 1.
Proof.
elim: t => [|l IHl k' v' h r IHr] /=; first by move=> _; split; [|lia].
move=> [Hl [Hr [-> Hb]]].
have Hhl := balanced_height _ Hl. have Hhr := balanced_height _ Hr.
case: bool_decide_reflect => _.
{ move: IHl => /(_ Hl) [Hl' Hh'].
  have [Hbal Hcase] := bal_spec _ k' v' _ Hl' Hr ltac:(lia).
  split; first done. case: Hcase => [[? ->]|[? [? ?]]]; lia. }
case: bool_decide_reflect => _; last by rewrite /=; split; [balanced_tac | lia].
move: IHr => /(_ Hr) [Hr' Hh'].
have [Hbal Hcase] := bal_spec _ k' v' _ Hl Hr' ltac:(lia).
split; first done. case: Hcase => [[? ->]|[? [? ?]]]; lia.
Qed.

End AVL.

(** * HeapLang implementation *)

Fixpoint repr_tree (t : AVL.tree) : val :=
  match t with
  | AVL.Leaf => NONEV
  | AVL.Node l k v h r => SOMEV (repr_tree l, #k, #v, #h, repr_tree r)
  end.

#[global] Instance repr_tree_inst : Repr AVL.tree := repr_tree.
Arguments repr_tree_inst !_ /.

Lemma tree_pure (t : AVL.tree) : pure_val (repr t).
Proof. elim: t => [|l IHl k v h r IHr] //=. rewrite !andb_True. by repeat split. Qed.

Definition avl_empty : val := NONEV.

Definition avl_height : val := λ: "t",
  match: "t" with NONE => #0 | SOME "n" => Snd (Fst "n") end.

Definition avl_node : val := λ: "l" "k" "v" "r",
  let: "hl" := avl_height "l" in
  let: "hr" := avl_height "r" in
  let: "h" := if: "hl" < "hr" then "hr" else "hl" in
  SOME ("l", "k", "v", #1 + "h", "r").

Definition avl_bal : val := λ: "l" "k" "v" "r",
  let: "hl" := avl_height "l" in
  let: "hr" := avl_height "r" in
  if: "hr" + #1 < "hl" then
    match: "l" with
      NONE => avl_node "l" "k" "v" "r"
    | SOME "n" =>
      let: "ll" := Fst (Fst (Fst (Fst "n"))) in
      let: "lk" := Snd (Fst (Fst (Fst "n"))) in
      let: "lv" := Snd (Fst (Fst "n")) in
      let: "lr" := Snd "n" in
      if: avl_height "lr" ≤ avl_height "ll" then
        avl_node "ll" "lk" "lv" (avl_node "lr" "k" "v" "r")
      else
        match: "lr" with
          NONE => avl_node "l" "k" "v" "r"
        | SOME "m" =>
          let: "lrl" := Fst (Fst (Fst (Fst "m"))) in
          let: "lrk" := Snd (Fst (Fst (Fst "m"))) in
          let: "lrv" := Snd (Fst (Fst "m")) in
          let: "lrr" := Snd "m" in
          avl_node (avl_node "ll" "lk" "lv" "lrl") "lrk" "lrv"
                   (avl_node "lrr" "k" "v" "r")
        end
    end
  else if: "hl" + #1 < "hr" then
    match: "r" with
      NONE => avl_node "l" "k" "v" "r"
    | SOME "n" =>
      let: "rl" := Fst (Fst (Fst (Fst "n"))) in
      let: "rk" := Snd (Fst (Fst (Fst "n"))) in
      let: "rv" := Snd (Fst (Fst "n")) in
      let: "rr" := Snd "n" in
      if: avl_height "rl" ≤ avl_height "rr" then
        avl_node (avl_node "l" "k" "v" "rl") "rk" "rv" "rr"
      else
        match: "rl" with
          NONE => avl_node "l" "k" "v" "r"
        | SOME "m" =>
          let: "rll" := Fst (Fst (Fst (Fst "m"))) in
          let: "rlk" := Snd (Fst (Fst (Fst "m"))) in
          let: "rlv" := Snd (Fst (Fst "m")) in
          let: "rlr" := Snd "m" in
          avl_node (avl_node "l" "k" "v" "rll") "rlk" "rlv"
                   (avl_node "rlr" "rk" "rv" "rr")
        end
    end
  else avl_node "l" "k" "v" "r".

Definition avl_insert : val := rec: "loop" "k" "v" "t" :=
  match: "t" with
    NONE => SOME (NONE, "k", "v", #1, NONE)
  | SOME "n" =>
    let: "l" := Fst (Fst (Fst (Fst "n"))) in
    let: "k'" := Snd (Fst (Fst (Fst "n"))) in
    let: "v'" := Snd (Fst (Fst "n")) in
    let: "h" := Snd (Fst "n") in
    let: "r" := Snd "n" in
    if: "k" < "k'" then avl_bal ("loop" "k" "v" "l") "k'" "v'" "r"
    else if: "k'" < "k" then avl_bal "l" "k'" "v'" ("loop" "k" "v" "r")
    else SOME ("l", "k", "v", "h", "r")
  end.

Definition avl_lookup : val := rec: "loop" "k" "t" :=
  match: "t" with
    NONE => NONE
  | SOME "n" =>
    let: "l" := Fst (Fst (Fst (Fst "n"))) in
    let: "k'" := Snd (Fst (Fst (Fst "n"))) in
    let: "v'" := Snd (Fst (Fst "n")) in
    let: "r" := Snd "n" in
    if: "k" < "k'" then "loop" "k" "l"
    else if: "k'" < "k" then "loop" "k" "r"
    else SOME "v'"
  end.

Definition avl_to_list_acc : val := rec: "loop" "t" "acc" :=
  match: "t" with
    NONE => "acc"
  | SOME "n" =>
    let: "l" := Fst (Fst (Fst (Fst "n"))) in
    let: "k" := Snd (Fst (Fst (Fst "n"))) in
    let: "v" := Snd (Fst (Fst "n")) in
    let: "r" := Snd "n" in
    "loop" "l" (SOME (("k", "v"), "loop" "r" "acc"))
  end.

Definition avl_to_list : val := λ: "t", avl_to_list_acc "t" NONE.

Section Specs.

Context `{!heapGS Σ}.

Implicit Types (t : AVL.tree) (Ψ : val → iProp Σ).

Lemma twp_avl_height E Ψ t :
  Ψ #(AVL.height t) ⊢ WP avl_height (repr t) @ E [{ Ψ }].
Proof. iIntros "post"; case: t => [|l k v h r] /=; by wp_rec; wp_pures. Qed.

Lemma twp_avl_node E Ψ l k v r :
  Ψ (repr (AVL.node l k v r)) ⊢ WP avl_node (repr l) #k #v (repr r) @ E [{ Ψ }].
Proof.
iIntros "post". wp_rec. wp_pures.
wp_apply twp_avl_height. wp_pures. wp_apply twp_avl_height. wp_pures.
rewrite /AVL.node /AVL.zmax. by case: bool_decide_reflect => _; wp_pures.
Qed.

Lemma twp_avl_bal E Ψ l k v r :
  Ψ (repr (AVL.bal l k v r)) ⊢ WP avl_bal (repr l) #k #v (repr r) @ E [{ Ψ }].
Proof.
iIntros "post". wp_rec. wp_pures.
wp_apply twp_avl_height. wp_pures. wp_apply twp_avl_height. wp_pures.
rewrite /AVL.bal. case: bool_decide_reflect => _; wp_pures.
{ case: l => [|ll lk lv lh lr] /=; wp_pures;
    first by iApply (twp_avl_node _ _ AVL.Leaf).
  wp_apply twp_avl_height. wp_apply twp_avl_height. wp_pures.
  case: bool_decide_reflect => _; wp_pures.
  - wp_apply twp_avl_node.
    by iApply (twp_avl_node _ _ ll lk lv (AVL.node lr k v r)).
  - case: lr => [|lrl lrk lrv lrh lrr] /=; wp_pures;
      first by iApply (twp_avl_node _ _ (AVL.Node ll lk lv lh AVL.Leaf)).
    wp_apply twp_avl_node. wp_apply twp_avl_node.
    by iApply (twp_avl_node _ _ (AVL.node ll lk lv lrl) lrk lrv (AVL.node lrr k v r)). }
case: bool_decide_reflect => _; wp_pures; last by iApply twp_avl_node.
case: r => [|rl rk rv rh rr] /=; wp_pures;
  first by iApply (twp_avl_node _ _ _ _ _ AVL.Leaf).
wp_apply twp_avl_height. wp_apply twp_avl_height. wp_pures.
case: bool_decide_reflect => _; wp_pures.
- wp_apply twp_avl_node. by iApply (twp_avl_node _ _ (AVL.node l k v rl) rk rv rr).
- case: rl => [|rll rlk rlv rlh rlr] /=; wp_pures;
    first by iApply (twp_avl_node _ _ _ _ _ (AVL.Node AVL.Leaf rk rv rh rr)).
  wp_apply twp_avl_node. wp_apply twp_avl_node.
  by iApply (twp_avl_node _ _ (AVL.node l k v rll) rlk rlv (AVL.node rlr rk rv rr)).
Qed.

Lemma twp_avl_insert E Ψ k v t :
  Ψ (repr (AVL.insert k v t)) ⊢ WP avl_insert #k #v (repr t) @ E [{ Ψ }].
Proof.
elim: t Ψ => [|l IHl k' v' h r IHr] Ψ /=; iIntros "post"; wp_rec; wp_pures;
  first done.
case: bool_decide_reflect => _; wp_pures.
{ wp_apply IHl. by iApply twp_avl_bal. }
case: bool_decide_reflect => _; wp_pures; last done.
wp_apply IHr. by iApply twp_avl_bal.
Qed.

Lemma twp_avl_lookup E Ψ k t :
  Ψ (repr (AVL.lookup k t)) ⊢ WP avl_lookup #k (repr t) @ E [{ Ψ }].
Proof.
elim: t Ψ => [|l IHl k' v' h r IHr] Ψ /=; iIntros "post"; wp_rec; wp_pures;
  first done.
case: bool_decide_reflect => _; wp_pures; first by iApply IHl.
case: bool_decide_reflect => _; wp_pures; first by iApply IHr.
done.
Qed.

Lemma twp_avl_to_list_acc E Ψ t acc :
  Ψ (repr (AVL.to_list_acc t acc)) ⊢
  WP avl_to_list_acc (repr t) (repr acc) @ E [{ Ψ }].
Proof.
elim: t Ψ acc => [|l IHl k v h r IHr] Ψ acc /=; iIntros "post"; wp_rec; wp_pures;
  first done.
wp_apply IHr. wp_pures.
rewrite -[InjRV _](repr_listE ((k, v) :: AVL.to_list_acc r acc)).
by iApply IHl.
Qed.

Lemma twp_avl_to_list E Ψ t :
  Ψ (repr (AVL.to_list t)) ⊢ WP avl_to_list (repr t) @ E [{ Ψ }].
Proof.
iIntros "post". wp_rec. wp_pures.
rewrite -[InjLV _](repr_listE (@nil (Z * Z))).
by iApply twp_avl_to_list_acc.
Qed.

End Specs.
