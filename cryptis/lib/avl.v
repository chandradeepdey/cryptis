(** Maps from integers to integers, stored as AVL trees in HeapLang, together
  with a Gallina model [AVL].

  [AVL.to_list] produces an association list corresponding to [AVL.to_map] using
  in-order traversal, making the list independent of the tree shape. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import sorting gmap.
From iris.heap_lang Require Import lang notation proofmode.
From cryptis Require Import lib.

Module AVL.

#[local] Open Scope Z_scope.

Section AssocList.

#[local] Definition key_lt (p q : Z * Z) := p.1 < q.1.
Arguments key_lt _ _ /.

#[local] Fixpoint ins k v (l : list (Z * Z)) :=
  match l with
  | [] => [(k, v)]
  | (k', v') :: l =>
    if bool_decide (k < k') then (k, v) :: (k', v') :: l
    else if bool_decide (k' < k) then (k', v') :: ins k v l
    else (k, v) :: l
  end.

#[local] Lemma keys_lt_notin k (l : list (Z * Z)) :
  Forall (λ p, p.1 < k) l → k ∉ l.*1.
Proof. move/Forall_forall => H /list_elem_of_fmap [[k' v'] [/= e /H /=]]. lia. Qed.

#[local] Lemma keys_gt_notin k (l : list (Z * Z)) :
  Forall (λ p, k < p.1) l → k ∉ l.*1.
Proof. move/Forall_forall => H /list_elem_of_fmap [[k' v'] [/= e /H /=]]. lia. Qed.

#[local] Lemma ins_app_l k v l1 l2 :
  Forall (λ p, k < p.1) l2 → ins k v (l1 ++ l2) = ins k v l1 ++ l2.
Proof.
elim: l1 => [|[k' v'] l1 IH] /= Hl2.
- case: l2 Hl2 => //= - [k2 v2] l2 /Forall_cons [/= Hk _].
  by rewrite bool_decide_eq_true_2.
- by do 2![case: bool_decide_reflect => //= _]; rewrite IH.
Qed.

#[local] Lemma ins_app_r k v l1 l2 :
  Forall (λ p, p.1 < k) l1 → ins k v (l1 ++ l2) = l1 ++ ins k v l2.
Proof.
elim: l1 => [|[k' v'] l1 IH] //= /Forall_cons [/= Hk' Hl1].
rewrite bool_decide_eq_false_2; last lia.
rewrite bool_decide_eq_true_2; last lia.
by rewrite IH.
Qed.

#[local] Lemma list_to_map_ins k v l :
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

#[local] Lemma ins_elem k v l p : p ∈ ins k v l → p.1 = k ∨ p ∈ l.
Proof.
elim: l => [|[k' v'] l IH] /=.
{ rewrite list_elem_of_singleton => ->. by left. }
case: bool_decide_reflect => _.
{ rewrite !elem_of_cons => - [->|?]; [by left | by right]. }
case: bool_decide_reflect => _; rewrite !elem_of_cons.
- move=> [->|/IH [?|?]]; [by right; left | by left | by right; right].
- move=> [->|?]; [by left | by right; right].
Qed.

#[local] Lemma StronglySorted_ins k v l :
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

#[local] Instance key_lt_antisymm : AntiSymm (=@{Z * Z}) key_lt.
Proof. move=> [k v] [k' v'] /=. lia. Qed.

#[local] Lemma StronglySorted_key_lt_NoDup (l : list (Z * Z)) :
  StronglySorted key_lt l → NoDup l.*1.
Proof.
elim: l => [|[k v] l IH] /= Hs; first by constructor.
move/StronglySorted_cons: Hs => [/Forall_forall Hk Hl].
apply/NoDup_cons; split; last exact: IH.
move=> /list_elem_of_fmap [[k' v'] [/= e /Hk /=]]. lia.
Qed.

#[local] Lemma sorted_assoc_unique (l1 l2 : list (Z * Z)) :
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

End AssocList.

Section Tree.

Inductive tree := Leaf | Node (l : tree) (k v h : Z) (r : tree).

Definition height t : Z := match t with Leaf => 0 | Node _ _ _ h _ => h end.

Definition node l k v r := Node l k v (1 + Z.max (height l) (height r)) r.

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

Definition bst t := StronglySorted key_lt (to_list t).

Definition to_map t : gmap Z Z := list_to_map (to_list t).

End Tree.

Section InOrder.

#[local] Lemma to_list_acc_app t acc : to_list_acc t acc = to_list t ++ acc.
Proof.
elim: t acc => [|l IHl k v h r IHr] acc //=.
by rewrite /to_list /= !IHl !IHr app_nil_r -app_assoc.
Qed.

#[local] Lemma to_list_node l k v h r :
  to_list (Node l k v h r) = to_list l ++ (k, v) :: to_list r.
Proof. by rewrite {1}/to_list /= to_list_acc_app. Qed.

#[local] Lemma to_list_acc_bal l k v r acc :
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

#[local] Lemma to_list_bal l k v r :
  to_list (bal l k v r) = to_list l ++ (k, v) :: to_list r.
Proof. by rewrite /to_list to_list_acc_bal to_list_acc_app. Qed.

#[local] Lemma bst_node l k v h r :
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

#[local] Lemma to_list_insert k v t :
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

Lemma to_map_leaf : to_map Leaf = ∅.
Proof. by []. Qed.

Lemma to_map_insert k v t :
  bst t → to_map (insert k v t) = <[k:=v]> (to_map t).
Proof. move=> Hb. by rewrite /to_map to_list_insert // list_to_map_ins. Qed.

Lemma bst_foldl_insert kvs t :
  bst t → bst (foldl (λ t p, insert p.1 p.2 t) t kvs).
Proof.
elim: kvs t => [|p kvs IH] t Ht //=.
apply: IH. exact: bst_insert.
Qed.

Lemma to_map_foldl_insert kvs t :
  bst t →
  to_map (foldl (λ t p, insert p.1 p.2 t) t kvs) =
  list_to_map (reverse kvs) ∪ to_map t.
Proof.
elim: kvs t => [|p kvs IH] t Ht /=.
- by rewrite left_id_L.
- rewrite IH; last exact: bst_insert.
  rewrite to_map_insert // reverse_cons list_to_map_app /=.
  by rewrite -map_union_assoc -insert_union_l left_id_L.
Qed.

Lemma to_list_to_map t1 t2 :
  bst t1 → bst t2 → to_map t1 = to_map t2 → to_list t1 = to_list t2.
Proof. exact: sorted_assoc_unique. Qed.

End InOrder.

Section Balance.

Fixpoint balanced t :=
  match t with
  | Leaf => True
  | Node l _ _ h r =>
    balanced l ∧ balanced r ∧
    h = 1 + Z.max (height l) (height r) ∧
    -1 ≤ height l - height r ≤ 1
  end.

#[local] Lemma balanced_height t : balanced t → 0 ≤ height t.
Proof. elim: t => [|l IHl k v h r IHr] //= [/IHl ? [/IHr ? [-> _]]]. lia. Qed.

#[local] Lemma balanced_node l k v r :
  balanced l → balanced r → -1 ≤ height l - height r ≤ 1 →
  balanced (node l k v r).
Proof. by move=> /= ???; do !split=> //; lia. Qed.

#[local] Lemma bal_spec l k v r :
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
  - split=> /=; [do !split=> //; lia | right].
    split; lia.
  - case: lr Hlr Hhlr Hb Hd H1 H2 E => [|lrl lrk lrv lrh lrr] /= Hlr Hhlr Hb Hd H1 H2 E;
      first lia.
    move: Hlr => [Hlrl [Hlrr [E' Hb']]].
    have Hhlrl := balanced_height _ Hlrl. have Hhlrr := balanced_height _ Hlrr.
    split=> /=; [do !split=> //; lia | right].
    split; lia. }
case: bool_decide_reflect => H2; last first.
{ split=> /=; last by left; split; lia.
  apply: balanced_node => //. lia. }
case: r Hr Hhr Hd H1 H2 => [|rl rk rv rh rr] /= Hr Hhr Hd H1 H2; first lia.
move: Hr => [Hrl [Hrr [E Hb]]].
have Hhrl := balanced_height _ Hrl. have Hhrr := balanced_height _ Hrr.
case: bool_decide_reflect => H3.
- split=> /=; [do !split=> //; lia | right].
  split; lia.
- case: rl Hrl Hhrl Hb Hd H1 H2 H3 E => [|rll rlk rlv rlh rlr] /= Hrl Hhrl Hb Hd H1 H2 H3 E;
    first lia.
  move: Hrl => [Hrll [Hrlr [E' Hb']]].
  have Hhrll := balanced_height _ Hrll. have Hhrlr := balanced_height _ Hrlr.
  split=> /=; [do !split=> //; lia | right].
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
case: bool_decide_reflect => _; last by do !split=> //=; lia.
move: IHr => /(_ Hr) [Hr' Hh'].
have [Hbal Hcase] := bal_spec _ k' v' _ Hl Hr' ltac:(lia).
split; first done. case: Hcase => [[? ->]|[? [? ?]]]; lia.
Qed.

End Balance.

End AVL.

Section Repr.

Context {Σ : gFunctors} (pt : loc → val → iProp Σ).

Fixpoint avl_tree_at (t : AVL.tree) (w : val) : iProp Σ :=
  match t with
  | AVL.Leaf => ⌜w = NONEV⌝
  | AVL.Node l k v h r =>
    ∃ (p : loc) (wl wr : val),
      ⌜w = SOMEV #p⌝ ∗ pt p (wl, #k, #v, #h, wr)%V ∗
      avl_tree_at l wl ∗ avl_tree_at r wr
  end.

Definition avl_at (m : val) (t : AVL.tree) : iProp Σ :=
  ∃ (p : loc) (w : val), ⌜m = #p⌝ ∗ pt p w ∗ avl_tree_at t w.

End Repr.

Section Impl.

Definition avl_new : val := λ: <>, ref NONE.

Definition avl_height : val := λ: "t",
  match: "t" with NONE => #0 | SOME "p" => Snd (Fst !"p") end.

Definition avl_set_node : val := λ: "p" "l" "k" "v" "r",
  let: "hl" := avl_height "l" in
  let: "hr" := avl_height "r" in
  let: "h" := if: "hl" < "hr" then "hr" else "hl" in
  "p" <- ("l", "k", "v", #1 + "h", "r");;
  SOME "p".

Definition avl_bal : val := λ: "p" "l" "k" "v" "r",
  let: "hl" := avl_height "l" in
  let: "hr" := avl_height "r" in
  if: "hr" + #1 < "hl" then
    match: "l" with
      NONE => avl_set_node "p" "l" "k" "v" "r"
    | SOME "pl" =>
      let: "n" := !"pl" in
      let: "ll" := Fst (Fst (Fst (Fst "n"))) in
      let: "lk" := Snd (Fst (Fst (Fst "n"))) in
      let: "lv" := Snd (Fst (Fst "n")) in
      let: "lr" := Snd "n" in
      if: avl_height "lr" ≤ avl_height "ll" then
        avl_set_node "pl" "ll" "lk" "lv" (avl_set_node "p" "lr" "k" "v" "r")
      else
        match: "lr" with
          NONE => avl_set_node "p" "l" "k" "v" "r"
        | SOME "plr" =>
          let: "m" := !"plr" in
          let: "lrl" := Fst (Fst (Fst (Fst "m"))) in
          let: "lrk" := Snd (Fst (Fst (Fst "m"))) in
          let: "lrv" := Snd (Fst (Fst "m")) in
          let: "lrr" := Snd "m" in
          avl_set_node "plr" (avl_set_node "pl" "ll" "lk" "lv" "lrl") "lrk" "lrv"
                   (avl_set_node "p" "lrr" "k" "v" "r")
        end
    end
  else if: "hl" + #1 < "hr" then
    match: "r" with
      NONE => avl_set_node "p" "l" "k" "v" "r"
    | SOME "pr" =>
      let: "n" := !"pr" in
      let: "rl" := Fst (Fst (Fst (Fst "n"))) in
      let: "rk" := Snd (Fst (Fst (Fst "n"))) in
      let: "rv" := Snd (Fst (Fst "n")) in
      let: "rr" := Snd "n" in
      if: avl_height "rl" ≤ avl_height "rr" then
        avl_set_node "pr" (avl_set_node "p" "l" "k" "v" "rl") "rk" "rv" "rr"
      else
        match: "rl" with
          NONE => avl_set_node "p" "l" "k" "v" "r"
        | SOME "prl" =>
          let: "m" := !"prl" in
          let: "rll" := Fst (Fst (Fst (Fst "m"))) in
          let: "rlk" := Snd (Fst (Fst (Fst "m"))) in
          let: "rlv" := Snd (Fst (Fst "m")) in
          let: "rlr" := Snd "m" in
          avl_set_node "prl" (avl_set_node "p" "l" "k" "v" "rll") "rlk" "rlv"
                   (avl_set_node "pr" "rlr" "rk" "rv" "rr")
        end
    end
  else avl_set_node "p" "l" "k" "v" "r".

Definition avl_insert_node : val := rec: "loop" "k" "v" "t" :=
  match: "t" with
    NONE => SOME (ref (NONE, "k", "v", #1, NONE))
  | SOME "p" =>
    let: "n" := !"p" in
    let: "l" := Fst (Fst (Fst (Fst "n"))) in
    let: "k'" := Snd (Fst (Fst (Fst "n"))) in
    let: "v'" := Snd (Fst (Fst "n")) in
    let: "h" := Snd (Fst "n") in
    let: "r" := Snd "n" in
    if: "k" < "k'" then avl_bal "p" ("loop" "k" "v" "l") "k'" "v'" "r"
    else if: "k'" < "k" then avl_bal "p" "l" "k'" "v'" ("loop" "k" "v" "r")
    else "p" <- ("l", "k", "v", "h", "r");; "t"
  end.

Definition avl_insert : val := λ: "k" "v" "m",
  "m" <- avl_insert_node "k" "v" !"m".

Definition avl_lookup_node : val := rec: "loop" "k" "t" :=
  match: "t" with
    NONE => NONE
  | SOME "p" =>
    let: "n" := !"p" in
    let: "l" := Fst (Fst (Fst (Fst "n"))) in
    let: "k'" := Snd (Fst (Fst (Fst "n"))) in
    let: "v'" := Snd (Fst (Fst "n")) in
    let: "r" := Snd "n" in
    if: "k" < "k'" then "loop" "k" "l"
    else if: "k'" < "k" then "loop" "k" "r"
    else SOME "v'"
  end.

Definition avl_lookup : val := λ: "k" "m", avl_lookup_node "k" !"m".

Definition avl_to_list_acc : val := rec: "loop" "t" "acc" :=
  match: "t" with
    NONE => "acc"
  | SOME "p" =>
    let: "n" := !"p" in
    let: "l" := Fst (Fst (Fst (Fst "n"))) in
    let: "k" := Snd (Fst (Fst (Fst "n"))) in
    let: "v" := Snd (Fst (Fst "n")) in
    let: "r" := Snd "n" in
    "loop" "l" (SOME (("k", "v"), "loop" "r" "acc"))
  end.

Definition avl_to_list : val := λ: "m", avl_to_list_acc !"m" NONE.

End Impl.

Section Specs.

Context `{!heapGS Σ}.

Implicit Types (t : AVL.tree) (m w : val) (p : loc) (Ψ : val → iProp Σ).

Definition is_avl : val → AVL.tree → iProp Σ := avl_at (λ p w, p ↦ w)%I.

#[local] Abbreviation is_tree := (avl_tree_at (λ p w, p ↦ w)%I).

#[local] Lemma twp_avl_height E Ψ t w :
  is_tree t w -∗ (is_tree t w -∗ Ψ #(AVL.height t)) -∗
  WP avl_height w @ E [{ Ψ }].
Proof.
iIntros "Ht post". case: t => [|l k v h r] /=.
- iDestruct "Ht" as %->. wp_rec. wp_pures. by iApply "post".
- iDestruct "Ht" as (p wl wr ->) "(Hp & Hl & Hr)". wp_rec. wp_pures. wp_load.
  wp_pures. iApply "post". iExists p, wl, wr. by iFrame.
Qed.

#[local] Lemma twp_avl_node E Ψ p w0 l k v r wl wr :
  p ↦ w0 -∗ is_tree l wl -∗ is_tree r wr -∗
  (∀ w, is_tree (AVL.node l k v r) w -∗ Ψ w) -∗
  WP avl_set_node #p wl #k #v wr @ E [{ Ψ }].
Proof.
iIntros "Hp Hl Hr post". wp_rec. wp_pures.
wp_apply (twp_avl_height with "Hl"). iIntros "Hl". wp_pures.
wp_apply (twp_avl_height with "Hr"). iIntros "Hr". wp_pures.
case: bool_decide_reflect => ?; wp_pures; wp_store; wp_pures;
  iApply "post"; iExists p, wl, wr.
- rewrite Z.max_r; last lia. by iFrame.
- rewrite Z.max_l; last lia. by iFrame.
Qed.

#[local] Lemma twp_avl_bal E Ψ p w0 l k v r wl wr :
  p ↦ w0 -∗ is_tree l wl -∗ is_tree r wr -∗
  (∀ w, is_tree (AVL.bal l k v r) w -∗ Ψ w) -∗
  WP avl_bal #p wl #k #v wr @ E [{ Ψ }].
Proof.
iIntros "Hp Hl Hr post". wp_rec. wp_pures.
wp_apply (twp_avl_height with "Hl"). iIntros "Hl". wp_pures.
wp_apply (twp_avl_height with "Hr"). iIntros "Hr". wp_pures.
rewrite /AVL.bal. case: bool_decide_reflect => _; wp_pures.
{ case: l => [|ll lk lv lh lr] /=.
  { iDestruct "Hl" as %->. wp_pures.
    by wp_apply (twp_avl_node _ _ _ _ AVL.Leaf with "Hp [//] Hr"). }
  iDestruct "Hl" as (pl wll wlr ->) "(Hpl & Hll & Hlr)". wp_pures. wp_load.
  wp_pures.
  wp_apply (twp_avl_height with "Hll"). iIntros "Hll".
  wp_apply (twp_avl_height with "Hlr"). iIntros "Hlr". wp_pures.
  case: bool_decide_reflect => _; wp_pures.
  { wp_apply (twp_avl_node with "Hp Hlr Hr"). iIntros (w) "Hw".
    by wp_apply (twp_avl_node with "Hpl Hll Hw"). }
  case: lr => [|lrl lrk lrv lrh lrr] /=.
  { iDestruct "Hlr" as %->. wp_pures.
    wp_apply (twp_avl_node _ _ _ _ (AVL.Node ll lk lv lh AVL.Leaf)
                with "Hp [Hpl Hll] Hr"); last done.
    iExists pl, wll, NONEV. by iFrame. }
  iDestruct "Hlr" as (plr wlrl wlrr ->) "(Hplr & Hlrl & Hlrr)". wp_pures.
  wp_load. wp_pures.
  wp_apply (twp_avl_node with "Hp Hlrr Hr"). iIntros (w1) "H1".
  wp_apply (twp_avl_node with "Hpl Hll Hlrl"). iIntros (w2) "H2".
  by wp_apply (twp_avl_node with "Hplr H2 H1"). }
case: bool_decide_reflect => _; wp_pures;
  last by wp_apply (twp_avl_node with "Hp Hl Hr").
case: r => [|rl rk rv rh rr] /=.
{ iDestruct "Hr" as %->. wp_pures.
  by wp_apply (twp_avl_node _ _ _ _ _ _ _ AVL.Leaf with "Hp Hl [//]"). }
iDestruct "Hr" as (pr wrl wrr ->) "(Hpr & Hrl & Hrr)". wp_pures. wp_load.
wp_pures.
wp_apply (twp_avl_height with "Hrr"). iIntros "Hrr".
wp_apply (twp_avl_height with "Hrl"). iIntros "Hrl". wp_pures.
case: bool_decide_reflect => _; wp_pures.
{ wp_apply (twp_avl_node with "Hp Hl Hrl"). iIntros (w) "Hw".
  by wp_apply (twp_avl_node with "Hpr Hw Hrr"). }
case: rl => [|rll rlk rlv rlh rlr] /=.
{ iDestruct "Hrl" as %->. wp_pures.
  wp_apply (twp_avl_node _ _ _ _ _ _ _ (AVL.Node AVL.Leaf rk rv rh rr)
              with "Hp Hl [Hpr Hrr]"); last done.
  iExists pr, NONEV, wrr. by iFrame. }
iDestruct "Hrl" as (prl wrll wrlr ->) "(Hprl & Hrll & Hrlr)". wp_pures.
wp_load. wp_pures.
wp_apply (twp_avl_node with "Hpr Hrlr Hrr"). iIntros (w1) "H1".
wp_apply (twp_avl_node with "Hp Hl Hrll"). iIntros (w2) "H2".
by wp_apply (twp_avl_node with "Hprl H2 H1").
Qed.

#[local] Lemma twp_avl_insert_node E Ψ k v t w :
  is_tree t w -∗ (∀ w', is_tree (AVL.insert k v t) w' -∗ Ψ w') -∗
  WP avl_insert_node #k #v w @ E [{ Ψ }].
Proof.
elim: t Ψ w => [|l IHl k' v' h r IHr] Ψ w /=; iIntros "Ht post".
{ iDestruct "Ht" as %->. wp_rec. wp_pures. wp_alloc p as "Hp". wp_pures.
  iApply "post". iExists p, NONEV, NONEV. by iFrame. }
iDestruct "Ht" as (p wl wr ->) "(Hp & Hl & Hr)". wp_rec. wp_pures. wp_load.
wp_pures.
case: bool_decide_reflect => _; wp_pures.
{ wp_apply (IHl with "Hl"). iIntros (wl') "Hl".
  by wp_apply (twp_avl_bal with "Hp Hl Hr"). }
case: bool_decide_reflect => _; wp_pures.
{ wp_apply (IHr with "Hr"). iIntros (wr') "Hr".
  by wp_apply (twp_avl_bal with "Hp Hl Hr"). }
wp_store. iApply "post". iExists p, wl, wr. by iFrame.
Qed.

#[local] Lemma twp_avl_lookup_node E Ψ k t w :
  is_tree t w -∗ (is_tree t w -∗ Ψ (repr (AVL.lookup k t))) -∗
  WP avl_lookup_node #k w @ E [{ Ψ }].
Proof.
elim: t Ψ w => [|l IHl k' v' h r IHr] Ψ w /=; iIntros "Ht post".
{ iDestruct "Ht" as %->. wp_rec. wp_pures. by iApply "post". }
iDestruct "Ht" as (p wl wr ->) "(Hp & Hl & Hr)". wp_rec. wp_pures. wp_load.
wp_pures.
case: bool_decide_reflect => _; wp_pures.
{ wp_apply (IHl with "Hl"). iIntros "Hl".
  iApply "post". iExists p, wl, wr. by iFrame. }
case: bool_decide_reflect => _; wp_pures.
{ wp_apply (IHr with "Hr"). iIntros "Hr".
  iApply "post". iExists p, wl, wr. by iFrame. }
iApply "post". iExists p, wl, wr. by iFrame.
Qed.

#[local] Lemma twp_avl_to_list_acc E Ψ t w acc :
  is_tree t w -∗ (is_tree t w -∗ Ψ (repr (AVL.to_list_acc t acc))) -∗
  WP avl_to_list_acc w (repr acc) @ E [{ Ψ }].
Proof.
elim: t Ψ w acc => [|l IHl k v h r IHr] Ψ w acc /=; iIntros "Ht post".
{ iDestruct "Ht" as %->. wp_rec. wp_pures. by iApply "post". }
iDestruct "Ht" as (p wl wr ->) "(Hp & Hl & Hr)". wp_rec. wp_pures. wp_load.
wp_pures.
wp_apply (IHr with "Hr"). iIntros "Hr". wp_pures.
rewrite -[InjRV (PairV _ _)](repr_listE ((k, v) :: AVL.to_list_acc r acc)).
wp_apply (IHl with "Hl"). iIntros "Hl".
iApply "post". iExists p, wl, wr. by iFrame.
Qed.

Lemma twp_avl_new E Ψ :
  (∀ m, is_avl m AVL.Leaf -∗ Ψ m) ⊢ WP avl_new #() @ E [{ Ψ }].
Proof.
rewrite /is_avl /avl_at /=. iIntros "post". wp_rec. wp_alloc p as "Hp".
iApply "post". iExists p, NONEV. by iFrame.
Qed.

Lemma twp_avl_insert E Ψ k v m t :
  is_avl m t -∗ (is_avl m (AVL.insert k v t) -∗ Ψ #()) -∗
  WP avl_insert #k #v m @ E [{ Ψ }].
Proof.
rewrite /is_avl /avl_at /=. iIntros "(%p & %w & -> & Hp & Ht) post".
wp_rec. wp_pures. wp_load.
wp_apply (twp_avl_insert_node with "Ht"). iIntros (w') "Ht". wp_store.
iApply "post". iExists p, w'. by iFrame.
Qed.

Lemma twp_avl_lookup E Ψ k m t :
  is_avl m t -∗ (is_avl m t -∗ Ψ (repr (AVL.lookup k t))) -∗
  WP avl_lookup #k m @ E [{ Ψ }].
Proof.
rewrite /is_avl /avl_at /=. iIntros "(%p & %w & -> & Hp & Ht) post".
wp_rec. wp_pures. wp_load.
wp_apply (twp_avl_lookup_node with "Ht"). iIntros "Ht".
iApply "post". iExists p, w. by iFrame.
Qed.

Lemma twp_avl_to_list E Ψ m t :
  is_avl m t -∗ (is_avl m t -∗ Ψ (repr (AVL.to_list t))) -∗
  WP avl_to_list m @ E [{ Ψ }].
Proof.
rewrite /is_avl /avl_at /=. iIntros "(%p & %w & -> & Hp & Ht) post".
wp_rec. wp_load. wp_pures.
rewrite -[InjLV _](repr_listE (@nil (Z * Z))).
wp_apply (twp_avl_to_list_acc with "Ht"). iIntros "Ht".
iApply "post". iExists p, w. by iFrame.
Qed.

End Specs.
