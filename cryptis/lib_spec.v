From stdpp Require Import base countable gmap.
From iris.heap_lang Require Import lang notation proofmode.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.algebra Require Import gmap gset auth reservation_map.
From iris.base_logic Require Import gen_heap invariants.
From mathcomp Require ssrbool order path.
From deriving Require deriving.
From cryptis Require Export mathcomp_compat lib.
From reloc Require Import reloc.

Section ListLemmas.

Context `{!Repr A, !relocG Σ}.

Implicit Types (x : A) (xs : list A).

Lemma tp_get_list E j (l : list A) (n : nat) :
  nclose specN ⊆ E →
  refines_right j (repr l !! #n) -∗
  |={E}=> refines_right j (repr (l !! n)).
Proof.
intros HE.
rewrite /= repr_list_unseal.
elim: n l j => [|n IH] [|x l] /= j; iIntros "Hj";
tp_rec j; tp_pures j; eauto; simpl; auto.
rewrite (_ : (S n - 1)%Z = n); try lia.
by iApply IH.
Qed.

Lemma tp_nil E j :
  nclose specN ⊆ E →
  refines_right j (repr (@nil A)) -∗
  |={E}=> refines_right j (Val []%V).
Proof.
intros HE.
by rewrite /NILV /= repr_list_unseal; iIntros "Hj"; tp_pures j.
Qed.

Lemma tp_cons E j x xs :
  nclose specN ⊆ E →
  refines_right j (repr (x :: xs)) -∗
  |={E}=> refines_right j (repr x :: repr xs).
Proof.
intros HE.
rewrite /= repr_list_unseal; iIntros "post"; rewrite /CONS; tp_pures j.
Qed.

Lemma wp_list_match_aux E (vs : list A) evs vars k Ψ :
  elements (free_vars k) ## vars →
  (∀ Ψ, Ψ (repr_list vs) -∗ WP evs @ E {{ Ψ }}) -∗
  (if decide (length vars = length vs) then
     WP fill (napp vars (map repr vs)) k @ E {{ Ψ }}
   else Ψ NONEV) -∗
  WP list_match_aux vars evs k @ E {{ Ψ }}.
Proof.
rewrite repr_list_unseal.
elim: vars vs => [|var vars IH] [|v vs] /= in evs k *; iIntros (dis) "evs pS".
- by wp_pures; wp_bind evs; iApply "evs"; wp_pures.
- by wp_pures; wp_bind evs; iApply "evs"; wp_pures.
- by wp_pures; wp_bind evs; iApply "evs"; wp_pures.
rewrite /=; wp_pures; wp_bind evs; iApply "evs"; wp_pures.
rewrite subst_list_match_aux /=.
rewrite [if decide (var = var) then _ else _]decide_True //=.
assert (fresh_var : var ∉ free_vars k) by set_solver.
assert (dis' : elements (free_vars k) ## vars) by set_solver.
iApply (IH with "[]"); try by iIntros (Ψ') "p'"; wp_pures; eauto.
  case: decide => _ //=.
  rewrite free_vars_subst decide_True //=.
  set_solver.
case: (decide (length vars = length vs)) => [eq_l|neq_l]; last first.
  rewrite decide_False //; congruence.
rewrite eq_l decide_True //.
case: decide => [//|nin_vars] /=.
rewrite decide_True //= subst_free_vars //.
wp_pures; iApply wp_bind; wp_pures; by iApply wp_bind_inv.
Qed.

Lemma wp_close_vars E vars vs k Ψ :
  length vars = length vs →
  WP nsubst vars vs k @ E {{ Ψ }} -∗
  WP fill (napp vars vs) (close_vars vars k) @ E {{ Ψ }}.
Proof.
elim: vars vs => [|var vars IH] [|v vs] //= in k Ψ *.
  by iIntros (?) "p"; wp_pures.
move=> [] e; iIntros "p".
case: decide => [in_vars|nin_vars].
  rewrite subst_free_vars; first by iApply IH.
  rewrite free_vars_nsubst // elem_of_difference.
  case => _; rewrite elem_of_union_list.
  by apply; exists {[var]}; split; try set_solver.
rewrite /=.
iApply wp_bind.
wp_pures.
rewrite subst_nsubst_nin //.
iApply wp_bind_inv.
rewrite subst_close_vars //.
by iApply IH.
Qed.

Lemma wp_list_match E vars (vs : list A) k Ψ :
  (if decide (length vars = length vs) then
     WP nsubst vars (map repr vs) k @ E {{ Ψ }}
   else Ψ NONEV) ⊢
  WP list_match vars (repr vs) k @ E {{ Ψ }}.
Proof.
rewrite unlock; iIntros "post".
assert (disj : elements (free_vars (close_vars vars k)) ## vars).
  elim: vars => [|var vars IH] /= in k *; try case: decide => ?; set_solver.
iApply (wp_list_match_aux E vs (repr vs)); eauto.
  by iIntros (?) "?"; iApply wp_value.
case: decide => ? //.
iApply (wp_close_vars with "post").
by rewrite length_map.
Qed.

Lemma twp_eq_list `{EqDecision A} (f : val) (l1 l2 : list A) Φ E :
  (∀ (x1 x2 : A) Ψ,
      x1 ∈ l1 →
      Ψ #(bool_decide (x1 = x2)) -∗
      WP f (repr x1) (repr x2) @ E [{ Ψ }]) →
  Φ #(bool_decide (l1 = l2)) ⊢
  WP eq_list f (repr l1) (repr l2) @ E [{ Φ }].
Proof.
rewrite repr_list_unseal /=.
elim: l1 l2 Φ => [|x1 l1 IH] [|x2 l2] Φ wp_f /=;
iIntros "post" ; wp_rec; wp_pures; do 1?by iApply "post".
wp_bind (f _ _); iApply (wp_f x1 x2); first by set_solver.
case: (bool_decide_reflect (x1 = x2)) => [->|n_x1x2]; wp_pures; last first.
  rewrite bool_decide_decide decide_False; by [iApply "post"|congruence].
iApply IH; first by move=> *; iApply wp_f; set_solver.
case: (bool_decide_reflect (l1 = l2)) => [->|n_l1l2].
- by rewrite bool_decide_decide decide_True.
- by rewrite bool_decide_decide decide_False //; congruence.
Qed.

Lemma wp_scan_list `{Repr A} φ ψ (f : val) (l : list A) :
  □ (∀ x : A,
    {{{ ψ NONEV ∗ φ x }}}
      f (repr x)
    {{{ (r : option val), RET (repr r); ψ (repr r) }}}) -∗
  ψ NONEV ∗ ([∗ list] x ∈ l, φ x) -∗
  WP scan_list f (repr l) {{ ψ }}.
Proof.
rewrite repr_list_unseal /=.
iIntros "#wp_f"; iLöb as "IH" forall (l); iIntros "[ψ φ_l]".
wp_rec; case: l => [|h t] /=; wp_pures; first done.
iDestruct "φ_l" as "[φ_h φ_t]".
wp_apply ("wp_f" with "[$ψ $φ_h]").
iIntros "%r ψ_r"; case: r => [r|]; wp_pures; first done.
by wp_apply ("IH" with "[$]").
Qed.

Lemma wp_find_list (f : A → bool) (fimpl : val) (l : list A) E :
  (∀ x : A, {{{ True }}} fimpl (repr x) @ E {{{ RET #(f x); True }}}) →
  {{{ True }}} find_list fimpl (repr l) @ E {{{ RET (repr (find f l)); True }}}.
Proof.
rewrite repr_list_unseal /=.
iIntros "%fP"; iLöb as "IH" forall (l); iIntros "%Φ _ Hpost"; wp_rec.
case: l => [|h t] /=; wp_pures; first by iApply "Hpost".
wp_bind (fimpl _); iApply fP => //; iIntros "!> _".
case: (f h) => //; wp_pures; first by iApply "Hpost".
by iApply "IH".
Qed.

Lemma wp_filter_list (f : A → bool) (fimpl : val) (l : list A) E :
  (∀ x : A, {{{ True }}} fimpl (repr x) @ E {{{ RET #(f x); True }}}) →
  {{{ True }}}
    filter_list fimpl (repr l) @ E
  {{{ RET (repr (List.filter f l)); True }}}.
Proof.
rewrite repr_list_unseal /=.
iIntros "%fP"; iLöb as "IH" forall (l); iIntros "%Φ _ Hpost"; wp_rec.
case: l => [|x l] /=; wp_pures; first by iApply "Hpost".
wp_bind (filter_list _ _). iApply "IH" => //. iIntros "!> _".
wp_pures. wp_bind (fimpl _); iApply fP => //; iIntros "!> _".
case f_x: (f x); wp_pures; by iApply "Hpost".
Qed.

End ListLemmas.

Section DoUntil.

Context `{!heapGS Σ}.

Lemma wp_do_until E (f : val) φ (Ψ : val → iProp Σ) :
  □ (φ -∗
     WP f #() @ E {{ v, ⌜v = NONEV⌝ ∗ φ ∨
                        ∃ v', ⌜v = SOMEV v'⌝ ∗ Ψ v' }}) -∗
  φ -∗
  WP do_until f @ E {{ Ψ }}.
Proof.
iIntros "#wp_f Hφ"; iLöb as "IH".
wp_rec. wp_bind (f _).
iApply (wp_wand with "[Hφ]"); first iApply "wp_f" => //.
iIntros "%v [[-> Hφ] | (%v' & -> & Hv')]"; wp_pures; eauto.
iApply ("IH" with "Hφ").
Qed.

Lemma wp_do_until' E (f : val) (φ : val → iProp Σ) :
  □ WP f #() @ E {{ v, ⌜v = NONEV⌝ ∨ (∃ v', ⌜v = SOMEV v'⌝ ∗ φ v') }} -∗
  WP do_until f @ E {{ φ }}.
Proof.
iIntros "#wp_f".
iAssert True%I as "I" => //.
iRevert "I".
iApply wp_do_until.
iIntros "!> _".
iApply wp_wand; eauto.
iIntros "%v [->|post]"; eauto.
Qed.

End DoUntil.

Section Loc.

Context `{!heapGS Σ}.
Import ssreflect.order deriving.instances.

Lemma twp_leq_loc_loop E (l1 l2 : loc) (n k : nat) Ψ :
  loc_car l2 = (loc_car l1 + (n + k)%nat)%Z ∨
  loc_car l1 = (loc_car l2 + (n + k)%nat)%Z ∧ n + k ≠ 0%nat →
  Ψ #(l1 <= l2)%O ⊢
  WP leq_loc_loop #l1 #l2 #n @ E [{ Ψ }].
Proof.
have leq_locE l1' l2' :
    (l1' <= l2')%O = bool_decide (loc_car l1' ≤ loc_car l2')%Z.
  exact/(ssrbool.sameP (Z.leb_spec0 _ _))/bool_decide_reflect.
have eq_locE (l1' l2' : loc) :
    bool_decide (#l1' = #l2') = bool_decide (loc_car l1' = loc_car l2').
  apply: bool_decide_ext; split => [[->] //|].
  by case: l1' l2' => [?] [?] /= ->.
elim: k n => [|k IH] n e_l1l2; iIntros "post"; wp_pures; wp_rec; wp_pures.
- rewrite eq_locE.
  case: bool_decide_reflect => /= [eq|neq]; wp_pures.
    rewrite leq_locE bool_decide_decide decide_True //=.
    lia.
  rewrite eq_locE bool_decide_decide decide_True /=; try lia.
  wp_pures; rewrite leq_locE bool_decide_decide decide_False //.
  move=> H; apply: neq; rewrite /Loc.add /= in H; lia.
- rewrite eq_locE bool_decide_decide decide_False; last by move=> /= ?; lia.
  wp_pures.
  rewrite eq_locE bool_decide_decide decide_False; last by move=> /= ?; lia.
  wp_pures.
  rewrite (_ : (n + 1)%Z = S n :> Z); try lia.
  iApply IH => //; lia.
Qed.

Lemma twp_leq_loc E (l1 l2 : loc) Ψ :
  Ψ #(l1 <= l2)%O ⊢
  WP leq_loc #l1 #l2 @ E [{ Ψ }].
Proof.
have [off offP] :
    ∃ off : nat, (loc_car l2 = loc_car l1 + off ∨
                  loc_car l1 = loc_car l2 + off ∧ off ≠ 0%nat)%Z.
  exists (Z.to_nat (Z.abs (loc_car l1 - loc_car l2))); lia.
iIntros "post"; rewrite /leq_loc -[0%Z]/(Z.of_nat 0); wp_pures.
by iApply twp_leq_loc_loop => //.
Qed.

End Loc.

Section Ordered.

Import ssrbool seq ssreflect.order path deriving.instances.
Variable (d : Order.disp_t) (A : orderType d).
Context `{!Repr A, !heapGS Σ}.
Import Order Order.POrderTheory Order.TotalTheory.
Implicit Types (x y z : A) (s : seqlexi_with d A).

Lemma twp_insert_sorted (f : val) (x : A) (l : list A) E :
  is_true (sorted le l) →
  (∀ (y z : A),
      [[{ True }]] f (repr y) (repr z) @ E [[{ RET #(le y z); True }]]) →
  [[{ True }]]
    insert_sorted f (repr x) (repr l) @ E
  [[{ RET (repr (sort le (x :: l))); True }]].
Proof.
rewrite repr_list_unseal => sorted_l wp_f Φ; iIntros "_ post".
iSpecialize ("post" with "[//]"); iStopProof.
elim: l sorted_l Φ => //= [|y l IH] path_l Φ;
iIntros "post"; wp_rec; wp_pures => //.
move/(_ (path_sorted path_l)) in IH.
wp_bind (f _ _); iApply wp_f => //; iIntros "_".
have [le_xy|le_yx] := boolP (x <= y)%O; wp_pures.
  by rewrite sort_le_id //= ?le_xy.
move: le_yx; rewrite -ltNge => /ltW le_yx.
wp_bind (insert_sorted _ _ _); iApply IH.
suff -> : sort le [:: x, y & l] = y :: sort le (x :: l) by wp_pures.
rewrite -[RHS]sort_le_id /=.
  apply/perm_sort_leP/perm_consP.
  exists 1, (l ++ [:: x])%SEQ.
  by rewrite /= perm_catC perm_sym /= perm_sort; split.
rewrite path_min_sorted ?sort_le_sorted // all_sort /= le_yx /=.
apply: order_path_min => //; apply: le_trans.
Qed.

Lemma twp_leq_list (feq : val) (fle : val) s1 s2 E :
  (∀ x1 x2,
      [[{ True }]]
        feq (repr x1) (repr x2) @ E
      [[{ RET #(eqtype.eq_op x1 x2); True }]]) →
  (∀ x1 x2,
      is_true (x1 \in s1) →
      [[{ True }]]
        fle (repr x1) (repr x2) @ E
      [[{ RET #(le x1 x2); True }]]) →
  [[{ True }]]
    leq_list feq fle (repr s1) (repr s2) @ E
  [[{ RET #(le s1 s2); True }]].
Proof.
move=> feqP fleqP Φ; iIntros "_ post".
iSpecialize ("post" with "[//]"); iStopProof.
move: fleqP; rewrite /= repr_list_unseal.
elim: s1 s2 => [|x1 s1 IH] [|x2 s2] fleP; iIntros "HΦ"; wp_rec; wp_pures => //.
rewrite lexi_cons; wp_bind (feq _ _); iApply feqP => //; iIntros "_".
case: (ltgtP x1 x2) => [l_x1x2|l_x2x1|<-] /=; wp_pures.
- by iApply fleP; rewrite ?inE ?eqtype.eqxx // ltW //; iIntros "_".
- by iApply fleP; rewrite ?inE ?eqtype.eqxx // leNgt l_x2x1 //; iIntros "_".
- iApply IH => // x1' ? x1'_in ?; iIntros "_ post".
  by iApply fleP; rewrite // inE x1'_in orbT.
Qed.

End Ordered.

#[global]
Instance repr_prod `{Repr A, Repr B} : Repr (A * B) :=
  λ p, (repr p.1, repr p.2)%V.
Arguments repr_prod {_ _ _ _} !_.

Fixpoint nforall {A} (n : nat) (P : list A → Prop) :=
  match n with
  | 0 => P []
  | S n => forall x : A, nforall n (λ xs, P (x :: xs))
  end.

Lemma nforallP {A} (n : nat) (P : list A -> Prop) :
  nforall n P ↔ ∀ vs, n = length vs → P vs.
Proof.
elim: n => [|n IH] /= in P *.
  split; [by move=> ? [|//]|by apply].
split.
- move=> H [|x xs] //= [e]; by move/IH: (H x); apply.
- by move=> H x; apply/IH => xs len_xs; apply: H; rewrite len_xs.
Qed.

Definition nforall_eq {A} (n : nat) (vs : list A) (P : list A -> Prop) :=
  nforall n (λ vs', vs = vs' → P vs').

Lemma nforall_eqP {A} (n : nat) (xs : list A) (P : list A -> Prop) :
  nforall_eq n xs P ↔ (n = length xs → P xs).
Proof.
rewrite /nforall_eq nforallP; split.
- by move=> H len_xs; apply: H.
- by move=> H xs' len_xs' e_xs'; rewrite e_xs' in H; apply: H.
Qed.

Arguments nforall_eq {A} /.

Lemma list_len_rect (n : nat) A (P : list A → Prop) :
  (nforall n P) →
  (∀ xs, length xs ≠ n → P xs) →
  ∀ xs, P xs.
Proof.
move=> eq_n neq_n xs.
case: (decide (n = length xs)) => [eq|neq].
- by move: xs eq; apply/nforallP.
- exact: neq_n.
Qed.

Fixpoint prod_of_list_aux_type A B n :=
  match n with
  | 0 => A
  | S n => prod_of_list_aux_type (A * B)%type B n
  end.

Fixpoint prod_of_list_aux {A B} n :
  A → list B → option (prod_of_list_aux_type A B n) :=
  match n with
  | 0 => fun x ys =>
    match ys with
    | [] => Some x
    | _  => None
    end
  | S n => fun x ys =>
    match ys with
    | [] => None
    | y :: ys => prod_of_list_aux n (x, y) ys
    end
  end.

Definition prod_of_list_type A n : Type :=
  match n with
  | 0 => unit
  | S n => prod_of_list_aux_type A A n
  end.

Fact prod_of_list_key : unit. Proof. exact: tt. Qed.

Definition prod_of_list {A} n xs : option (prod_of_list_type A n) :=
  locked_with prod_of_list_key (
    match n return list A → option (prod_of_list_type A n) with
    | 0 => fun xs => match xs with
                     | [] => Some tt
                     | _  => None
                     end
    | S n => fun xs => match xs with
                       | [] => None
                       | x :: xs => prod_of_list_aux n x xs
                       end
    end xs).

Canonical prod_of_list_unlockable A n xs :=
  [unlockable of @prod_of_list A n xs].

Lemma prod_of_list_neq {A} n (xs : list A) :
  length xs ≠ n → prod_of_list n xs = None.
Proof.
rewrite unlock; case: n xs=> [|n] [|x xs] //= ne.
have {}ne : length xs ≠ n by congruence.
suffices : ∀ B (x : B), prod_of_list_aux n x xs = None by apply.
elim: n xs {x} => [|n IH] [|y ys] //= in ne * => B x.
rewrite IH //; congruence.
Qed.

Lemma fmap_binder_delete {A B} (f : A → B) (m : gmap string A) x :
  f <$> binder_delete x m = binder_delete x (f <$> m).
Proof. case: x => [|x] //=; by rewrite fmap_delete. Qed.

Lemma fmap_binder_insert {A B} (f : A → B) (m : gmap string A) i x :
  f <$> binder_insert i x m = binder_insert i (f x) (f <$> m).
Proof. case: i => [|i] //=; by rewrite fmap_insert. Qed.

Lemma insert_same {A} (m1 m2 : gmap string A) (i : string) (x : A) :
  (∀ j, j ≠ i → m1 !! j = m2 !! j) →
  <[i := x]>m1 = <[i := x]>m2.
Proof.
move=> e12; apply map_eq => j.
destruct (decide (j = i)) as [->|ne].
- by rewrite !lookup_insert.
- by rewrite !lookup_insert_ne // e12.
Qed.

Lemma binder_insert_same {A} (m1 m2 : gmap string A) (i : binder) (x : A) :
  (∀ j : string, BNamed j ≠ i → m1 !! j = m2 !! j) →
  binder_insert i x m1 = binder_insert i x m2.
Proof.
case: i => [|i] /= e12.
- by apply: map_eq => i; apply: e12.
- apply: insert_same => ??; apply: e12; congruence.
Qed.

Lemma binder_insert_delete {A} (m : gmap string A) (i : binder) (x : A) :
  binder_insert i x (binder_delete i m) = binder_insert i x m.
Proof. case: i => //= i; exact: insert_delete_insert. Qed.

Lemma binder_insert_delete2 {A} (m : gmap string A) (i j : binder) (x y : A) :
  binder_insert i x (binder_insert j y (binder_delete i (binder_delete j m))) =
  binder_insert i x (binder_insert j y m).
Proof.
rewrite -(binder_insert_delete m j y).
case: i j => [|i] [|j] //=.
- by rewrite insert_delete_insert.
- rewrite delete_commute !insert_delete_insert.
  destruct (decide (i = j)) as [->|i_j].
    by rewrite insert_delete_insert.
  by rewrite insert_commute // insert_delete_insert insert_commute //.
Qed.

Lemma binder_delete_commute {A} (m : gmap string A) i j :
  binder_delete i (binder_delete j m) =
  binder_delete j (binder_delete i m).
Proof. case: i j => [|i] [|j] //=; exact: delete_commute. Qed.

Definition nondet_nat_loop : val := rec: "loop" "n" :=
  if: nondet_bool #() then "n" else "loop" ("n" + #1).

Definition nondet_nat : val := λ: <>, nondet_nat_loop #0.

Definition nondet_int : val := λ: <>,
  let: "n" := nondet_nat #() in
  if: nondet_bool #() then "n" else - "n".

Section NonDetProofs.

Context `{!heapGS Σ}.

Implicit Types E : coPset.
Implicit Types v : val.
Implicit Types Ψ : val → iProp Σ.

Lemma wp_nondet_nat_loop Ψ (m : nat) :
  (∀ n : nat, Ψ #n) ⊢
  WP nondet_nat_loop #m {{ Ψ }}.
Proof.
iIntros "post"; iLöb as "IH" forall (m); wp_rec.
wp_apply nondet_bool_spec => //.
iIntros "%b _"; case: b; wp_if; first by iApply "post".
wp_pures. have -> : (m + 1)%Z = (m + 1)%nat by lia.
by iApply "IH".
Qed.

Lemma wp_nondet_nat Ψ :
  (∀ n : nat, Ψ #n) ⊢
  WP nondet_nat #() {{ Ψ }}.
Proof.
iIntros "post". wp_lam. by wp_apply (wp_nondet_nat_loop _ 0).
Qed.

Lemma wp_nondet_int Ψ :
  (∀ n : Z, Ψ #n) ⊢
  WP nondet_int #() {{ Ψ }}.
Proof.
iIntros "post"; rewrite /nondet_int; wp_pures.
wp_apply wp_nondet_nat. iIntros "%n"; wp_pures.
wp_apply nondet_bool_spec => //. iIntros "%b _".
case: b; wp_if; first by iApply "post".
by wp_pures; iApply "post".
Qed.

End NonDetProofs.
