From stdpp Require Import base countable gmap.
From iris.heap_lang Require Import lang notation proofmode.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.algebra Require Import gmap gset auth reservation_map.
From iris.base_logic Require Import gen_heap invariants.
From mathcomp Require ssrbool order path.
From deriving Require deriving.
From cryptis Require Export mathcomp_compat lib.
From cryptis Require Import lib.adequacy.
From reloc Require Import reloc.

Lemma pure_twp_tp Σ `{!heapGpreS Σ} E j e (v: val) :
  pure_expr e →
  (∀ `{!heapGS Σ}, ⊢ inv_heap_inv -∗ WP e [{ v', ⌜v' = v⌝ }]) →
  ∀ `{!relocG Σ},
  nclose specN ⊆ E →
  refines_right j e ={E}=∗
  refines_right j v.
Proof.
  move=> Hpure Hinv HE.
  have H := heap_twp_pure_exec _ _ _ Hpure Hinv.
  apply H in heapGpreS0 as (v' & Hev' & ->).
  clear Hinv H.
  move=> ?.
  rewrite /refines_right.
  apply rtc_nsteps in Hev' as (n & Hev').
  have H2: PureExec True n e v by rewrite /PureExec //.
  iApply step_pure=> //.
Qed.

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
  refines_right j (repr x :: repr xs) -∗
  |={E}=> refines_right j (repr (x :: xs)).
Proof.
intros HE.
by rewrite /= repr_list_unseal; iIntros "post"; rewrite /CONS; tp_pures j.
Qed.

Lemma tp_list_match_aux E j (vs : list A) evs vars k :
  nclose specN ⊆ E →
  elements (free_vars k) ## vars →
  refines_right j (list_match_aux vars evs k) -∗
  (∀ j', refines_right j' evs ={E}=∗ refines_right j' (repr_list vs)) -∗
  |={E}=>
    let v := if decide (length vars = length vs) then
               fill (napp vars (map repr vs)) k
             else NONEV in
    refines_right j v.
Proof.
move => HE.
rewrite repr_list_unseal.
elim: vars vs => [|var vars IH] [|v vs] /= in evs k *; iIntros (dis) "pS evs".
- tp_bind j evs; rewrite refines_right_bind.
  iPoseProof ("evs" with "pS") as ">evs".
  rewrite -refines_right_bind /=. by tp_pures j.
- tp_bind j evs; rewrite refines_right_bind.
  iPoseProof ("evs" with "pS") as ">evs".
  rewrite -refines_right_bind /=. by tp_pures j.
- tp_bind j evs; rewrite refines_right_bind.
  iPoseProof ("evs" with "pS") as ">evs".
  rewrite -refines_right_bind /=. by tp_pures j.
tp_bind j evs; rewrite refines_right_bind.
iPoseProof ("evs" with "pS") as ">evs".
rewrite -refines_right_bind /=. tp_pures j.
rewrite subst_list_match_aux /= decide_True //.
assert (fresh_var : var ∉ free_vars k) by set_solver.
assert (dis' : elements (free_vars k) ## vars) by set_solver.
have {}IH := IH vs. iPoseProof (IH with "evs []") as ">IH".
- case: decide => _ //=.
  rewrite free_vars_subst decide_True //=.
  set_solver.
- iIntros "%j' pS". by tp_pures j'.
case: (decide (length vars = length vs)) => [eq_l|neq_l]; last first.
  rewrite decide_False //=; congruence.
rewrite eq_l (decide_True (P := S _ = _)) //.
case: decide => [//|nin_vars] /=.
rewrite decide_True //= subst_free_vars //.
tp_bind j (Fst _). rewrite refines_right_bind.
set j' := RefId _ _. tp_pures j'. by rewrite /j' -refines_right_bind /=.
Qed.

Lemma tp_close_vars E j vars vs k :
  nclose specN ⊆ E →
  length vars = length vs →
  refines_right j (fill (napp vars vs) (close_vars vars k)) ={E}=∗
  refines_right j (nsubst vars vs k).
Proof.
move=> HE Hlen. iIntros "Hj".
elim: vars vs => [|var vars IH] [|v vs] //= in k Hlen *.
- by tp_pures j.
- case: Hlen => Hlen;
  case: decide => [in_vars|nin_vars].
  rewrite subst_free_vars; first by apply IH.
  rewrite free_vars_nsubst // elem_of_difference.
  case => _; rewrite elem_of_union_list.
  by apply; exists {[var]}; split; try set_solver.
rewrite /=.
rewrite refines_right_bind.
set j' := RefId _ _.
tp_pures j'.
rewrite subst_nsubst_nin //.
rewrite -refines_right_bind.
rewrite subst_close_vars //.
by apply IH.
Qed.

Lemma tp_list_match E j vars (vs : list A) k :
  nclose specN ⊆ E →
  refines_right j (list_match vars (repr vs) k) ={E}=∗
  let v := if decide (length vars = length vs) then
              nsubst vars (map repr vs) k
           else NONEV in
  refines_right j v.
Proof.
move=> HE.
rewrite unlock; iIntros "Hj".
assert (disj : elements (free_vars (close_vars vars k)) ## vars).
  elim: vars => [|var vars IH] /= in k *; try case: decide => ?; set_solver.
iPoseProof (tp_list_match_aux _ _ _ _ _ _ HE disj with "Hj []") as ">Hj".
  by iIntros (?) "?".
case: decide => ? //.
iApply (tp_close_vars with "Hj") => //.
by rewrite length_map.
Qed.

Lemma tp_eq_list `{EqDecision A} E j (f : val) (l1 l2 : list A) :
  nclose specN ⊆ E →
  (∀ (x1 x2 : A) j',
      x1 ∈ l1 →
      refines_right j' (f (repr x1) (repr x2)) -∗
      |={E}=> refines_right j' #(bool_decide (x1 = x2))) →
  refines_right j (eq_list f (repr l1) (repr l2)) -∗
  |={E}=> refines_right j #(bool_decide (l1 = l2)).
Proof.
move=> HE Hf.
rewrite repr_list_unseal /=.
elim: l1 l2 => [|x1 l1 IH] [|x2 l2] /= in Hf *; iIntros "Hj";
  tp_rec j; tp_pures j; do 1?by iApply "Hj".
tp_bind j (f _ _).
rewrite refines_right_bind.
iPoseProof (Hf with "Hj") as ">Hj"; try set_solver.
rewrite -refines_right_bind /=.
case: (bool_decide_reflect (x1 = x2)) => [->|n_x1x2]; tp_pures j; last first.
  rewrite bool_decide_decide decide_False //; congruence.
iPoseProof (IH with "Hj") as ">Hj"; first by move=> *; iApply Hf; set_solver.
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

Context `{!relocG Σ}.

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

Section Ordered.

Import ssrbool seq ssreflect.order path deriving.instances.
Variable (d : Order.disp_t) (A : orderType d).
Context `{!Repr A, !relocG Σ}.
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

Section NonDetProofs.

Context `{!relocG Σ}.

Implicit Types E : coPset.
Implicit Types v : val.
Implicit Types Ψ : val → iProp Σ.

Lemma tp_nondet_nat_loop E j Ψ (m : nat) :
  nclose specN ⊆ E →
  (∀ n : nat, Ψ #n) -∗
  refines_right j (nondet_nat_loop #m) -∗
  |={E}=> ∃ v, refines_right j v ∗ Ψ v.
Proof.
Admitted.

Lemma tp_nondet_nat E j Ψ :
  nclose specN ⊆ E →
  (∀ n : nat, Ψ #n) -∗
  refines_right j (nondet_nat #()) -∗
  |={E}=> ∃ v, refines_right j v ∗ Ψ v.
Proof.
iIntros "%HE post Hj". tp_lam j.
iPoseProof (tp_nondet_nat_loop _ _ Ψ 0 HE with "post Hj") as ">[%v [Hj Hv]]".
by iFrame.
Qed.

Lemma wp_nondet_int E j Ψ :
  nclose specN ⊆ E →
  (∀ n : Z, Ψ #n) -∗
  refines_right j (nondet_int #()) -∗
  |={E}=> ∃ v, refines_right j v ∗ Ψ v.
Proof.
iIntros "%HE post Hj"; rewrite /nondet_int; tp_pures j.
iApply (tp_nondet_nat _ _ _ HE with "[post]"); first auto.
Admitted.
(* iIntros "%n"; wp_pures.
wp_apply nondet_bool_spec => //. iIntros "%b _".
case: b; wp_if; first by iApply "post".
by wp_pures; iApply "post".
Qed. *)

End NonDetProofs.
