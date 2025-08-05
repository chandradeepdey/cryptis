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
Admitted.

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

Lemma tp_close_vars E j vars vs k Ψ :
  nclose specN ⊆ E →
  length vars = length vs →
  (forall j, nclose specN ⊆ E → refines_right j (nsubst vars vs k) -∗
    |={E}=> ∃ v, refines_right j v ∗ Ψ v) →
  refines_right j (fill (napp vars vs) (close_vars vars k)) -∗
  |={E}=> ∃ v, refines_right j v ∗ Ψ v.
Proof.
move=> HE Hlen Hyp.
iIntros "Hj".
Admitted.
(* elim: vars vs => [|var vars IH] [|v vs] //= in k Ψ *.
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
Qed. *)

(* Lemma tp_list_match E j vars (vs : list A) k Ψ :
  nclose specN ⊆ E →
  (forall j, nclose specN ⊆ E →
  if decide (length vars = length vs) then
     (refines_right j (nsubst vars (map repr vs) k) -∗
     |={E}=> ∃ v, refines_right j v ∗ Ψ v)
   else Ψ NONEV) -∗
  refines_right j (list_match vars (repr vs) k) -∗
  |={E}=> ∃ v, refines_right j v ∗ Ψ v.
Proof.
rewrite unlock; iIntros "post".
assert (disj : elements (free_vars (close_vars vars k)) ## vars).
  elim: vars => [|var vars IH] /= in k *; try case: decide => ?; set_solver.
iApply (wp_list_match_aux E vs (repr vs)); eauto.
  by iIntros (?) "?"; iApply wp_value.
case: decide => ? //.
iApply (wp_close_vars with "post").
by rewrite length_map.
Qed. *)

Lemma tp_eq_list `{EqDecision A} E j (f : val) (l1 l2 : list A) Φ :
  (∀ (x1 x2 : A) Ψ j,
      nclose specN ⊆ E →
      x1 ∈ l1 →
      Ψ (of_val #(bool_decide (x1 = x2))) → (* of_val ?? *)
      refines_right j (f (repr x1) (repr x2)) -∗
      |={E}=> ∃ v, refines_right j v ∗ Ψ v) →
  Φ #(bool_decide (l1 = l2)) -∗
  refines_right j (eq_list f (repr l1) (repr l2)) -∗
  |={E}=> ∃ v, refines_right j v ∗ Φ v.
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

Context `{!relocG Σ}.
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
iIntros "%n"; wp_pures.
wp_apply nondet_bool_spec => //. iIntros "%b _".
case: b; wp_if; first by iApply "post".
by wp_pures; iApply "post".
Qed.

End NonDetProofs.
