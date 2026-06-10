From reloc Require Import reloc.
From cryptis.lib Require Import repr list_match.

Section ListLemmas.

Context `{!Repr A, !Repr B, !relocG Σ}.

Implicit Types (x : A) (xs : list A).

Lemma tp_list_match_aux E j (vs : list A) evs vars k :
  ↑specN ⊆ E →
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
  ↑specN ⊆ E →
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
  ↑specN ⊆ E →
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

End ListLemmas.
