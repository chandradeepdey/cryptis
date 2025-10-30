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

Context `{!heapGpreS Σ, !Repr A, !relocG Σ}.

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

Lemma tp_scan_list `{Repr A} E j φ ψ (f : val) (l : list A) :
  nclose specN ⊆ E →
  □ (∀ j (x : A), ψ NONEV ∗ φ x ∗
        refines_right j (f (repr x)) ={E}=∗
      ∃ (ov : option val), ψ (repr ov) ∗ refines_right j (repr ov)) -∗
  ψ NONEV ∗ ([∗ list] x ∈ l, φ x) ∗
    refines_right j (scan_list f (repr l)) ={E}=∗
  ∃ (ov : option val), ψ (repr ov) ∗ refines_right j (repr ov).
Proof.
move=> HE.
elim: l => [|h t IHt] /=; rewrite repr_list_unseal /=;
iIntros "#Hf (Hψ & Hφ & Hj)"; tp_rec j; tp_pures j;
  first by iExists None; iFrame.
iDestruct "Hφ" as "[Hφ_h Hφ_t]".
tp_bind j (f _).
rewrite refines_right_bind.
iPoseProof ("Hf" with "[Hψ Hφ_h Hj]") as ">(%r & Hψ & Hj)";
  first by iFrame.
case: r => [r|]; tp_pures j.
all: rewrite -refines_right_bind /=; tp_pures j.
by iExists (Some r); iFrame.
iPoseProof (IHt with "Hf [Hψ Hφ_t Hj]") as ">(%r & Hψ & Hj)";
  first by rewrite /= repr_list_unseal; iFrame.
by iFrame.
Qed.

Lemma tp_find_list E j (f : A → bool) (fimpl : val) (l : list A) :
  nclose specN ⊆ E →
  (∀ j (x : A), refines_right j (fimpl (repr x)) ={E}=∗
    refines_right j #(f x)) →
  refines_right j (find_list fimpl (repr l)) ={E}=∗
    refines_right j (repr (find f l)).
Proof.
move=> HE.
rewrite repr_list_unseal /=.
elim: l => [|h t IHt] /=;
iIntros "%Hf"; iIntros "Hj"; tp_rec j; tp_pures j; eauto.
tp_bind j (fimpl _).
rewrite refines_right_bind.
iPoseProof (Hf with "Hj") as ">Hj".
rewrite -refines_right_bind.
case: (f h) => // /=; tp_pures j => //.
iPoseProof (IHt with "Hj") as "Hj" => //.
Qed.

Lemma tp_filter_list E j (f : A → bool) (fimpl : val) (l : list A) :
  nclose specN ⊆ E →
  (∀ j (x : A), refines_right j (fimpl (repr x)) ={E}=∗
    refines_right j #(f x)) →
  refines_right j (filter_list fimpl (repr l)) ={E}=∗
    refines_right j (repr (List.filter f l)).
Proof.
move=> HE.
rewrite repr_list_unseal /=.
elim: l j => [|h t IHt] j /=;
iIntros "%Hf"; iIntros "Hj"; tp_rec j; tp_pures j; eauto.
tp_bind j (filter_list _ _).
rewrite refines_right_bind.
iPoseProof (IHt with "Hj") as ">Hj"; eauto.
rewrite -refines_right_bind /=.
tp_pures j.
tp_bind j (fimpl _).
rewrite refines_right_bind.
iPoseProof (Hf with "Hj") as ">Hj".
rewrite -refines_right_bind /=.
case : (f h) => // /=; tp_pures j; done.
Qed.

End ListLemmas.

Section DoUntil.

Context `{!relocG Σ}.

Lemma rel_do_until (f f' : val) φ Ψ :
  □ (φ -∗ REL f' #() << f #() : (fun o1 o2 =>
    ⌜o1 = NONEV⌝ ∗ ⌜o2 = NONEV⌝ ∗ φ ∨
    ∃ (v v' : val), ⌜o1 = SOMEV v⌝ ∗ ⌜o2 = SOMEV v'⌝ ∗
    Ψ v v')) -∗
  φ -∗
  REL do_until f' << do_until f : Ψ.
Proof.
iIntros "#Hf Hφ". iLöb as "IH".
rel_rec_l; rel_rec_r.
rel_bind_l (f' _); rel_bind_r (f _).
iApply (refines_bind with "[Hφ] []").
by iApply "Hf".
iIntros (v v') "Hv" => /=.
iDestruct "Hv" as "[(-> & -> & Hφ)| (%v1 & %v2 & -> & -> & HΨ)]";
rel_pures_l; rel_pures_r; first by iApply "IH".
rel_values.
Qed.

Lemma rel_do_until' (f f' : val) Ψ :
  □ (REL f' #() << f #() : (fun o1 o2 =>
    ⌜o1 = NONEV⌝ ∗ ⌜o2 = NONEV⌝ ∨
    ∃ (v v' : val), ⌜o1 = SOMEV v⌝ ∗ ⌜o2 = SOMEV v'⌝ ∗
    Ψ v v')) -∗
  REL do_until f' << do_until f : Ψ.
Proof.
iIntros "#Hf".
iApply (rel_do_until _ _ True%I) => //.
iIntros "!> _".
iApply refines_wand => //.
iIntros (v v') "[(-> & ->)|(%v1 & %v2 & HΨ)]"; eauto.
Qed.

End DoUntil.

Section Ordered.

Import ssrbool seq ssreflect.order path deriving.instances.
Variable (d : Order.disp_t) (A : orderType d).
Context `{!Repr A, !relocG Σ}.
Import Order Order.POrderTheory Order.TotalTheory.
Implicit Types (x y z : A) (s : seqlexi_with d A).

Lemma tp_insert_sorted E j (f : val) (x : A) (l : list A) :
  nclose specN ⊆ E →
  is_true (sorted le l) →
  (∀ j (y z : A),
      refines_right j (f (repr y) (repr z)) ={E}=∗
        refines_right j #(le y z)) →
  refines_right j (insert_sorted f (repr x) (repr l)) ={E}=∗
    refines_right j (repr (sort le (x :: l))).
Proof.
move=> HE.
rewrite repr_list_unseal => sorted_l Hf.
elim: l sorted_l j => //= [|y l IH] path_l j; iIntros "Hj";
tp_rec j => /=; tp_pures j => //;
move/(_ (path_sorted path_l)) in IH.
tp_bind j (f _ _).
rewrite refines_right_bind.
iPoseProof (Hf with "Hj") as ">Hj".
rewrite -refines_right_bind /=.
have [le_xy|le_yx] := boolP (x <= y)%O; tp_pures j.
  by rewrite sort_le_id //= ?le_xy.
move: le_yx; rewrite -ltNge => /ltW le_yx.
tp_bind j (insert_sorted _ _ _).
rewrite refines_right_bind.
iPoseProof (IH with "Hj") as ">Hj".
rewrite -refines_right_bind /=.
tp_pures j.
suff -> : sort le [:: x, y & l] = y :: sort le (x :: l) by tp_pures j.
rewrite -[RHS]sort_le_id /=.
  apply/perm_sort_leP/perm_consP.
  exists 1, (l ++ [:: x])%SEQ.
  by rewrite /= perm_catC perm_sym /= perm_sort; split.
rewrite path_min_sorted ?sort_le_sorted // all_sort /= le_yx /=.
apply: order_path_min => //; apply: le_trans.
Qed.

Lemma tp_leq_list E j (feq : val) (fle : val) s1 s2 :
  nclose specN ⊆ E →
  (∀ j x1 x2,
      refines_right j (feq (repr x1) (repr x2)) ={E}=∗
        refines_right j #(eqtype.eq_op x1 x2)) →
  (∀ j x1 x2,
      is_true (x1 \in s1) →
        refines_right j (fle (repr x1) (repr x2)) ={E}=∗
        refines_right j #(le x1 x2)) →
  refines_right j (leq_list feq fle (repr s1) (repr s2)) ={E}=∗
    refines_right j #(le s1 s2).
Proof.
move=> HE.
move=> feqP.
rewrite /= repr_list_unseal.
elim: s1 s2 => [|x1 s1 IH] [|x2 s2] fleP; iIntros "Hj";
  tp_rec j => /=; tp_pures j => //.
rewrite lexi_cons; tp_bind j (feq _ _).
rewrite refines_right_bind => /=.
iPoseProof (feqP with "Hj") as ">Hj".
case: (ltgtP x1 x2) => [l_x1x2|l_x2x1|<-] /=; tp_pures j.
all: simpl; set ctx := IfCtx _ _;
     rewrite -(refines_right_bind j [ctx] #_) => /=; tp_pures j.
- iPoseProof (fleP with "Hj") as ">Hj";
  rewrite ?inE ?eqtype.eqxx // ltW //.
- iPoseProof (fleP with "Hj") as ">Hj";
  rewrite ?inE ?eqtype.eqxx // leNgt l_x2x1 //.
- iPoseProof (IH with "Hj") as ">Hj"=> // j' x1' ? x1'_in;
  apply fleP; rewrite inE x1'_in orbT //.
Qed.

End Ordered.

Section NonDetProofs.

Context `{!relocG Σ}.

Implicit Types E : coPset.
Implicit Types v : val.
Implicit Types Ψ : val → iProp Σ.

Lemma tp_nondet_bool E j (b : bool) :
  nclose specN ⊆ E →
  refines_right j (nondet_bool #()) ={E}=∗
  refines_right j #b.
Proof.
move=> HE.
iIntros "Hj".
tp_rec j. tp_alloc j as l "Hl".
tp_pures j.
tp_bind j (Fork _).
rewrite refines_right_bind.
set j' := (RefId _ _).
tp_fork j' => /=.
rewrite -refines_right_bind => /=.
clear j'.
tp_pures j.
iIntros "%j' Hj'".
case : b; last tp_store j'.
all: tp_load j=> //.
Qed.

Lemma tp_nondet_nat_loop E j (m : nat) (n : nat) :
  nclose specN ⊆ E →
  refines_right j (nondet_nat_loop #m) ={E}=∗
  refines_right j #(n + m)%nat.
Proof.
move=> HE.
elim : n m j => [|n' IHn'] m j; iIntros "Hj";
tp_rec j; tp_bind j (nondet_bool _); rewrite refines_right_bind;
  set j' := RefId _ _.
- iPoseProof ((tp_nondet_bool _ _ true HE) with "Hj") as ">Hj".
  rewrite -refines_right_bind => /=.
  by tp_pures j.
- iPoseProof ((tp_nondet_bool _ _ false HE) with "Hj") as ">Hj".
  rewrite -refines_right_bind => /=.
  tp_pures j.
  have ->: (m + 1)%Z = (m + 1)%nat by lia.
  iPoseProof (IHn' with "Hj") as ">Hj".
  have ->: (n' + (m + 1))%nat = S (n' + m) by lia.
  done.
Qed.

Lemma tp_nondet_nat E j (n: nat) :
  nclose specN ⊆ E →
  refines_right j (nondet_nat #()) ={E}=∗
  refines_right j #n.
Proof.
move=> HE.
iIntros "Hj". tp_lam j.
iPoseProof (tp_nondet_nat_loop _ _ 0 n HE with "Hj") as ">Hj".
have ->: (n + 0)%nat = n by lia.
done.
Qed.

Lemma tp_nondet_int E j (n : Z) :
  nclose specN ⊆ E →
  refines_right j (nondet_int #()) ={E}=∗
  refines_right j #n.
Proof.
move=> HE.
iIntros "Hj"; rewrite /nondet_int; tp_pures j.
tp_bind j (nondet_nat _).
rewrite refines_right_bind.
set j' := RefId _ _.
pose n' := if (0 <=? n)%Z then Z.to_nat n else Z.to_nat (-n).
iPoseProof (tp_nondet_nat _ _ n' HE with "Hj") as ">Hj".
rewrite -refines_right_bind => /=.
clear j'.
tp_pures j.
tp_bind j (nondet_bool _).
rewrite refines_right_bind.
set j' := RefId _ _.
iPoseProof (tp_nondet_bool _ _ (0 <=? n)%Z HE with "Hj") as ">Hj".
rewrite -refines_right_bind => /=.
clear j'.
case Hn: (0 <=? n)%Z in n' *; tp_pures j.
- by have ->: n = n' by lia.
- by have ->: n = (- n')%Z by lia.
Qed.

End NonDetProofs.
