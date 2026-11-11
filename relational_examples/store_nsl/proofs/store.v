(** * The store of the NSL store case study

The left run stores [ops] and the right run [ops'], a permutation of [ops]
with distinct keys; both then load [k].  The [n]-th request of the client
is the [n]-th store of each list, or the load once the stores are done.
Every reply is the same integer in both runs.

After [r] requests, the server holds the database of the first [r] stores
of each list.  At the load, each run holds the database of all its stores,
and these give the same value for every key. *)

From reloc Require Import reloc.
From cryptis Require Import lib cryptis.
From cryptis.lib Require Import avl.
From cryptis.hyper.lib Require Import avl.
From cryptis.hyper.core Require Import minted_spec public.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples.store_nsl Require Import impl facts.
From cryptis.hyper.examples.store_nsl.proofs Require Import onesided conn rpc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition store_body (o : Z * Z) : term :=
  Spec.tag (Tag (storeN.@"store")) (Spec.of_list [TInt o.1; TInt o.2]).

Definition load_body (k : Z) : term :=
  Spec.tag (Tag (storeN.@"load")) (TInt k).

Definition store_msg (ops ops' : list (Z * Z)) (k rl : Z) (n : nat) (p p' : term) : Prop :=
  if decide (rl = 0%Z) then
    (∃ o o', ops !! n = Some o ∧ ops' !! n = Some o' ∧
             p = store_body o ∧ p' = store_body o') ∨
    (n = length ops ∧ p = load_body k ∧ p' = load_body k)
  else ∃ z, p = TInt z ∧ p' = TInt z.

Lemma handle_model_store db o :
  handle_model db (store_body o) = Some (TInt 0, AVL.insert o.1 o.2 db).
Proof. by rewrite /handle_model /store_body Spec.tagK /handle_store_model Spec.of_listK. Qed.

Lemma handle_model_load db k :
  handle_model db (load_body k) = Some (TInt (default 0%Z (AVL.lookup k db)), db).
Proof.
rewrite /handle_model /load_body Spec.untag_tag_ne ?Spec.tagK //.
move=> /Tag_inj e.
have Hd : (↑storeN.@"store" : coPset) ## ↑storeN.@"load" by solve_ndisj.
rewrite e in Hd. have := nclose_non_empty (storeN.@"load"). set_solver.
Qed.

Lemma db_of_take_S ops r o :
  ops !! r = Some o →
  db_of (take (S r) ops) = AVL.insert o.1 o.2 (db_of (take r ops)).
Proof. move=> Hr. by rewrite (take_S_r _ _ _ Hr) /db_of foldl_app. Qed.

Section Store.

Context `{!relocG Σ, !public_relGS Σ, !connGS Σ}.
Abbreviation iProp := (iProp Σ).

Variable γ : conn_names.
Variable sess : senc_key → senc_key → iProp.
Variable free : iProp.
Context `{!∀ k k', Persistent (sess k k'), !∀ k k', Timeless (sess k k'), !Timeless free}.
Hypothesis sess_agree : ∀ k1 k1' k2 k2',
  sess k1 k1' -∗ sess k2 k2' -∗ ⌜k1 = k2 ∧ k1' = k2'⌝.
Hypothesis free_sess : ∀ k k', free -∗ sess k k' -∗ False.

Variables (ops ops' : list (Z * Z)) (k : Z).
Hypothesis ops_nodup : NoDup ops.*1.
Hypothesis ops_perm : ops ≡ₚ ops'.

Definition store_Φ rl n p p' : iProp := ⌜store_msg ops ops' k rl n p p'⌝.

Abbreviation handle := (conn_handle γ sess).
Abbreviation ctx := (conn_ctx γ sess free store_Φ).

Lemma conn_payload_pair (o o' : Z * Z) :
  ⊢ conn_payload (Spec.of_list [TInt o.1; TInt o.2]) (Spec.of_list [TInt o'.1; TInt o'.2]).
Proof.
rewrite /conn_payload minted_of_list minted_spec_of_list /= !minted_TInt !minted_spec_TInt.
rewrite [Spec.of_list]unlock /= !(nonces_of_termE' (TPair _ _)).
rewrite !(nonces_of_termE' (TInt _)) !left_id_L.
by iSplit; [|iSplit; [|iSplit]].
Qed.

Definition server_inv n r (st st' : val) : iProp :=
  ⌜n = r⌝ ∗ is_avl st (db_of (take r ops)) ∗
  is_avl_spec st' (db_of (take r ops')).

Lemma store_handle_refinement n r st st' p p' :
  server_inv n r st st' -∗ store_Φ 0 r p p' -∗
  REL store_handle st p << store_handle st' p' : λ v v',
    ((⌜v = NONEV ∧ v' = NONEV⌝ ∗ server_inv n (S r) st st') ∨
     (∃ (q q' : term) st2 st2',
         ⌜v = SOMEV (q : val, st2)%V ∧ v' = SOMEV (q' : val, st2')%V⌝ ∗
         conn_payload q q' ∗ store_Φ 1 n q q' ∗ server_inv (S n) (S r) st2 st2'))%I.
Proof.
iIntros "(-> & Hdb & Hdb') %Hmsg". move: Hmsg. rewrite /store_msg. case: decide => // _.
have Hlen := Permutation_length ops_perm.
case=> [[o [o' [Ho [Ho' [-> ->]]]]]|[-> [-> ->]]].
- rel_apply_l (refines_store_handle_l with "Hdb"). iIntros "Hdb".
  rel_apply_r (refines_store_handle_r with "Hdb'"). iIntros "Hdb'".
  rewrite /handle_db !handle_model_store /=. rel_values. iModIntro. iRight.
  iExists (TInt 0), (TInt 0), _, _. iSplit; first done.
  iSplit; first by iApply conn_payload_TInt.
  iSplit; first by iPureIntro; exists 0%Z.
  rewrite /server_inv (db_of_take_S Ho) (db_of_take_S Ho'). by iFrame.
- rel_apply_l (refines_store_handle_l with "Hdb"). iIntros "Hdb".
  rel_apply_r (refines_store_handle_r with "Hdb'"). iIntros "Hdb'".
  rewrite /handle_db !handle_model_load /=.
  rewrite !take_ge; try lia.
  rewrite (lookup_db_of_perm k ops_nodup ops_perm).
  rel_values. iModIntro. iRight.
  iExists _, _, _, _. iSplit; first done.
  iSplit; first by iApply conn_payload_TInt.
  iSplit; first by iPureIntro; eexists.
  rewrite /server_inv !take_ge; try lia. by iFrame.
Qed.

Lemma store_all_refinement cs cs' i :
  i ≤ length ops →
  cryptis_rel_ctx -∗ ctx -∗ handle 0 cs cs' i i -∗
  REL store_all cs (repr (map op_val (drop i ops))) <<
      store_all cs' (repr (map op_val (drop i ops'))) :
    λ v v', (⌜v = #() ∧ v' = #()⌝ ∗ handle 0 cs cs' (length ops) (length ops))%I.
Proof.
have Hlen := Permutation_length ops_perm.
iIntros (Hi) "#Hctx #Hinv". iLöb as "IH" forall (i Hi). iIntros "Hh".
destruct (ops !! i) as [o|] eqn:Ho; last first.
{ have Hi' : i = length ops by move/lookup_ge_None: Ho; lia.
  rewrite !drop_ge; try lia. rewrite !repr_listE /=.
  rel_rec_l. rel_rec_r. rel_pures. rel_values. iModIntro. iSplit; first done.
  by rewrite -Hi'. }
have [o' Ho'] : is_Some (ops' !! i).
{ apply: lookup_lt_is_Some_2. have := lookup_lt_Some _ _ _ Ho. lia. }
rewrite (drop_S _ _ _ Ho) (drop_S _ _ _ Ho') !repr_listE /=.
rel_rec_l. rel_rec_r. rel_pures. rewrite /store_store. rel_prims.
rel_apply (rpc_call_refinement γ sess_agree free_sess 0 cs cs' i i (storeN.@"store")
             (Spec.of_list [TInt o.1; TInt o.2]) (Spec.of_list [TInt o'.1; TInt o'.2])
             with "Hctx Hinv Hh [] []").
- by iApply conn_payload_pair.
- iPureIntro. rewrite /store_msg. case: decide => // _. left. by exists o, o'.
iIntros (? ?) "(%p & %p' & [-> ->] & Hh & _)". rel_pures.
iApply ("IH" $! (S i) with "[] Hh"). iPureIntro. have := lookup_lt_Some _ _ _ Ho. lia.
Qed.

End Store.
