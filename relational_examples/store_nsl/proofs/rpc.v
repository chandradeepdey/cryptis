(** * Remote calls of the NSL store case study

A call sends a request on a connection and waits for the reply.  The server
answers the requests of a connection one at a time.  The specs carry the
facts of [conn.v]: a request is the [n]-th pair that role 0 sends, and a
reply the [n]-th pair that role 1 sends.  The server keeps a relation [I]
between the states of the two runs, indexed by the number of replies sent
and of requests received. *)

From reloc Require Import reloc.
From cryptis Require Import cryptis.
From cryptis.hyper.core Require Import public.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples.store_nsl Require Import impl.
From cryptis.hyper.examples.store_nsl.proofs Require Import conn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RPC.

Context `{!relocG Σ, !publicGS Σ, !connGS Σ}.
Abbreviation iProp := (iProp Σ).

Variable γ : conn_names.
Variable sess : senc_key → senc_key → iProp.
Variable free : iProp.
Variable Φ : Z → nat → term → term → iProp.
Context `{!∀ k k', Persistent (sess k k'), !∀ k k', Timeless (sess k k'), !Timeless free}.
Context `{!∀ rl n t t', Persistent (Φ rl n t t'), !∀ rl n t t', Timeless (Φ rl n t t')}.
Hypothesis sess_agree : ∀ k1 k1' k2 k2',
  sess k1 k1' -∗ sess k2 k2' -∗ ⌜k1 = k2 ∧ k1' = k2'⌝.
Hypothesis free_sess : ∀ k k', free -∗ sess k k' -∗ False.

Abbreviation handle := (conn_handle γ sess).
Abbreviation ctx := (conn_ctx γ sess free Φ).

Lemma rpc_call_refinement rl cs cs' n r (N : namespace) t t' :
  hypercryptis_ctx -∗ ctx -∗ handle rl cs cs' n r -∗
  conn_payload t t' -∗ Φ rl n (Spec.tag (Tag N) t) (Spec.tag (Tag N) t') -∗
  REL rpc_call cs (Tag N) t << rpc_call cs' (Tag N) t' :
    λ v v', (∃ p p' : term, ⌜v = p ∧ v' = p'⌝ ∗
      handle rl cs cs' (S n) (S r) ∗ Φ (1 - rl) r p p')%I.
Proof.
iIntros "#Hctx #Hinv Hh #Ht #HΦ". rewrite /rpc_call. rel_prims.
rel_apply (conn_send_refinement γ sess_agree free_sess with "Hctx Hinv Hh [] HΦ").
{ by iApply conn_payload_tag. }
iIntros (? ?) "[[-> ->] Hh]". rel_pures.
by iApply (conn_recv_refinement γ sess_agree free_sess with "Hctx Hinv Hh").
Qed.

Lemma rpc_server_refinement (I : nat → nat → val → val → iProp) (f f' : val) cs cs' n r st st' :
  hypercryptis_ctx -∗ ctx -∗
  □ (∀ n r st st' p p', I n r st st' -∗ Φ 0 r p p' -∗
      REL f st p << f' st' p' : λ v v',
        ((⌜v = NONEV ∧ v' = NONEV⌝ ∗ I n (S r) st st') ∨
         (∃ (q q' : term) st2 st2',
             ⌜v = SOMEV (q : val, st2)%V ∧ v' = SOMEV (q' : val, st2')%V⌝ ∗
             conn_payload q q' ∗ Φ 1 n q q' ∗ I (S n) (S r) st2 st2'))%I) -∗
  handle 1 cs cs' n r -∗ I n r st st' -∗
  REL rpc_server cs f st << rpc_server cs' f' st' : ().
Proof.
iIntros "#Hctx #Hinv #Hf". iLöb as "IH" forall (n r st st').
iIntros "Hh HI". rel_rec_l. rel_rec_r. rel_pures.
rel_apply (conn_recv_refinement γ sess_agree free_sess with "Hctx Hinv Hh").
iIntros (? ?) "(%p & %p' & [-> ->] & Hh & #HΦ)" => /=. rel_pures.
rel_bind_l (f st p). rel_bind_r (f' st' p').
iApply (refines_bind with "[HI]"); first by iApply ("Hf" with "HI HΦ").
iIntros (v v') "[[[-> ->] HI]|(%q & %q' & %st2 & %st2' & [-> ->] & #Hq & #HΦq & HI)]" => /=.
{ rel_pures. by iApply ("IH" with "Hh HI"). }
rel_pures.
rel_apply (conn_send_refinement γ sess_agree free_sess with "Hctx Hinv Hh Hq HΦq").
iIntros (? ?) "[[-> ->] Hh]". rel_pures.
by iApply ("IH" with "Hh HI").
Qed.

End RPC.
