(** * Connections of the NSL store case study

A connection sends terms encrypted under a session key.  The client has
role 0 and the server role 1; each message carries the role of its sender
and its position among the messages of that role.

The invariant keeps, for each role, the list of the pairs of terms it has
sent, one term from each run.  The protocol on top of the connections says
what each pair means ([Φ rl n]: the [n]-th pair that role [rl] sends), and
the receiver of a message learns it.

Encrypting a message records its partner in the other run on the seed of the
session key.  The invariant keeps the seed's tokens for every message that is
not sent yet, so a message that decrypts under the key was sent by an honest
party: both runs decrypt it to a pair of the lists, or both fail to.

The invariant serves a single session, given by [sess].  Until the session
is known, it holds what recording the session takes ([free]).

- [State]: the invariant, what the parties know about the session key, and
  one end of a connection.
- [Send] and [Receive]: the specs of [conn_send] and [conn_recv]. *)

From mathcomp Require Import ssreflect.
From iris.base_logic.lib Require Import ghost_var.
From reloc Require Import reloc.
From cryptis Require Import lib cryptis primitives.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.lib Require Import list_spec list_match_spec.
From cryptis.hyper.core Require Import minted_spec term_meta_spec rel.
From cryptis.hyper.primitives Require Import simple_spec with_cryptis_spec.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples.store_nsl Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation connIN := (storeN.@"conn_inv").

Class connGS Σ := ConnGS {
  #[local] connGS_log :: ghost_varG Σ (list (term * term));
}.

Definition connΣ : gFunctors := #[ghost_varΣ (list (term * term))].

#[global] Instance subG_connGS Σ : subG connΣ Σ → connGS Σ.
Proof. solve_inG. Qed.

Record conn_names := ConnNames { conn_log0 : gname; conn_log1 : gname }.

Definition conn_body (rl : Z) (n : nat) (t : term) : term :=
  Spec.tag (Tag connN) (Spec.of_list [TInt rl; TInt n; t]).

Lemma conn_body_inj rl1 n1 t1 rl2 n2 t2 :
  conn_body rl1 n1 t1 = conn_body rl2 n2 t2 → rl1 = rl2 ∧ n1 = n2 ∧ t1 = t2.
Proof.
rewrite /conn_body => e.
by case: (inj2 Spec.tag _ _ _ _ e) => _ /Spec.of_list_inj [-> /Nat2Z.inj -> ->].
Qed.

Definition log_of (rl : Z) (L0 L1 : list (term * term)) :=
  if decide (rl = 0%Z) then L0 else L1.

Definition logged L0 L1 rl n t t' : Prop :=
  (rl = 0 ∨ rl = 1)%Z ∧ log_of rl L0 L1 !! n = Some (t, t').

Definition log_snoc rl (L0 L1 : list (term * term)) x :=
  (if decide (rl = 0%Z) then L0 ++ [x] else L0,
   if decide (rl = 0%Z) then L1 else L1 ++ [x]).

Lemma logged_snoc L0 L1 rl t t' rl2 n2 p p' :
  (rl = 0 ∨ rl = 1)%Z →
  logged (log_snoc rl L0 L1 (t, t')).1 (log_snoc rl L0 L1 (t, t')).2 rl2 n2 p p' ↔
  logged L0 L1 rl2 n2 p p' ∨
  (rl2 = rl ∧ n2 = length (log_of rl L0 L1) ∧ p = t ∧ p' = t').
Proof.
rewrite /logged /log_of /log_snoc => Hrl.
destruct Hrl as [->| ->]; destruct (decide (rl2 = 0%Z)) as [->|ne2] => /=.
all: rewrite ?lookup_snoc_Some; intuition (simplify_eq; eauto; try lia).
all: left; split; last done; exact: lookup_lt_Some.
Qed.

Arguments logged_snoc {L0 L1 rl t t' rl2 n2 p p'} Hrl.

Section Conn.

Context `{!relocG Σ, !public_relGS Σ, !connGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (k : senc_key) (t p u : term) (rl : Z) (n r : nat).

Variable γ : conn_names.
Variable sess : senc_key → senc_key → iProp.
Variable free : iProp.
Variable Φ : Z → nat → term → term → iProp.
Context `{!∀ k k', Persistent (sess k k'), !∀ k k', Timeless (sess k k'), !Timeless free}.
Context `{!∀ rl n t t', Persistent (Φ rl n t t'), !∀ rl n t t', Timeless (Φ rl n t t')}.
Hypothesis sess_agree : ∀ k1 k1' k2 k2',
  sess k1 k1' -∗ sess k2 k2' -∗ ⌜k1 = k2 ∧ k1' = k2'⌝.
Hypothesis free_sess : ∀ k k', free -∗ sess k k' -∗ False.

Section State.

Definition log_name rl : gname :=
  if decide (rl = 0%Z) then conn_log0 γ else conn_log1 γ.

(** What a sender holds before its first message, and what the invariant
    holds before the session starts. *)
Definition conn_start rl : iProp := ghost_var (log_name rl) (1/2) [].

Definition conn_fresh : iProp :=
  ghost_var (conn_log0 γ) (1/2) [] ∗ ghost_var (conn_log1 γ) (1/2) [].

(** What the invariant knows about a sent pair. *)
Definition sent_pair k k' rl n t t' : iProp :=
  sealed_under k k' (conn_body rl n t) (conn_body rl n t') ∗ Φ rl n t t'.

Definition conn_state k k' : iProp :=
  ∃ L0 L1 Ek Ek',
    ghost_var (conn_log0 γ) (1/2) L0 ∗ ghost_var (conn_log1 γ) (1/2) L1 ∗
    never_sealed_under (seed_of_senc_key k) (seed_of_senc_key k') Ek Ek' ∗
    ⌜∀ u, ↑seal_ns k u ⊆ Ek ∨
          ∃ rl n t t', logged L0 L1 rl n t t' ∧ u = conn_body rl n t⌝ ∗
    ⌜∀ u', ↑seal_ns k' u' ⊆ Ek' ∨
           ∃ rl n t t', logged L0 L1 rl n t t' ∧ u' = conn_body rl n t'⌝ ∗
    □ (∀ rl n t t', ⌜logged L0 L1 rl n t t'⌝ → sent_pair k k' rl n t t').

Definition conn_inv : iProp :=
  (free ∗ conn_fresh) ∨
  ∃ k k', sess k k' ∗ conn_state k k'.

Definition conn_ctx : iProp := inv connIN conn_inv.

(** What the parties of the session know about its key. *)
Definition conn_keys k k' : iProp :=
  sess k k' ∗ minted k ∗ minted_spec k' ∗
  secret_in_l (k : term) ∗ secret_in_r (k' : term) ∗
  secret_in_l (seed_of_senc_key k) ∗ secret_in_r (seed_of_senc_key k') ∗
  □ (PUB⟨seed_of_senc_key k, seed_of_senc_key k'⟩ → False).

#[global] Instance conn_keys_persistent k k' : Persistent (conn_keys k k').
Proof. apply _. Qed.

(** A pair of terms that a party may send.  The terms contain no nonces. *)
Definition conn_payload t t' : iProp :=
  minted t ∗ minted_spec t' ∗ ⌜nonces_of_term t = ∅⌝ ∗ ⌜nonces_of_term t' = ∅⌝.

#[global] Instance conn_payload_persistent t t' : Persistent (conn_payload t t').
Proof. apply _. Qed.

Lemma conn_payload_TInt z : ⊢ conn_payload (TInt z) (TInt z).
Proof.
rewrite /conn_payload minted_TInt minted_spec_TInt (nonces_of_termE' (TInt _)).
by iSplit; [|iSplit; [|iSplit]].
Qed.

Lemma conn_payload_tag (N : namespace) t t' :
  conn_payload t t' -∗ conn_payload (Spec.tag (Tag N) t) (Spec.tag (Tag N) t').
Proof.
iIntros "#(mt & mt' & %Ht & %Ht')". rewrite /conn_payload minted_tag minted_spec_tag.
iFrame "mt mt'". iPureIntro.
rewrite [Spec.tag]unlock [Tag]unlock !(nonces_of_termE' (TPair _ _)).
by rewrite !(nonces_of_termE' (TInt _)) Ht Ht' !left_id_L.
Qed.

(** One end of the connection in both runs, after [n] messages sent and [r]
    received. *)
Definition conn_handle rl (cs cs' : val) n r : iProp :=
  ∃ k k' (l1 l2 l1' l2' : loc) (c c' : val) L,
    ⌜cs = (#l1, #l2, (k : term), c, #rl)%V⌝ ∗
    ⌜cs' = (#l1', #l2', (k' : term), c', #rl)%V⌝ ∗
    ⌜(rl = 0 ∨ rl = 1)%Z⌝ ∗ ⌜length L = n⌝ ∗
    channel_rel c c' ∗ conn_keys k k' ∗
    l1 ↦ #n ∗ l2 ↦ #r ∗ l1' ↦ₛ #n ∗ l2' ↦ₛ #r ∗
    ghost_var (log_name rl) (1/2) L.

Lemma conn_state_init k k' :
  never_sealed_under (seed_of_senc_key k) (seed_of_senc_key k')
    (↑cryptisN.@"public_rel".@"seal") (↑cryptisN.@"public_rel".@"seal") -∗
  conn_fresh -∗ conn_state k k'.
Proof.
iIntros "ns [log0 log1]". iExists [], [], _, _. iFrame.
iSplit; first by iPureIntro => ?; left; apply nclose_subseteq.
iSplit; first by iPureIntro => ?; left; apply nclose_subseteq.
iIntros "!>" (rl n t t' [_ Hl]). rewrite /log_of in Hl. by case: decide Hl.
Qed.

Lemma rel_conn_new rl c c' k k' :
  (rl = 0 ∨ rl = 1)%Z →
  channel_rel c c' -∗ conn_keys k k' -∗ conn_start rl -∗
  REL conn_new c (k : term) #rl << conn_new c' (k' : term) #rl :
    λ cs cs', conn_handle rl cs cs' 0 0.
Proof.
iIntros (Hrl) "#Hc #Hk log". rewrite /conn_new. rel_pures.
rel_alloc_l l1 as "Hl1". rel_alloc_r l1' as "Hl1'". rel_pures.
rel_alloc_l l2 as "Hl2". rel_alloc_r l2' as "Hl2'". rel_pures.
rel_values. iModIntro. iExists k, k', l1, l2, l1', l2', c, c', [].
by iFrame "#∗".
Qed.

End State.

Section Send.

(** Access to the log of a role, which the invariant keeps as two ghost
    variables. *)
Lemma log_acc rl L0 L1 :
  (rl = 0 ∨ rl = 1)%Z →
  ghost_var (conn_log0 γ) (1/2) L0 -∗ ghost_var (conn_log1 γ) (1/2) L1 -∗
  ghost_var (log_name rl) (1/2) (log_of rl L0 L1) ∗
  (∀ x, ghost_var (log_name rl) (1/2) (log_of rl L0 L1 ++ [x]) -∗
    ghost_var (conn_log0 γ) (1/2) (log_snoc rl L0 L1 x).1 ∗
    ghost_var (conn_log1 γ) (1/2) (log_snoc rl L0 L1 x).2).
Proof.
rewrite /log_name /log_of /log_snoc => - [->| ->] /=; iIntros "log0 log1".
- iFrame "log0". iIntros (x) "log0". iFrame.
- iFrame "log1". iIntros (x) "log1". iFrame.
Qed.

Lemma conn_seal_send E rl L k k' t t' :
  ↑connIN ⊆ E →
  (rl = 0 ∨ rl = 1)%Z →
  conn_ctx -∗ conn_keys k k' -∗
  ghost_var (log_name rl) (1/2) L -∗
  minted t -∗ minted_spec t' -∗ Φ rl (length L) t t' ={E}=∗
  ghost_var (log_name rl) (1/2) (L ++ [(t, t')]) ∗
  PUB⟨Spec.enc k (Tag connN) (Spec.of_list [TInt rl; TInt (length L); t]),
      Spec.enc k' (Tag connN) (Spec.of_list [TInt rl; TInt (length L); t'])⟩.
Proof.
iIntros (HE Hrl) "#Hinv #(Hs & mk & mk' & sk & sk' & _ & _ & Hno) log #mt #mt' #HΦ".
iInv "Hinv" as "[>(Hfree & _ & _)|(%k0 & %k0' & >#Hs0 & >(%L0 & %L1 & %Ek & %Ek' & log0 & log1 & ns & %Hcl & %Hcl' & #Hsent))]".
{ by iDestruct (free_sess with "Hfree Hs") as %[]. }
iDestruct (sess_agree with "Hs Hs0") as %[<- <-].
iDestruct (log_acc L0 L1 Hrl with "log0 log1") as "[logi back]".
iDestruct (ghost_var_agree with "logi log") as %HL. subst L.
set n := length (log_of rl L0 L1).
assert (Hsub : ↑seal_ns k (conn_body rl n t) ⊆ Ek).
{ case: (Hcl (conn_body rl n t)) => [//|[rl2 [n2 [p [p' [[_ Hl] /conn_body_inj [? [? ?]]]]]]]].
  subst. by rewrite lookup_ge_None_2 in Hl. }
assert (Hsub' : ↑seal_ns k' (conn_body rl n t') ⊆ Ek').
{ case: (Hcl' (conn_body rl n t')) => [//|[rl2 [n2 [p [p' [[_ Hl] /conn_body_inj [? [? ?]]]]]]]].
  subst. by rewrite lookup_ge_None_2 in Hl. }
iMod (rel_senc (N:=connN) (t:=Spec.of_list [TInt rl; TInt n; t])
        (t':=Spec.of_list [TInt rl; TInt n; t']) Hsub Hsub'
        with "mk mk' [] [] [] [] ns") as "(#Hpub & #Hsu & ns)".
{ minted_simpl. rewrite !minted_TInt. by iFrame "#". }
{ minted_simpl. rewrite !minted_spec_TInt. by iFrame "#". }
{ iSplit; [by iApply secret_in_l_linked_in_l | by iApply secret_in_r_linked_in_r]. }
{ iIntros "!> #Hseed". by iDestruct ("Hno" with "Hseed") as "[]". }
iMod (ghost_var_update_halves (log_of rl L0 L1 ++ [(t, t')]) with "logi log") as "[logi log]".
iDestruct ("back" with "logi") as "[log0 log1]".
iModIntro. iSplitR "log"; last by iFrame "log Hpub".
iNext. iRight. iExists k, k'. iFrame "Hs". iExists _, _, _, _. iFrame "log0 log1 ns".
iSplit.
{ iPureIntro => u. case: (decide (u = conn_body rl n t)) => [->|ne].
  { right. exists rl, n, t, t'. split; last done. apply (logged_snoc Hrl). by right. }
  case: (Hcl u) => [sub|[rl2 [n2 [p [p' [Hl ->]]]]]].
  - left. apply subseteq_difference_r; last done.
    apply ndot_ne_disjoint. by move=> [= ?].
  - right. exists rl2, n2, p, p'. split; last done. apply (logged_snoc Hrl). by left. }
iSplit.
{ iPureIntro => u. case: (decide (u = conn_body rl n t')) => [->|ne].
  { right. exists rl, n, t, t'. split; last done. apply (logged_snoc Hrl). by right. }
  case: (Hcl' u) => [sub|[rl2 [n2 [p [p' [Hl ->]]]]]].
  - left. apply subseteq_difference_r; last done.
    apply ndot_ne_disjoint. by move=> [= ?].
  - right. exists rl2, n2, p, p'. split; last done. apply (logged_snoc Hrl). by left. }
iIntros "!>" (rl2 n2 p p' Hl).
case: (proj1 (logged_snoc Hrl) Hl) => [Hl'|[-> [-> [-> ->]]]]; first by iApply "Hsent".
by iFrame "Hsu HΦ".
Qed.

Arguments conn_seal_send {E rl L k k' t t'} _ _.

Lemma rel_conn_send rl cs cs' n r t t' :
  cryptis_rel_ctx -∗ conn_ctx -∗ conn_handle rl cs cs' n r -∗
  conn_payload t t' -∗ Φ rl n t t' -∗
  REL conn_send cs t << conn_send cs' t' :
    λ v v', ⌜v = #() ∧ v' = #()⌝ ∗ conn_handle rl cs cs' (S n) r.
Proof.
iIntros "#Hctx #Hinv (%k & %k' & %l1 & %l2 & %l1' & %l2' & %c & %c' & %L & -> & -> &
  %Hrl & <- & #Hc & #Hk & Hl1 & Hl2 & Hl1' & Hl2' & log) #(mt & mt' & _) #HΦ".
rewrite /conn_send /conn_sent /conn_role /conn_channel /conn_key. rel_prims.
rel_load_l. rel_load_r. rel_prims.
iMod (conn_seal_send (E:=⊤) ltac:(solve_ndisj) Hrl
        with "Hinv Hk log mt mt' HΦ") as "[log #Hpub]".
rel_apply (rel_send with "Hc Hpub").
iIntros (? ?) "[-> ->]" => /=. rel_pures.
rel_load_l. rel_load_r. rel_pures. rel_store_l. rel_store_r.
rel_values. iModIntro. iSplit; first done.
iExists k, k', l1, l2, l1', l2', c, c', (L ++ [(t, t')]).
rewrite length_app /= Nat.add_1_r Nat2Z.inj_succ Z.add_1_r.
by iFrame "#∗".
Qed.

End Send.

Section Receive.

Lemma conn_sealed_l k Ek u t' (P : Prop) :
  ↑seal_ns k u ⊆ Ek ∨ P →
  term_token (seed_of_senc_key k) Ek -∗ sealed_under_l k u t' -∗ ⌜P⌝.
Proof.
case=> [|?]; last by iIntros.
rewrite (senc_key_TKey k) => sub. iIntros "tok rec".
by iDestruct (sealed_under_l_token t' sub with "tok rec") as "[]".
Qed.

Arguments conn_sealed_l {k Ek u t' P} _.

Lemma conn_sealed_r k' Ek' u' t (P : Prop) :
  ↑seal_ns k' u' ⊆ Ek' ∨ P →
  term_token_spec (seed_of_senc_key k') Ek' -∗ sealed_under_r k' u' t -∗ ⌜P⌝.
Proof.
case=> [|?]; last by iIntros.
rewrite (senc_key_TKey k') => sub. iIntros "tok rec".
by iDestruct (sealed_under_r_token t sub with "tok rec") as "[]".
Qed.

Arguments conn_sealed_r {k' Ek' u' t P} _.

Lemma conn_open E k k' t t' :
  ↑cryptisN ⊆ E → ↑connIN ⊆ E →
  cryptis_rel_ctx -∗ conn_ctx -∗ conn_keys k k' -∗ PUB⟨t, t'⟩ ={E}=∗
  ⌜Spec.dec k (Tag connN) t = None ∧ Spec.dec k' (Tag connN) t' = None⌝ ∨
  ∃ rl n p p', ⌜(rl = 0 ∨ rl = 1)%Z⌝ ∗
    ⌜Spec.dec k (Tag connN) t = Some (Spec.of_list [TInt rl; TInt n; p])⌝ ∗
    ⌜Spec.dec k' (Tag connN) t' = Some (Spec.of_list [TInt rl; TInt n; p'])⌝ ∗
    Φ rl n p p'.
Proof.
iIntros (HE HE') "#Hctx #Hinv #(Hs & mk & mk' & sk & sk' & ss & ss' & Hno) #Ht".
iMod (publicly_related_open_senc_fupd k k' t t' HE with "Hctx ss ss' Ht") as "Hop".
iInv "Hinv" as "[>(Hfree & _ & _)|(%k0 & %k0' & >#Hs0 & >(%L0 & %L1 & %Ek & %Ek' & log0 & log1 & [tok tok'] & %Hcl & %Hcl' & #Hsent))]".
{ by iDestruct (free_sess with "Hfree Hs") as %[]. }
iDestruct (sess_agree with "Hs Hs0") as %[<- <-].
rewrite /Spec.dec.
case eL: (Spec.open k t) => [u|]; case eR: (Spec.open k' t') => [u'|].
- iDestruct "Hop" as "#[rec _]".
  iDestruct (conn_sealed_l (Hcl u) with "tok rec") as %(rl & n & p & p' & Hl & ->).
  iDestruct ("Hsent" $! rl n p p' with "[//]") as "([rec0 _] & HΦ)".
  iDestruct (sealed_under_l_agree with "rec rec0") as %[= ->].
  iModIntro. iSplitL "log0 log1 tok tok'".
  { iNext. iRight. iExists k, k'. iFrame "Hs". iExists L0, L1, Ek, Ek'.
    by iFrame (Hcl Hcl') "log0 log1 tok tok' Hsent". }
  iModIntro. iRight. iExists rl, n, p, p'. iFrame "HΦ".
  by rewrite /conn_body !Spec.tagK; case: Hl.
- iDestruct "Hop" as "#rec".
  iDestruct (conn_sealed_l (Hcl u) with "tok rec") as %(rl & n & p & p' & Hl & ->).
  iDestruct ("Hsent" $! rl n p p' with "[//]") as "([rec0 _] & _)".
  iDestruct (sealed_under_l_agree with "rec rec0") as %->.
  by rewrite (proj2 (Spec.open_senc_key_Some _ _ _) eq_refl) in eR.
- iDestruct "Hop" as "#rec'".
  iDestruct (conn_sealed_r (Hcl' u') with "tok' rec'") as %(rl & n & p & p' & Hl & ->).
  iDestruct ("Hsent" $! rl n p p' with "[//]") as "([_ rec0'] & _)".
  iDestruct (sealed_under_r_agree with "rec' rec0'") as %->.
  by rewrite (proj2 (Spec.open_senc_key_Some _ _ _) eq_refl) in eL.
- iModIntro. iSplitL "log0 log1 tok tok'".
  { iNext. iRight. iExists k, k'. iFrame "Hs". iExists L0, L1, Ek, Ek'.
    by iFrame (Hcl Hcl') "log0 log1 tok tok' Hsent". }
  iModIntro. by iLeft.
Qed.

Arguments conn_open {E k k' t t'} _ _.

Lemma rel_conn_recv rl cs cs' n r :
  cryptis_rel_ctx -∗ conn_ctx -∗ conn_handle rl cs cs' n r -∗
  REL conn_recv cs << conn_recv cs' :
    λ v v', (∃ p p' : term, ⌜v = p ∧ v' = p'⌝ ∗
      conn_handle rl cs cs' n (S r) ∗ Φ (1 - rl) r p p')%I.
Proof.
iIntros "#Hctx #Hinv Hh". rewrite /conn_recv /sdec. rel_pures.
iApply (rel_do_until _ _ (conn_handle rl cs cs' n r) with "[] Hh").
iIntros "!> (%k & %k' & %l1 & %l2 & %l1' & %l2' & %c & %c' & %L & -> & -> &
  %Hrl & %HL & #Hc & #Hk & Hl1 & Hl2 & Hl1' & Hl2' & log)".
rewrite /conn_channel /conn_received /conn_role /conn_key. rel_pures.
rel_apply (rel_recv with "Hc"). iIntros (t t') "#Ht" => /=. rel_pures.
iMod (conn_open with "Hctx Hinv Hk Ht")
  as "[[%eL %eR]|(%rl2 & %m & %p & %p' & %Hrl2 & %eL & %eR & #HΦ)]";
  [solve_ndisj..| |].
{ rel_prims. rewrite eL eR. rel_pures. rel_values. iModIntro. iLeft.
  do 2 (iSplit; first done). iExists k, k', l1, l2, l1', l2', c, c', L. by iFrame "#∗". }
rel_prims. rewrite eL eR. rel_prims. rewrite !Spec.of_listK /=.
rel_pures. rewrite ?subst_list_match /=.
rel_apply_l (rel_list_match_l (A:=term)). rewrite /=.
rel_apply_r (rel_list_match_r (A:=term)). rewrite /=.
rel_apply_l rel_to_int_l. rel_apply_r rel_to_int_r. rewrite /=. rel_pures.
rel_apply_l rel_to_int_l. rel_apply_r rel_to_int_r. rewrite /=. rel_pures.
case: (decide (rl = rl2)) => [<-|ne].
{ rewrite bool_decide_eq_true_2 //=. rel_pures. rel_values. iModIntro. iLeft.
  do 2 (iSplit; first done). iExists k, k', l1, l2, l1', l2', c, c', L. by iFrame "#∗". }
rewrite bool_decide_eq_false_2; last by move=> [=].
rel_pures. rel_load_l. rel_load_r. rel_pures.
case: (decide (r = m)) => [<-|ne'].
2: { rewrite bool_decide_eq_false_2; last by move=> [/Nat2Z.inj].
     rel_pures. rel_values. iModIntro. iLeft.
     do 2 (iSplit; first done). iExists k, k', l1, l2, l1', l2', c, c', L. by iFrame "#∗". }
rewrite bool_decide_eq_true_2 //. rel_pures.
rel_load_l. rel_load_r. rel_pures. rel_store_l. rel_store_r. rel_pures. rel_values.
iModIntro. iRight. iExists p, p'. do 2 (iSplit; first done). iExists p, p'.
iSplit; first done.
rewrite (_ : 1 - rl = rl2)%Z; last lia. iFrame "HΦ".
iExists k, k', l1, l2, l1', l2', c, c', L.
rewrite Nat2Z.inj_succ Z.add_1_r. by iFrame "#∗".
Qed.

End Receive.

End Conn.

Lemma conn_names_alloc `{!relocG Σ, !public_relGS Σ, !connGS Σ} :
  ⊢ |==> ∃ γ, conn_fresh γ ∗ conn_start γ 0 ∗ conn_start γ 1.
Proof.
iMod (ghost_var_alloc ([] : list (term * term))) as (γ0) "[log0 log0']".
iMod (ghost_var_alloc ([] : list (term * term))) as (γ1) "[log1 log1']".
iModIntro. iExists (ConnNames γ0 γ1). iFrame.
Qed.
