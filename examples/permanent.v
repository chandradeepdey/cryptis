From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import numbers.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis.primitives Require Import attacker.

(* This example demonstrates a simple use of digital signatures to guarantee
integrity properties: a server uses a signature to inform the client that some
part of its state will never change.  *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (l : loc) (k t : term) (sk : sign_key).

Definition server : val := rec: "loop" "c" "l" "sk" :=
  (* Receive request from the network *)
  let: <> := recv "c" in
  (* Sign message *)
  let: "reply" := sign "sk" (Tag nroot) (! "l") in
  send "c" "reply";;
  "loop" "c" "l" "sk".

Definition client : val := λ: "c" "pk",
  do_until (λ: <>,
    (* Send out request *)
    let: "request" := tag (Tag $ nroot.@"get") (tint #0) in
    send "c" "request" ;;
    (* Wait for response *)
    let: "reply" := recv "c" in
    (* Check signature *)
    bind: "value" := verify "pk" (Tag nroot) "reply" in
    SOME "value"
  ).

Definition msg_pred l sk t : iProp :=
  l ↦□ (t : val).

Lemma wp_server c l sk t :
  cryptis_ctx -∗
  channel c -∗
  sign_pred nroot (msg_pred l) -∗
  minted sk -∗
  l ↦□ (t : val) -∗
  public t -∗
  WP server c #l sk {{ _, True }}.
Proof.
iIntros "#ctx #chan_c #sig_pred #s_sk #Hl #p_t".
(* Unfold the definition of the server *)
iLöb as "IH". wp_rec. wp_pures.
(* Receive request from the network *)
wp_bind (recv _). iApply wp_recv => //. iIntros "%request _". wp_pures.
(* Load contents and sign message *)
wp_load. wp_apply wp_sign; eauto. iIntros "%m #p_m". wp_pures.
(* Send message. Prove that it is well formed. *)
wp_bind (send _ _). iApply wp_send => //.
(* Loop *)
by wp_pures.
Qed.

Lemma wp_client c l sk φ :
  cryptis_ctx -∗
  channel c -∗
  sign_pred nroot (msg_pred l) -∗
  minted sk -∗
  □ (public sk → ▷ False) -∗
  (∀ t : term, l ↦□ (t : val) -∗ φ (t : val)) -∗
  WP client c (Spec.pkey sk) {{ v, φ v }}.
Proof.
iIntros "#ctx #chan_c #sig_pred #m_sk #s_sk post".
(* Unfold definition of client *)
rewrite /client. wp_pures.
iRevert "post". iApply wp_do_until. iIntros "!> post". wp_pures.
(* Construct request *)
wp_bind (tint _). iApply wp_tint. wp_tag. wp_pures.
(* Send message. Prove it is well formed. *)
wp_bind (send _ _). iApply wp_send => //.
{ by rewrite public_tag public_TInt. }
(* Wait for response. *)
wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%reply #p_reply". wp_pures.
(* Verify the signature *)
wp_apply wp_verify; eauto. iSplit; last by wp_pures; eauto.
iIntros "%m #p_m [fail|#inv_m]".
(* The signature could have been forged if the key was compromised, but we have
   ruled out this possibility.  *)
{ by iDestruct ("s_sk" with "fail") as ">[]". }
(* Therefore, the invariant must hold. *)
wp_pures. iModIntro. iRight. iExists _. iSplit => //.
by iApply "post".
Qed.

(* Security game: ensure that the response that the client gets matches the
state of the server. *)

Definition game : val := λ: <>,
  (* Initialize attacker (network) *)
  let: "c"   := init_network #() in

  (* Generate signature keys and publicize verification key *)
  let: "k"   := mk_sign_key #() in
  let: "pk"  := pkey "k" in
  send "c" "pk" ;;

  (* Initialize server state *)
  let: "t" := recv "c" in
  let: "l" := ref "t" in

  (* Run server *)
  Fork (server "c" "l" "k");;

  (* Run client *)
  let: "t'" := client "c" "pk" in

  (* Check if client's value agrees with the server state *)
  eq_term (!"l") "t'".

Lemma wp_game :
  cryptis_ctx ∗
  seal_pred_token SIGN ⊤ ∗
  honest 0 ∅ ∗
  ●Ph 0 -∗
  WP game #() {{ v, ⌜v = #true⌝ }}.
Proof.
iIntros "(#ctx & enc_tok & #hon & phase)".
rewrite /game. wp_pures.
(* Setup attacker *)
wp_apply wp_init_network => //. iIntros "%c #cP". wp_pures.
(* Generate server key. Keep the signing key secret. *)
wp_bind (mk_sign_key _). iApply (wp_mk_sign_key with "[//]") => //.
iIntros (sk) "#m_sk s_sk token".
iMod (freeze_secret with "s_sk") as "#[??]".
wp_pures. wp_apply wp_pkey. wp_pures.
(* Publicize verification key. *)
wp_pures. wp_bind (send _ _). iApply wp_send => //.
{ by iApply public_verify_key. }
wp_pures.
(* Attacker chooses value stored by the server. *)
wp_bind (recv _). iApply wp_recv => //. iIntros "%t #p_t". wp_pures.
wp_alloc l as "Hl".
(* Promise that the stored value will not change. *)
iMod (pointsto_persist with "Hl") as "#Hl".
(* Initialize signature invariant *)
iMod (sign_pred_set (N := nroot) (msg_pred l) with "enc_tok") as "[#? _]" => //.
(* Run server in a loop in parallel. *)
wp_pures. wp_bind (Fork _). iApply wp_fork.
{ iApply wp_server => //. }
iModIntro.
(* Let client contact server *)
wp_pures. wp_bind (client _ _). iApply wp_client => //.
iIntros (t') "#Hl'".
(* Now the client knows which value is stored in the server. *)
iPoseProof (pointsto_agree with "Hl' Hl") as "->". wp_pures. wp_load.
iApply wp_eq_term. by rewrite bool_decide_true.
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ].

(* The same result, but without using the Cryptis logic. *)
Lemma game_secure σ₁ σ₂ (v : val) ts :
  rtc erased_step ([game #()], σ₁) (Val v :: ts, σ₂) →
  v = #true.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_result NotStuck _ _ (λ v _, v = #true)).
apply: heap_adequacy.
iIntros (?) "?".
iMod (cryptisGS_alloc _)
  as (?) "(#ctx & enc_tok & sign_tok & senc_tok & hash_tok & hon)".
by iApply (wp_game) => //; try by iFrame.
Qed.
