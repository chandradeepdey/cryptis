From cryptis Require Import lib.
From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import numbers reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par assert ticket_lock.
From cryptis Require Import cryptis primitives tactics gmeta.
From cryptis Require Import role iso_dh rpc conn store.
From cryptis.primitives Require Import attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !storeGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types rl : role.

Definition gameN := nroot.@"game".

Definition kvsN := nroot.@"kvs".

Definition server_loop : val := rec: "loop" "c" "server" :=
  Server.listen kvsN "c" "server";;
  "loop" "c" "server".

Definition start_server : val := λ: "c" "skR",
  let: "server" := Server.start "skR" in
  server_loop "c" "server".

Definition game : val := λ: <>,
  let: "c" := init_network #() in

  (* Create key pairs and give verification keys to attacker *)
  let: "skI" := mksigkey #() in
  let: "skR" := mksigkey #() in
  let: "vkI" := vkey "skI" in
  let: "vkR" := vkey "skR" in
  send "c" "vkI";; send "c" "vkR";;

  (* Run storage server in parallel *)
  Fork (start_server "c" "skR");;

  (* Connect client to server *)
  let: "conn" := Client.connect kvsN "c" "skI" "vkR" in

  (* Store value in server *)
  let: "k" := recv "c" in
  let: "v" := recv "c" in
  Client.create kvsN "c" "conn" "k" "v";;
  Client.close kvsN "c" "conn";;
  (* Leak session key *)
  send "c" (Conn.session_key "conn");;

  let: "conn" := Client.connect kvsN "c" "skI" "vkR" in
  (* Leak long-term keys *)
  send "c" "skI";;
  send "c" "skR";;

  (* Retrive value and check that it matches the one that was stored *)
  let: "v'" := Client.load kvsN "c" "conn" "k" in
  assert: eq_term "v" "v'".

Lemma wp_server_loop c ss :
  {{{ cryptis_ctx ∗ channel c ∗ store_ctx kvsN ∗
      server kvsN ss }}}
    server_loop c (repr ss)
  {{{ RET #(); True }}}.
Proof.
iLöb as "IH". iIntros "%Ψ (#? & #? & #? & server) post".
wp_rec. wp_pures.
wp_apply (wp_server_listen with "[$server]"); eauto.
iIntros "server". wp_pures.
by iApply ("IH" with "[$server]"); eauto.
Qed.

Lemma wp_start_server c skR :
  {{{ cryptis_ctx ∗ channel c ∗ store_ctx kvsN ∗
      sign_key skR ∗
      term_token skR ⊤ }}}
    start_server c skR
  {{{ RET #(); True }}}.
Proof.
iIntros "%Ψ (#? & #? & #? & #? & token) post".
wp_lam. wp_pures.
wp_apply (wp_server_start with "[$token]") => //; eauto.
iIntros "%ss server". wp_pures.
wp_apply (wp_server_loop with "[$server]"); eauto.
Qed.

Lemma wp_game :
  cryptis_ctx -∗
  seal_pred_token ⊤ -∗
  WP game #() {{ _, True }}.
Proof.
iIntros "#ctx enc_tok"; rewrite /game; wp_pures.
iMod (store_ctx_alloc (N := kvsN) with "enc_tok") as "[#? _]" => //.
wp_apply wp_init_network => //. iIntros "%c #cP". wp_pures.
wp_apply (wp_mksigkey with "[]"); eauto.
iIntros "%skI #p_vkI #sign_skI s_skI tokenI". wp_pures.
wp_pures. wp_apply (wp_mksigkey with "[]"); eauto.
iIntros "%skR #p_vkR #sign_skR s_skR tokenR". wp_pures.
wp_apply wp_vkey. wp_pures.
wp_apply wp_vkey. wp_pures.
wp_apply wp_send => //. wp_pures.
wp_apply wp_send => //. wp_pures.
wp_apply (wp_fork with "[tokenR]").
{ iModIntro. wp_apply (wp_start_server with "[$tokenR]"); eauto. }
wp_pures.
iMod (@client_alloc _ _ _ _ _ _ skR with "tokenI")
  as "(client & free & token)"; eauto.
wp_apply (wp_client_connect with "[] [] [] [] [] client"); eauto.
iIntros "%cs client". wp_pure _ credit:"c". wp_pures.
iPoseProof (db_connected_ok with "client s_skI s_skR [//] [//]") as "#>ok".
wp_apply wp_recv => //. iIntros "%k #p_k". wp_pures.
wp_apply wp_recv => //. iIntros "%v #p_v". wp_pures.
rewrite (@db_free_at_diff _ _ _ _ _ _ _ {[k]}) //.
iDestruct "free" as "[free_k free]".
wp_apply (wp_client_create with "[] [] [] [] [] [$client $free_k]") => //.
iIntros "[client k_v]". wp_pures.
wp_apply (wp_client_close with "[] [] [$client]") => //.
iIntros "[client #p_sk]".
wp_pures.
wp_apply Conn.wp_session_key => //. iIntros "_".
wp_apply (wp_send with "[//]") => //. wp_pures.
wp_apply (wp_client_connect with "[] [] [] [] [] client"); eauto.
iIntros "%cs' client". wp_pure _ credit:"c'". wp_pures.
iPoseProof (db_connected_ok with "client s_skI s_skR [//] [//]") as "#>#ok'".
iMod (secret_public with "s_skI") as "#p_skI".
iMod (secret_public with "s_skR") as "#p_skR".
wp_apply wp_send => //. wp_pures.
wp_apply wp_send => //. wp_pures.
wp_apply (wp_client_load with "[] [] [] [] [$client $k_v]") => //.
iIntros "%v' (client & k_v & _ & [fail|->])".
{ by iPoseProof ("ok'" with "fail") as "[]". }
wp_pures. wp_apply wp_assert. wp_apply wp_eq_term.
by rewrite bool_decide_eq_true_2.
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ; tlockΣ; Conn.connΣ; storeΣ].

Lemma store_secure σ₁ σ₂ (v : val) t₂ e₂ :
  rtc erased_step ([game #()], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_not_stuck NotStuck _ _ (λ v _, True)) => //.
apply: heap_adequacy.
iIntros (?) "?".
iMod (cryptisGS_alloc _) as (?) "(#ctx & enc_tok & key_tok & ? & hon & phase)".
by iApply (wp_game with "ctx [enc_tok]") => //.
Qed.
