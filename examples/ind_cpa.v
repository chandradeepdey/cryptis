From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par nondet_bool.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role.
From cryptis.primitives Require Import attacker.

From reloc Require Import reloc.
From cryptis Require Import lib_spec.
From cryptis.core Require Import minted_spec term_meta_spec rel rel_inv_updates.
From cryptis.primitives Require Import simple_spec comp_spec with_cryptis_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CPA.

Context `{!relocG Σ, !public_relGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (t nonce : term).
Implicit Types (skA : aenc_key).

Variable N : namespace.

(*

* --> A: msg_0
* --> A: msg_1
A --> *: if b then {nonce, msg_0}@pkA else {nonce, msg_1}@pkA

*)

Definition aenc' : val := λ: "pk" "m",
  let: "nonce" := mk_nonce #() in
  aenc "pk" (Tag $ N.@"m") (term_of_list ["nonce"; "m"]).

Definition alice : val := λ: "c",
  let: "skA" := mk_aenc_key #() in
  let: "pkA" := pkey "skA" in
  send "c" "pkA";;
  let: "msg_0" := recv "c" in
  let: "msg_1" := recv "c" in
  let: "b" := nondet_bool #() in
  let: "msg" := if: "b" then "msg_0" else "msg_1" in
  send "c" (aenc' "pkA" "msg");;
  let: "guess" := recv "c" in
  let: "guess" := eq_term (TInt 1) "guess" in
  ("b", "guess").

Lemma rel_aenc' (skA skA' : aenc_key) (m m' : term) (Ψ : val → val → iProp) :
  cryptis_rel_ctx -∗
  ⌜is_nonce (seed_of_aenc_key skA)⌝ -∗
  minted (Spec.pkey skA) -∗
  minted_spec (Spec.pkey skA') -∗
  publicly_linked (Spec.pkey skA) (Spec.pkey skA') -∗
  secret_in_l (seed_of_aenc_key skA) -∗
  minted m -∗ minted_spec m' -∗
  (∀ c c', PUB⟨c, c'⟩ -∗ Ψ c c') -∗
  REL aenc' (Spec.pkey skA) m
   << aenc' (Spec.pkey skA') m' : Ψ.
Proof.
iIntros "#Hctx %Hnonce_a #mint_pk #mint_spec_pk' #elem_pk #secret_a #mint_m #mint_spec_m' post".
rewrite /aenc'.
rel_pures_l. rel_pures_r.
rel_apply_l (rel_mk_nonce_l _ _
  (λ n, {[ n;
           Spec.of_list [n; m];
           Spec.tag (Tag (N.@"m")) (Spec.of_list [n; m]);
           Spec.enc (Spec.pkey skA) (Tag (N.@"m")) (Spec.of_list [n; m]) ]})
  with "[//]").
{ iIntros "%t". rewrite big_sepS_forall. iIntros (t' Ht').
  rewrite !elem_of_union !elem_of_singleton in Ht'.
  case: Ht' => [[[->|->]|->]|->]; iModIntro.
  - by iSplit; iIntros "?".
  - rewrite minted_of_list /=. iSplit; iIntros "#H".
    + by iFrame "#".
    + by iDestruct "H" as "[? _]".
  - rewrite minted_tag minted_of_list /=. iSplit; iIntros "#H".
    + by iFrame "#".
    + by iDestruct "H" as "[? _]".
  - rewrite /Spec.enc minted_TSeal minted_tag minted_of_list /=. iSplit; iIntros "#H".
    + by iFrame "#".
    + by iDestruct "H" as "[_ [? _]]". }
iIntros (n) "%Hn #mint_n Htt".
rel_apply_r (rel_mk_nonce_r _ _
  (λ n, {[ n;
           Spec.of_list [n; m'];
           Spec.tag (Tag (N.@"m")) (Spec.of_list [n; m']);
           Spec.enc (Spec.pkey skA') (Tag (N.@"m")) (Spec.of_list [n; m']) ]})
  with "[//]").
{ iIntros "%t". rewrite big_sepS_forall. iIntros (t' Ht').
  rewrite !elem_of_union !elem_of_singleton in Ht'.
  case: Ht' => [[[->|->]|->]|->]; iModIntro.
  - by iSplit; iIntros "?".
  - rewrite minted_spec_of_list /=. iSplit; iIntros "#H".
    + by iFrame "#".
    + by iDestruct "H" as "[? _]".
  - rewrite minted_spec_tag minted_spec_of_list /=. iSplit; iIntros "#H".
    + by iFrame "#".
    + by iDestruct "H" as "[? _]".
  - rewrite /Spec.enc minted_spec_TSeal minted_spec_tag minted_spec_of_list /=.
    iSplit; iIntros "#H".
    + by iFrame "#".
    + by iDestruct "H" as "[_ [? _]]". }
iIntros (n') "%Hn' #mint_spec_n' Htts".
set pl := Spec.of_list [n; m].
set tg := Spec.tag (Tag (N.@"m")) pl.
set c := Spec.enc (Spec.pkey skA) (Tag (N.@"m")) pl.
set pl' := Spec.of_list [n'; m'].
set tg' := Spec.tag (Tag (N.@"m")) pl'.
set c' := Spec.enc (Spec.pkey skA') (Tag (N.@"m")) pl'.
case/is_nonceP: (Hn) => [an En]. case/is_nonceP: (Hn') => [an' En'].
(* Split the tokens. *)
have Hd_c : ({[n]} ∪ {[pl]} ∪ {[tg]} : gset term) ## {[c]}.
{ rewrite /c /tg /pl /Spec.enc Spec.tag_unseal Spec.of_list_unseal En /=. set_solver. }
have Hd_tg : ({[n]} ∪ {[pl]} : gset term) ## {[tg]}.
{ rewrite /tg /pl Spec.tag_unseal Spec.of_list_unseal Tag_unseal En /=. set_solver. }
have Hd_pl : ({[n]} : gset term) ## {[pl]}.
{ rewrite /pl Spec.of_list_unseal En /=. set_solver. }
have Hd_c' : ({[n']} ∪ {[pl']} ∪ {[tg']} : gset term) ## {[c']}.
{ rewrite /c' /tg' /pl' /Spec.enc Spec.tag_unseal Spec.of_list_unseal En' /=. set_solver. }
have Hd_tg' : ({[n']} ∪ {[pl']} : gset term) ## {[tg']}.
{ rewrite /tg' /pl' Spec.tag_unseal Spec.of_list_unseal Tag_unseal En' /=. set_solver. }
have Hd_pl' : ({[n']} : gset term) ## {[pl']}.
{ rewrite /pl' Spec.of_list_unseal En' /=. set_solver. }
rewrite big_sepS_union // big_sepS_union // big_sepS_union // !big_sepS_singleton.
iDestruct "Htt" as "(((tt_n & tt_pl) & tt_tg) & tt_c)".
rewrite big_sepS_union // big_sepS_union // big_sepS_union // !big_sepS_singleton.
iDestruct "Htts" as "(((tts_n & tts_pl) & tts_tg) & tts_c)".
rewrite (term_token_difference n (↑cryptisN.@"public_rel".@"flow") ⊤)=> //.
iDestruct "tt_n" as "[tt_n_flow tt_n]".
rewrite (term_token_difference n (↑cryptisN.@"public_rel".@"map")
           (⊤ ∖ ↑cryptisN.@"public_rel".@"flow")); last solve_ndisj.
iDestruct "tt_n" as "[tt_n_map _]".
rewrite (term_token_difference pl (↑cryptisN.@"public_rel".@"flow") ⊤)=> //.
iDestruct "tt_pl" as "[tt_pl_flow tt_pl]".
rewrite (term_token_difference pl (↑cryptisN.@"public_rel".@"map")
           (⊤ ∖ ↑cryptisN.@"public_rel".@"flow")); last solve_ndisj.
iDestruct "tt_pl" as "[tt_pl_map _]".
rewrite (term_token_difference tg (↑cryptisN.@"public_rel".@"map") ⊤)=> //.
iDestruct "tt_tg" as "[tt_tg_map _]".
rewrite (term_token_difference c (↑cryptisN.@"public_rel".@"flow") ⊤)=> //.
iDestruct "tt_c" as "[tt_c_flow tt_c]".
rewrite (term_token_difference c (↑cryptisN.@"public_rel".@"map")
           (⊤ ∖ ↑cryptisN.@"public_rel".@"flow")); last solve_ndisj.
iDestruct "tt_c" as "[tt_c_map _]".
rewrite (term_token_spec_difference n' (↑cryptisN.@"public_rel".@"flow") ⊤)=> //.
iDestruct "tts_n" as "[tts_n_flow tts_n]".
rewrite (term_token_spec_difference n' (↑cryptisN.@"public_rel".@"map")
           (⊤ ∖ ↑cryptisN.@"public_rel".@"flow")); last solve_ndisj.
iDestruct "tts_n" as "[tts_n_map _]".
rewrite (term_token_spec_difference pl' (↑cryptisN.@"public_rel".@"flow") ⊤)=> //.
iDestruct "tts_pl" as "[tts_pl_flow tts_pl]".
rewrite (term_token_spec_difference pl' (↑cryptisN.@"public_rel".@"map")
           (⊤ ∖ ↑cryptisN.@"public_rel".@"flow")); last solve_ndisj.
iDestruct "tts_pl" as "[tts_pl_map _]".
rewrite (term_token_spec_difference tg' (↑cryptisN.@"public_rel".@"map") ⊤)=> //.
iDestruct "tts_tg" as "[tts_tg_map _]".
rewrite (term_token_spec_difference c' (↑cryptisN.@"public_rel".@"flow") ⊤)=> //.
iDestruct "tts_c" as "[tts_c_flow tts_c]".
rewrite (term_token_spec_difference c' (↑cryptisN.@"public_rel".@"map")
           (⊤ ∖ ↑cryptisN.@"public_rel".@"flow")); last solve_ndisj.
iDestruct "tts_c" as "[tts_c_map _]".
(* The tagged payload is protected by the chain nonce → payload → tagged payload. *)
have Hsub_pl : is_immediate_subterm n pl.
{ rewrite /pl Spec.of_list_unseal /=. exact: SubtermPairL. }
have Hsub_tg : is_immediate_subterm pl tg.
{ rewrite /tg Spec.tag_unseal. exact: SubtermPairR. }
have Hsub_pl' : is_immediate_subterm n' pl'.
{ rewrite /pl' Spec.of_list_unseal /=. exact: SubtermPairL. }
have Hsub_tg' : is_immediate_subterm pl' tg'.
{ rewrite /tg' Spec.tag_unseal. exact: SubtermPairR. }
iMod (public_rel_flow_l_extend (E:=⊤) n ltac:(solve_ndisj)
        with "Hctx tt_n_flow tt_n_map") as "[prot_n tt_n_map]".
iMod (public_rel_flow_l_grow_2 (E:=⊤) Hn ltac:(solve_ndisj) Hsub_pl
        with "Hctx prot_n tt_n_map") as "(prot_n & protby_pl & tt_n_map)".
iMod (public_rel_flow_l_extend (E:=⊤) pl ltac:(solve_ndisj)
        with "Hctx tt_pl_flow tt_pl_map") as "[prot_pl tt_pl_map]".
iMod (public_rel_flow_l_grow_3 (E:=⊤) n ltac:(solve_ndisj) Hsub_tg
        with "Hctx protby_pl prot_pl tt_pl_map") as "(prot_pl & protby_tg & protby_pl & tt_pl_map)".
iMod (public_rel_flow_r_extend (E:=⊤) n' ltac:(solve_ndisj)
        with "Hctx tts_n_flow tts_n_map") as "[prot_n' tts_n_map]".
iMod (public_rel_flow_r_grow_2 (E:=⊤) Hn' ltac:(solve_ndisj) Hsub_pl'
        with "Hctx prot_n' tts_n_map") as "(prot_n' & protby_pl' & tts_n_map)".
iMod (public_rel_flow_r_extend (E:=⊤) pl' ltac:(solve_ndisj)
        with "Hctx tts_pl_flow tts_pl_map") as "[prot_pl' tts_pl_map]".
iMod (public_rel_flow_r_grow_3 (E:=⊤) n' ltac:(solve_ndisj) Hsub_tg'
        with "Hctx protby_pl' prot_pl' tts_pl_map") as "(prot_pl' & protby_tg' & protby_pl' & tts_pl_map)".
iMod (linked_extend (E:=⊤) tg tg' pl pl' ltac:(solve_ndisj)
        with "Hctx protby_tg protby_tg' tt_tg_map tts_tg_map") as "(_ & _ & #priv_tg & _ & _)".
(* The secret keys can never become publicly related. *)
iAssert (□ (PUB⟨skA, skA'⟩ → PUB⟨pl, pl'⟩))%I as "#Hbox".
{ iIntros "!> #Hsk". iExFalso.
  rewrite publicly_related_adec_key'.
  iDestruct (publicly_related_nonce_term _ Hnonce_a with "Hsk") as "[Hl _]".
  by iDestruct (secret_in_l_publicly_linked_in_l with "secret_a Hl") as "[]". }
(* The ciphertexts are publicly related. *)
iAssert (minted pl) as "#mint_pl".
{ rewrite /pl minted_of_list /=. by iFrame "#". }
iAssert (minted_spec pl') as "#mint_spec_pl'".
{ rewrite /pl' minted_spec_of_list /=. by iFrame "#". }
iAssert (□ (publicly_linked c c' -∗ PUB⟨c, c'⟩))%I as "#Hwand".
{ iIntros "!> #elem_c". rewrite publicly_related_aenc. iRight.
  do 5 (iSplit; first done).
  iSplit; first by iApply publicly_linked_linked.
  by iSplit. }
iMod (public_rel_flow_l_extend (E:=⊤) c ltac:(solve_ndisj)
        with "Hctx tt_c_flow tt_c_map") as "[prot_c tt_c_map]".
iMod (public_rel_flow_r_extend (E:=⊤) c' ltac:(solve_ndisj)
        with "Hctx tts_c_flow tts_c_map") as "[prot_c' tts_c_map]".
iMod (public_rel_extend (E:=⊤) c c' ltac:(solve_ndisj)
        with "Hctx Hwand prot_c prot_c' tt_c_map tts_c_map") as "#elem_c".
(* Run the program. *)
rel_pures_l. rel_pures_r.
rel_apply_l rel_nil_l.
repeat rel_apply_l rel_cons_l. rel_apply_l rel_term_of_list_l.
rel_apply_r rel_nil_r.
repeat rel_apply_r rel_cons_r. rel_apply_r rel_term_of_list_r.
rel_apply_l rel_aenc'_l. iModIntro.
rel_apply_r rel_aenc'_r.
rel_values. iApply "post". by iApply "Hwand".
Qed.

Lemma rel_alice c c' (b: bool) :
  cryptis_rel_ctx -∗
  channel_rel c c' -∗
  REL alice c << alice c' : λ p1 p2,
    ⌜∃ b1 b'1 b2 b'2 : bool,
    p1 = (#b1, #b'1)%V ∧ p2 = (#b2, #b'2)%V ∧
    (b = b1 → b ≠ b2 ∧ b'1 = b'2)⌝.
Proof.
iIntros "#Hctx #Hc". rewrite /alice.
rel_pures_l. rel_pures_r.
have Hdisj : ∀ sk : aenc_key,
    seed_of_aenc_key sk ∉ (∅ : gset term) ∧
    seed_of_aenc_key sk ∉ ({[Spec.pkey sk]} : gset term) ∧
    (∅ : gset term) ## ({[Spec.pkey sk]} : gset term).
{ move=> sk. rewrite /Spec.pkey [term_of_aenc_key]unlock /=.
  have Hne : ∀ kt (t : term), t ≠ TKey kt t.
  { move=> kt t H. have := f_equal tsize H.
    rewrite (tsize_eq (TKey kt t)). lia. }
  set_solver. }
rel_apply_l (rel_mk_aenc_key_l _ _ (λ _, ∅) (λ t, {[t]}) _ Hdisj with "[//]").
{ iIntros "%sk". by rewrite big_sepS_empty. }
{ iIntros "%sk". rewrite big_sepS_singleton. iModIntro. by iSplit; iIntros "?". }
iIntros (skA) "%Hnonce_a #mint_skA token_a _ token_pkA".
rewrite big_sepS_singleton.
rel_apply_r (rel_mk_aenc_key_r _ _ (λ _, ∅) (λ t, {[t]}) _ Hdisj with "[//]").
{ iIntros "%sk". by rewrite big_sepS_empty. }
{ iIntros "%sk". rewrite big_sepS_singleton. iModIntro. by iSplit; iIntros "?". }
iIntros (skA') "%Hnonce_a' #mint_spec_skA' token_spec_a _ token_spec_pkA'".
rewrite big_sepS_singleton.
rel_pures_l. rel_pures_r.
rel_apply_l rel_pkey_l. rel_apply_r rel_pkey_r.
rel_pures_l. rel_pures_r.
(* Tokens. *)
rewrite (term_token_difference (seed_of_aenc_key skA) (↑cryptisN.@"public_rel".@"map") ⊤)=> //.
iDestruct "token_a" as "[token_a _]".
rewrite (term_token_spec_difference (seed_of_aenc_key skA') (↑cryptisN.@"public_rel".@"map") ⊤)=> //.
iDestruct "token_spec_a" as "[token_spec_a _]".
rewrite (term_token_difference (Spec.pkey skA)
           (↑cryptisN.@"public_rel".@"flow") ⊤)=> //.
iDestruct "token_pkA" as "[token_pkA_flow token_pkA]".
rewrite (term_token_difference (Spec.pkey skA)
           (↑cryptisN.@"public_rel".@"map") (⊤ ∖ ↑cryptisN.@"public_rel".@"flow"));
  last solve_ndisj.
iDestruct "token_pkA" as "[token_pkA_map _]".
rewrite (term_token_spec_difference (Spec.pkey skA')
           (↑cryptisN.@"public_rel".@"flow") ⊤)=> //.
iDestruct "token_spec_pkA'" as "[token_spec_pkA_flow token_spec_pkA']".
rewrite (term_token_spec_difference (Spec.pkey skA')
           (↑cryptisN.@"public_rel".@"map") (⊤ ∖ ↑cryptisN.@"public_rel".@"flow"));
  last solve_ndisj.
iDestruct "token_spec_pkA'" as "[token_spec_pkA_map _]".
(* The seeds never become public. *)
iMod (public_rel_secret_l_2 (E:=⊤) Hnonce_a ltac:(solve_ndisj) with "Hctx token_a") as "#secret_a".
iMod (public_rel_secret_r_2 (E:=⊤) Hnonce_a' ltac:(solve_ndisj) with "Hctx token_spec_a") as "#secret_a'".
(* The public keys are publicly related. *)
iMod (public_rel_flow_l_extend (E:=⊤) (Spec.pkey skA) ltac:(solve_ndisj)
        with "Hctx token_pkA_flow token_pkA_map") as "[prot_pkA token_pkA_map]".
iMod (public_rel_flow_r_extend (E:=⊤) (Spec.pkey skA') ltac:(solve_ndisj)
        with "Hctx token_spec_pkA_flow token_spec_pkA_map") as "[prot_pkA' token_spec_pkA_map]".
iAssert (□ (publicly_linked (Spec.pkey skA) (Spec.pkey skA') -∗
            PUB⟨Spec.pkey skA, Spec.pkey skA'⟩))%I as "#Hwand".
{ iIntros "!> #elem". rewrite publicly_related_aenc_key. iRight.
  do 3 (iSplit; first done).
  iSplit; [by iApply secret_in_l_linked_in_l | by iApply secret_in_r_linked_in_r]. }
iMod (public_rel_extend (E:=⊤) (Spec.pkey skA) (Spec.pkey skA')
        ltac:(solve_ndisj)
        with "Hctx Hwand prot_pkA prot_pkA' token_pkA_map token_spec_pkA_map") as "#elem_pkA".
iPoseProof ("Hwand" with "elem_pkA") as "#Hpub".
rel_bind_l (send _ _). rel_bind_r (send _ _).
iApply refines_bind; first by iApply rel_send.
iIntros (? ?) "[-> ->]"=> /=.
rel_pures_l. rel_pures_r.
rel_bind_l (recv _). rel_bind_r (recv _).
iApply refines_bind'. iApply rel_recv=> //.
iIntros (msg_0 msg_0') "#Hmsg_0"=> /=.
rel_pures_l. rel_pures_r.
rel_bind_l (recv _). rel_bind_r (recv _).
iApply refines_bind'. iApply rel_recv=> //.
iIntros (msg_1 msg_1') "#Hmsg_1"=> /=.
rel_pures_l. rel_pures_r.
rel_apply_l rel_nondet_bool_l. iIntros (choice); rel_pures_l.
rel_apply_r (rel_nondet_bool_r _ _ (negb choice)); rel_pures_r.
rel_bind_l (if: _ then _ else _)%E.
rel_bind_r (if: _ then _ else _)%E.
iApply (refines_bind _ _ _ (λ v v', ∃ m m' : term, ⌜v = m⌝ ∧ ⌜v' = m'⌝ ∧ minted m ∧ minted_spec m')%I).
{ rewrite (publicly_related_minted msg_0) (publicly_related_minted msg_1).
  iDestruct "Hmsg_0" as "[? ?]".
  iDestruct "Hmsg_1" as "[? ?]".
  case: choice; rel_pures_l; rel_pures_r; rel_values.
  iExists msg_0, msg_1'; iFrame "#"; eauto.
  iExists msg_1, msg_0'; iFrame "#"; eauto. }
iIntros (? ?) "(%msg & %msg' & -> & -> & #mint_msg & #mint_spec_msg')"=> /=.
rel_pures_l. rel_pures_r.
rel_bind_l (aenc' _ _). rel_bind_r (aenc' _ _).
iApply refines_bind'. iApply rel_aenc'=> //=.
by rewrite minted_pkey. by rewrite minted_spec_pkey.
iIntros (c_msg c_msg') "#Hcmsg".
rel_bind_l (send _ _). rel_bind_r (send _ _).
iApply refines_bind; first by iApply rel_send.
iIntros (? ?) "[-> ->]"=> /=.
rel_pures_l. rel_pures_r.
rel_bind_l (recv _). rel_bind_r (recv _).
iApply refines_bind'. iApply rel_recv=> //.
iIntros (guess guess') "#Hguess"=> /=.
rel_pures_l. rel_pures_r.
rel_bind_l (eq_term _ _). rel_bind_r (eq_term _ _).
iApply refines_bind'. iApply rel_eq_term=> /=.
rel_pures_l. rel_pures_r.
rel_values.
iMod (publicly_related_part_bij' (E:=⊤) (TInt 1) (TInt 1) guess guess'
        ltac:(solve_ndisj)
        with "Hctx [] Hguess") as %H.
{ by rewrite publicly_related_TInt. }
iPureIntro.
eexists _, _, _, _. repeat split; eauto.
destruct choice=> /=; congruence.
by apply bool_decide_ext.
Qed.

End CPA.
