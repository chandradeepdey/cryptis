(** * Proofs of the NSL store case study

The client and the server agree on a session key with NSL, and then run the
store of [store.v] over a connection under that key.

- R records the session of its run on I's seed, when NSL hands it the
  session.  Recording it makes the session key secret, and starts the
  connection invariant of [conn.v] with the never-sealed tokens of the
  session secret, which is the key's seed.
- The game creates the keys, starts the server in a new thread, and runs
  the client: the stores, then the load, whose result goes to the
  attacker. *)

From reloc Require Import reloc.
From cryptis Require Import cryptis primitives.
From cryptis.hyper.lib Require Import avl.
From cryptis.hyper.core Require Import minted_spec term_meta_spec public.
From cryptis.hyper.primitives Require Import with_cryptis.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples.nsl.proofs Require Import base init resp.
From cryptis.hyper.examples.store_nsl Require Import impl.
From cryptis.hyper.examples.store_nsl.proofs Require Import conn rpc store.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation sessN := (storeN.@"sess").
Abbreviation sess2N := (storeN.@"sess2").

Section Proofs.

Context `{!relocG Σ, !publicGS Σ, !connGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (s : term) (skI skR : aenc_key).

(** The session that R records on I's seed, with what recording it made
    secret. *)
Definition store_sess skI s s' : iProp :=
  term_meta (seed_of_aenc_key skI) sessN (s, s') ∗
  term_meta (seed_of_aenc_key skI) sess2N () ∗
  minted (sess_key s) ∗ minted_spec (sess_key s') ∗
  secret_in_l (sess_key s) ∗ secret_in_r (sess_key s').

#[global] Instance store_sess_persistent skI s s' : Persistent (store_sess skI s s').
Proof. apply _. Qed.

#[global] Instance store_sess_timeless skI s s' : Timeless (store_sess skI s s').
Proof. apply _. Qed.

Definition key_sess skI (k k' : senc_key) : iProp :=
  ∃ s s', ⌜k = SEncKey s ∧ k' = SEncKey s'⌝ ∗ store_sess skI s s'.

#[global] Instance key_sess_persistent skI k k' : Persistent (key_sess skI k k').
Proof. apply _. Qed.

#[global] Instance key_sess_timeless skI k k' : Timeless (key_sess skI k k').
Proof. apply _. Qed.

Definition key_free skI : iProp := term_token (seed_of_aenc_key skI) (↑sess2N).

Lemma key_sess_agree skI k1 k1' k2 k2' :
  key_sess skI k1 k1' -∗ key_sess skI k2 k2' -∗ ⌜k1 = k2 ∧ k1' = k2'⌝.
Proof.
iIntros "(%s1 & %s1' & [-> ->] & #m1 & _) (%s2 & %s2' & [-> ->] & #m2 & _)".
by iDestruct (term_meta_agree with "m1 m2") as %[= -> ->].
Qed.

Lemma key_free_sess skI k k' : key_free skI -∗ key_sess skI k k' -∗ False.
Proof.
iIntros "tok (%s & %s' & _ & _ & #m & _)".
by iDestruct (term_meta_token with "tok m") as "[]".
Qed.

Section Game.

Variables (ops ops' : list (Z * Z)) (k : Z).
Hypothesis ops_nodup : NoDup ops.*1.
Hypothesis ops_perm : ops ≡ₚ ops'.

Abbreviation Φs := (store_Φ ops ops' k).

Definition store_ctx skI γ : iProp :=
  conn_ctx γ (key_sess skI) (key_free skI) Φs.

Lemma store_alloc skI γ :
  hypercryptis_ctx -∗ store_ctx skI γ -∗ term_token (seed_of_aenc_key skI) (↑sessN) -∗
  ∀ s s', key_tokens s s' -∗ secret_in_l s -∗ secret_in_r s' -∗
    protects_superterms_l s ∅ -∗ protects_superterms_r s' ∅ ={⊤}=∗ store_sess skI s s'.
Proof.
iIntros "#Hctx #Hinv tok" (s s') "(ns & tt_k & tts_k & _) #sec #sec' prot prot'".
iPoseProof (term_token_minted with "tt_k") as "#mk".
iPoseProof (term_token_spec_minted_spec with "tts_k") as "#mk'".
iDestruct (term_token_public_token_l with "tt_k") as "(tt_k & _ & _)";
  first (rewrite /sess_key; solve_not_TSeal).
iDestruct (term_token_public_token_r with "tts_k") as "(tts_k & _ & _)";
  first (rewrite /sess_key; solve_not_TSeal).
iMod (public_secret_step_l (E:=⊤) (t:=s) (tsup:=sess_key s)
        ltac:(rewrite /sess_key [term_of_senc_key]unlock; constructor) ltac:(solve_ndisj)
        with "Hctx sec prot tt_k") as "[#sec_k _]".
iMod (public_secret_step_r (E:=⊤) (t':=s') (t'sup:=sess_key s')
        ltac:(rewrite /sess_key [term_of_senc_key]unlock; constructor) ltac:(solve_ndisj)
        with "Hctx sec' prot' tts_k") as "[#sec_k' _]".
iInv "Hinv" as "[>(free & log0 & log1)|(%k0 & %k0' & >(%s0 & %s0' & _ & #m0 & _) & _)]";
  last by iDestruct (term_meta_token with "tok m0") as "[]".
iMod (term_meta_set sessN (s, s') with "tok") as "#m1"; first done.
iMod (term_meta_set sess2N () with "free") as "#m2"; first done.
iAssert (store_sess skI s s') as "#Hs"; first by iFrame "#".
iModIntro. iSplitL; last done.
iNext. iRight. iExists (SEncKey s), (SEncKey s').
iSplitR; first by iExists s, s'; iFrame "Hs".
by iApply (conn_state_init γ Φs (SEncKey s) (SEncKey s') with "ns [$log0 $log1]").
Qed.

Lemma session_keys E skI skI' skR skR' s s' :
  ↑sealsIN ⊆ E → ↑cryptisN ⊆ E ∖ ↑sealsIN →
  hypercryptis_ctx -∗
  nsl_ctx skI skI' skR skR' (store_sess skI) -∗
  session skI skI' skR skR' s s' ={E}=∗
  conn_keys (key_sess skI) (SEncKey s) (SEncKey s').
Proof.
iIntros (HN HE) "#Hctx #Hnsl #Hs".
iMod (session_sess with "Hctx Hnsl Hs") as (nI nI' nR nR' [-> ->]) "(_ & #HnR & #ss & #ss' & #Hss)";
  [done..|].
iModIntro. iPoseProof "Hss" as "(_ & _ & mk & mk' & sk & sk')".
iSplit; first by iExists _, _; iSplit; last iFrame "Hss".
iFrame "mk mk' sk sk' ss ss'".
by iApply (seed_not_pub with "HnR").
Qed.

Lemma store_client_refinement skI skI' skR skR' γ c c' :
  hypercryptis_ctx -∗ lrel_channel c c' -∗ nsl_ctx skI skI' skR skR' (store_sess skI) -∗
  conn_start γ 0 -∗
  REL client c skI (Spec.pkey skR) << client c' skI' (Spec.pkey skR') : λ v v',
    (⌜v = NONEV ∧ v' = NONEV⌝ ∨
     ∃ cs cs', ⌜v = SOMEV cs ∧ v' = SOMEV cs'⌝ ∗ conn_handle γ (key_sess skI) 0 cs cs' 0 0)%I.
Proof.
iIntros "#Hctx #Hc #Hnsl log". rewrite /client. rel_pures.
iPoseProof "Hnsl" as "(_ & (_ & _ & _ & _ & #pub_pkR & _) & _)".
rel_apply (init_refinement with "Hctx Hc Hnsl pub_pkR").
iIntros (? ?) "[[-> ->]|(%kk & %kk' & [-> ->] & Hsess)]" => /=.
{ rel_pures. rel_values. }
iDestruct ("Hsess" with "[//]") as (s s' [-> ->]) "Hs".
iMod (session_keys with "Hctx Hnsl Hs") as "#Hk"; [solve_ndisj..|].
rel_pures. rewrite /sess_key.
rel_apply (conn_new_refinement γ (rl:=0) with "Hc Hk log"); first by left.
iIntros (cs cs') "Hh". rel_pures. rel_values. iModIntro. iRight. iExists cs, cs'. by iFrame.
Qed.

Lemma store_server_refinement skI skI' skR skR' γ c c' :
  hypercryptis_ctx -∗ lrel_channel c c' -∗ nsl_ctx skI skI' skR skR' (store_sess skI) -∗
  store_ctx skI γ -∗ term_token (seed_of_aenc_key skI) (↑sessN) -∗
  conn_start γ 1 -∗
  REL server c skR (Spec.pkey skI) << server c' skR' (Spec.pkey skI') : ().
Proof.
iIntros "#Hctx #Hc #Hnsl #Hinv tok log". rewrite /server. rel_pures.
rel_apply (resp_refinement with "Hctx Hc Hnsl [tok]").
{ by iApply (store_alloc with "Hctx Hinv tok"). }
iIntros (? ?) "[[-> ->]|(%pkI & %pkI' & %kk & %kk' & [-> ->] & #HpkI & Hsess)]" => /=.
{ rel_pures. by rel_values. }
rel_prims.
iPoseProof "Hnsl" as "((_ & _ & _ & _ & #pub_pkI & _) & _)".
iMod (public_part_bij' (E:=⊤) with "Hctx HpkI pub_pkI") as %HX;
  first solve_ndisj.
case: (decide (pkI = Spec.pkey skI)) => [eX|neX]; last first.
{ rewrite bool_decide_eq_false_2 // bool_decide_eq_false_2; last by rewrite -HX.
  rel_pures. by rel_values. }
rewrite bool_decide_eq_true_2 // bool_decide_eq_true_2; last by apply HX.
rel_pures.
iDestruct ("Hsess" with "[//]") as (s s' [-> ->]) "Hs".
iMod (session_keys with "Hctx Hnsl Hs") as "#Hk"; [solve_ndisj..|].
rewrite /sess_key.
rel_apply_l refines_avl_new_l. iIntros (db) "Hdb".
rel_apply_r refines_avl_new_r. iIntros (db') "Hdb'". rel_pures.
rel_apply (conn_new_refinement γ (rl:=1) with "Hc Hk log"); first by right.
iIntros (cs cs') "Hh". rel_pures.
iApply (rpc_server_refinement γ (key_sess_agree skI) (key_free_sess skI) (server_inv ops ops')
          with "Hctx Hinv [] Hh [Hdb Hdb']").
- iIntros "!>" (n r st st' p p') "HI HΦ".
  by iApply (store_handle_refinement k ops_nodup ops_perm with "HI HΦ").
- by iFrame.
Qed.

Lemma store_game_refinement c c' :
  hypercryptis_ctx -∗ lrel_channel c c' -∗
  REL game ops k c << game ops' k c' : ().
Proof.
iIntros "#Hctx #Hc". rewrite /game. rel_pures.
rel_bind_l (mk_aenc_key #()). rel_bind_r (mk_aenc_key #()).
iApply (mk_honest_key_refinement with "Hctx").
iIntros (skI skI') "#HI sealsI tokI" => /=. rel_pures.
rel_bind_l (mk_aenc_key #()). rel_bind_r (mk_aenc_key #()).
iApply (mk_honest_key_refinement with "Hctx").
iIntros (skR skR') "#HR sealsR _" => /=. rel_pures.
iMod (inv_alloc sealsIN _ (seals_inv skI skI' (seals_I_info skI skI' skR skR' (store_sess skI)))
        with "[sealsI]") as "#HinvI".
{ iNext. iExists ∅, _, _. iFrame "sealsI".
  iSplit; first by iPureIntro => ?; left; apply nclose_subseteq.
  iSplit; first by iPureIntro => ?; left; apply nclose_subseteq.
  by rewrite !big_sepS_empty. }
iMod (inv_alloc sealsRN _ (seals_inv skR skR' (seals_R_info skI skI'))
        with "[sealsR]") as "#HinvR".
{ iNext. iExists ∅, _, _. iFrame "sealsR".
  iSplit; first by iPureIntro => ?; left; apply nclose_subseteq.
  iSplit; first by iPureIntro => ?; left; apply nclose_subseteq.
  by rewrite !big_sepS_empty. }
rewrite (term_token_difference (seed_of_aenc_key skI) (↑sessN)
           (⊤ ∖ ↑hypercryptisN)); last solve_ndisj.
iDestruct "tokI" as "[tok_sess tokI]".
rewrite (term_token_difference (seed_of_aenc_key skI) (↑sess2N)
           (⊤ ∖ ↑hypercryptisN ∖ ↑sessN)); last solve_ndisj.
iDestruct "tokI" as "[tok_sess2 _]".
iMod conn_names_alloc as (γ) "(fresh & log0 & log1)".
iMod (inv_alloc connIN _ (conn_inv γ (key_sess skI) (key_free skI) Φs)
        with "[tok_sess2 fresh]") as "#Hinv".
{ iNext. iLeft. iFrame. }
iAssert (nsl_ctx skI skI' skR skR' (store_sess skI)) as "#Hnsl"; first by iFrame "#".
rel_prims.
rel_apply (refines_send with "Hc []").
{ iNext. by iDestruct "HI" as "(_ & _ & _ & _ & ? & _)". }
iIntros (? ?) "[-> ->]" => /=. rel_prims.
rel_apply (refines_send with "Hc []").
{ iNext. by iDestruct "HR" as "(_ & _ & _ & _ & ? & _)". }
iIntros (? ?) "[-> ->]" => /=. rel_pures.
rel_bind_l (Fork _). rel_bind_r (Fork _).
iApply (refines_bind with "[tok_sess log1]").
{ iApply refines_fork. rel_prims.
  by iApply (store_server_refinement with "Hctx Hc Hnsl Hinv tok_sess log1"). }
iIntros (? ?) "_" => /=. rel_prims.
rel_apply (store_client_refinement skI skI' skR skR' γ with "Hctx Hc Hnsl log0").
iIntros (? ?) "[[-> ->]|(%cs & %cs' & [-> ->] & Hh)]" => /=.
{ rel_pures. by rel_values. }
rel_pures.
rel_apply (store_all_refinement γ (key_sess_agree skI) (key_free_sess skI) k ops_perm
             cs cs' (i:=0) ltac:(lia) with "Hctx Hinv Hh").
iIntros (? ?) "[[-> ->] Hh]". rel_pures. rewrite /store_load. rel_prims.
rel_apply (rpc_call_refinement γ (key_sess_agree skI) (key_free_sess skI)
             0 cs cs' (length ops) (length ops) (storeN.@"load") (TInt k) (TInt k)
             with "Hctx Hinv Hh [] []").
{ iApply conn_payload_TInt. }
{ iPureIntro. rewrite /store_msg. case: decide => // _. by right. }
iIntros (? ?) "(%p & %p' & [-> ->] & Hh & %Hp)" => /=.
move: Hp. rewrite /store_msg. case: decide => // _ [z [-> ->]].
iAssert (PUB⟨TInt z, TInt z⟩) as "#Hz"; first by rewrite public_TInt.
by rel_apply (refines_send with "Hc Hz").
Qed.

End Game.

End Proofs.
