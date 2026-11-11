(** * Proofs of the NSL case study

Each role has its own file.  A test creates the honest keys, runs both roles,
and lets R record its session on I's seed.  It then takes the tokens of the
hash of the tested session key out of the test's invariant, and reveals the
key derived from the hash or a fresh key.

- [Claim]: the test's invariant, which R fills when it records its session.
- [Tests]: the setup, the reveal, and the two tests. *)

From cryptis.hyper.examples.nsl.proofs Require Export base init resp.
From cryptis Require Import lib cryptis primitives.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib.
From cryptis.hyper.core Require Import minted_spec term_meta_spec public.
From cryptis.hyper.primitives Require Import simple comp with_cryptis.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples.nsl Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Proofs.

Context `{!relocG Σ, !public_relGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (t s : term).

Abbreviation rorN := (nslN.@"ror").
Abbreviation sessN := (nslN.@"sess").
Abbreviation sess2N := (nslN.@"sess_alloc").

Section Claim.

(** The right to take the tokens of the hash out of the test's invariant,
    once. *)
Definition claim skI : iProp := term_token (seed_of_aenc_key skI) (↑claimN).

(** The session that the test may claim: R records it on I's seed, and makes
    its key secret. *)
Definition ror_sess skI s s' : iProp :=
  term_meta (seed_of_aenc_key skI) sessN (s, s') ∗
  secret_in_l (sess_key s) ∗ secret_in_r (sess_key s').

(** The test derives its key from the hash of the session key. *)
Definition hash_tokens s s' : iProp :=
  term_token (THash (sess_key s)) ⊤ ∗ term_token_spec (THash (sess_key s')) ⊤.

#[global] Instance ror_sess_persistent skI s s' : Persistent (ror_sess skI s s').
Proof. apply _. Qed.

#[global] Instance ror_sess_timeless skI s s' : Timeless (ror_sess skI s s').
Proof. apply _. Qed.

(** Before R records its session, the invariant holds the token that does
    it; afterwards, the tokens of the hash until the test claims them. *)
Definition ror_inv skI : iProp :=
  term_token (seed_of_aenc_key skI) (↑sessN) ∨
  ∃ s s', ror_sess skI s s' ∗ term_token (seed_of_aenc_key skI) (↑sess2N) ∗
    (hash_tokens s s' ∨ claim skI).

Lemma ror_alloc skI :
  cryptis_rel_ctx -∗
  inv rorN (ror_inv skI) -∗
  term_token (seed_of_aenc_key skI) (↑sess2N) -∗
  ∀ s s', key_tokens s s' -∗ secret_in_l s -∗ secret_in_r s' -∗
    protects_superterms_l s ∅ -∗ protects_superterms_r s' ∅ ={⊤}=∗ ror_sess skI s s'.
Proof.
iIntros "#Hctx #Hinv tok2" (s s') "(_ & tt_k & tts_k & toks) #sec #sec' prot prot'".
iDestruct (term_token_rel_token_l with "tt_k") as "(tt_k & _ & _)";
  first (rewrite /sess_key; solve_not_TSeal).
iDestruct (term_token_rel_token_r with "tts_k") as "(tts_k & _ & _)";
  first (rewrite /sess_key; solve_not_TSeal).
iMod (public_rel_secret_step_l (E:=⊤) (t:=s) (tsup:=sess_key s)
        ltac:(rewrite /sess_key [term_of_senc_key]unlock; constructor) ltac:(solve_ndisj)
        with "Hctx sec prot tt_k") as "[#sec_k _]".
iMod (public_rel_secret_step_r (E:=⊤) (t':=s') (t'sup:=sess_key s')
        ltac:(rewrite /sess_key [term_of_senc_key]unlock; constructor) ltac:(solve_ndisj)
        with "Hctx sec' prot' tts_k") as "[#sec_k' _]".
iInv "Hinv" as "[>tok|(%s0 & %s0' & _ & >tok2' & _)]"; last first.
{ iDestruct (term_token_disj with "tok2 tok2'") as %dis.
  pose proof (nclose_non_empty sess2N). set_solver. }
iMod (term_meta_set sessN (s, s') with "tok") as "#Hm"; first done.
iAssert (ror_sess skI s s') as "#Hs"; first by iFrame "#".
iModIntro. iSplitL; last done.
iNext. iRight. iExists s, s'. iFrame "Hs tok2". by iLeft.
Qed.

Lemma claim_hash E skI skI' skR skR' s s' :
  ↑sealsIN ⊆ E → ↑cryptisN ⊆ E ∖ ↑sealsIN → ↑rorN ⊆ E →
  cryptis_rel_ctx -∗
  nsl_ctx skI skI' skR skR' (ror_sess skI) -∗
  inv rorN (ror_inv skI) -∗
  session skI skI' skR skR' s s' -∗ claim skI ={E}=∗
  hash_tokens s s' ∗ secret_in_l (sess_key s) ∗ secret_in_r (sess_key s').
Proof.
iIntros (HN HE HE') "#Hctx #Hnsl #Hinv #Hs claim".
iMod (session_sess with "Hctx Hnsl Hs") as (nI nI' nR nR' [Hs1 Hs2]) "(_ & _ & _ & _ & #Hss)";
  [done..|].
rewrite -Hs1 -Hs2. iPoseProof "Hss" as "(Hm & sec & sec')".
iInv "Hinv" as "[>tok|(%s0 & %s0' & >#[Hm0 _] & >tok2 & >slot)]".
{ by iDestruct (term_meta_token with "tok Hm") as "[]". }
iDestruct (term_meta_agree with "Hm Hm0") as %[= <- <-].
iDestruct "slot" as "[toks|claim']"; last first.
{ iDestruct (term_token_disj with "claim claim'") as %dis.
  pose proof (nclose_non_empty claimN). set_solver. }
iModIntro. iSplitR "toks"; last by iFrame "toks sec sec'".
iNext. iRight. iExists s, s'. iFrame "Hss tok2". by iRight.
Qed.

End Claim.

Section Tests.

Lemma setup_refinement c c' :
  cryptis_rel_ctx -∗
  lrel_channel c c' -∗
  REL setup c << setup c' : λ v v',
    (∃ (skI skI' skR skR' : aenc_key) (pkX pkX' : term),
      ⌜v = (skI : term, skR : term, pkX)%V⌝ ∗
      ⌜v' = (skI' : term, skR' : term, pkX')%V⌝ ∗
      nsl_ctx skI skI' skR skR' (ror_sess skI) ∗ inv rorN (ror_inv skI) ∗
      claim skI ∗ term_token (seed_of_aenc_key skI) (↑sess2N) ∗ PUB⟨pkX, pkX'⟩)%I.
Proof.
iIntros "#Hctx #Hc". rewrite /setup. rel_pures.
rel_bind_l (mk_aenc_key #()). rel_bind_r (mk_aenc_key #()).
iApply (mk_honest_key_refinement with "Hctx").
iIntros (skI skI') "#HI sealsI tokI" => /=. rel_pures.
rel_bind_l (mk_aenc_key #()). rel_bind_r (mk_aenc_key #()).
iApply (mk_honest_key_refinement with "Hctx").
iIntros (skR skR') "#HR sealsR _" => /=. rel_pures.
iMod (inv_alloc sealsIN _ (seals_inv skI skI' (seals_I_info skI skI' skR skR' (ror_sess skI)))
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
rewrite (term_token_difference (seed_of_aenc_key skI) (↑claimN)
           (⊤ ∖ ↑hypercryptisN)); last solve_ndisj.
iDestruct "tokI" as "[claim tokI]".
rewrite (term_token_difference (seed_of_aenc_key skI) (↑sessN)
           (⊤ ∖ ↑hypercryptisN ∖ ↑claimN)); last solve_ndisj.
iDestruct "tokI" as "[tok_sess tokI]".
rewrite (term_token_difference (seed_of_aenc_key skI) (↑sess2N)
           (⊤ ∖ ↑hypercryptisN ∖ ↑claimN ∖ ↑sessN)); last solve_ndisj.
iDestruct "tokI" as "[tok_sess2 _]".
iMod (inv_alloc rorN _ (ror_inv skI) with "[tok_sess]") as "#Hror".
{ iNext. by iLeft. }
rel_prims.
rel_apply (refines_send with "Hc []").
{ iNext. by iDestruct "HI" as "(_ & _ & _ & _ & ? & _)". }
iIntros (? ?) "[-> ->]" => /=. rel_prims.
rel_apply (refines_send with "Hc []").
{ iNext. by iDestruct "HR" as "(_ & _ & _ & _ & ? & _)". }
iIntros (? ?) "[-> ->]" => /=. rel_pures.
rel_apply (refines_recv with "Hc").
iIntros (pkX pkX') "#HpkX" => /=. rel_pures. rel_values. iModIntro.
iExists skI, skI', skR, skR', pkX, pkX'. do 2 (iSplit; first done).
iFrame "claim tok_sess2 HpkX". by iFrame "#".
Qed.

Lemma reveal_refinement b c c' s s' :
  cryptis_rel_ctx -∗
  lrel_channel c c' -∗
  hash_tokens s s' -∗ secret_in_l (sess_key s) -∗ secret_in_r (sess_key s') -∗
  REL reveal b c (sess_key s) << reveal (negb b) c' (sess_key s') : ().
Proof.
iIntros "#Hctx #Hc (tok & tok') #sec #sec'". rewrite /reveal.
iPoseProof (term_token_minted with "tok") as "#mint".
iPoseProof (term_token_spec_minted_spec with "tok'") as "#mint'".
case: b; rel_pures.
- rel_apply_r (refines_mk_senc_key_r _ _ (λ _, ∅) _ (λ _, not_elem_of_empty _) with "Hctx []").
  { by iIntros (?); rewrite big_sepS_empty. }
  iIntros (k') "%Hk' #mint_k' tok_k' _".
  destruct k' as [n']. simpl in Hk'. case/is_nonceP: Hk' => a' e. subst n'.
  iEval (rewrite minted_spec_senc) in "mint_k'".
  iDestruct (term_token_rel_token_l with "tok") as "(tok & _ & _)"; first solve_not_TSeal.
  iDestruct (term_token_rel_token_r with "tok_k'") as "(tok_k' & _ & _)";
    first solve_not_TSeal.
  iMod (public_rel_publish (E:=⊤) (t:=THash (sess_key s)) (t':=TNonce a') ltac:(solve_ndisj)
          with "Hctx [] tok tok_k'")
    as "[_ #Hpub]".
  { iIntros "!> #link". by iApply (publicly_related_opaque with "mint mint_k' link sec"). }
  iAssert (PUB⟨SEncKey (THash (sess_key s)), SEncKey (TNonce a')⟩) as "#Hk".
  { rewrite [term_of_senc_key]unlock publicly_related_TKey. by iSplit. }
  rel_prims.
  by rel_apply (refines_send with "Hc Hk").
- rel_apply_l (refines_mk_senc_key_l _ _ (λ _, ∅) _ (λ _, not_elem_of_empty _) with "Hctx []").
  { by iIntros (?); rewrite big_sepS_empty. }
  iIntros (k) "%Hk #mint_k tok_k _".
  destruct k as [n]. simpl in Hk. case/is_nonceP: Hk => a e. subst n.
  iEval (rewrite minted_senc) in "mint_k".
  iDestruct (term_token_rel_token_l with "tok_k") as "(tok_k & _ & _)"; first solve_not_TSeal.
  iDestruct (term_token_rel_token_r with "tok'") as "(tok' & _ & _)"; first solve_not_TSeal.
  iMod (public_rel_publish (E:=⊤) (t:=TNonce a) (t':=THash (sess_key s')) ltac:(solve_ndisj)
          with "Hctx [] tok_k tok'")
    as "[_ #Hpub]".
  { iIntros "!> #link". by iApply (publicly_related_opaque with "mint_k mint' link"). }
  iAssert (PUB⟨SEncKey (TNonce a), SEncKey (THash (sess_key s'))⟩) as "#Hk".
  { rewrite [term_of_senc_key]unlock publicly_related_TKey. by iSplit. }
  rel_prims.
  by rel_apply (refines_send with "Hc Hk").
Qed.

Lemma resp_test_refinement b c c' :
  cryptis_rel_ctx -∗
  lrel_channel c c' -∗
  REL resp_test b c << resp_test (negb b) c' : ().
Proof.
iIntros "#Hctx #Hc". rewrite /resp_test. rel_pures.
rel_apply (setup_refinement with "Hctx Hc").
iIntros (? ?) "(%skI & %skI' & %skR & %skR' & %pkX & %pkX' & -> & -> &
                #Hnsl & #Hror & claim & tok2 & #HpkX)" => /=.
rel_pures.
rel_bind_l (Fork _). rel_bind_r (Fork _).
iApply (refines_bind with "[]").
{ iApply refines_fork. rel_pures.
  rel_apply (init_refinement with "Hctx Hc Hnsl HpkX").
  iIntros (? ?) "_" => /=. rel_pures. by rel_values. }
iIntros (? ?) "_" => /=. rel_pures.
rel_apply (resp_refinement with "Hctx Hc Hnsl [tok2]").
{ by iApply (ror_alloc with "Hctx Hror tok2"). }
iIntros (? ?) "[[-> ->]|(%pkI & %pkI' & %k & %k' & [-> ->] & #HpkI & Hsess)]" => /=.
{ rel_pures. by rel_values. }
rel_prims.
iPoseProof "Hnsl" as "((_ & _ & _ & _ & #pub_pkI & _) & _)".
iMod (publicly_related_part_bij' (E:=⊤) with "Hctx HpkI pub_pkI") as %HX;
  first solve_ndisj.
case: (decide (pkI = Spec.pkey skI)) => [eX|neX]; last first.
{ rewrite bool_decide_eq_false_2 // bool_decide_eq_false_2; last by rewrite -HX.
  rel_pures. by rel_values. }
rewrite bool_decide_eq_true_2 // bool_decide_eq_true_2; last by apply HX.
rel_pures.
iDestruct ("Hsess" with "[//]") as (s s' [-> ->]) "Hs".
iMod (claim_hash with "Hctx Hnsl Hror Hs claim") as "(toks & #sec & #sec')"; [solve_ndisj..|].
by iApply (reveal_refinement with "Hctx Hc toks sec sec'").
Qed.

Lemma init_test_refinement b c c' :
  cryptis_rel_ctx -∗
  lrel_channel c c' -∗
  REL init_test b c << init_test (negb b) c' : ().
Proof.
iIntros "#Hctx #Hc". rewrite /init_test. rel_pures.
rel_apply (setup_refinement with "Hctx Hc").
iIntros (? ?) "(%skI & %skI' & %skR & %skR' & %pkX & %pkX' & -> & -> &
                #Hnsl & #Hror & claim & tok2 & #HpkX)" => /=.
rel_pures.
rel_bind_l (Fork _). rel_bind_r (Fork _).
iApply (refines_bind with "[tok2]").
{ iApply refines_fork. rel_pures.
  rel_apply (resp_refinement with "Hctx Hc Hnsl [tok2]").
  { by iApply (ror_alloc with "Hctx Hror tok2"). }
  iIntros (? ?) "_" => /=. rel_pures. by rel_values. }
iIntros (? ?) "_" => /=. rel_pures.
rel_apply (init_refinement with "Hctx Hc Hnsl HpkX").
iIntros (? ?) "[[-> ->]|(%k & %k' & [-> ->] & Hsess)]" => /=.
{ rel_pures. by rel_values. }
rel_prims.
iPoseProof "Hnsl" as "(_ & (_ & _ & _ & _ & #pub_pkR & _) & _)".
iMod (publicly_related_part_bij' (E:=⊤) with "Hctx HpkX pub_pkR") as %HX;
  first solve_ndisj.
case: (decide (pkX = Spec.pkey skR)) => [eX|neX]; last first.
{ rewrite bool_decide_eq_false_2 // bool_decide_eq_false_2; last by rewrite -HX.
  rel_pures. by rel_values. }
rewrite bool_decide_eq_true_2 // bool_decide_eq_true_2; last by apply HX.
rel_pures.
iDestruct ("Hsess" with "[//]") as (s s' [-> ->]) "Hs".
iMod (claim_hash with "Hctx Hnsl Hror Hs claim") as "(toks & #sec & #sec')"; [solve_ndisj..|].
by iApply (reveal_refinement with "Hctx Hc toks sec sec'").
Qed.

End Tests.

End Proofs.
