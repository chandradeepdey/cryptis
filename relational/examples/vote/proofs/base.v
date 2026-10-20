(** Ghost state of the voting case study: the arbitrator's and the voters'
    keys, the seal sets recording each voter's one ballot, and the facts
    about signatures under a secret key that the arbitrator relies on. *)

From cryptis Require Import lib cryptis primitives.
From cryptis.lib Require Import avl.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.core Require Import minted_spec term_meta_spec rel rel_inv_updates.
From cryptis.hyper.primitives Require Import simple_spec comp_spec with_cryptis_spec attacker_spec.
From cryptis.hyper.lib Require Import avl_spec.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples.vote Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Base.

Context `{!relocG Σ, !public_relGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (t n v : term).
Implicit Types (skT : aenc_key) (skV : sign_key).
Implicit Types (votes cands : list Z) (ks : list sign_key).
Implicit Types (st : list (option (term * term))).

(** * Ghost state *)

Definition ballot_ct skT n v : term :=
  Spec.random_aenc (Spec.pkey skT) (Tag (voteN.@"vote")) n v.

Definition ballot_seal skV skV' skT skT' n n' v v' : wf_seal_data * wf_seal_data :=
  (Some (skV : term, Spec.tag (Tag (voteN.@"ballot")) (ballot_ct skT n v)),
   Some (skV' : term, Spec.tag (Tag (voteN.@"ballot")) (ballot_ct skT' n' v'))).

Definition ballot_inv skV skV' skT skT' v v' : iProp :=
  (seals_auth_l (seed_of_sign_key skV) ∅ ∗
   seals_auth_r (seed_of_sign_key skV') ∅) ∨
  (∃ n n',
    seals_auth_l (seed_of_sign_key skV) {[ballot_seal skV skV' skT skT' n n' v v']} ∗
    seals_auth_r (seed_of_sign_key skV') {[ballot_seal skV skV' skT skT' n n' v v']} ∗
    term_meta (seed_of_sign_key skV) signedN ()).

Definition urn_inv skT skT' : iProp :=
  ∃ S S', seals_auth_l (seed_of_aenc_key skT) S ∗
          seals_auth_r (seed_of_aenc_key skT') S'.

Definition arb_key skT skT' : iProp :=
  ⌜is_nonce (seed_of_aenc_key skT)⌝ ∗ ⌜is_nonce (seed_of_aenc_key skT')⌝ ∗
  minted skT ∗ minted_spec skT' ∗
  PUB⟨Spec.pkey skT, Spec.pkey skT'⟩ ∗
  publicly_linked (Spec.pkey skT) (Spec.pkey skT') ∗
  secret_in_l (seed_of_aenc_key skT) ∗ secret_in_r (seed_of_aenc_key skT') ∗
  inv urnN (urn_inv skT skT').

#[global] Instance arb_key_persistent skT skT' : Persistent (arb_key skT skT').
Proof. apply _. Qed.

Definition voter_key skV skV' skT skT' v v' : iProp :=
  ⌜is_nonce (seed_of_sign_key skV)⌝ ∗ ⌜is_nonce (seed_of_sign_key skV')⌝ ∗
  minted skV ∗ minted_spec skV' ∗
  PUB⟨Spec.pkey skV, Spec.pkey skV'⟩ ∗
  secret_in_l (seed_of_sign_key skV) ∗ secret_in_r (seed_of_sign_key skV') ∗
  secret_in_l skV ∗ secret_in_r skV' ∗
  inv ballotN (ballot_inv skV skV' skT skT' v v').

#[global] Instance voter_key_persistent skV skV' skT skT' v v' :
  Persistent (voter_key skV skV' skT skT' v v').
Proof. apply _. Qed.

Lemma voter_key_pkey skV skV' skT skT' v v' :
  voter_key skV skV' skT skT' v v' -∗ PUB⟨Spec.pkey skV, Spec.pkey skV'⟩.
Proof. by iIntros "(_ & _ & _ & _ & ? & _)". Qed.

Lemma urn_inv_insert E skT skT' e (P : iProp) :
  ↑urnN ⊆ E →
  inv urnN (urn_inv skT skT') -∗
  (∀ S S', seals_auth_l (seed_of_aenc_key skT) S -∗
           seals_auth_r (seed_of_aenc_key skT') S' ={E ∖ ↑urnN}=∗
           seals_auth_l (seed_of_aenc_key skT) (S ∪ {[e]}) ∗
           seals_auth_r (seed_of_aenc_key skT') (S' ∪ {[e]}) ∗ P) ={E}=∗ P.
Proof.
iIntros (HE) "#Hinv upd".
iInv "Hinv" as "(%S & %S' & >seals & >seals')".
iMod ("upd" with "seals seals'") as "(seals & seals' & HP)".
iModIntro. iSplitR "HP"; last done.
iNext. iExists _, _. iFrame.
Qed.

Lemma ballot_inv_sign E skV skV' skT skT' v v' n n' :
  ↑ballotN ⊆ E →
  inv ballotN (ballot_inv skV skV' skT skT' v v') -∗
  term_token (seed_of_sign_key skV) (↑signedN) ={E}=∗
  seals_l (seed_of_sign_key skV) (ballot_seal skV skV' skT skT' n n' v v') ∗
  seals_r (seed_of_sign_key skV') (ballot_seal skV skV' skT skT' n n' v v').
Proof.
iIntros (HE) "#Hinv token".
iInv "Hinv" as "[(>seals & >seals')|(%n0 & %n0' & _ & _ & >#Hsigned)]"; last first.
{ by iDestruct (term_meta_token with "token Hsigned") as "[]". }
iMod (term_meta_set signedN () (↑signedN) (seed_of_sign_key skV) ltac:(done)
        with "token") as "#Hsigned".
iMod (seals_auth_l_insert _ _ (ballot_seal skV skV' skT skT' n n' v v')
        with "seals") as "[seals #Hl]".
iMod (seals_auth_r_insert _ _ (ballot_seal skV skV' skT skT' n n' v v')
        with "seals'") as "[seals' #Hr]".
rewrite !left_id_L.
iModIntro. iSplitL; last by iFrame "#".
iNext. iRight. iExists n, n'. by iFrame "#∗".
Qed.

Lemma ballot_inv_lookup E skV skV' skT skT' v v' e :
  ↑ballotN ⊆ E →
  inv ballotN (ballot_inv skV skV' skT skT' v v') -∗
  seals_l (seed_of_sign_key skV) e ={E}=∗
  ⌜∃ n n', e = ballot_seal skV skV' skT skT' n n' v v'⌝.
Proof.
iIntros (HE) "#Hinv #Hl".
iInv "Hinv" as "[(>seals & >seals')|(%n & %n' & >seals & >seals' & >#Hsigned)]".
- by iDestruct (seals_auth_l_elem_of with "seals Hl") as %?%not_elem_of_empty.
- iDestruct (seals_auth_l_elem_of with "seals Hl") as %->%elem_of_singleton.
  iModIntro. iSplitL; last by eauto.
  iNext. iRight. iExists n, n'. by iFrame "#∗".
Qed.

(** * Signatures under a secret key *)

Lemma pub_verify_key skV skV' :
  minted skV -∗ minted_spec skV' -∗
  secret_in_l (seed_of_sign_key skV) -∗ secret_in_r (seed_of_sign_key skV') -∗
  publicly_linked (Spec.pkey skV) (Spec.pkey skV') -∗
  PUB⟨Spec.pkey skV, Spec.pkey skV'⟩.
Proof.
case: skV skV' => [s] [s']. rewrite [term_of_sign_key]unlock.
rewrite -[Spec.pkey (TKey Sign s)]/(TKey Verify s) -[Spec.pkey (TKey Sign s')]/(TKey Verify s').
rewrite minted_TKey minted_spec_TKey publicly_related_TKey.
iIntros "#? #? #? #? #?". iSplit; first done. iRight.
do 3 (iSplit; first done).
iSplit; [by iApply secret_in_l_linked_in_l | by iApply secret_in_r_linked_in_r].
Qed.

Lemma pub_sign skV skV' t t' :
  minted skV -∗ minted_spec skV' -∗
  secret_in_l skV -∗ secret_in_r skV' -∗
  PUB⟨Spec.pkey skV, Spec.pkey skV'⟩ -∗
  PUB⟨t, t'⟩ -∗
  publicly_linked t t' -∗
  seals_l (seed_of_sign_key skV) (Some (skV : term, t), Some (skV' : term, t')) -∗
  seals_r (seed_of_sign_key skV') (Some (skV : term, t), Some (skV' : term, t')) -∗
  publicly_linked (TSeal skV t) (TSeal skV' t') -∗
  PUB⟨TSeal skV t, TSeal skV' t'⟩.
Proof.
case: skV skV' => [s] [s']. rewrite [term_of_sign_key]unlock.
rewrite -[Spec.pkey (TKey Sign s)]/(TKey Verify s) -[Spec.pkey (TKey Sign s')]/(TKey Verify s').
iIntros "#mint #mint' #sec #sec' #Hpk #Ht #Ht_link #Hsl #Hsr #Hlink".
iPoseProof (publicly_related_minted with "Ht") as "[? ?]".
rewrite publicly_related_TSeal. iRight.
rewrite minted_TSeal minted_spec_TSeal.
iSplit; first by iSplit. iSplit; first by iSplit. iSplit; first done.
iSplit; first by iSplit; [iApply secret_in_l_linked_in_l | iApply secret_in_r_linked_in_r].
iSplit; first by iApply publicly_linked_linked.
iModIntro. iSplit; first done. iSplit; first done. iSplit; first done.
by iSplit.
Qed.

Lemma pub_sign_inv skV w t' :
  is_nonce (seed_of_sign_key skV) →
  secret_in_l (seed_of_sign_key skV) -∗
  PUB⟨TSeal skV w, t'⟩ -∗
  ∃ s' w', ⌜t' = TSeal (TKey Sign s') w'⌝ ∧ PUB⟨w, w'⟩ ∧
    seals_l (seed_of_sign_key skV) (Some (skV : term, w), Some (TKey Sign s', w')).
Proof.
case: skV => [s] Hnonce. rewrite [term_of_sign_key]unlock.
iIntros "#sec #Ht".
have [[k' [w' ->]]|Hns] : (∃ k' w', t' = TSeal k' w') ∨ (∀ k' w', t' ≠ TSeal k' w').
{ case: t' => *; try by right. left; eauto. }
- rewrite publicly_related_TSeal.
  iDestruct "Ht" as "[[Hk _]|(_ & _ & _ & _ & _ & #Hbox)]".
  + iDestruct (publicly_related_TKey_term with "Hk") as %[s' ->].
    rewrite publicly_related_TKey. iDestruct "Hk" as "[_ Hk]".
    iDestruct (publicly_related_nonce_term _ Hnonce with "Hk") as "[Hl _]".
    by iDestruct (secret_in_l_publicly_linked_in_l with "sec Hl") as "[]".
  + case: k' => [n'|a' b'|a'|kt' s'|k' b'|s'|pt' wf' nf']; try by iDestruct "Hbox" as "[]".
    iDestruct "Hbox" as "[<- (_ & Hw & [Hl _])]".
    iExists s', w'. by eauto.
- by iDestruct (publicly_related_TSeal_term_wf Sign _ _ Hns with "Ht") as "[]".
Qed.

(** The arbitrator's view of a message: either it is not a ballot of this
    voter in either run, or it is the voter's ballot in both. *)
Lemma pub_verify_cases skV skV' skT skT' v v' t t' :
  cryptis_rel_ctx -∗
  voter_key skV skV' skT skT' v v' -∗
  PUB⟨t, t'⟩ ={⊤}=∗
  ⌜Spec.dec (Spec.pkey skV) (Tag (voteN.@"ballot")) t = None ∧
   Spec.dec (Spec.pkey skV') (Tag (voteN.@"ballot")) t' = None⌝ ∨
  ∃ n n',
    ⌜t = TSeal skV (Spec.tag (Tag (voteN.@"ballot")) (ballot_ct skT n v))⌝ ∧
    ⌜t' = TSeal skV' (Spec.tag (Tag (voteN.@"ballot")) (ballot_ct skT' n' v'))⌝.
Proof.
iIntros "#Hctx (%Hnonce & %Hnonce' & _ & _ & #Hpk & #sec & _ & _ & _ & #Hinv) #Ht".
iMod (publicly_related_open_fupd (E:=⊤) _ _ t t' ltac:(solve_ndisj)
        with "Hctx Hpk Ht") as %Hiff.
rewrite /Spec.dec.
case: (Spec.openP (Spec.pkey skV) t) Hiff => [k w Hk -> Hiff|Hiff].
- move/Spec.open_key_signK: Hk => ->.
  iDestruct (pub_sign_inv _ _ Hnonce with "sec Ht") as "(%s' & %w' & -> & _ & #Hl)".
  iMod (ballot_inv_lookup with "Hinv Hl") as %(n & n' & e); first solve_ndisj.
  move: e. rewrite /ballot_seal. case=> -> e' ->. rewrite e'.
  iModIntro. iRight. iExists n, n'. by iSplit.
- have Hnone : Spec.open (Spec.pkey skV') t' = None.
  { case e: (Spec.open _ t') => [w'|] //.
    by have := proj2 Hiff (mk_is_Some _ _ e). }
  rewrite Hnone. by iLeft.
Qed.

(** * Key generation *)

Lemma rel_mk_arb_key K K' Ψ :
  cryptis_rel_ctx -∗
  (∀ skT skT', arb_key skT skT' -∗
     REL fill K (skT : expr) << fill K' (skT' : expr) : Ψ) -∗
  REL fill K (mk_aenc_key #()) << fill K' (mk_aenc_key #()) : Ψ.
Proof.
iIntros "#Hctx post".
have Hdisj : ∀ sk : aenc_key,
    seed_of_aenc_key sk ∉ (∅ : gset term) ∧
    seed_of_aenc_key sk ∉ ({[Spec.pkey sk]} : gset term) ∧
    (∅ : gset term) ## ({[Spec.pkey sk]} : gset term).
{ move=> sk. rewrite /Spec.pkey [term_of_aenc_key]unlock /=.
  have Hne : ∀ kt (t : term), t ≠ TKey kt t.
  { move=> kt t H. have := f_equal tsize H.
    rewrite (tsize_eq (TKey kt t)). lia. }
  set_solver. }
rel_apply_l (rel_mk_aenc_key_l _ _ (λ _, ∅) (λ t, {[t]}) _ Hdisj with "[//]");
  [solve_minted_iff.. |].
iIntros (skT) "%Hnonce #mint_sk token_s _ token_pk".
rel_apply_r (rel_mk_aenc_key_r _ _ (λ _, ∅) (λ t, {[t]}) _ Hdisj with "[//]");
  [solve_minted_iff.. |].
iIntros (skT') "%Hnonce' #mint_sk' token_s' _ token_pk'".
split_term_tokens.
iMod (public_rel_secret_seals_l (E:=⊤) Hnonce ltac:(solve_ndisj) with "Hctx token_s")
  as "(#secret_s & seals & _ & _)".
iMod (public_rel_secret_seals_r (E:=⊤) Hnonce' ltac:(solve_ndisj) with "Hctx token_s'")
  as "(#secret_s' & seals' & _ & _)".
iMod (public_rel_publish (E:=⊤) ltac:(solve_ndisj) with "Hctx [] token_pk token_pk'")
  as "[#elem_pk #pub_pk]".
{ iIntros "!> #elem". rewrite publicly_related_aenc_key. iRight.
  do 3 (iSplit; first done).
  iSplit; [by iApply secret_in_l_linked_in_l | by iApply secret_in_r_linked_in_r]. }
iMod (inv_alloc urnN _ (urn_inv skT skT') with "[seals seals']") as "#Hurn".
{ iNext. iExists ∅, ∅. iFrame. }
iApply "post". do 4 (iSplit; first done). by iFrame "#".
Qed.

Lemma rel_mk_voter_key K K' skT skT' v v' Ψ :
  cryptis_rel_ctx -∗
  (∀ skV skV', voter_key skV skV' skT skT' v v' -∗
     term_token (seed_of_sign_key skV) (↑signedN) -∗
     REL fill K (skV : expr) << fill K' (skV' : expr) : Ψ) -∗
  REL fill K (mk_sign_key #()) << fill K' (mk_sign_key #()) : Ψ.
Proof.
iIntros "#Hctx post".
have Hdisj : ∀ sk : sign_key,
    seed_of_sign_key sk ∉ ({[sk : term]} : gset term) ∧
    seed_of_sign_key sk ∉ ({[Spec.pkey sk]} : gset term) ∧
    ({[sk : term]} : gset term) ## ({[Spec.pkey sk]} : gset term).
{ move=> sk. rewrite /Spec.pkey [term_of_sign_key]unlock /=.
  have Hne : ∀ kt (t : term), t ≠ TKey kt t.
  { move=> kt t H. have := f_equal tsize H.
    rewrite (tsize_eq (TKey kt t)). lia. }
  set_solver. }
rel_apply_l (rel_mk_sign_key_l _ _ (λ t, {[t]}) (λ t, {[t]}) _ Hdisj with "[//]");
  [solve_minted_iff.. |].
iIntros (skV) "%Hnonce #mint_sk token_s token_sk token_pk".
rel_apply_r (rel_mk_sign_key_r _ _ (λ t, {[t]}) (λ t, {[t]}) _ Hdisj with "[//]");
  [solve_minted_iff.. |].
iIntros (skV') "%Hnonce' #mint_sk' token_s' token_sk' token_pk'".
split_term_tokens.
(* Seeds: secret; they protect the signing keys, which are secret in turn. *)
iMod (public_rel_secret_seals_l (E:=⊤) Hnonce ltac:(solve_ndisj) with "Hctx token_s")
  as "(#secret_s & seals & prot_s & token_s)".
iMod (public_rel_secret_seals_r (E:=⊤) Hnonce' ltac:(solve_ndisj) with "Hctx token_s'")
  as "(#secret_s' & seals' & prot_s' & _)".
rewrite (term_token_difference (seed_of_sign_key skV) (↑signedN)
           (⊤ ∖ ↑cryptisN.@"public_rel")); last solve_ndisj.
iDestruct "token_s" as "[token_signed _]".
iMod (public_rel_secret_step_l (E:=⊤) (is_immediate_subterm_sign_key skV)
        ltac:(solve_ndisj) with "Hctx secret_s prot_s token_sk") as "(#secret_sk & _ & _)".
iMod (public_rel_secret_step_r (E:=⊤) (is_immediate_subterm_sign_key skV')
        ltac:(solve_ndisj) with "Hctx secret_s' prot_s' token_sk'") as "(#secret_sk' & _ & _)".
(* Verification keys: publicly related. *)
iMod (public_rel_publish (E:=⊤) ltac:(solve_ndisj) with "Hctx [] token_pk token_pk'")
  as "[#elem_pk #pub_pk]".
{ iIntros "!> #elem". by iApply (pub_verify_key with "mint_sk mint_sk' secret_s secret_s' elem"). }
iMod (inv_alloc ballotN _ (ballot_inv skV skV' skT skT' v v') with "[seals seals']")
  as "#Hballot".
{ iNext. iLeft. iFrame. }
iApply ("post" with "[] token_signed").
do 4 (iSplit; first done). by iFrame "#".
Qed.

Definition pkeys ks : list term := map (λ sk : sign_key, Spec.pkey sk) ks.

Definition voter_keys skT skT' ks ks' votes votes' : iProp :=
  [∗ list] j ↦ sk; sk' ∈ ks; ks',
    voter_key sk sk' skT skT' (TInt (votes !!! j)) (TInt (votes' !!! j)).

#[global] Instance voter_keys_persistent skT skT' ks ks' votes votes' :
  Persistent (voter_keys skT skT' ks ks' votes votes').
Proof. apply _. Qed.

Definition voter_tokens ks : iProp :=
  [∗ list] sk ∈ ks, term_token (seed_of_sign_key sk) (↑signedN).

Lemma pub_of_list (ts ts' : list term) :
  ([∗ list] t; t' ∈ ts; ts', PUB⟨t, t'⟩) -∗ PUB⟨Spec.of_list ts, Spec.of_list ts'⟩.
Proof.
rewrite [Spec.of_list]unlock.
iInduction ts as [|t ts] "IH" forall (ts'); iIntros "H".
- iDestruct (big_sepL2_nil_inv_l with "H") as %->.
  rewrite -[foldr TPair (TInt 0) []]/(TInt 0) publicly_related_TInt. by iPureIntro.
- iDestruct (big_sepL2_cons_inv_l with "H") as (t' ts'' ->) "[Ht H]".
  rewrite -[foldr TPair (TInt 0) (t :: ts)]/(TPair t (foldr TPair (TInt 0) ts)).
  rewrite -[foldr TPair (TInt 0) (t' :: ts'')]/(TPair t' (foldr TPair (TInt 0) ts'')).
  rewrite publicly_related_TPair. iSplit; first done. by iApply "IH".
Qed.

Lemma pub_pkeys skT skT' ks ks' votes votes' :
  voter_keys skT skT' ks ks' votes votes' -∗
  [∗ list] t; t' ∈ pkeys ks; pkeys ks', PUB⟨t, t'⟩.
Proof.
rewrite /voter_keys /pkeys.
iInduction ks as [|sk ks] "IH" forall (ks' votes votes'); iIntros "H".
- by iDestruct (big_sepL2_nil_inv_l with "H") as %->.
- iDestruct (big_sepL2_cons_inv_l with "H") as (sk' ks'' ->) "[HV H]". simpl.
  iSplit; first by iApply (voter_key_pkey with "HV").
  iApply ("IH" $! ks'' (tail votes) (tail votes') with "[H]").
  iApply (big_sepL2_mono with "H") => k y1 y2 _ _.
  by case: votes; case: votes' => /=.
Qed.

End Base.
