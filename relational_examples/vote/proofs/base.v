(** * Ghost state of the voting case study

- [GhostState]: the arbitrator's and the voters' keys, and the invariants
  that record each voter's one ballot.
- [Signatures]: what a signature under a voter's secret key tells the
  arbitrator.
- [KeyGeneration]: creating the arbitrator's and the voters' keys.
- [Voters]: the keys of all the voters together. *)

From cryptis Require Import cryptis primitives.
From reloc Require Import reloc.
From cryptis.hyper.core Require Import minted_spec term_meta_spec public.
From cryptis.hyper.primitives Require Import with_cryptis.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples Require Import nondet_aenc.
From cryptis.hyper.examples.vote Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Base.

Context `{!relocG Σ, !publicGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (t n v : term).
Implicit Types (skT : aenc_key) (skV : sign_key).
Implicit Types (votes cands : list Z) (ks : list sign_key).
Implicit Types (st : list (option (term * term))).

Section GhostState.

Definition ballot_body ct : term :=
  Spec.tag (Tag (voteN.@"ballot")) ct.

Definition ballot_sig skV ct : term :=
  Spec.enc skV (Tag (voteN.@"ballot")) ct.

Definition ballot_inv skV skV' skT skT' v v' : iProp :=
  (term_token skV (↑sealN) ∗
   term_token_spec skV' (↑sealN)) ∨
  (∃ ct ct',
    ⌜nondet_open skT (Tag (voteN.@"vote")) ct = Some v⌝ ∗
    ⌜nondet_open skT' (Tag (voteN.@"vote")) ct' = Some v'⌝ ∗
    term_token skV
      (↑sealN ∖ ↑seal_namespace (ballot_body ct)) ∗
    term_token_spec skV'
      (↑sealN ∖ ↑seal_namespace (ballot_body ct')) ∗
    publicly_linked (ballot_sig skV ct) (ballot_sig skV' ct') ∗
    term_meta (seed_of_sign_key skV) signedN ()).

Definition urn_inv skT skT' : iProp :=
  ∃ Ek Ek' Eh Eh',
    never_sealed_under (Spec.pkey skT) (Spec.pkey skT') Ek Ek' ∗
    term_token (Spec.pkey skT) Eh ∗
    term_token_spec (Spec.pkey skT') Eh' ∗
    □ (∀ p, ⌜↑seal_namespace p ⊆ Ek ∧ ↑holdN.@p ⊆ Eh⌝ ∨
            term_meta (TSeal (Spec.pkey skT) p) urnN ()) ∗
    □ (∀ p', ⌜↑seal_namespace p' ⊆ Ek' ∧ ↑holdN.@p' ⊆ Eh'⌝ ∨
             term_meta_spec (TSeal (Spec.pkey skT') p') urnN ()).

Definition arb_key skT skT' : iProp :=
  ⌜is_nonce (seed_of_aenc_key skT)⌝ ∗ ⌜is_nonce (seed_of_aenc_key skT')⌝ ∗
  minted skT ∗ minted_spec skT' ∗
  PUB⟨Spec.pkey skT, Spec.pkey skT'⟩ ∗
  publicly_linked (Spec.pkey skT) (Spec.pkey skT') ∗
  secret_in_l (seed_of_aenc_key skT) ∗ secret_in_r (seed_of_aenc_key skT') ∗
  secret_in_l skT ∗ secret_in_r skT' ∗
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

Lemma urn_inv_seal E skT skT' p p' (P : iProp) :
  ↑urnN ⊆ E →
  inv urnN (urn_inv skT skT') -∗
  term_token (TSeal (Spec.pkey skT) p) (↑urnN) -∗
  term_token_spec (TSeal (Spec.pkey skT') p') (↑urnN) -∗
  (never_sealed_under (Spec.pkey skT) (Spec.pkey skT')
     (↑seal_namespace p) (↑seal_namespace p') -∗
   holds_key_l p (Spec.pkey skT) -∗
   holds_key_r p' (Spec.pkey skT') ={E ∖ ↑urnN}=∗ P) ={E}=∗ P.
Proof.
iIntros (HE) "#Hinv tc tc' upd".
iInv "Hinv" as "(%Ek & %Ek' & %Eh & %Eh' & >[ns ns'] & >hold & >hold' & >#Hall & >#Hall')".
iDestruct ("Hall" $! p) as "[[%sub_s %sub_h]|#Hm]"; last first.
{ by iDestruct (term_meta_token with "tc Hm") as "[]". }
iDestruct ("Hall'" $! p') as "[[%sub_s' %sub_h']|#Hm']"; last first.
{ by iDestruct (term_meta_spec_token with "tc' Hm'") as "[]". }
rewrite (term_token_difference _ (↑seal_namespace p) Ek) //.
rewrite (term_token_spec_difference _ (↑seal_namespace p') Ek') //.
rewrite (term_token_difference _ (↑holdN.@p) Eh) //.
rewrite (term_token_spec_difference _ (↑holdN.@p') Eh') //.
iDestruct "ns" as "[ns_p ns]". iDestruct "ns'" as "[ns_p' ns']".
iDestruct "hold" as "[hold_p hold]". iDestruct "hold'" as "[hold_p' hold']".
iMod ("upd" with "[$ns_p $ns_p'] hold_p hold_p'") as "HP".
iMod (term_meta_set urnN () with "tc") as "#Hm"; first done.
iMod (term_meta_spec_set urnN () with "tc'") as "#Hm'"; first done.
iModIntro. iSplitR "HP"; last done.
iNext. iExists _, _, _, _. iFrame "ns ns' hold hold'". iSplit; iIntros "!>".
- iIntros (q). case: (decide (q = p)) => [->|ne]; first by iRight.
  iDestruct ("Hall" $! q) as "[[%subq %subhq]|$]". iLeft. iPureIntro.
  split; apply subseteq_difference_r => //; apply ndot_ne_disjoint; congruence.
- iIntros (q'). case: (decide (q' = p')) => [->|ne]; first by iRight.
  iDestruct ("Hall'" $! q') as "[[%subq %subhq]|$]". iLeft. iPureIntro.
  split; apply subseteq_difference_r => //; apply ndot_ne_disjoint; congruence.
Qed.

Lemma ballot_inv_sign E skV skV' skT skT' v v' ct ct' :
  nondet_open skT (Tag (voteN.@"vote")) ct = Some v →
  nondet_open skT' (Tag (voteN.@"vote")) ct' = Some v' →
  ↑ballotN ⊆ E → ↑cryptisN ⊆ E ∖ ↑ballotN →
  hypercryptis_ctx -∗
  inv ballotN (ballot_inv skV skV' skT skT' v v') -∗
  term_token (seed_of_sign_key skV) (↑signedN) -∗
  PUB⟨ballot_body ct, ballot_body ct'⟩ -∗
  □ (publicly_linked (ballot_sig skV ct) (ballot_sig skV' ct') -∗
     PUB⟨ballot_sig skV ct, ballot_sig skV' ct'⟩) ={E}=∗
  PUB⟨ballot_sig skV ct, ballot_sig skV' ct'⟩.
Proof.
iIntros (Ho Ho' HN HE) "#Hctx #Hinv token #Hbody #Hwand".
iInv "Hinv" as "[(>tok & >tok')|(%ct1 & %ct1' & _ & _ & _ & _ & _ & >#Hsigned)]" "Hclose"; last first.
{ by iDestruct (term_meta_token with "token Hsigned") as "[]". }
iMod (term_meta_set signedN () (↑signedN) (seed_of_sign_key skV) ltac:(done)
        with "token") as "#Hsigned".
rewrite /ballot_inv /ballot_sig /Spec.enc !(sign_key_TKey skV) !(sign_key_TKey skV').
iMod (public_seal _ _ HE (nclose_subseteq _ _) (nclose_subseteq _ _)
        with "Hctx Hwand [] [$tok $tok']") as "(#Hl & #Hpub & tok & tok')".
{ iIntros "_ _". by iSplit. }
iMod ("Hclose" with "[tok tok']") as "_".
{ iNext. iRight. iExists ct, ct'. by iFrame "#∗". }
by iModIntro.
Qed.

Lemma ballot_inv_lookup E skV skV' skT skT' v v' w x :
  ↑ballotN ⊆ E → ↑cryptisN ⊆ E ∖ ↑ballotN →
  hypercryptis_ctx -∗
  inv ballotN (ballot_inv skV skV' skT skT' v v') -∗
  publicly_linked (TSeal skV w) x ={E}=∗
  ⌜∃ ct ct',
     nondet_open skT (Tag (voteN.@"vote")) ct = Some v ∧
     nondet_open skT' (Tag (voteN.@"vote")) ct' = Some v' ∧
     w = ballot_body ct ∧ x = TSeal skV' (ballot_body ct')⌝.
Proof.
iIntros (HN HE) "#Hctx #Hinv #[Hl _]".
iDestruct (publicly_linked_in_l_linked_in_l with "Hl") as "#Hll".
iInv "Hinv" as "[(>tok & >tok')|(%ct & %ct' & >%Ho & >%Ho' & >tok & >tok' & >#Hsu & >#Hsigned)]".
- rewrite (sign_key_TKey skV).
  iMod (linked_in_l_states_token_fupd _ _ HE with "Hctx Hll [tok]") as "[]".
  rewrite /states_token_l /=. iApply (term_token_drop with "tok"). rewrite /seal_namespace. solve_ndisj.
- case: (decide (w = ballot_body ct)) => [ew|ne]; last first.
  { have Hd : (↑seal_namespace w : coPset) ## ↑seal_namespace (ballot_body ct).
    { rewrite /seal_namespace. by apply ndot_ne_disjoint. }
    have Hsub : (↑seal_namespace w.@"states" : coPset) ⊆
                ↑sealN ∖ ↑seal_namespace (ballot_body ct).
    { apply subseteq_difference_r; last by rewrite /seal_namespace; solve_ndisj.
      have : (↑seal_namespace w.@"states" : coPset) ⊆ ↑seal_namespace w by solve_ndisj.
      set_solver. }
    rewrite (sign_key_TKey skV) in Hsub *.
    iMod (linked_in_l_states_token_fupd _ _ HE with "Hctx Hll [tok]") as "[]".
    rewrite /states_token_l /=. by iApply (term_token_drop with "tok"). }
  subst w. iPoseProof "Hsu" as "[Hsul _]".
  iDestruct (publicly_linked_in_l_agree with "Hl Hsul") as %->.
  iModIntro. iSplitL "tok tok'".
  { iNext. iRight. iExists ct, ct'. do 2 (iSplit; first done). iFrame "tok tok'". by iSplit. }
  iPureIntro. by exists ct, ct'.
Qed.

End GhostState.

Section Signatures.

Lemma pub_verify_key skV skV' :
  minted skV -∗ minted_spec skV' -∗
  secret_in_l (seed_of_sign_key skV) -∗ secret_in_r (seed_of_sign_key skV') -∗
  publicly_linked (Spec.pkey skV) (Spec.pkey skV') -∗
  PUB⟨Spec.pkey skV, Spec.pkey skV'⟩.
Proof.
case: skV skV' => [s] [s']. rewrite [term_of_sign_key]unlock.
rewrite -[Spec.pkey (TKey Sign s)]/(TKey Verify s) -[Spec.pkey (TKey Sign s')]/(TKey Verify s').
rewrite minted_TKey minted_spec_TKey public_TKey.
iIntros "#? #? #? #? #?". iSplit; first done. iRight.
do 3 (iSplit; first done). iSplit; last done.
by iApply secret_in_linked.
Qed.

Lemma pub_sign skV skV' t t' :
  minted skV -∗ minted_spec skV' -∗
  secret_in_l skV -∗ secret_in_r skV' -∗
  PUB⟨Spec.pkey skV, Spec.pkey skV'⟩ -∗
  PUB⟨t, t'⟩ -∗
  publicly_linked (TSeal skV t) (TSeal skV' t') -∗
  PUB⟨TSeal skV t, TSeal skV' t'⟩.
Proof.
case: skV skV' => [s] [s']. rewrite [term_of_sign_key]unlock.
rewrite -[Spec.pkey (TKey Sign s)]/(TKey Verify s) -[Spec.pkey (TKey Sign s')]/(TKey Verify s').
iIntros "#mint #mint' #sec #sec' #Hpk #Ht #Hl".
iPoseProof (public_minted with "Ht") as "[? ?]".
rewrite public_TSeal. iRight.
rewrite minted_TSeal minted_spec_TSeal.
iSplit; first by iSplit. iSplit; first by iSplit. iSplit; first done.
iLeft. iSplit.
- by iApply secret_in_linked.
- iModIntro. by iSplit.
Qed.

Lemma pub_sign_inv skV w t' :
  is_nonce (seed_of_sign_key skV) →
  secret_in_l (seed_of_sign_key skV) -∗ secret_in_l skV -∗
  PUB⟨TSeal skV w, t'⟩ -∗
  ∃ s' w', ⌜t' = TSeal (TKey Sign s') w'⌝ ∧ PUB⟨w, w'⟩ ∧
    publicly_linked (TSeal skV w) t'.
Proof.
case: skV => [s] Hnonce. rewrite [term_of_sign_key]unlock.
iIntros "#sec #sec_k #Ht".
iDestruct (public_TSeal_term with "Ht") as "[(%k' & %w' & ->)|(_ & Ho & _)]";
  last by iSimpl in "Ho"; iDestruct "Ho" as "[]".
iDestruct (public_TSeal with "Ht") as "[[Hk _]|(_ & _ & Hl & [[_ #Hbox]|[Ho _]])]".
- iExFalso. by iApply (secret_in_l_TKey_public _ _ Hnonce with "sec sec_k Hk").
- case: k' => [n'|a' b'|a'|kt' s'|k' b'|s'|pt' wf' nf']; try by iDestruct "Hbox" as "[]".
  case: kt'; try by iDestruct "Hbox" as "[]".
  iDestruct "Hbox" as "[_ Hw]".
  iExists s', w'. by eauto.
- iSimpl in "Ho". by iDestruct "Ho" as "[]".
Qed.

(** The arbitrator's view of a message: either it is not a ballot of this
    voter in either run, or it is the voter's ballot in both. *)
Lemma pub_verify_cases skV skV' skT skT' v v' t t' :
  hypercryptis_ctx -∗
  voter_key skV skV' skT skT' v v' -∗
  PUB⟨t, t'⟩ ={⊤}=∗
  ⌜Spec.dec (Spec.pkey skV) (Tag (voteN.@"ballot")) t = None ∧
   Spec.dec (Spec.pkey skV') (Tag (voteN.@"ballot")) t' = None⌝ ∨
  ∃ ct ct',
    ⌜nondet_open skT (Tag (voteN.@"vote")) ct = Some v⌝ ∧
    ⌜nondet_open skT' (Tag (voteN.@"vote")) ct' = Some v'⌝ ∧
    ⌜t = TSeal skV (Spec.tag (Tag (voteN.@"ballot")) ct)⌝ ∧
    ⌜t' = TSeal skV' (Spec.tag (Tag (voteN.@"ballot")) ct')⌝.
Proof.
iIntros "#Hctx (%Hnonce & %Hnonce' & _ & _ & #Hpk & #sec & _ & #sec_k & _ & #Hinv) #Ht".
iMod (public_open_fupd (E:=⊤) _ _ t t' ltac:(solve_ndisj)
        with "Hctx Hpk Ht") as %Hiff.
rewrite /Spec.dec.
case: (Spec.openP (Spec.pkey skV) t) Hiff => [k w Hk -> Hiff|Hiff].
- move/Spec.open_key_signK: Hk => ->.
  iDestruct (pub_sign_inv _ _ Hnonce with "sec sec_k Ht") as "(%s' & %w' & _ & _ & #Hl)".
  iMod (ballot_inv_lookup with "Hctx Hinv Hl") as %(ct & ct' & Ho & Ho' & -> & ->); [solve_ndisj..|].
  iModIntro. iRight. iExists ct, ct'. by repeat iSplit.
- have Hnone : Spec.open (Spec.pkey skV') t' = None.
  { case e: (Spec.open _ t') => [w'|] //.
    by have := proj2 Hiff (mk_is_Some _ _ e). }
  rewrite Hnone. by iLeft.
Qed.

End Signatures.

Section KeyGeneration.

Lemma mk_arb_key_refinement K K' Ψ :
  hypercryptis_ctx -∗
  (∀ skT skT', arb_key skT skT' -∗
     REL fill K (skT : expr) << fill K' (skT' : expr) : Ψ) -∗
  REL fill K (mk_aenc_key #()) << fill K' (mk_aenc_key #()) : Ψ.
Proof.
iIntros "#Hctx post".
have Hdisj : ∀ sk : aenc_key,
    seed_of_aenc_key sk ∉ ({[sk : term]} : gset term) ∧
    seed_of_aenc_key sk ∉ ({[Spec.pkey sk]} : gset term) ∧
    ({[sk : term]} : gset term) ## ({[Spec.pkey sk]} : gset term).
{ move=> sk. rewrite /Spec.pkey [term_of_aenc_key]unlock /=.
  have Hne : ∀ kt (t : term), t ≠ TKey kt t.
  { move=> kt t H. have := f_equal tsize H.
    rewrite (tsize_eq (TKey kt t)). lia. }
  have Hkt : ∀ t, TKey ADec t ≠ TKey AEnc t by congruence.
  set_solver. }
rel_apply_l (refines_mk_aenc_key_l _ _ (λ t, {[t]}) (λ t, {[t]}) _ Hdisj with "[//]");
  [solve_minted_iff.. |].
iIntros (skT) "%Hnonce #mint_sk token_s token_sk token_pk".
rel_apply_r (refines_mk_aenc_key_r _ _ (λ t, {[t]}) (λ t, {[t]}) _ Hdisj with "[//]");
  [solve_minted_iff.. |].
iIntros (skT') "%Hnonce' #mint_sk' token_s' token_sk' token_pk'".
split_term_tokens.
iMod (public_secret_nonce_l (E:=⊤) Hnonce ltac:(solve_ndisj) with "Hctx token_s")
  as "[#secret_s _]".
iMod (public_secret_nonce_r (E:=⊤) Hnonce' ltac:(solve_ndisj) with "Hctx token_s'")
  as "[#secret_s' _]".
iDestruct (term_token_public_token_l with "token_sk") as "(token_sk & _ & _)";
  first solve_not_TSeal.
iDestruct (term_token_public_token_r with "token_sk'") as "(token_sk' & _ & _)";
  first solve_not_TSeal.
iMod (public_secret_step_l (E:=⊤) (is_immediate_subterm_aenc_key skT) ltac:(solve_ndisj)
        with "Hctx secret_s token_sk") as "#secret_sk".
iMod (public_secret_step_r (E:=⊤) (is_immediate_subterm_aenc_key skT') ltac:(solve_ndisj)
        with "Hctx secret_s' token_sk'") as "#secret_sk'".
iDestruct (term_token_public_token_l with "token_pk") as "(token_pk & seals & holds & _)";
  first solve_not_TSeal.
iDestruct (term_token_public_token_r with "token_pk'") as "(token_pk' & seals' & holds' & _)";
  first solve_not_TSeal.
iMod (public_publish (E:=⊤) ltac:(solve_ndisj)
        with "Hctx [] [] [] token_pk token_pk'") as "[#elem_pk #pub_pk]".
{ iIntros "!> #elem". rewrite public_aenc_key. iRight.
  do 3 (iSplit; first done).
  by iApply secret_in_linked. }
{ by rewrite [term_of_aenc_key]unlock. }
{ by rewrite [term_of_aenc_key]unlock. }
iMod (inv_alloc urnN _ (urn_inv skT skT') with "[seals seals' holds holds']") as "#Hurn".
{ iNext. iExists _, _, _, _. iFrame "seals seals' holds holds'".
  iSplit; iIntros "!>" (?); iLeft; iPureIntro; split; apply nclose_subseteq. }
iApply "post". do 4 (iSplit; first done). by iFrame "#".
Qed.

Lemma mk_voter_key_refinement K K' skT skT' v v' Ψ :
  hypercryptis_ctx -∗
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
rel_apply_l (refines_mk_sign_key_l _ _ (λ t, {[t]}) (λ t, {[t]}) _ Hdisj with "[//]");
  [solve_minted_iff.. |].
iIntros (skV) "%Hnonce #mint_sk token_s token_sk token_pk".
rel_apply_r (refines_mk_sign_key_r _ _ (λ t, {[t]}) (λ t, {[t]}) _ Hdisj with "[//]");
  [solve_minted_iff.. |].
iIntros (skV') "%Hnonce' #mint_sk' token_s' token_sk' token_pk'".
split_term_tokens.
(* Seeds: secret; they protect the signing keys, which are secret in turn. *)
iMod (public_secret_nonce_l (E:=⊤) Hnonce ltac:(solve_ndisj) with "Hctx token_s")
  as "[#secret_s token_s]".
iMod (public_secret_nonce_r (E:=⊤) Hnonce' ltac:(solve_ndisj) with "Hctx token_s'")
  as "[#secret_s' _]".
rewrite (term_token_difference (seed_of_sign_key skV) (↑signedN)
           (⊤ ∖ ↑hypercryptisN)); last solve_ndisj.
iDestruct "token_s" as "[token_signed _]".
iDestruct (term_token_public_token_l with "token_sk") as "(token_sk & seals & _)";
  first solve_not_TSeal.
iDestruct (term_token_public_token_r with "token_sk'") as "(token_sk' & seals' & _)";
  first solve_not_TSeal.
iMod (public_secret_step_l (E:=⊤) (is_immediate_subterm_sign_key skV)
        ltac:(solve_ndisj) with "Hctx secret_s token_sk") as "#secret_sk".
iMod (public_secret_step_r (E:=⊤) (is_immediate_subterm_sign_key skV')
        ltac:(solve_ndisj) with "Hctx secret_s' token_sk'") as "#secret_sk'".
iDestruct (term_token_public_token_l with "token_pk") as "(token_pk & _ & _)";
  first solve_not_TSeal.
iDestruct (term_token_public_token_r with "token_pk'") as "(token_pk' & _ & _)";
  first solve_not_TSeal.
iMod (public_publish (E:=⊤) ltac:(solve_ndisj)
        with "Hctx [] [] [] token_pk token_pk'") as "[#elem_pk #pub_pk]".
{ iIntros "!> #elem". by iApply (pub_verify_key with "mint_sk mint_sk' secret_s secret_s' elem"). }
{ by rewrite [term_of_sign_key]unlock. }
{ by rewrite [term_of_sign_key]unlock. }
iMod (inv_alloc ballotN _ (ballot_inv skV skV' skT skT' v v') with "[seals seals']")
  as "#Hballot".
{ iNext. iLeft. iFrame. }
iApply ("post" with "[] token_signed").
do 4 (iSplit; first done). by iFrame "#".
Qed.

End KeyGeneration.

Section Voters.

Definition pkeys ks : list term := map (λ sk : sign_key, Spec.pkey sk) ks.

Definition voter_keys skT skT' ks ks' votes votes' : iProp :=
  [∗ list] j ↦ sk; sk' ∈ ks; ks',
    voter_key sk sk' skT skT' (TInt (votes !!! j)) (TInt (votes' !!! j)).

#[global] Instance voter_keys_persistent skT skT' ks ks' votes votes' :
  Persistent (voter_keys skT skT' ks ks' votes votes').
Proof. apply _. Qed.

Definition voter_tokens ks : iProp :=
  [∗ list] sk ∈ ks, term_token (seed_of_sign_key sk) (↑signedN).

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

End Voters.

End Base.
