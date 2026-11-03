(** The initiator.  When its peer is R, its nonce is secret and protects the
    plaintext of the first message.  The only reply it then accepts is R's
    honest one, which fixes the session secret and holds what I needs to send
    the third message. *)

From cryptis Require Import lib cryptis primitives.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.core Require Import minted_spec term_meta_spec rel rel_inv_updates.
From cryptis.hyper.lib Require Import list_match_spec.
From cryptis.hyper.primitives Require Import simple_spec comp_spec with_cryptis_spec attacker_spec.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples.nsl Require Import impl.
From cryptis.hyper.examples.nsl.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Init.

Context `{!relocG Σ, !public_relGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (t u m n : term).

Variables skI skI' skR skR' : aenc_key.

Local Abbreviation nsl_ctx := (nsl_ctx skI skI' skR skR').
Local Abbreviation session := (session skI skI' skR skR').
Local Abbreviation m2_facts := (m2_facts skI skI' skR skR').
Local Abbreviation m2_seal := (m2_seal skI skI' skR skR').
Local Abbreviation m1_seal := (m1_seal skI skI' skR skR').
Local Abbreviation m3_seal := (m3_seal skR skR').
Local Abbreviation seed_l := (seed_l skI skR).
Local Abbreviation seed_r := (seed_r skI' skR').

(** The components of a reply, as the initiator decodes them: related, or
    those of R's honest reply. *)
Definition m2_comp x1 x1' x2 x2' x3 x3' : iProp :=
  PUB⟨x3, x3'⟩ ∗
  ((PUB⟨x1, x1'⟩ ∗ PUB⟨x2, x2'⟩) ∨
   (⌜x3 = Spec.pkey skR ∧ x3' = Spec.pkey skR'⌝ ∗
    m2_facts x1 x1' x2 x2' ∗
    seals_l (seed_of_aenc_key skI) (m2_seal x1 x1' x2 x2'))).

Lemma m2_open E t t' :
  ↑cryptisN ⊆ E → ↑sealsIN ⊆ E →
  cryptis_rel_ctx -∗ nsl_ctx -∗ PUB⟨t, t'⟩ ={E}=∗
  ⌜Spec.dec skI (Tag m2N) t = None ∧ Spec.dec skI' (Tag m2N) t' = None⌝ ∨
  ∃ m m', ⌜Spec.dec skI (Tag m2N) t = Some m ∧ Spec.dec skI' (Tag m2N) t' = Some m'⌝ ∗
    (PUB⟨m, m'⟩ ∨
     ∃ x1 x1' x2 x2',
       ⌜m = m2_pl x1 x2 (Spec.pkey skR) ∧ m' = m2_pl x1' x2' (Spec.pkey skR')⌝ ∗
       m2_facts x1 x1' x2 x2' ∗
       seals_l (seed_of_aenc_key skI) (m2_seal x1 x1' x2 x2')).
Proof.
iIntros (HE HN) "#Hctx #Hnsl #Ht". iPoseProof "Hnsl" as "(#HI & _ & #HinvI & _)".
rewrite /Spec.dec.
iMod (seals_inv_open with "Hctx HI HinvI Ht")
  as "[[-> ->]|(%u & %u' & [-> ->] & [#Hu|#Hl])]"; [done|done|..].
- iModIntro. by iLeft.
- iPoseProof (publicly_related_untag m2N with "Hu") as "Hp".
  destruct (Spec.untag (Tag m2N) u) as [m|], (Spec.untag (Tag m2N) u') as [m'|];
    try done.
  + iModIntro. iRight. iExists m, m'. iSplit; first done. by iLeft.
  + iModIntro. by iLeft.
- iMod (seals_I_lookup with "Hnsl Hl") as (x1 x1' x2 x2' e) "#Hf"; first done.
  move: (e); rewrite /m2_seal /base.m2_seal /aenc_seal => - [-> ->].
  rewrite !Spec.tagK.
  iModIntro. iRight. iExists _, _. iSplit; first done.
  iRight. iExists x1, x1', x2, x2'. iSplit; first done. iFrame "Hf".
  by rewrite /base.m2_seal /aenc_seal.
Qed.

Lemma m2_decode m m' :
  honest_key skR skR' -∗
  (PUB⟨m, m'⟩ ∨
   ∃ x1 x1' x2 x2',
     ⌜m = m2_pl x1 x2 (Spec.pkey skR) ∧ m' = m2_pl x1' x2' (Spec.pkey skR')⌝ ∗
     m2_facts x1 x1' x2 x2' ∗
     seals_l (seed_of_aenc_key skI) (m2_seal x1 x1' x2 x2')) -∗
  ⌜Spec.to_list m = None ∧ Spec.to_list m' = None⌝ ∨
  ∃ ts ts', ⌜Spec.to_list m = Some ts ∧ Spec.to_list m' = Some ts'⌝ ∗
    (⌜length ts ≠ 3 ∧ length ts' ≠ 3⌝ ∨
     ∃ x1 x2 x3 x1' x2' x3', ⌜ts = [x1; x2; x3] ∧ ts' = [x1'; x2'; x3']⌝ ∗
       m2_comp x1 x1' x2 x2' x3 x3').
Proof.
iIntros "#HR [#Hm|(%x1 & %x1' & %x2 & %x2' & [-> ->] & #Hf & #Hl)]".
- iDestruct (pub_list 3 with "Hm") as "[%Hnone|(%ts & %ts' & %Hsome & [%Hlen|[%Hlen Hts]])]".
  + by iLeft.
  + iRight. iExists ts, ts'. iSplit; first done. by iLeft.
  + iRight. iExists ts, ts'. iSplit; first done. iRight.
    iDestruct (big_sepL2_length with "Hts") as %Hlen'.
    case: ts ts' Hsome Hlen Hlen' => [|x1 [|x2 [|x3 []]]] //= [|x1' [|x2' [|x3' []]]] //= Hsome _ _.
    iDestruct "Hts" as "(#H1 & #H2 & #H3 & _)".
    iExists x1, x2, x3, x1', x2', x3'. iSplit; first done.
    iSplit; first done. iLeft. by iSplit.
- iRight. iExists _, _. rewrite /m2_pl !Spec.of_listK. iSplit; first done.
  iRight. iExists x1, x2, (Spec.pkey skR), x1', x2', (Spec.pkey skR'). iSplit; first done.
  iDestruct "HR" as "(_ & _ & _ & _ & #Hpk & _)". iSplit; first done.
  iRight. by iFrame "#".
Qed.

(** The initiator returns a session key, which is that of an honest session
    when its peer is R. *)
Definition init_post pkX : val → val → iProp := λ v v',
  (⌜v = NONEV ∧ v' = NONEV⌝ ∨
   ∃ k k' : term, ⌜v = SOMEV k ∧ v' = SOMEV k'⌝ ∗
     (⌜pkX = Spec.pkey skR⌝ →
      ∃ s s', ⌜k = sess_key s ∧ k' = sess_key s'⌝ ∗ session s s'))%I.

Lemma rel_init c c' pkX pkX' :
  cryptis_rel_ctx -∗
  channel_rel c c' -∗
  nsl_ctx -∗
  PUB⟨pkX, pkX'⟩ -∗
  REL init c skI pkX << init c' skI' pkX' : init_post pkX.
Proof.
iIntros "#Hctx #Hc #Hnsl #HpkX".
iPoseProof "Hnsl" as "(#HI & #HR & _ & #HinvR)".
iPoseProof "HI" as "(_ & _ & #mint_skI & #mint_skI' & #pub_pkI & _)".
iPoseProof "HR" as "(_ & _ & _ & _ & #pub_pkR & _)".
iPoseProof (publicly_related_minted with "HpkX") as "#[mint_pkX mint_pkX']".
iAssert (minted (Spec.pkey skI)) as "#mint_pkI"; first by rewrite minted_pkey.
iAssert (minted_spec (Spec.pkey skI')) as "#mint_pkI'";
  first by rewrite minted_spec_pkey.
iMod (publicly_related_part_bij' (E:=⊤) with "Hctx HpkX pub_pkR") as %HX;
  first solve_ndisj.
rewrite /init /adec. rel_prims.
(* Tokens for the nonce, the first message and the terms in between. *)
rel_apply_l (rel_mk_nonce_l _ _ (λ nI,
  {[nI; Spec.of_list [nI; Spec.pkey skI];
    Spec.tag (Tag m1N) (Spec.of_list [nI; Spec.pkey skI]);
    Spec.enc pkX (Tag m1N) (Spec.of_list [nI; Spec.pkey skI])]})
  with "[//]"); first solve_minted_iff.
iIntros (nI) "%HnI #mint_nI tok".
rel_apply_r (rel_mk_nonce_r _ _ (λ nI',
  {[nI'; Spec.of_list [nI'; Spec.pkey skI'];
    Spec.tag (Tag m1N) (Spec.of_list [nI'; Spec.pkey skI']);
    Spec.enc pkX' (Tag m1N) (Spec.of_list [nI'; Spec.pkey skI'])]})
  with "[//]"); first solve_minted_iff.
iIntros (nI') "%HnI' #mint_nI' tok'".
split_term_tokens.
iDestruct "tok" as "(((tt_n & tt_pl) & tt_tg) & tt_c)".
iDestruct "tok'" as "(((tts_n & tts_pl) & tts_tg) & tts_c)".
rel_prims.
(* The nonce is secret exactly when the peer is R. *)
iAssert (|={⊤}=> ((⌜pkX = Spec.pkey skR⌝ ∗ init_nonce nI nI') ∨
                  (⌜pkX ≠ Spec.pkey skR⌝ ∗ PUB⟨nI, nI'⟩)) ∗
                 (⌜pkX = Spec.pkey skR⌝ -∗ term_token nI (↑m3claimN)) ∗
                 PUB⟨Spec.enc pkX (Tag m1N) (Spec.of_list [nI; Spec.pkey skI]),
                     Spec.enc pkX' (Tag m1N) (Spec.of_list [nI'; Spec.pkey skI'])⟩)%I
  with "[tt_n tt_pl tt_tg tt_c tts_n tts_pl tts_tg tts_c]" as ">(#HnI & claim3 & #Hc1)".
{ case: (decide (pkX = Spec.pkey skR)) => [eX|neX].
  - have eX' := proj1 HX eX. subst pkX pkX'.
    iMod (public_rel_secret_seals_l (E:=⊤) HnI with "Hctx tt_n")
      as "(#sec & _ & prot & tok)"; first solve_ndisj.
    iMod (public_rel_secret_seals_r (E:=⊤) HnI' with "Hctx tts_n")
      as "(#sec' & _ & prot' & tok')"; first solve_ndisj.
    rewrite (term_token_difference nI (↑m3claimN) (⊤ ∖ ↑cryptisN.@"public_rel"));
      last solve_ndisj.
    iDestruct "tok" as "[claim3 tok]".
    iMod (term_meta_set initN nI' with "tok") as "#meta"; first solve_ndisj.
    iMod (term_meta_spec_set initN nI with "tok'") as "#meta'"; first solve_ndisj.
    iMod (public_rel_flow_l_grow_2 (E:=⊤) (tsup:=Spec.of_list [nI; Spec.pkey skI])
            with "Hctx prot sec") as "[_ by_pl]";
      [solve_ndisj | apply not_elem_of_empty | solve_immediate_subterm |].
    iMod (public_rel_flow_r_grow_2 (E:=⊤) (t'sup:=Spec.of_list [nI'; Spec.pkey skI'])
            with "Hctx prot' sec'") as "[_ by_pl']";
      [solve_ndisj | apply not_elem_of_empty | solve_immediate_subterm |].
    have Htg : ∀ t, is_immediate_subterm t (Spec.tag (Tag m1N) t).
    { move=> t0. rewrite [Spec.tag]unlock. exact: SubtermPairR. }
    iMod (public_rel_protect_step_l (E:=⊤) (t:=Spec.of_list [nI; Spec.pkey skI])
            (tsup:=Spec.tag (Tag m1N) (Spec.of_list [nI; Spec.pkey skI]))
            (Htg _) ltac:(solve_ndisj)
            with "Hctx by_pl tt_pl") as "by_tg".
    iMod (public_rel_protect_step_r (E:=⊤) (t':=Spec.of_list [nI'; Spec.pkey skI'])
            (t'sup:=Spec.tag (Tag m1N) (Spec.of_list [nI'; Spec.pkey skI']))
            (Htg _) ltac:(solve_ndisj)
            with "Hctx by_pl' tts_pl") as "by_tg'".
    iMod (aenc_link (E:=⊤) skR skR' m1N (Spec.of_list [nI; Spec.pkey skI])
            (Spec.of_list [nI'; Spec.pkey skI']) ltac:(solve_ndisj)
            with "Hctx HR [] [] by_tg by_tg' tt_tg tts_tg tt_c tts_c") as "link".
    { rewrite minted_of_list /=. by iFrame "#". }
    { rewrite minted_spec_of_list /=. by iFrame "#". }
    have Hsh : aenc_shape skR skR' (m1_seal nI nI') by eexists _, _.
    iMod (seals_inv_link (E:=⊤) (N:=sealsRN) _ _ ltac:(solve_ndisj) ltac:(solve_ndisj) Hsh
      with "HinvR [] link") as "[#Hc1 _]".
    { iLeft. iExists nI, nI'. iSplit; first done. by iFrame "#". }
    iModIntro. iFrame "Hc1". iSplitR; last by iIntros "_".
    iLeft. iSplit; first done. by iFrame "#".
  - iMod (public_rel_publish (E:=⊤) ltac:(solve_ndisj) with "Hctx [] tt_n tts_n")
      as "[_ #Hpub]".
    { iIntros "!> #?". rewrite (publicly_related_nonce HnI HnI').
      by do 2 (iSplit; first done). }
    iModIntro. iSplit; first by iRight; iSplit.
    iSplit; first by iIntros (?).
    iApply (publicly_related_enc with "HpkX").
    iApply publicly_related_of_list. by iFrame "#". }
iAssert (nonce_info initN nI nI') as "#Hinfo".
{ by iDestruct "HnI" as "[[_ ?]|[_ ?]]"; [iRight|iLeft]. }
rel_apply (rel_send with "Hc Hc1").
iIntros (? ?) "[-> ->]" => /=. rel_pures.
(* The second message. *)
rel_apply (rel_recv with "Hc").
iIntros (t t') "#Ht" => /=.
iMod (m2_open with "Hctx Hnsl Ht") as "[[%eL %eR]|(%m & %m' & [%eL %eR] & #Hm)]";
  [solve_ndisj..| |].
{ rel_prims. rewrite eL eR. rel_pures. rel_values. iModIntro. by iLeft. }
rel_prims. rewrite eL eR. rel_prims.
iDestruct (m2_decode with "HR Hm")
  as "[[%eL2 %eR2]|(%ts & %ts' & [%eL2 %eR2] & [[%Hl %Hl']|Hcomp])]".
{ rewrite eL2 eR2. rel_pures. rel_values. iModIntro. by iLeft. }
{ rewrite eL2 eR2. rel_pures. rewrite !subst_list_match /=.
  rel_apply_l (rel_list_match_l (A:=term)). rewrite decide_False; last by move=> /= ?; lia.
  rel_apply_r (rel_list_match_r (A:=term)). rewrite decide_False; last by move=> /= ?; lia.
  rel_pures. rel_values. iModIntro. by iLeft. }
iDestruct "Hcomp" as (x1 x2 x3 x1' x2' x3' [-> ->]) "#[Hx3 Hcomp]".
rewrite eL2 eR2. rel_pures. rewrite !subst_list_match /=.
rel_apply_l (rel_list_match_l (A:=term)). rewrite /= ?decide_True //=.
rel_apply_r (rel_list_match_r (A:=term)). rewrite /= ?decide_True //=.
rel_prims.
(* Both runs pass the checks, or both fail. *)
iAssert (nonce_info initN x1 x1') as "#Hx1".
{ iDestruct "Hcomp" as "[[? _]|(_ & (? & _) & _)]"; by [iLeft|]. }
iMod (nonce_info_eq (E:=⊤) with "Hctx Hx1 Hinfo") as %H1; first solve_ndisj.
iMod (publicly_related_part_bij' (E:=⊤) with "Hctx Hx3 HpkX") as %H3;
  first solve_ndisj.
case: (decide (x1 = nI)) => [e1|ne1]; last first.
{ rewrite bool_decide_eq_false_2 // bool_decide_eq_false_2; last by rewrite -H1.
  rel_pures. rel_values. iModIntro. by iLeft. }
rewrite bool_decide_eq_true_2 // bool_decide_eq_true_2; last by apply H1.
have e1' := proj1 H1 e1. subst x1 x1'.
rel_prims.
case: (decide (x3 = pkX)) => [e3|ne3]; last first.
{ rewrite bool_decide_eq_false_2 // bool_decide_eq_false_2; last by rewrite -H3.
  rel_pures. rel_values. iModIntro. by iLeft. }
rewrite bool_decide_eq_true_2 // bool_decide_eq_true_2; last by apply H3.
have e3' := proj1 H3 e3. subst x3 x3'.
rel_prims.
(* The third message. *)
iAssert ((⌜pkX = Spec.pkey skR⌝ ∗ resp_nonce x2 x2' ∗
          seals_l (seed_of_aenc_key skI) (m2_seal nI nI' x2 x2')) ∨
         (⌜pkX ≠ Spec.pkey skR⌝ ∗ PUB⟨x2, x2'⟩))%I as "#Hcase".
{ iDestruct "HnI" as "[[%eX (_ & _ & _ & _ & #sec & _)]|[%neX _]]";
  iDestruct "Hcomp" as "[[#Hpub #Hx2]|([%eK %eK'] & (_ & #Hx2 & _) & #Hl)]".
  - iDestruct (publicly_related_nonce_term _ HnI with "Hpub") as "[Hl _]".
    by iDestruct (secret_in_l_publicly_linked_in_l with "sec Hl") as "[]".
  - iLeft. by iFrame "#".
  - iRight. by iSplit.
  - by case: neX. }
iAssert (|={⊤}=> PUB⟨Spec.enc pkX (Tag m3N) x2, Spec.enc pkX' (Tag m3N) x2'⟩)%I
  with "[claim3]" as ">#Hc3".
{ iDestruct "Hcase" as "[(%eX & #Hx2 & #Hl)|[%neX #Hx2]]"; last first.
  { by iApply (publicly_related_enc with "HpkX Hx2"). }
  iSpecialize ("claim3" with "[//]").
  have eX' := proj1 HX eX. subst pkX pkX'.
  iMod (claim_m3 with "Hnsl Hl claim3")
    as "(by_tg & by_tg' & tt_tg & tts_tg & tt_c & tts_c)"; first solve_ndisj.
  iAssert (minted x2 ∗ minted_spec x2')%I as "#[mint_x2 mint_x2']".
  { iDestruct "Hx2" as "(_ & _ & #mt & #mt' & _)".
    iSplit; [by iApply (term_meta_minted (L:=term))
            | by iApply (term_meta_spec_minted_spec (L:=term))]. }
  iMod (aenc_link (E:=⊤) skR skR' m3N x2 x2' ltac:(solve_ndisj)
          with "Hctx HR mint_x2 mint_x2' by_tg by_tg' tt_tg tts_tg tt_c tts_c")
    as "link".
  have Hsh : aenc_shape skR skR' (m3_seal x2 x2') by eexists _, _.
  iMod (seals_inv_link (E:=⊤) (N:=sealsRN) _ _ ltac:(solve_ndisj) ltac:(solve_ndisj) Hsh
    with "HinvR [] link") as "[#Hc3 _]".
  { iRight. iExists x2, x2'. by iSplit. }
  by iModIntro. }
rel_apply (rel_send with "Hc Hc3").
iIntros (? ?) "[-> ->]" => /=.
rewrite /session_key. rel_prims. rel_values. iModIntro.
iRight. iExists _, _. iSplit; first done.
iIntros (eX).
iDestruct "Hcase" as "[(_ & _ & #Hl)|[%neX _]]"; last by case: neX.
iExists _, _. iSplit; last first.
{ iExists nI, nI', x2, x2'. by do 2 (iSplit; first done). }
by rewrite eX (proj1 HX eX).
Qed.

End Init.
