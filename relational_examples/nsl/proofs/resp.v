(** The responder.  When its peer is I, its nonce is secret, and it protects
    the session secret and the plaintexts of the reply and of the third
    message.  The honest reply goes into the invariant of I's key, together
    with what the session gives both roles and what I needs to send the
    third message. *)

From cryptis Require Import lib cryptis primitives.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib.
From cryptis.hyper.core Require Import minted_spec term_meta_spec public.
From cryptis.hyper.lib Require Import list_match.
From cryptis.hyper.primitives Require Import simple comp with_cryptis attacker.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples.nsl Require Import impl.
From cryptis.hyper.examples.nsl.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Resp.

Context `{!relocG Σ, !public_relGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (t u m n : term).

Variables skI skI' skR skR' : aenc_key.
Variable sess : term → term → iProp.
Context {sess_persistent : ∀ s s', Persistent (sess s s')}.
Context {sess_timeless : ∀ s s', Timeless (sess s s')}.

#[local] Abbreviation nsl_ctx := (nsl_ctx skI skI' skR skR' sess).
#[local] Abbreviation session := (session skI skI' skR skR').
#[local] Abbreviation m2_facts := (m2_facts skI skI' skR skR' sess).
#[local] Abbreviation m2_seal := (m2_seal skI skI' skR skR').
#[local] Abbreviation seals_I_info := (seals_I_info skI skI' skR skR' sess).
#[local] Abbreviation seed_l := (seed_l skI skR).
#[local] Abbreviation seed_r := (seed_r skI' skR').

(** The terms that contain the responder's nonce. *)
Definition resp_terms pkI pkR nI nR : gset term :=
  {[nR; TPair nR (TInt 0); TPair nI (TPair nR (TInt 0));
    TPair pkR (TPair nI (TPair nR (TInt 0)));
    Spec.of_list [pkI; pkR; nI; nR];
    (SEncKey (Spec.of_list [pkI; pkR; nI; nR]) : term);
    THash (SEncKey (Spec.of_list [pkI; pkR; nI; nR]));
    TPair nR (TPair pkR (TInt 0));
    Spec.of_list [nI; nR; pkR];
    Spec.tag (Tag m2N) (Spec.of_list [nI; nR; pkR]);
    Spec.enc pkI (Tag m2N) (Spec.of_list [nI; nR; pkR]);
    Spec.tag (Tag m3N) nR;
    Spec.enc pkR (Tag m3N) nR]}.

Lemma m1_open E t t' :
  ↑cryptisN ⊆ E → ↑sealsRN ⊆ E →
  cryptis_rel_ctx -∗ nsl_ctx -∗ PUB⟨t, t'⟩ ={E}=∗
  ⌜Spec.dec skR (Tag m1N) t = None ∧ Spec.dec skR' (Tag m1N) t' = None⌝ ∨
  ∃ m m', ⌜Spec.dec skR (Tag m1N) t = Some m ∧ Spec.dec skR' (Tag m1N) t' = Some m'⌝ ∗
    (PUB⟨m, m'⟩ ∨
     ∃ x1 x1', ⌜m = m1_pl x1 (Spec.pkey skI) ∧ m' = m1_pl x1' (Spec.pkey skI')⌝ ∗
       init_nonce x1 x1').
Proof.
iIntros (HE HN) "#Hctx #Hnsl #Ht". iPoseProof "Hnsl" as "(_ & #HR & _ & #HinvR)".
rewrite /Spec.dec.
iMod (seals_inv_open with "Hctx HR HinvR Ht")
  as "[[-> ->]|(%u & %u' & [-> ->] & [#Hu|#Hl])]"; [done|solve_ndisj|..].
- iModIntro. by iLeft.
- iPoseProof (publicly_related_untag m1N with "Hu") as "Hp".
  destruct (Spec.untag (Tag m1N) u) as [m|], (Spec.untag (Tag m1N) u') as [m'|];
    try done.
  + iModIntro. iRight. iExists m, m'. iSplit; first done. by iLeft.
  + iModIntro. by iLeft.
- iMod (seals_R_lookup with "Hctx Hnsl Hl")
    as "[(%x1 & %x1' & %e & #Hx1)|(%x2 & %x2' & %e & _)]"; [done|solve_ndisj|..].
  + move: e; rewrite /base.m1_seal /aenc_seal => - [-> ->].
    rewrite !Spec.tagK.
    iModIntro. iRight. iExists _, _. iSplit; first done.
    iRight. iExists x1, x1'. by iSplit.
  + move: e; rewrite /base.m3_seal /aenc_seal => - [-> ->].
    rewrite !Spec.untag_tag_ne; try by move/Tag_inj; exact: m1N_m3N.
    iModIntro. by iLeft.
Qed.

(** The components of a first message: the nonce is the attacker's, or it
    is I's own and the claimed identity is I's. *)
Definition m1_comp x1 x1' x2 x2' : iProp :=
  PUB⟨x2, x2'⟩ ∗
  (PUB⟨x1, x1'⟩ ∨
   ⌜x2 = Spec.pkey skI ∧ x2' = Spec.pkey skI'⌝ ∗ init_nonce x1 x1').

Lemma m1_decode m m' :
  honest_key skI skI' -∗
  (PUB⟨m, m'⟩ ∨
   ∃ x1 x1', ⌜m = m1_pl x1 (Spec.pkey skI) ∧ m' = m1_pl x1' (Spec.pkey skI')⌝ ∗
     init_nonce x1 x1') -∗
  ⌜Spec.to_list m = None ∧ Spec.to_list m' = None⌝ ∨
  ∃ ts ts', ⌜Spec.to_list m = Some ts ∧ Spec.to_list m' = Some ts'⌝ ∗
    (⌜length ts ≠ 2 ∧ length ts' ≠ 2⌝ ∨
     ∃ x1 x2 x1' x2', ⌜ts = [x1; x2] ∧ ts' = [x1'; x2']⌝ ∗
       m1_comp x1 x1' x2 x2').
Proof.
iIntros "#HI [#Hm|(%x1 & %x1' & [-> ->] & #Hx1)]".
- iDestruct (publicly_related_to_list_length 2 with "Hm") as "[%Hnone|(%ts & %ts' & %Hsome & [%Hlen|[%Hlen Hts]])]".
  + by iLeft.
  + iRight. iExists ts, ts'. iSplit; first done. by iLeft.
  + iRight. iExists ts, ts'. iSplit; first done. iRight.
    iDestruct (big_sepL2_length with "Hts") as %Hlen'.
    case: ts ts' Hsome Hlen Hlen' => [|x1 [|x2 []]] //= [|x1' [|x2' []]] //= Hsome _ _.
    iDestruct "Hts" as "(#H1 & #H2 & _)".
    iExists x1, x2, x1', x2'. iSplit; first done.
    iSplit; first done. by iLeft.
- iRight. iExists _, _. rewrite /m1_pl !Spec.of_listK. iSplit; first done.
  iRight. iExists x1, (Spec.pkey skI), x1', (Spec.pkey skI'). iSplit; first done.
  iDestruct "HI" as "(_ & _ & _ & _ & #Hpk & _)". iSplit; first done.
  iRight. by iSplit.
Qed.

Lemma m3_open E t t' :
  ↑cryptisN ⊆ E → ↑sealsRN ⊆ E →
  cryptis_rel_ctx -∗ nsl_ctx -∗ PUB⟨t, t'⟩ ={E}=∗
  ⌜Spec.dec skR (Tag m3N) t = None ∧ Spec.dec skR' (Tag m3N) t' = None⌝ ∨
  ∃ m m', ⌜Spec.dec skR (Tag m3N) t = Some m ∧ Spec.dec skR' (Tag m3N) t' = Some m'⌝ ∗
    nonce_info respN m m'.
Proof.
iIntros (HE HN) "#Hctx #Hnsl #Ht". iPoseProof "Hnsl" as "(_ & #HR & _ & #HinvR)".
rewrite /Spec.dec.
iMod (seals_inv_open with "Hctx HR HinvR Ht")
  as "[[-> ->]|(%u & %u' & [-> ->] & [#Hu|#Hl])]"; [done|solve_ndisj|..].
- iModIntro. by iLeft.
- iPoseProof (publicly_related_untag m3N with "Hu") as "Hp".
  destruct (Spec.untag (Tag m3N) u) as [m|], (Spec.untag (Tag m3N) u') as [m'|];
    try done.
  + iModIntro. iRight. iExists m, m'. iSplit; first done. by iLeft.
  + iModIntro. by iLeft.
- iMod (seals_R_lookup with "Hctx Hnsl Hl")
    as "[(%x1 & %x1' & %e & _)|(%x2 & %x2' & %e & #Hx2)]"; [done|solve_ndisj|..].
  + move: e; rewrite /base.m1_seal /aenc_seal => - [-> ->].
    rewrite !Spec.untag_tag_ne; try by move/Tag_inj => e; apply: m1N_m3N.
    iModIntro. by iLeft.
  + move: e; rewrite /base.m3_seal /aenc_seal => - [-> ->].
    rewrite !Spec.tagK.
    iModIntro. iRight. iExists _, _. iSplit; first done. by iRight.
Qed.

(** The responder returns its peer's key and a session key, which is that
    of an honest session when the peer is I. *)
Definition resp_post : val → val → iProp := λ v v',
  (⌜v = NONEV ∧ v' = NONEV⌝ ∨
   ∃ pkI pkI' k k' : term,
     ⌜v = SOMEV (pkI, k)%V ∧ v' = SOMEV (pkI', k')%V⌝ ∗ PUB⟨pkI, pkI'⟩ ∗
     (⌜pkI = Spec.pkey skI⌝ →
      ∃ s s', ⌜k = sess_key s ∧ k' = sess_key s'⌝ ∗ session s s'))%I.

Lemma resp_refinement c c' :
  cryptis_rel_ctx -∗
  lrel_channel c c' -∗
  nsl_ctx -∗
  (∀ s s', key_tokens s s' -∗ secret_in_l s -∗ secret_in_r s' -∗
     protects_superterms_l s ∅ -∗ protects_superterms_r s' ∅ ={⊤}=∗ sess s s') -∗
  REL resp c skR << resp c' skR' : resp_post.
Proof.
iIntros "#Hctx #Hc #Hnsl Halloc".
iPoseProof "Hnsl" as "(#HI & #HR & #HinvI & _)".
iPoseProof "HI" as "(%HsI & %HsI' & #mint_skI & #mint_skI' & #pub_pkI & #link_pkI & #sec_I & _)".
iPoseProof "HR" as "(_ & _ & #mint_skR & #mint_skR' & #pub_pkR & _)".
iAssert (minted (Spec.pkey skR)) as "#mint_pkR"; first by rewrite minted_pkey.
iAssert (minted_spec (Spec.pkey skR')) as "#mint_pkR'";
  first by rewrite minted_spec_pkey.
rewrite /resp /adec. rel_prims.
(* The first message. *)
rel_apply (refines_recv with "Hc").
iIntros (t t') "#Ht" => /=.
iMod (m1_open with "Hctx Hnsl Ht") as "[[%eL %eR]|(%m & %m' & [%eL %eR] & #Hm)]";
  [solve_ndisj..| |].
{ rel_prims. rewrite eL eR. rel_pures. rel_values. iModIntro. by iLeft. }
rel_prims. rewrite eL eR. rel_prims.
iDestruct (m1_decode with "HI Hm")
  as "[[%eL2 %eR2]|(%ts & %ts' & [%eL2 %eR2] & [[%Hl %Hl']|Hcomp])]".
{ rewrite eL2 eR2. rel_pures. rel_values. iModIntro. by iLeft. }
{ rewrite eL2 eR2. rel_pures. rewrite !subst_list_match /=.
  rel_apply_l (refines_list_match_l (A:=term)). rewrite decide_False; last by move=> /= ?; lia.
  rel_apply_r (refines_list_match_r (A:=term)). rewrite decide_False; last by move=> /= ?; lia.
  rel_pures. rel_values. iModIntro. by iLeft. }
iDestruct "Hcomp" as (x1 x2 x1' x2' [-> ->]) "#[Hx2 Hx1]".
rewrite eL2 eR2. rel_pures. rewrite !subst_list_match /=.
rel_apply_l (refines_list_match_l (A:=term)). rewrite /= ?decide_True //=.
rel_apply_r (refines_list_match_r (A:=term)). rewrite /= ?decide_True //=.
rewrite /is_aenc_key. rel_pures.
rel_apply_l (refines_has_key_type_l _ _ _ AEnc). rel_apply_r (refines_has_key_type_r _ _ AEnc).
iDestruct (publicly_related_has_key_type AEnc with "Hx2") as %->.
case: (Spec.has_key_type AEnc x2'); last first.
{ rel_pures. rel_values. iModIntro. by iLeft. }
rel_pures.
iAssert (nonce_info initN x1 x1') as "#Hinfo1".
{ iDestruct "Hx1" as "[?|[_ ?]]"; by [iLeft|iRight]. }
iAssert (minted x1 ∗ minted_spec x1')%I as "#[mint_x1 mint_x1']".
{ iDestruct "Hinfo1" as "[#H|(_ & _ & #mt & #mt' & _)]".
  - by iApply publicly_related_minted.
  - iSplit; [by iApply (term_meta_minted (L:=term))
            | by iApply (term_meta_spec_minted_spec (L:=term))]. }
iPoseProof (publicly_related_minted with "Hx2") as "#[mint_x2 mint_x2']".
iMod (publicly_related_part_bij' (E:=⊤) with "Hctx Hx2 pub_pkI") as %HX;
  first solve_ndisj.
(* The responder's nonce. *)
rel_apply_l (refines_mk_nonce_l _ _ (λ nR, resp_terms x2 (Spec.pkey skR) x1 nR)
  with "[//]"); first solve_minted_iff.
iIntros (nR) "%HnR #mint_nR tok".
rel_apply_r (refines_mk_nonce_r _ _ (λ nR, resp_terms x2' (Spec.pkey skR') x1' nR)
  with "[//]"); first solve_minted_iff.
iIntros (nR') "%HnR' #mint_nR' tok'".
rewrite /resp_terms. split_term_tokens.
all: try by rewrite /Spec.pkey [term_of_aenc_key]unlock /=; solve_term_disj.
iDestruct "tok" as "((((((((((((tt_n & tt_p1) & tt_p2) & tt_p3) & tt_s) & tt_k) & tt_h) &
                    tt_q1) & tt_pl) & tt_tg) & tt_c) & tt_tg3) & tt_c3)".
iDestruct "tok'" as "((((((((((((tts_n & tts_p1) & tts_p2) & tts_p3) & tts_s) & tts_k) & tts_h) &
                     tts_q1) & tts_pl) & tts_tg) & tts_c) & tts_tg3) & tts_c3)".
rel_prims.
have Htag : ∀ N t, is_immediate_subterm t (Spec.tag (Tag N) t).
{ move=> N0 t0. rewrite [Spec.tag]unlock. exact: SubtermPairR. }
iAssert (|={⊤}=> nonce_info respN nR nR' ∗
  PUB⟨Spec.enc x2 (Tag m2N) (Spec.of_list [x1; nR; Spec.pkey skR]),
      Spec.enc x2' (Tag m2N) (Spec.of_list [x1'; nR'; Spec.pkey skR'])⟩ ∗
  (⌜x2 = Spec.pkey skI⌝ → session (seed_l x1 nR) (seed_r x1' nR')))%I
  with "[-]" as ">#(Hinfo & Hc2 & Hsess)".
{ case: (decide (x2 = Spec.pkey skI)) => [eX|neX]; last first.
  { iDestruct (term_token_rel_token_l with "tt_n") as "(tt_n & _ & _)";
      first solve_not_TSeal.
    iDestruct (term_token_rel_token_r with "tts_n") as "(tts_n & _ & _)";
      first solve_not_TSeal.
    iMod (public_rel_publish (E:=⊤) ltac:(solve_ndisj)
            with "Hctx [] tt_n tts_n")
      as "[_ #Hpub]".
    { iIntros "!> #?". rewrite (publicly_related_nonce HnR HnR').
      by do 2 (iSplit; first done). }
    iModIntro. iSplit; first by iLeft. iSplit; last by iIntros (?).
    iApply (publicly_related_enc with "Hx2"). iApply publicly_related_of_list.
    iDestruct "Hx1" as "[#H1|[%eX _]]"; last by case: neX; case: eX.
    by iFrame "#". }
  have eX' := proj1 HX eX. subst x2 x2'.
  iDestruct (term_token_rel_token_l with "tt_p1") as "(tt_p1 & _ & _)";
    first solve_not_TSeal.
  iDestruct (term_token_rel_token_l with "tt_p2") as "(tt_p2 & _ & _)";
    first solve_not_TSeal.
  iDestruct (term_token_rel_token_l with "tt_p3") as "(tt_p3 & _ & _)";
    first solve_not_TSeal.
  iDestruct (term_token_rel_token_l with "tt_q1") as "(tt_q1 & _ & _)";
    first solve_not_TSeal.
  iDestruct (term_token_rel_token_l with "tt_pl") as "(tt_pl & _ & _)";
    first solve_not_TSeal.
  iDestruct (term_token_rel_token_r with "tts_p1") as "(tts_p1 & _ & _)";
    first solve_not_TSeal.
  iDestruct (term_token_rel_token_r with "tts_p2") as "(tts_p2 & _ & _)";
    first solve_not_TSeal.
  iDestruct (term_token_rel_token_r with "tts_p3") as "(tts_p3 & _ & _)";
    first solve_not_TSeal.
  iDestruct (term_token_rel_token_r with "tts_q1") as "(tts_q1 & _ & _)";
    first solve_not_TSeal.
  iDestruct (term_token_rel_token_r with "tts_pl") as "(tts_pl & _ & _)";
    first solve_not_TSeal.
  iDestruct (term_token_rel_token_l with "tt_s") as "(tt_s & tt_s_seal & _)";
    first solve_not_TSeal.
  iDestruct (term_token_rel_token_r with "tts_s") as "(tts_s & tts_s_seal & _)";
    first solve_not_TSeal.
  iMod (public_rel_secret_seals_l (E:=⊤) HnR with "Hctx tt_n")
    as "(#sec & _ & prot & tok)"; first solve_ndisj.
  iMod (public_rel_secret_seals_r (E:=⊤) HnR' with "Hctx tts_n")
    as "(#sec' & _ & prot' & tok')"; first solve_ndisj.
  iMod (term_meta_set respN nR' with "tok") as "#meta"; first solve_ndisj.
  iMod (term_meta_spec_set respN nR with "tok'") as "#meta'"; first solve_ndisj.
  iAssert (resp_nonce nR nR') as "#HnR"; first by iFrame "#".
  (* The nonce protects the three chains. *)
  iMod (public_rel_flow_l_grow_2 (E:=⊤) (tsup:=TPair nR (TInt 0))
          with "Hctx prot sec") as "[prot by_p1]";
    [solve_ndisj | set_solver | solve_immediate_subterm |].
  iMod (public_rel_flow_l_grow_2 (E:=⊤) (tsup:=TPair nR (TPair (Spec.pkey skR) (TInt 0)))
          with "Hctx prot sec") as "[prot by_q1]";
    [solve_ndisj | set_solver | solve_immediate_subterm |].
  iMod (public_rel_flow_l_grow_2 (E:=⊤) (tsup:=Spec.tag (Tag m3N) nR)
          with "Hctx prot sec") as "[_ by_tg3]";
    [solve_ndisj | solve_term_disj | exact: Htag |].
  iMod (public_rel_flow_r_grow_2 (E:=⊤) (t'sup:=TPair nR' (TInt 0))
          with "Hctx prot' sec'") as "[prot' by_p1']";
    [solve_ndisj | set_solver | solve_immediate_subterm |].
  iMod (public_rel_flow_r_grow_2 (E:=⊤) (t'sup:=TPair nR' (TPair (Spec.pkey skR') (TInt 0)))
          with "Hctx prot' sec'") as "[prot' by_q1']";
    [solve_ndisj | set_solver | solve_immediate_subterm |].
  iMod (public_rel_flow_r_grow_2 (E:=⊤) (t'sup:=Spec.tag (Tag m3N) nR')
          with "Hctx prot' sec'") as "[_ by_tg3']";
    [solve_ndisj | solve_term_disj | exact: Htag |].
  (* The session secret. *)
  iMod (public_rel_protect_step_l (E:=⊤) (t:=TPair nR (TInt 0))
          (tsup:=TPair x1 (TPair nR (TInt 0)))
          ltac:(solve_immediate_subterm) ltac:(solve_ndisj)
          with "Hctx by_p1 tt_p1") as "by_p2".
  iMod (public_rel_protect_step_l (E:=⊤) (t:=TPair x1 (TPair nR (TInt 0)))
          (tsup:=TPair (Spec.pkey skR) (TPair x1 (TPair nR (TInt 0))))
          ltac:(solve_immediate_subterm) ltac:(solve_ndisj)
          with "Hctx by_p2 tt_p2") as "by_p3".
  iMod (public_rel_protect_step_l (E:=⊤)
          (t:=TPair (Spec.pkey skR) (TPair x1 (TPair nR (TInt 0))))
          (tsup:=Spec.of_list [Spec.pkey skI; Spec.pkey skR; x1; nR])
          ltac:(solve_immediate_subterm) ltac:(solve_ndisj)
          with "Hctx by_p3 tt_p3") as "by_s".
  iDestruct (rel_token_l_split with "tt_s") as "[tt_s tt_s_flow]".
  iMod (public_rel_flow_l_extend (E:=⊤) _ ltac:(solve_ndisj) with "Hctx tt_s_flow") as "fl_s".
  iMod (public_rel_secret_l (E:=⊤) _ _ ltac:(solve_ndisj) with "Hctx by_s tt_s")
    as "[_ #sec_s]".
  iMod (public_rel_protect_step_r (E:=⊤) (t':=TPair nR' (TInt 0))
          (t'sup:=TPair x1' (TPair nR' (TInt 0)))
          ltac:(solve_immediate_subterm) ltac:(solve_ndisj)
          with "Hctx by_p1' tts_p1") as "by_p2'".
  iMod (public_rel_protect_step_r (E:=⊤) (t':=TPair x1' (TPair nR' (TInt 0)))
          (t'sup:=TPair (Spec.pkey skR') (TPair x1' (TPair nR' (TInt 0))))
          ltac:(solve_immediate_subterm) ltac:(solve_ndisj)
          with "Hctx by_p2' tts_p2") as "by_p3'".
  iMod (public_rel_protect_step_r (E:=⊤)
          (t':=TPair (Spec.pkey skR') (TPair x1' (TPair nR' (TInt 0))))
          (t'sup:=Spec.of_list [Spec.pkey skI'; Spec.pkey skR'; x1'; nR'])
          ltac:(solve_immediate_subterm) ltac:(solve_ndisj)
          with "Hctx by_p3' tts_p3") as "by_s'".
  iDestruct (rel_token_r_split with "tts_s") as "[tts_s tts_s_flow]".
  iMod (public_rel_flow_r_extend (E:=⊤) _ ltac:(solve_ndisj) with "Hctx tts_s_flow") as "fl_s'".
  iMod (public_rel_secret_r (E:=⊤) _ _ ltac:(solve_ndisj) with "Hctx by_s' tts_s")
    as "[_ #sec_s']".
  (* The plaintext of the reply. *)
  iMod (public_rel_protect_step_l (E:=⊤) (t:=TPair nR (TPair (Spec.pkey skR) (TInt 0)))
          (tsup:=Spec.of_list [x1; nR; Spec.pkey skR])
          ltac:(solve_immediate_subterm) ltac:(solve_ndisj)
          with "Hctx by_q1 tt_q1") as "by_pl".
  iMod (public_rel_protect_step_l (E:=⊤) (t:=Spec.of_list [x1; nR; Spec.pkey skR])
          (tsup:=Spec.tag (Tag m2N) (Spec.of_list [x1; nR; Spec.pkey skR]))
          (Htag _ _) ltac:(solve_ndisj)
          with "Hctx by_pl tt_pl") as "by_tg".
  iMod (public_rel_protect_step_r (E:=⊤) (t':=TPair nR' (TPair (Spec.pkey skR') (TInt 0)))
          (t'sup:=Spec.of_list [x1'; nR'; Spec.pkey skR'])
          ltac:(solve_immediate_subterm) ltac:(solve_ndisj)
          with "Hctx by_q1' tts_q1") as "by_pl'".
  iMod (public_rel_protect_step_r (E:=⊤) (t':=Spec.of_list [x1'; nR'; Spec.pkey skR'])
          (t'sup:=Spec.tag (Tag m2N) (Spec.of_list [x1'; nR'; Spec.pkey skR']))
          (Htag _ _) ltac:(solve_ndisj)
          with "Hctx by_pl' tts_pl") as "by_tg'".
  iMod (aenc_link (E:=⊤) skI skI' m2N (Spec.of_list [x1; nR; Spec.pkey skR])
          (Spec.of_list [x1'; nR'; Spec.pkey skR']) ltac:(solve_ndisj)
          with "Hctx HI [] [] by_tg by_tg' tt_tg tts_tg tt_c tts_c") as "[link [mk mk']]".
  { rewrite minted_of_list /=. by iFrame "#". }
  { rewrite minted_spec_of_list /=. by iFrame "#". }
  iMod ("Halloc" $! (seed_l x1 nR) (seed_r x1' nR')
          with "[tt_s_seal tts_s_seal tt_k tts_k tt_h tts_h] sec_s sec_s' fl_s fl_s'")
    as "#Hss".
  { rewrite /key_tokens /never_sealed_under. iFrame. }
  iMod (seals_inv_link (E:=⊤) (N:=sealsIN) ltac:(solve_ndisj) ltac:(solve_ndisj)
    with "HinvI [by_tg3 by_tg3' tt_tg3 tts_tg3 tt_c3 tts_c3] link mk mk'")
    as "[#Hc2 #Hl]".
  { iExists x1, x1', nR, nR'. iSplit; first done.
    iSplitR; first by iFrame "#".
    iLeft. by iFrame. }
  iModIntro. iSplit; first by iRight. iFrame "Hc2".
  iIntros "_". iExists x1, x1', nR, nR'. by do 2 (iSplit; first done). }
rel_apply (refines_send with "Hc Hc2").
iIntros (? ?) "[-> ->]" => /=. rel_pures.
(* The third message. *)
rel_apply (refines_recv with "Hc").
iIntros (t3 t3') "#Ht3" => /=.
iMod (m3_open with "Hctx Hnsl Ht3") as "[[%eL3 %eR3]|(%m3 & %m3' & [%eL3 %eR3] & #Hm3)]";
  [solve_ndisj..| |].
{ rel_prims. rewrite eL3 eR3. rel_pures. rel_values. iModIntro. by iLeft. }
rel_prims. rewrite eL3 eR3. rel_prims.
iMod (nonce_info_eq (E:=⊤) with "Hctx Hm3 Hinfo") as %H3; first solve_ndisj.
case: (decide (m3 = nR)) => [e3|ne3]; last first.
{ rewrite bool_decide_eq_false_2 // bool_decide_eq_false_2; last by rewrite -H3.
  rel_pures. rel_values. iModIntro. by iLeft. }
rewrite bool_decide_eq_true_2 // bool_decide_eq_true_2; last by apply H3.
rel_prims. rel_values. iModIntro.
iRight. iExists _, _, _, _. iSplit; first done. iFrame "Hx2".
iIntros (eX). iExists _, _. iSplit; last by iApply "Hsess".
by rewrite eX (proj1 HX eX).
Qed.

End Resp.
