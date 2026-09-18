From iris.algebra Require Import auth cmra ofe gmap gset local_updates.
From iris.base_logic.lib Require Import own.
From reloc Require Import reloc.
From cryptis Require Import lib.
From cryptis.lib Require Import saved_prop.
From cryptis.core Require Import term minted.
From cryptis Require Import cryptis.
From cryptis.core Require Import minted_spec.
From cryptis.core Require Import term_meta_spec.
From cryptis.core Require Export rel_state rel_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Rel.

Context `{!relocG Σ, !public_relGS Σ}.

Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).

Implicit Types t : term.
Implicit Types st : state.
Implicit Types pub_l pub_r : gmap term state.
Implicit Types flow_l flow_r : gmap term (gset term).
Implicit Types P : term -> term -> iProp.

Section Constructors.

Lemma publicly_related_minted t t' :
  PUB⟨t, t'⟩ ⊢ minted t ∗ minted_spec t'.
Proof.
case: t => /= *; iIntros "(#? & #? & _)"; by iFrame "#".
Qed.

Lemma publicly_related_TInt n n' :
  PUB⟨TInt n, TInt n'⟩ ⊣⊢ ⌜n = n'⌝.
Proof.
rewrite /= minted_TInt minted_spec_TInt.
by rewrite !left_id.
Qed.

Lemma publicly_related_TInt_term n (t' : term) :
  PUB⟨TInt n, t'⟩ -∗ ⌜t' = TInt n⌝.
Proof.
case: t' => /= *; try by iIntros "(_ & _ & [])".
by iIntros "(_ & _ & ->)".
Qed.

Lemma publicly_related_term_TInt (t : term) n :
  PUB⟨t, TInt n⟩ -∗ ⌜t = TInt n⌝.
Proof.
case: t => /= *; try by iIntros "(_ & _ & [])".
by iIntros "(_ & _ & ->)".
Qed.

Lemma publicly_related_TPair t1 t2 t1' t2' :
  PUB⟨TPair t1 t2, TPair t1' t2'⟩ ⊣⊢
  PUB⟨t1, t1'⟩ ∧ PUB⟨t2, t2'⟩.
Proof.
rewrite /= minted_TPair minted_spec_TPair. iSplit.
- by iIntros "(_ & _ & ?)".
- iIntros "#[H1 H2]".
  iPoseProof (publicly_related_minted with "H1") as "[? ?]".
  iPoseProof (publicly_related_minted with "H2") as "[? ?]".
  iSplit; first by iSplit. iSplit; first by iSplit. by iSplit.
Qed.

Lemma publicly_related_TPair_term t1 t2 (t' : term) :
  PUB⟨TPair t1 t2, t'⟩ -∗
  ∃ t1' t2', ⌜t' = TPair t1' t2'⌝.
Proof.
case: t' => /= *; try by iIntros "(_ & _ & [])".
iIntros "_". by eauto.
Qed.

Lemma publicly_related_term_TPair (t : term) t1' t2' :
  PUB⟨t, TPair t1' t2'⟩ -∗
  ∃ t1 t2, ⌜t = TPair t1 t2⌝.
Proof.
case: t => /= *; try by iIntros "(_ & _ & [])".
iIntros "_". by eauto.
Qed.

Lemma publicly_related_TNonce a a' :
  PUB⟨TNonce a, TNonce a'⟩ ⊣⊢
  minted (TNonce a) ∧ minted_spec (TNonce a') ∧
  publicly_linked (TNonce a) (TNonce a').
Proof. done. Qed.

Lemma publicly_related_TNonce_term a (t' : term) :
  PUB⟨TNonce a, t'⟩ -∗ publicly_linked (TNonce a) t'.
Proof.
case: t' => /= *; try by iIntros "(_ & _ & [])".
- by iIntros "(_ & _ & ?)".
- by iIntros "(_ & _ & ? & _)".
Qed.

Lemma publicly_related_term_TNonce (t : term) a' :
  PUB⟨t, TNonce a'⟩ -∗ publicly_linked t (TNonce a').
Proof.
case: t => /= *; try by iIntros "(_ & _ & [])".
- by iIntros "(_ & _ & ?)".
- by iIntros "(_ & _ & ? & _)".
Qed.

Lemma publicly_related_nonce t t' :
  is_nonce t → is_nonce t' →
  PUB⟨t, t'⟩ ⊣⊢ minted t ∧ minted_spec t' ∧ publicly_linked t t'.
Proof. by move=> /is_nonceP [a ->] /is_nonceP [a' ->]. Qed.

Lemma publicly_related_nonce_term t t' :
  is_nonce t → PUB⟨t, t'⟩ -∗ publicly_linked t t'.
Proof. move=> /is_nonceP [a ->]. exact: publicly_related_TNonce_term. Qed.

Lemma publicly_related_term_nonce t t' :
  is_nonce t' → PUB⟨t, t'⟩ -∗ publicly_linked t t'.
Proof. move=> /is_nonceP [a' ->]. exact: publicly_related_term_TNonce. Qed.

Lemma publicly_related_TKey kt kt' t t' :
  PUB⟨TKey kt t, TKey kt' t'⟩ ⊣⊢
  ⌜kt = kt'⌝ ∧
  match kt with
  | AEnc => PUB⟨t, t'⟩ ∨
            (minted t ∧ minted_spec t' ∧
             publicly_linked (TKey kt t) (TKey kt' t') ∧ linked t t')
  | ADec => PUB⟨t, t'⟩
  | Sign => PUB⟨t, t'⟩
  | Verify => PUB⟨t, t'⟩ ∨
              (minted t ∧ minted_spec t' ∧
               publicly_linked (TKey kt t) (TKey kt' t') ∧ linked t t')
  | SEnc => PUB⟨t, t'⟩
  end.
Proof.
rewrite /= minted_TKey minted_spec_TKey. iSplit.
- iIntros "#(? & ? & -> & H)". iSplit; first done.
  case: kt' => /=; try (by iExact "H");
    (iDestruct "H" as "[H|(? & ?)]"; [by iLeft | iRight; by do 3 (iSplit; first done)]).
- iIntros "#(-> & H)".
  case: kt' => /=.
  1,4: iDestruct "H" as "[H|(? & ? & ? & ?)]";
       [ iPoseProof (publicly_related_minted with "H") as "[? ?]";
         do 3 (iSplit; first done); by iLeft
       | do 3 (iSplit; first done); iRight; by iSplit ].
  all: iPoseProof (publicly_related_minted with "H") as "[? ?]"; by do 3 (iSplit; first done).
Qed.

Lemma publicly_related_TSeal k k' t t' :
  PUB⟨TSeal k t, TSeal k' t'⟩ ⊣⊢
  (PUB⟨k, k'⟩ ∧ PUB⟨t, t'⟩) ∨
  (minted (TSeal k t) ∧ minted_spec (TSeal k' t') ∧
   publicly_linked (TSeal k t) (TSeal k' t') ∧
   linked k k' ∧ linked t t' ∧
   □ (match k, k' with
      | TKey kt k1, TKey kt' k1' => ⌜kt = kt'⌝ ∧
        match kt with
        | ADec | Verify => False
        | Sign => PUB⟨t, t'⟩
        | AEnc | SEnc => PUB⟨k1, k1'⟩ → PUB⟨t, t'⟩
        end
      | _, _ => False
      end)).
Proof.
rewrite /=. iSplit.
- iIntros "#(? & ? & [?|(? & ? & ? & ?)])"; [by iLeft | iRight; by do 5 (iSplit; first done)].
- iIntros "#[[H1 H2]|(? & ? & ? & ? & ? & ?)]";
    last by (do 2 (iSplit; first done); iRight; do 3 (iSplit; first done)).
  iPoseProof (publicly_related_minted with "H1") as "[? ?]".
  iPoseProof (publicly_related_minted with "H2") as "[? ?]".
  rewrite minted_TSeal minted_spec_TSeal.
  iSplit; first by iSplit. iSplit; first by iSplit. iLeft. by iSplit.
Qed.

Lemma publicly_related_THash t t' :
  PUB⟨THash t, THash t'⟩ ⊣⊢
  PUB⟨t, t'⟩ ∨
  (minted t ∧ minted_spec t' ∧
   publicly_linked (THash t) (THash t') ∧ linked t t').
Proof.
rewrite /= minted_THash minted_spec_THash. iSplit.
- iIntros "#(? & ? & [?|(? & ?)])"; [by iLeft | iRight; by do 3 (iSplit; first done)].
- iIntros "#[H|(? & ? & ? & ?)]";
    last by (do 2 (iSplit; first done); iRight; iSplit).
  iPoseProof (publicly_related_minted with "H") as "[? ?]".
  do 2 (iSplit; first done). by iLeft.
Qed.

Lemma publicly_related_open k k' t t' t1 t1' :
  Spec.open k t = Some t1 →
  Spec.open k' t' = Some t1' →
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  PUB⟨t1, t1'⟩.
Proof.
rewrite /Spec.open.
case: t => // k_t t.
case: t' => // k_t' t'.
rewrite publicly_related_TSeal.
case: decide => // k_t_k [<-].
case: decide => // k_t_k' [<-].
iIntros "#Hk #[[_ Ht]|(_ & _ & _ & _ & _ & #Hrest)]"; first done.
case: k_t k_t' => // kt k1 [] // kt' k1' in k_t_k k_t_k' *.
iDestruct "Hrest" as "[<- Hrest]".
case: kt k_t_k k_t_k' => // - [<-] [<-] //.
- iApply "Hrest". rewrite publicly_related_TKey.
  by iDestruct "Hk" as "[??]".
- iApply "Hrest". rewrite publicly_related_TKey.
  by iDestruct "Hk" as "[??]".
Qed.

Lemma publicly_related_Tag N N' : PUB⟨Tag N, Tag N'⟩ ⊣⊢ ⌜N = N'⌝.
Proof.
rewrite Tag_unseal publicly_related_TInt. iSplit.
- iIntros "%H". injection H as H. by apply encode_inj in H.
- iIntros "->". done.
Qed.

Lemma publicly_related_Tag_term N (t' : term) :
  PUB⟨Tag N, t'⟩ -∗
  ⌜t' = Tag N⌝.
Proof.
iIntros "#H".
rewrite Tag_unseal /Tag_def.
by iPoseProof (publicly_related_TInt_term with "H") as "->".
Qed.

Lemma publicly_related_term_Tag (t : term) N' :
  PUB⟨t, Tag N'⟩ -∗
  ⌜t = Tag N'⌝.
Proof.
iIntros "#H".
rewrite Tag_unseal /Tag_def.
by iPoseProof (publicly_related_term_TInt with "H") as "->".
Qed.

Lemma publicly_related_tag N N' t t' :
  PUB⟨Spec.tag (Tag N) t, Spec.tag (Tag N') t'⟩ ⊣⊢
  ⌜N = N'⌝ ∧ PUB⟨t, t'⟩.
Proof.
by rewrite Spec.tag_unseal /Spec.tag_def publicly_related_TPair publicly_related_Tag.
Qed.

Lemma publicly_related_tag_term N t (t' : term) :
  PUB⟨Spec.tag (Tag N) t, t'⟩ -∗
  ∃ t1', ⌜t' = Spec.tag (Tag N) t1'⌝.
Proof.
iIntros "#H".
rewrite Spec.tag_unseal /Spec.tag_def.
iPoseProof (publicly_related_TPair_term with "H") as "(%t1' & %t2' & ->)".
rewrite publicly_related_TPair.
iDestruct "H" as "[H1 H2]".
iPoseProof (publicly_related_Tag_term with "H1") as "->".
by iExists t2'.
Qed.

Lemma publicly_related_term_tag (t : term) N t' :
  PUB⟨t, Spec.tag (Tag N) t'⟩ -∗
  ∃ t1, ⌜t = Spec.tag (Tag N) t1⌝.
Proof.
iIntros "#H".
rewrite Spec.tag_unseal /Spec.tag_def.
iPoseProof (publicly_related_term_TPair with "H") as "(%t1 & %t2 & ->)".
rewrite publicly_related_TPair.
iDestruct "H" as "[H1 H2]".
iPoseProof (publicly_related_term_Tag with "H1") as "->".
by iExists t2.
Qed.

Lemma publicly_related_adec_key' (k k' : aenc_key) :
  PUB⟨k, k'⟩ ⊣⊢
  PUB⟨seed_of_aenc_key k, seed_of_aenc_key k'⟩.
Proof.
rewrite [term_of_aenc_key]unlock /= minted_TKey minted_spec_TKey.
iSplit; first by iIntros "(_ & _ & _ & ?)".
iIntros "#H". iPoseProof (publicly_related_minted with "H") as "[? ?]".
by do 3 (iSplit; first done).
Qed.

Lemma publicly_related_aenc_key_term (k : aenc_key) (t' : term) :
  PUB⟨k, t'⟩ -∗
  ∃ (k' : aenc_key), ⌜t' = k'⌝.
Proof.
rewrite [term_of_aenc_key]unlock /=.
case: t' => /= [n'|a' b'|a'|kt' s'|k' b'|s'|pt' wf' nf']; try by iIntros "(_ & _ & [])".
iIntros "(_ & _ & <- & _)". by iExists (AEncKey s').
Qed.

Lemma publicly_related_term_aenc_key (t : term) (k' : aenc_key) :
  PUB⟨t, k'⟩ -∗
  ∃ (k : aenc_key), ⌜t = k⌝.
Proof.
rewrite [term_of_aenc_key]unlock /=.
case: t => /= [n|a b|a|kt s|k b|s|pt wf nf]; try by iIntros "(_ & _ & [])".
iIntros "(_ & _ & -> & _)". by iExists (AEncKey s).
Qed.

Lemma publicly_related_aenc_key (k k' : aenc_key) :
  PUB⟨Spec.pkey k, Spec.pkey k'⟩ ⊣⊢
  PUB⟨k, k'⟩ ∨
  (minted k ∧ minted_spec k' ∧
   publicly_linked (Spec.pkey k) (Spec.pkey k') ∧
   linked (seed_of_aenc_key k) (seed_of_aenc_key k')).
Proof.
rewrite publicly_related_adec_key'.
rewrite /Spec.pkey [term_of_aenc_key]unlock /= !minted_TKey !minted_spec_TKey.
iSplit.
- iIntros "#(? & ? & _ & [?|(? & ?)])"; [by iLeft | iRight; by do 3 (iSplit; first done)].
- iIntros "#[H|(? & ? & ? & ?)]";
    last by (do 3 (iSplit; first done); iRight; iSplit).
  iPoseProof (publicly_related_minted with "H") as "[? ?]".
  do 3 (iSplit; first done). by iLeft.
Qed.

Lemma publicly_related_aenc_key_pkey_term (sk : aenc_key) (t' : term) :
  PUB⟨Spec.pkey sk, t'⟩ -∗
  ∃ (sk' : aenc_key), ⌜t' = Spec.pkey sk'⌝.
Proof.
rewrite /Spec.pkey [term_of_aenc_key]unlock /=.
case: t' => /= [n'|a' b'|a'|kt' s'|k' b'|s'|pt' wf' nf']; try by iIntros "(_ & _ & [])".
iIntros "(_ & _ & <- & _)". by iExists (AEncKey s').
Qed.

Lemma publicly_related_term_aenc_key_pkey (t : term) (sk' : aenc_key) :
  PUB⟨t, Spec.pkey sk'⟩ -∗
  ∃ (sk : aenc_key), ⌜t = Spec.pkey sk⌝.
Proof.
rewrite /Spec.pkey [term_of_aenc_key]unlock /=.
case: t => /= [n|a b|a|kt s|k b|s|pt wf nf]; try by iIntros "(_ & _ & [])".
iIntros "(_ & _ & -> & _)". by iExists (AEncKey s).
Qed.

Lemma publicly_related_aenc (sk sk' : aenc_key) N (t t' : term) :
  PUB⟨Spec.enc (Spec.pkey sk) (Tag N) t,
      Spec.enc (Spec.pkey sk') (Tag N) t'⟩ ⊣⊢
  (PUB⟨Spec.pkey sk, Spec.pkey sk'⟩ ∧ PUB⟨t, t'⟩) ∨
  (minted (Spec.pkey sk) ∧ minted t ∧
   minted_spec (Spec.pkey sk') ∧ minted_spec t' ∧
   publicly_linked (Spec.enc (Spec.pkey sk) (Tag N) t)
                   (Spec.enc (Spec.pkey sk') (Tag N) t') ∧
   linked (Spec.pkey sk) (Spec.pkey sk') ∧
   linked (Spec.tag (Tag N) t) (Spec.tag (Tag N) t') ∧
   □ (PUB⟨sk, sk'⟩ → PUB⟨t, t'⟩)).
Proof.
rewrite publicly_related_adec_key'.
rewrite /Spec.enc publicly_related_TSeal.
rewrite minted_TSeal minted_spec_TSeal minted_tag minted_spec_tag.
rewrite /Spec.pkey [term_of_aenc_key]unlock /= publicly_related_tag.
iSplit.
- iIntros "#[[Hk [_ Ht]]|([Hmk Hmt] & [Hmk' Hmt'] & Hel & Hpk & Hpt & #Hrest)]";
    first by iLeft; iSplit.
  iRight. do 7 (iSplit; first done).
  iIntros "!> #Hs". iDestruct "Hrest" as "[_ Hrest]".
  by iDestruct ("Hrest" with "Hs") as "[_ ?]".
- iIntros "#[[Hk Ht]|(Hmk & Hmt & Hmk' & Hmt' & Hel & Hpk & Hpt & #Hrest)]";
    first by iLeft; iSplit; last iSplit.
  iRight. iSplit; first by iSplit. iSplit; first by iSplit.
  do 3 (iSplit; first done).
  iIntros "!>". iSplit; first done.
  iIntros "#Hs". iSplit; first done. by iApply "Hrest".
Qed.

End Constructors.

Section PartBij.

#[local] Lemma public_rel_protected_inv_l pub_l flow_l t :
  public_rel_Private_l_protected pub_l flow_l →
  public_rel_flow_l_consistent pub_l flow_l →
  (∃ st, pub_l !! t = Some st ∧ not_Public st) ∨ (∃ ts, flow_l !! t = Some ts ∧ ts ≠ ∅) →
  (∀ t', pub_l !! t ≠ Some (Public t')) ∧
  (is_nonce t ∨
   ∃ tsub, is_immediate_subterm tsub t ∧
     ((∃ st, pub_l !! tsub = Some st ∧ not_Public st) ∨
      (∃ ts, flow_l !! tsub = Some ts ∧ ts ≠ ∅))).
Proof.
move=> HPriv Hcons [[st [Hpub Hst]]|[ts [Hflow Hts]]].
- split; first by move=> t' Ht'; rewrite Hpub in Ht'; case: Ht' Hst => -> [].
  case: (HPriv _ _ Hpub Hst) => [Ha|[tsub [ts1 [Hflow Hin]]]]; first by left.
  have Hts1 : ts1 ≠ ∅ by set_solver.
  case: (Hcons _ _ Hflow Hts1) => [Hsubs _].
  right. exists tsub. split; first by apply Hsubs. right. by exists ts1.
- case: (Hcons _ _ Hflow Hts) => [Hsubs [Hchain Hpub]].
  split.
  + move=> t' Ht'. case: Hpub => [H|[st [H Hst]]]; rewrite H in Ht'; first congruence.
    by case: Ht' Hst => -> [].
  + case: Hchain => [Ha|[tsub [ts1 [Hflow1 Hin]]]]; first by left.
    have Hts1 : ts1 ≠ ∅ by set_solver.
    case: (Hcons _ _ Hflow1 Hts1) => [Hsubs1 _].
    right. exists tsub. split; first by apply Hsubs1. right. by exists ts1.
Qed.

#[local] Lemma public_rel_protected_inv_r pub_r flow_r t' :
  public_rel_Private_r_protected pub_r flow_r →
  public_rel_flow_r_consistent pub_r flow_r →
  (∃ st, pub_r !! t' = Some st ∧ not_Public st) ∨ (∃ ts, flow_r !! t' = Some ts ∧ ts ≠ ∅) →
  (∀ t, pub_r !! t' ≠ Some (Public t)) ∧
  (is_nonce t' ∨
   ∃ t'sub, is_immediate_subterm t'sub t' ∧
     ((∃ st, pub_r !! t'sub = Some st ∧ not_Public st) ∨
      (∃ ts, flow_r !! t'sub = Some ts ∧ ts ≠ ∅))).
Proof.
move=> HPriv Hcons [[st [Hpub Hst]]|[ts [Hflow Hts]]].
- split; first by move=> t Ht; rewrite Hpub in Ht; case: Ht Hst => -> [].
  case: (HPriv _ _ Hpub Hst) => [Ha|[t'sub [ts1 [Hflow Hin]]]]; first by left.
  have Hts1 : ts1 ≠ ∅ by set_solver.
  case: (Hcons _ _ Hflow Hts1) => [Hsubs _].
  right. exists t'sub. split; first by apply Hsubs. right. by exists ts1.
- case: (Hcons _ _ Hflow Hts) => [Hsubs [Hchain Hpub]].
  split.
  + move=> t Ht. case: Hpub => [H|[st [H Hst]]]; rewrite H in Ht; first congruence.
    by case: Ht Hst => -> [].
  + case: Hchain => [Ha|[t'sub [ts1 [Hflow1 Hin]]]]; first by left.
    have Hts1 : ts1 ≠ ∅ by set_solver.
    case: (Hcons _ _ Hflow1 Hts1) => [Hsubs1 _].
    right. exists t'sub. split; first by apply Hsubs1. right. by exists ts1.
Qed.

#[local] Lemma publicly_related_protected_l pub_l flow_l t :
  public_rel_Private_l_protected pub_l flow_l →
  public_rel_flow_l_consistent pub_l flow_l →
  (∃ st, pub_l !! t = Some st ∧ not_Public st) ∨ (∃ ts, flow_l !! t = Some ts ∧ ts ≠ ∅) →
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  ∀ t', PUB⟨t, t'⟩ -∗ False.
Proof.
move=> HPriv Hcons.
elim/term_ind': t => [n|a IHa b IHb|a|kt s IH|k IHk b IHb|s IH|pt wf nf] Hprot;
  iIntros "Hauth" (t') "#Hpub";
  case: (public_rel_protected_inv_l HPriv Hcons Hprot) => HnotPub Hsub.
- case: Hsub => [[]|[tsub [Hsub _]]] //. by inversion Hsub.
- iDestruct (publicly_related_TPair_term with "Hpub") as %(a' & b' & ->).
  rewrite publicly_related_TPair. iDestruct "Hpub" as "[Ha Hb]".
  case: Hsub => [[]|[tsub [Hsub Hprot']]] //.
  inversion Hsub; subst.
  + iApply (IHa Hprot' with "Hauth Ha").
  + iApply (IHb Hprot' with "Hauth Hb").
- iDestruct (publicly_related_TNonce_term with "Hpub") as "Hel".
  iDestruct (publicly_linked_lookup_l with "Hauth Hel") as %Hlookup.
  by case: (HnotPub _ Hlookup).
- case: t' => /= *; try by iDestruct "Hpub" as "(_ & _ & [])".
  iDestruct "Hpub" as "(_ & _ & <- & Hpub)".
  case: Hsub => [[]|[tsub [Hsub Hprot']]] //.
  inversion Hsub; subst.
  destruct kt;
    try (by iApply (IH Hprot' with "Hauth Hpub"));
    (iDestruct "Hpub" as "[Hpub|[Hel _]]";
     [ by iApply (IH Hprot' with "Hauth Hpub")
     | iDestruct (publicly_linked_lookup_l with "Hauth Hel") as %Hlookup;
       by case: (HnotPub _ Hlookup) ]).
- case: t' => /= *; try by iDestruct "Hpub" as "(_ & _ & [])".
  { iDestruct "Hpub" as "(_ & _ & Hel & _)".
    iDestruct (publicly_linked_lookup_l with "Hauth Hel") as %Hlookup.
    by case: (HnotPub _ Hlookup). }
  case: Hsub => [[]|[tsub [Hsub Hprot']]] //.
  iDestruct "Hpub" as "(_ & _ & [[Hk Hb]|[Hel _]])"; last first.
  { iDestruct (publicly_linked_lookup_l with "Hauth Hel") as %Hlookup.
    by case: (HnotPub _ Hlookup). }
  inversion Hsub; subst.
  + iApply (IHk Hprot' with "Hauth Hk").
  + iApply (IHb Hprot' with "Hauth Hb").
- case: t' => /= *; try by iDestruct "Hpub" as "(_ & _ & [])".
  case: Hsub => [[]|[tsub [Hsub Hprot']]] //.
  inversion Hsub; subst.
  iDestruct "Hpub" as "(_ & _ & [Hpub|[Hel _]])";
    first by iApply (IH Hprot' with "Hauth Hpub").
  iDestruct (publicly_linked_lookup_l with "Hauth Hel") as %Hlookup.
  by case: (HnotPub _ Hlookup).
- by iDestruct "Hpub" as "(_ & _ & [])".
Qed.

#[local] Lemma publicly_related_protected_r pub_r flow_r t' :
  public_rel_Private_r_protected pub_r flow_r →
  public_rel_flow_r_consistent pub_r flow_r →
  (∃ st, pub_r !! t' = Some st ∧ not_Public st) ∨ (∃ ts, flow_r !! t' = Some ts ∧ ts ≠ ∅) →
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  ∀ t, PUB⟨t, t'⟩ -∗ False.
Proof.
move=> HPriv Hcons.
elim/term_ind': t' => [n|a IHa b IHb|a|kt s IH|k IHk b IHb|s IH|pt wf nf] Hprot;
  iIntros "Hauth" (t) "#Hpub";
  case: (public_rel_protected_inv_r HPriv Hcons Hprot) => HnotPub Hsub.
- case: Hsub => [[]|[t'sub [Hsub _]]] //. by inversion Hsub.
- iDestruct (publicly_related_term_TPair with "Hpub") as %(a' & b' & ->).
  rewrite publicly_related_TPair. iDestruct "Hpub" as "[Ha Hb]".
  case: Hsub => [[]|[t'sub [Hsub Hprot']]] //.
  inversion Hsub; subst.
  + iApply (IHa Hprot' with "Hauth Ha").
  + iApply (IHb Hprot' with "Hauth Hb").
- iDestruct (publicly_related_term_TNonce with "Hpub") as "Hel".
  iDestruct (publicly_linked_lookup_r with "Hauth Hel") as %Hlookup.
  by case: (HnotPub _ Hlookup).
- case: t => /= *; try by iDestruct "Hpub" as "(_ & _ & [])".
  iDestruct "Hpub" as "(_ & _ & -> & Hpub)".
  case: Hsub => [[]|[t'sub [Hsub Hprot']]] //.
  inversion Hsub; subst.
  destruct kt;
    try (by iApply (IH Hprot' with "Hauth Hpub"));
    (iDestruct "Hpub" as "[Hpub|[Hel _]]";
     [ by iApply (IH Hprot' with "Hauth Hpub")
     | iDestruct (publicly_linked_lookup_r with "Hauth Hel") as %Hlookup;
       by case: (HnotPub _ Hlookup) ]).
- case: t => /= *; try by iDestruct "Hpub" as "(_ & _ & [])".
  { iDestruct "Hpub" as "(_ & _ & Hel & _)".
    iDestruct (publicly_linked_lookup_r with "Hauth Hel") as %Hlookup.
    by case: (HnotPub _ Hlookup). }
  case: Hsub => [[]|[t'sub [Hsub Hprot']]] //.
  iDestruct "Hpub" as "(_ & _ & [[Hk Hb]|[Hel _]])"; last first.
  { iDestruct (publicly_linked_lookup_r with "Hauth Hel") as %Hlookup.
    by case: (HnotPub _ Hlookup). }
  inversion Hsub; subst.
  + iApply (IHk Hprot' with "Hauth Hk").
  + iApply (IHb Hprot' with "Hauth Hb").
- case: t => /= *; try by iDestruct "Hpub" as "(_ & _ & [])".
  case: Hsub => [[]|[t'sub [Hsub Hprot']]] //.
  inversion Hsub; subst.
  iDestruct "Hpub" as "(_ & _ & [Hpub|[Hel _]])";
    first by iApply (IH Hprot' with "Hauth Hpub").
  iDestruct (publicly_linked_lookup_r with "Hauth Hel") as %Hlookup.
  by case: (HnotPub _ Hlookup).
- by case: t => /= *; iDestruct "Hpub" as "(_ & _ & [])".
Qed.

#[local] Lemma publicly_related_linked_in_l pub_l flow_l :
  public_rel_Private_l_protected pub_l flow_l →
  public_rel_flow_l_consistent pub_l flow_l →
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  public_rel_Public_consistent pub_l -∗
  ∀ t t1' t2', PUB⟨t, t1'⟩ -∗ linked_in_l t t2' -∗ PUB⟨t, t2'⟩.
Proof.
move=> HPriv Hcons. iIntros "Hauth Hrel" (t t1' t2') "#H1 #H2".
iDestruct (linked_in_l_lookup with "Hauth H2") as %[Hpriv|[Hpriv|Hpub]].
- by iPoseProof (publicly_related_protected_l HPriv Hcons (or_introl (ex_intro _ _ (conj Hpriv I)))
                  with "Hauth H1") as "[]".
- by iPoseProof (publicly_related_protected_l HPriv Hcons (or_introl (ex_intro _ _ (conj Hpriv I)))
                  with "Hauth H1") as "[]".
- by iApply ("Hrel" with "[//]").
Qed.

#[local] Lemma publicly_related_linked_in_r pub_l pub_r flow_r :
  public_rel_Private_r_protected pub_r flow_r →
  public_rel_flow_r_consistent pub_r flow_r →
  public_rel_Public_bijection pub_l pub_r →
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  public_rel_Public_consistent pub_l -∗
  ∀ t1 t2 t', PUB⟨t1, t'⟩ -∗ linked_in_r t2 t' -∗ PUB⟨t2, t'⟩.
Proof.
move=> HPriv Hcons Hbij. iIntros "Hauth Hrel" (t1 t2 t') "#H1 #H2".
iDestruct (linked_in_r_lookup with "Hauth H2") as %[Hpriv|[Hpriv|Hpub]].
- by iPoseProof (publicly_related_protected_r HPriv Hcons (or_introl (ex_intro _ _ (conj Hpriv I)))
                  with "Hauth H1") as "[]".
- by iPoseProof (publicly_related_protected_r HPriv Hcons (or_introl (ex_intro _ _ (conj Hpriv I)))
                  with "Hauth H1") as "[]".
- by iApply (public_rel_Public_consistent_r Hbij Hpub with "Hrel").
Qed.

Lemma publicly_related_part_bij_1 E t t1' t2' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  PUB⟨t, t1'⟩ -∗
  PUB⟨t, t2'⟩ -∗
  |={E}=> ⌜t1' = t2'⌝.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #H1 #H2".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  Hflow & [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iAssert ⌜t1' = t2'⌝%I as %Heq; last first.
{ iModIntro. iSplitL; last done.
  iModIntro. iExists pub_l, pub_r, flow_l, flow_r. iFrame. iFrame "#". by iPureIntro. }
iClear "Hmap_l_frag Hmap_r Hflow".
iInduction t as [n|a b|a|kt s|k b|s|pt wf nf] "IH" using term_ind' forall (t1' t2') "H1 H2".
- iDestruct (publicly_related_TInt_term with "H1") as %->.
  by iDestruct (publicly_related_TInt_term with "H2") as %->.
- iDestruct (publicly_related_TPair_term with "H1") as %(a1' & b1' & ->).
  iDestruct (publicly_related_TPair_term with "H2") as %(a2' & b2' & ->).
  rewrite !publicly_related_TPair.
  iDestruct "H1" as "[Ha Hb]". iDestruct "H2" as "[Ha' Hb']".
  iDestruct ("IH" with "Hmap_l Hpub_consistent Ha Ha'") as %->.
  by iDestruct ("IH1" with "Hmap_l Hpub_consistent Hb Hb'") as %->.
- iDestruct (publicly_related_TNonce_term with "H1") as "Hel1".
  iDestruct (publicly_related_TNonce_term with "H2") as "Hel2".
  by iApply (publicly_linked_agree_l with "Hel1 Hel2").
- case: t1' => /= *; try by iDestruct "H1" as "(_ & _ & [])".
  case: t2' => /= *; try by iDestruct "H2" as "(_ & _ & [])".
  iDestruct "H1" as "(_ & _ & <- & H1)". iDestruct "H2" as "(_ & _ & <- & H2)".
  destruct kt;
    try (by iDestruct ("IH" with "Hmap_l Hpub_consistent H1 H2") as %->);
    iDestruct "H1" as "[H1|[Hel1 [Hpriv1 _]]]";
    iDestruct "H2" as "[H2|[Hel2 [Hpriv2 _]]]";
    first
      [ by iDestruct ("IH" with "Hmap_l Hpub_consistent H1 H2") as %->
      | iPoseProof (publicly_related_linked_in_l HPriv_l Hflow_l_cons
                      with "Hmap_l Hpub_consistent H1 Hpriv2") as "#H2";
        by iDestruct ("IH" with "Hmap_l Hpub_consistent H1 H2") as %->
      | iPoseProof (publicly_related_linked_in_l HPriv_l Hflow_l_cons
                      with "Hmap_l Hpub_consistent H2 Hpriv1") as "#H1";
        by iDestruct ("IH" with "Hmap_l Hpub_consistent H1 H2") as %->
      | by (iDestruct (publicly_linked_agree_l with "Hel1 Hel2") as %Heq;
            injection Heq as ->) ].
- case: t1' => /= *; try by iDestruct "H1" as "(_ & _ & [])".
  { iPoseProof "H1" as "(_ & _ & _ & Hsecret & _)".
    iDestruct (secret_in_l_lookup with "Hmap_l Hsecret") as %Hb.
    case: t2' => /= *; try by iDestruct "H2" as "(_ & _ & [])".
    - iDestruct "H1" as "(_ & _ & Hel1 & _)". iDestruct "H2" as "(_ & _ & Hel2 & _)".
      by iApply (publicly_linked_agree_l with "Hel1 Hel2").
    - iDestruct "H2" as "(_ & _ & [[_ Hb2]|(Hel2 & _)])".
      + by iPoseProof (publicly_related_protected_l HPriv_l Hflow_l_cons
                        (or_introl (ex_intro _ _ (conj Hb I))) with "Hmap_l Hb2") as "[]".
      + iDestruct "H1" as "(_ & _ & Hel1 & _)".
        by iDestruct (publicly_linked_agree_l with "Hel1 Hel2") as %[=]. }
  case: t2' => /= *; try by iDestruct "H2" as "(_ & _ & [])".
  { iPoseProof "H2" as "(_ & _ & _ & Hsecret & _)".
    iDestruct (secret_in_l_lookup with "Hmap_l Hsecret") as %Hb.
    iDestruct "H1" as "(_ & _ & [[_ Hb1]|(Hel1 & _)])".
    + by iPoseProof (publicly_related_protected_l HPriv_l Hflow_l_cons
                      (or_introl (ex_intro _ _ (conj Hb I))) with "Hmap_l Hb1") as "[]".
    + iDestruct "H2" as "(_ & _ & Hel2 & _)".
      by iDestruct (publicly_linked_agree_l with "Hel1 Hel2") as %[=]. }
  iDestruct "H1" as "(_ & _ & [[Hk1 Hb1]|(Hel1 & [Hpk1 _] & [Hpb1 _] & _)])";
  iDestruct "H2" as "(_ & _ & [[Hk2 Hb2]|(Hel2 & [Hpk2 _] & [Hpb2 _] & _)])".
  + iDestruct ("IH" with "Hmap_l Hpub_consistent Hk1 Hk2") as %->.
    by iDestruct ("IH1" with "Hmap_l Hpub_consistent Hb1 Hb2") as %->.
  + iPoseProof (publicly_related_linked_in_l HPriv_l Hflow_l_cons
                  with "Hmap_l Hpub_consistent Hk1 Hpk2") as "#Hk2".
    iPoseProof (publicly_related_linked_in_l HPriv_l Hflow_l_cons
                  with "Hmap_l Hpub_consistent Hb1 Hpb2") as "#Hb2".
    iDestruct ("IH" with "Hmap_l Hpub_consistent Hk1 Hk2") as %->.
    by iDestruct ("IH1" with "Hmap_l Hpub_consistent Hb1 Hb2") as %->.
  + iPoseProof (publicly_related_linked_in_l HPriv_l Hflow_l_cons
                  with "Hmap_l Hpub_consistent Hk2 Hpk1") as "#Hk1".
    iPoseProof (publicly_related_linked_in_l HPriv_l Hflow_l_cons
                  with "Hmap_l Hpub_consistent Hb2 Hpb1") as "#Hb1".
    iDestruct ("IH" with "Hmap_l Hpub_consistent Hk1 Hk2") as %->.
    by iDestruct ("IH1" with "Hmap_l Hpub_consistent Hb1 Hb2") as %->.
  + iDestruct (publicly_linked_agree_l with "Hel1 Hel2") as %Heq.
    by injection Heq as -> ->.
- case: t1' => /= *; try by iDestruct "H1" as "(_ & _ & [])".
  case: t2' => /= *; try by iDestruct "H2" as "(_ & _ & [])".
  iDestruct "H1" as "(_ & _ & [H1|[Hel1 [Hpriv1 _]]])";
  iDestruct "H2" as "(_ & _ & [H2|[Hel2 [Hpriv2 _]]])".
  + by iDestruct ("IH" with "Hmap_l Hpub_consistent H1 H2") as %->.
  + iPoseProof (publicly_related_linked_in_l HPriv_l Hflow_l_cons
                  with "Hmap_l Hpub_consistent H1 Hpriv2") as "#H2".
    by iDestruct ("IH" with "Hmap_l Hpub_consistent H1 H2") as %->.
  + iPoseProof (publicly_related_linked_in_l HPriv_l Hflow_l_cons
                  with "Hmap_l Hpub_consistent H2 Hpriv1") as "#H1".
    by iDestruct ("IH" with "Hmap_l Hpub_consistent H1 H2") as %->.
  + iDestruct (publicly_linked_agree_l with "Hel1 Hel2") as %Heq.
    by injection Heq as ->.
- by iDestruct "H1" as "(_ & _ & [])".
Qed.

Lemma publicly_related_part_bij_2 E t1 t2 t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  PUB⟨t1, t'⟩ -∗
  PUB⟨t2, t'⟩ -∗
  |={E}=> ⌜t1 = t2⌝.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #H1 #H2".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  Hflow & [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iAssert ⌜t1 = t2⌝%I as %Heq; last first.
{ iModIntro. iSplitL; last done.
  iModIntro. iExists pub_l, pub_r, flow_l, flow_r. iFrame. iFrame "#". by iPureIntro. }
iClear "Hmap_l Hmap_r_frag Hflow".
iInduction t' as [n'|a' b'|a'|kt' s'|k' b'|s'|pt' wf' nf'] "IH" using term_ind' forall (t1 t2) "H1 H2".
- iDestruct (publicly_related_term_TInt with "H1") as %->.
  by iDestruct (publicly_related_term_TInt with "H2") as %->.
- iDestruct (publicly_related_term_TPair with "H1") as %(a1 & b1 & ->).
  iDestruct (publicly_related_term_TPair with "H2") as %(a2 & b2 & ->).
  rewrite !publicly_related_TPair.
  iDestruct "H1" as "[Ha Hb]". iDestruct "H2" as "[Ha' Hb']".
  iDestruct ("IH" with "Hmap_r Hpub_consistent Ha Ha'") as %->.
  by iDestruct ("IH1" with "Hmap_r Hpub_consistent Hb Hb'") as %->.
- iDestruct (publicly_related_term_TNonce with "H1") as "Hel1".
  iDestruct (publicly_related_term_TNonce with "H2") as "Hel2".
  by iApply (publicly_linked_agree_r with "Hel1 Hel2").
- case: t1 => /= *; try by iDestruct "H1" as "(_ & _ & [])".
  case: t2 => /= *; try by iDestruct "H2" as "(_ & _ & [])".
  iDestruct "H1" as "(_ & _ & -> & H1)". iDestruct "H2" as "(_ & _ & -> & H2)".
  destruct kt';
    try (by iDestruct ("IH" with "Hmap_r Hpub_consistent H1 H2") as %->);
    iDestruct "H1" as "[H1|[Hel1 [_ Hpriv1]]]";
    iDestruct "H2" as "[H2|[Hel2 [_ Hpriv2]]]";
    first
      [ by iDestruct ("IH" with "Hmap_r Hpub_consistent H1 H2") as %->
      | iPoseProof (publicly_related_linked_in_r HPriv_r Hflow_r_cons Hbij
                      with "Hmap_r Hpub_consistent H1 Hpriv2") as "#H2";
        by iDestruct ("IH" with "Hmap_r Hpub_consistent H1 H2") as %->
      | iPoseProof (publicly_related_linked_in_r HPriv_r Hflow_r_cons Hbij
                      with "Hmap_r Hpub_consistent H2 Hpriv1") as "#H1";
        by iDestruct ("IH" with "Hmap_r Hpub_consistent H1 H2") as %->
      | by (iDestruct (publicly_linked_agree_r with "Hel1 Hel2") as %Heq;
            injection Heq as ->) ].
- case: t1 => /= *; try by iDestruct "H1" as "(_ & _ & [])".
  { iPoseProof "H1" as "(_ & _ & _ & Hsecret & _)".
    iDestruct (secret_in_r_lookup with "Hmap_r Hsecret") as %Hb.
    case: t2 => /= *; try by iDestruct "H2" as "(_ & _ & [])".
    - iDestruct "H1" as "(_ & _ & Hel1 & _)". iDestruct "H2" as "(_ & _ & Hel2 & _)".
      by iApply (publicly_linked_agree_r with "Hel1 Hel2").
    - iDestruct "H2" as "(_ & _ & [[_ Hb2]|(Hel2 & _)])".
      + by iPoseProof (publicly_related_protected_r HPriv_r Hflow_r_cons
                        (or_introl (ex_intro _ _ (conj Hb I))) with "Hmap_r Hb2") as "[]".
      + iDestruct "H1" as "(_ & _ & Hel1 & _)".
        by iDestruct (publicly_linked_agree_r with "Hel1 Hel2") as %[=]. }
  case: t2 => /= *; try by iDestruct "H2" as "(_ & _ & [])".
  { iPoseProof "H2" as "(_ & _ & _ & Hsecret & _)".
    iDestruct (secret_in_r_lookup with "Hmap_r Hsecret") as %Hb.
    iDestruct "H1" as "(_ & _ & [[_ Hb1]|(Hel1 & _)])".
    + by iPoseProof (publicly_related_protected_r HPriv_r Hflow_r_cons
                      (or_introl (ex_intro _ _ (conj Hb I))) with "Hmap_r Hb1") as "[]".
    + iDestruct "H2" as "(_ & _ & Hel2 & _)".
      by iDestruct (publicly_linked_agree_r with "Hel1 Hel2") as %[=]. }
  iDestruct "H1" as "(_ & _ & [[Hk1 Hb1]|(Hel1 & [_ Hpk1] & [_ Hpb1] & _)])";
  iDestruct "H2" as "(_ & _ & [[Hk2 Hb2]|(Hel2 & [_ Hpk2] & [_ Hpb2] & _)])".
  + iDestruct ("IH" with "Hmap_r Hpub_consistent Hk1 Hk2") as %->.
    by iDestruct ("IH1" with "Hmap_r Hpub_consistent Hb1 Hb2") as %->.
  + iPoseProof (publicly_related_linked_in_r HPriv_r Hflow_r_cons Hbij
                  with "Hmap_r Hpub_consistent Hk1 Hpk2") as "#Hk2".
    iPoseProof (publicly_related_linked_in_r HPriv_r Hflow_r_cons Hbij
                  with "Hmap_r Hpub_consistent Hb1 Hpb2") as "#Hb2".
    iDestruct ("IH" with "Hmap_r Hpub_consistent Hk1 Hk2") as %->.
    by iDestruct ("IH1" with "Hmap_r Hpub_consistent Hb1 Hb2") as %->.
  + iPoseProof (publicly_related_linked_in_r HPriv_r Hflow_r_cons Hbij
                  with "Hmap_r Hpub_consistent Hk2 Hpk1") as "#Hk1".
    iPoseProof (publicly_related_linked_in_r HPriv_r Hflow_r_cons Hbij
                  with "Hmap_r Hpub_consistent Hb2 Hpb1") as "#Hb1".
    iDestruct ("IH" with "Hmap_r Hpub_consistent Hk1 Hk2") as %->.
    by iDestruct ("IH1" with "Hmap_r Hpub_consistent Hb1 Hb2") as %->.
  + iDestruct (publicly_linked_agree_r with "Hel1 Hel2") as %Heq.
    by injection Heq as -> ->.
- case: t1 => /= *; try by iDestruct "H1" as "(_ & _ & [])".
  case: t2 => /= *; try by iDestruct "H2" as "(_ & _ & [])".
  iDestruct "H1" as "(_ & _ & [H1|[Hel1 [_ Hpriv1]]])";
  iDestruct "H2" as "(_ & _ & [H2|[Hel2 [_ Hpriv2]]])".
  + by iDestruct ("IH" with "Hmap_r Hpub_consistent H1 H2") as %->.
  + iPoseProof (publicly_related_linked_in_r HPriv_r Hflow_r_cons Hbij
                  with "Hmap_r Hpub_consistent H1 Hpriv2") as "#H2".
    by iDestruct ("IH" with "Hmap_r Hpub_consistent H1 H2") as %->.
  + iPoseProof (publicly_related_linked_in_r HPriv_r Hflow_r_cons Hbij
                  with "Hmap_r Hpub_consistent H2 Hpriv1") as "#H1".
    by iDestruct ("IH" with "Hmap_r Hpub_consistent H1 H2") as %->.
  + iDestruct (publicly_linked_agree_r with "Hel1 Hel2") as %Heq.
    by injection Heq as ->.
- by case: t1 => /= *; iDestruct "H1" as "(_ & _ & [])".
Qed.

Lemma publicly_related_part_bij E t t' :
  ↑cryptisN ⊆ E →
  (∀ t1', cryptis_rel_ctx -∗ PUB⟨t, t'⟩ -∗ PUB⟨t, t1'⟩ -∗ |={E}=> ⌜t' = t1'⌝) ∧
  (∀ t1, cryptis_rel_ctx -∗ PUB⟨t, t'⟩ -∗ PUB⟨t1, t'⟩ -∗ |={E}=> ⌜t = t1⌝).
Proof.
move=> HE. split.
- move=> t1'. exact: publicly_related_part_bij_1.
- move=> t1. exact: publicly_related_part_bij_2.
Qed.

Lemma publicly_related_part_bij' E t1 t1' t2 t2' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  PUB⟨t1, t1'⟩ -∗
  PUB⟨t2, t2'⟩ -∗
  |={E}=> ⌜t1 = t2 ↔ t1' = t2'⌝.
Proof.
iIntros (HE) "#Hctx #Ht1 #Ht2".
destruct (decide (t1 = t2)) as [->|Hne].
{ iMod (publicly_related_part_bij_1 with "Hctx Ht1 Ht2") as %->; first done.
  by iPureIntro. }
destruct (decide (t1' = t2')) as [->|Hne'].
{ iMod (publicly_related_part_bij_2 with "Hctx Ht1 Ht2") as %->; first done.
  by iPureIntro. }
iPureIntro. tauto.
Qed.

End PartBij.

End Rel.
