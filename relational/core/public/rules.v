(** * Structural rules for [PUB]

- [Constructors]: characterization of [PUB] for integers, pairs, nonces,
  keys, hashes, tags, and lists.
- [Ciphertexts]: characterization of [PUB] for sealed terms and
  encryption. *)

From reloc Require Import reloc.
From cryptis Require Import cryptis.
From cryptis.hyper.core Require Import minted_spec term_meta_spec.
From cryptis.hyper.core.public Require Import state states base.
Import State.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicRules.

Context `{!relocG Σ, !publicGS Σ}.

Abbreviation iProp := (iProp Σ).
Abbreviation iPropO := (iPropO Σ).

Implicit Types t tsub tsup troot tprot t'sub t'sup t'root t'prot : term.
Implicit Types st : state.
Implicit Types states_l states_r : gmap term state.
Implicit Types P : term -> term -> iProp.

Section Constructors.

Lemma public_minted t t' :
  PUB⟨t, t'⟩ ⊢ minted t ∗ minted_spec t'.
Proof. case: t => *; iIntros "(#? & #? & _)"; by iFrame "#". Qed.

Lemma public_cases t t' :
  PUB⟨t, t'⟩ -∗
  same_shape public t t' ∨
  (publicly_linked t t' ∧
   (linked_shape public t t' ∨ (opaque_l t ∧ opaque_r t'))).
Proof. case: t => *; by iIntros "(_ & _ & ?)". Qed.

Lemma public_opaque t t' :
  minted t -∗ minted_spec t' -∗ publicly_linked t t' -∗
  opaque_l t -∗ opaque_r t' -∗ PUB⟨t, t'⟩.
Proof.
case: t => *; iIntros "#? #? #? #? #?";
  do 2 (iSplit; try done); iRight; iSplit; try done; iRight; by iSplit.
Qed.

Lemma public_TInt n n' :
  PUB⟨TInt n, TInt n'⟩ ⊣⊢ ⌜n = n'⌝.
Proof.
rewrite /= minted_TInt minted_spec_TInt. iSplit.
- by iIntros "(_ & _ & [?|(_ & [[]|[[] _]])])".
- iIntros "->". do 2 (iSplit; first done). by iLeft.
Qed.

Lemma public_TInt_term n (t' : term) :
  PUB⟨TInt n, t'⟩ -∗ ⌜t' = TInt n⌝.
Proof.
case: t' => /= *; iIntros "(_ & _ & [H|(_ & [H|[H _]])])";
  try (by iDestruct "H" as "[]").
by iDestruct "H" as %->.
Qed.

Lemma public_term_TInt (t : term) n :
  PUB⟨t, TInt n⟩ -∗ ⌜t = TInt n⌝.
Proof.
case: t => /= *; iIntros "(_ & _ & [H|(_ & [H|[_ H]])])";
  try (by iDestruct "H" as "[]").
by iDestruct "H" as %->.
Qed.

Lemma public_TPair t1 t2 t1' t2' :
  PUB⟨TPair t1 t2, TPair t1' t2'⟩ ⊣⊢
  PUB⟨t1, t1'⟩ ∧ PUB⟨t2, t2'⟩.
Proof.
rewrite /= minted_TPair minted_spec_TPair. iSplit.
- by iIntros "(_ & _ & [?|(_ & [[]|[[] _]])])".
- iIntros "#[H1 H2]".
  iPoseProof (public_minted with "H1") as "[? ?]".
  iPoseProof (public_minted with "H2") as "[? ?]".
  iSplit; first by iSplit. iSplit; first by iSplit. iLeft. by iSplit.
Qed.

Lemma public_TPair_term t1 t2 (t' : term) :
  PUB⟨TPair t1 t2, t'⟩ -∗
  ∃ t1' t2', ⌜t' = TPair t1' t2'⌝.
Proof.
case: t' => /= *; iIntros "(_ & _ & [H|(_ & [H|[H _]])])";
  try (by iDestruct "H" as "[]").
by iExists _, _.
Qed.

Lemma public_term_TPair (t : term) t1' t2' :
  PUB⟨t, TPair t1' t2'⟩ -∗
  ∃ t1 t2, ⌜t = TPair t1 t2⌝.
Proof.
case: t => /= *; iIntros "(_ & _ & [H|(_ & [H|[_ H]])])";
  try (by iDestruct "H" as "[]").
by iExists _, _.
Qed.

Lemma public_TNonce a a' :
  PUB⟨TNonce a, TNonce a'⟩ ⊣⊢
  minted (TNonce a) ∧ minted_spec (TNonce a') ∧
  publicly_linked (TNonce a) (TNonce a').
Proof.
rewrite /=. iSplit.
- iIntros "#(? & ? & [[]|[? _]])". by do 2 (iSplit; first done).
- iIntros "#(? & ? & ?)". do 2 (iSplit; first done).
  iRight. iSplit; first done. iRight. by iSplit.
Qed.

Lemma public_TNonce_term a (t' : term) :
  PUB⟨TNonce a, t'⟩ -∗ publicly_linked (TNonce a) t'.
Proof. rewrite /=. by iIntros "(_ & _ & [[]|[? _]])". Qed.

Lemma public_term_TNonce (t : term) a' :
  PUB⟨t, TNonce a'⟩ -∗ publicly_linked t (TNonce a').
Proof. case: t => /= *; by iIntros "(_ & _ & [[]|[? _]])". Qed.

Lemma public_nonce t t' :
  is_nonce t → is_nonce t' →
  PUB⟨t, t'⟩ ⊣⊢ minted t ∧ minted_spec t' ∧ publicly_linked t t'.
Proof. move=> /is_nonceP [a ->] /is_nonceP [a' ->]. exact: public_TNonce. Qed.

Lemma public_nonce_term t t' :
  is_nonce t → PUB⟨t, t'⟩ -∗ publicly_linked t t'.
Proof. move=> /is_nonceP [a ->]. exact: public_TNonce_term. Qed.

Lemma public_term_nonce t t' :
  is_nonce t' → PUB⟨t, t'⟩ -∗ publicly_linked t t'.
Proof. move=> /is_nonceP [a' ->]. exact: public_term_TNonce. Qed.

Lemma public_TKey kt kt' t t' :
  PUB⟨TKey kt t, TKey kt' t'⟩ ⊣⊢
  ⌜kt = kt'⌝ ∧
  (PUB⟨t, t'⟩ ∨
   (minted t ∧ minted_spec t' ∧
    publicly_linked (TKey kt t) (TKey kt' t') ∧ linked t t' ∧
    match kt with
    | ADec => PUB⟨TKey AEnc t, TKey AEnc t'⟩
    | Sign => PUB⟨TKey Verify t, TKey Verify t'⟩
    | _ => True
    end)).
Proof.
iSplit.
- iIntros "#H". iEval (rewrite /= minted_TKey minted_spec_TKey) in "H".
  iDestruct "H" as "#(? & ? & [[-> H]|(? & [(-> & ? & Hpk)|[[] _]])])"; iSplit; try done.
  + by iLeft.
  + iRight. do 4 (iSplit; first done).
    iRevert "Hpk". case: kt'; iIntros "#Hpk"; try done;
      iEval (rewrite /= minted_TKey minted_spec_TKey); do 2 (iSplit; try done);
      iRight; iSplit; try done; iLeft; iSplit; try done; by iFrame "#".
- iIntros "#(-> & [H|(? & ? & ? & ? & Hpk)])"; iEval (rewrite /= minted_TKey minted_spec_TKey).
  + iPoseProof (public_minted with "H") as "[? ?]".
    do 2 (iSplit; first done). iLeft. by iSplit.
  + do 2 (iSplit; first done).
    iRevert "Hpk". case: kt'; iIntros "#Hpk";
      try (iRight; iSplit; first done; iLeft; iSplit; first done; by iFrame "#");
      iEval (rewrite /=) in "Hpk";
      iDestruct "Hpk" as "(_ & _ & [[_ ?]|(? & [_|[[] _]])])";
      [ iLeft; by iSplit
      | iRight; iSplit; first done; iLeft; iSplit; first done; by iFrame "#"
      | iLeft; by iSplit
      | iRight; iSplit; first done; iLeft; iSplit; first done; by iFrame "#" ].
Qed.

Lemma public_TKey_term kt t (t' : term) :
  PUB⟨TKey kt t, t'⟩ -∗ ∃ t1', ⌜t' = TKey kt t1'⌝.
Proof.
case: t' => /= *; iIntros "(_ & _ & [H|(_ & [H|[H _]])])";
  try (by iDestruct "H" as "[]").
all: iDestruct "H" as "[-> _]"; by iExists _.
Qed.

Lemma public_term_TKey (t : term) kt' t' :
  PUB⟨t, TKey kt' t'⟩ -∗ ∃ t1, ⌜t = TKey kt' t1⌝.
Proof.
case: t => /= *; iIntros "(_ & _ & [H|(_ & [H|[_ H]])])";
  try (by iDestruct "H" as "[]").
all: iDestruct "H" as "[-> _]"; by iExists _.
Qed.

Lemma secret_in_l_TKey_public kt s t' :
  is_nonce s →
  secret_in_l s -∗ secret_in_l (TKey kt s) -∗ PUB⟨TKey kt s, t'⟩ -∗ False.
Proof.
iIntros (Hs) "#sec #sec_k #H".
iDestruct (public_TKey_term with "H") as %[s' ->].
iDestruct (public_TKey with "H") as "[_ [Hs|(_ & _ & [Hl _] & _)]]".
- iDestruct (public_nonce_term _ Hs with "Hs") as "[Hl _]".
  by iApply (secret_in_l_publicly_linked_in_l with "sec Hl").
- by iApply (secret_in_l_publicly_linked_in_l with "sec_k Hl").
Qed.

Lemma secret_in_r_TKey_public kt s' t :
  is_nonce s' →
  secret_in_r s' -∗ secret_in_r (TKey kt s') -∗ PUB⟨t, TKey kt s'⟩ -∗ False.
Proof.
iIntros (Hs') "#sec #sec_k #H".
iDestruct (public_term_TKey with "H") as %[s ->].
iDestruct (public_TKey with "H") as "[_ [Hs|(_ & _ & [_ Hl] & _)]]".
- iDestruct (public_term_nonce _ Hs' with "Hs") as "[_ Hl]".
  by iApply (secret_in_r_publicly_linked_in_r with "sec Hl").
- by iApply (secret_in_r_publicly_linked_in_r with "sec_k Hl").
Qed.

Lemma public_pkey t t' :
  PUB⟨t, t'⟩ -∗ PUB⟨Spec.pkey t, Spec.pkey t'⟩.
Proof.
iIntros "#H".
case ek: (Spec.to_key t) => [[kt s]|]; last first.
{ case ek': (Spec.to_key t') => [[kt' s']|].
  { have -> : t' = TKey kt' s' by case: t' ek' => // ?? [-> ->].
    iDestruct (public_term_TKey with "H") as %[s0 ->].
    by rewrite /= in ek. }
  have -> : Spec.pkey t = t by case: t ek => //= - [].
  have -> : Spec.pkey t' = t' by case: t' ek' => //= - [].
  done. }
have {ek} -> : t = TKey kt s by case: t ek => // ?? [-> ->].
iDestruct (public_TKey_term with "H") as %[s' ->].
case: kt; try done.
- rewrite -[Spec.pkey (TKey ADec s)]/(TKey AEnc s)
          -[Spec.pkey (TKey ADec s')]/(TKey AEnc s').
  iDestruct (public_TKey with "H") as "[_ [Hs|(_ & _ & _ & _ & ?)]]"; last done.
  iApply public_TKey. iSplit; first done. by iLeft.
- rewrite -[Spec.pkey (TKey Sign s)]/(TKey Verify s)
          -[Spec.pkey (TKey Sign s')]/(TKey Verify s').
  iDestruct (public_TKey with "H") as "[_ [Hs|(_ & _ & _ & _ & ?)]]"; last done.
  iApply public_TKey. iSplit; first done. by iLeft.
Qed.

Lemma public_has_key_type kt t t' :
  PUB⟨t, t'⟩ ⊢ ⌜Spec.has_key_type kt t = Spec.has_key_type kt t'⌝.
Proof.
iIntros "#H". rewrite /Spec.has_key_type.
case: (Spec.is_keyP t) => [kt0 s ->|Ht].
- by iDestruct (public_TKey_term with "H") as %[s' ->].
- case: (Spec.is_keyP t') => [kt1 s' ->|] //.
  iDestruct (public_term_TKey with "H") as %[s ->].
  by case: (Ht kt1 s).
Qed.

Lemma public_THash t t' :
  PUB⟨THash t, THash t'⟩ ⊣⊢
  PUB⟨t, t'⟩ ∨
  (minted t ∧ minted_spec t' ∧
   publicly_linked (THash t) (THash t') ∧ linked t t').
Proof.
rewrite /= minted_THash minted_spec_THash. iSplit.
- iIntros "#(? & ? & [?|(? & [?|[? ?]])])".
  + by iLeft.
  + iRight. by iFrame "#".
  + iRight. do 3 (iSplit; first done).
    by iApply secret_in_linked.
- iIntros "#[H|(? & ? & ? & ?)]".
  + iPoseProof (public_minted with "H") as "[? ?]".
    do 2 (iSplit; first done). by iLeft.
  + do 2 (iSplit; first done). iRight. iSplit; first done. by iLeft.
Qed.

Lemma public_THash_term t (t' : term) :
  PUB⟨THash t, t'⟩ -∗
  (∃ t1', ⌜t' = THash t1'⌝) ∨
  (publicly_linked (THash t) t' ∧ secret_in_l t ∧ opaque_r t').
Proof.
case: t' => /= *; iIntros "(_ & _ & [H|(? & [H|[? ?]])])";
  try (by iDestruct "H" as "[]"); try (by iRight; iFrame).
all: iLeft; by iExists _.
Qed.

Lemma public_term_THash (t : term) t' :
  PUB⟨t, THash t'⟩ -∗
  (∃ t1, ⌜t = THash t1⌝) ∨
  (publicly_linked t (THash t') ∧ opaque_l t ∧ secret_in_r t').
Proof.
case: t => /= *; iIntros "(_ & _ & [H|(? & [H|[? ?]])])";
  try (by iDestruct "H" as "[]"); try (by iRight; iFrame).
all: iLeft; by iExists _.
Qed.

Lemma public_Tag N N' : PUB⟨Tag N, Tag N'⟩ ⊣⊢ ⌜N = N'⌝.
Proof.
rewrite [Tag]unlock public_TInt. iSplit.
- iIntros "%H". injection H as H. by apply encode_inj in H.
- iIntros "->". done.
Qed.

Lemma public_Tag_term N (t' : term) :
  PUB⟨Tag N, t'⟩ -∗
  ⌜t' = Tag N⌝.
Proof.
iIntros "#H".
rewrite [Tag]unlock.
by iPoseProof (public_TInt_term with "H") as "->".
Qed.

Lemma public_term_Tag (t : term) N' :
  PUB⟨t, Tag N'⟩ -∗
  ⌜t = Tag N'⌝.
Proof.
iIntros "#H".
rewrite [Tag]unlock.
by iPoseProof (public_term_TInt with "H") as "->".
Qed.

Lemma public_tag N N' t t' :
  PUB⟨Spec.tag (Tag N) t, Spec.tag (Tag N') t'⟩ ⊣⊢
  ⌜N = N'⌝ ∧ PUB⟨t, t'⟩.
Proof.
by rewrite [Spec.tag]unlock public_TPair public_Tag.
Qed.

Lemma public_tag_term N t (t' : term) :
  PUB⟨Spec.tag (Tag N) t, t'⟩ -∗
  ∃ t1', ⌜t' = Spec.tag (Tag N) t1'⌝.
Proof.
iIntros "#H".
rewrite [Spec.tag]unlock.
iPoseProof (public_TPair_term with "H") as "(%t1' & %t2' & ->)".
rewrite public_TPair.
iDestruct "H" as "[H1 H2]".
iPoseProof (public_Tag_term with "H1") as "->".
by iExists t2'.
Qed.

Lemma public_term_tag (t : term) N t' :
  PUB⟨t, Spec.tag (Tag N) t'⟩ -∗
  ∃ t1, ⌜t = Spec.tag (Tag N) t1⌝.
Proof.
iIntros "#H".
rewrite [Spec.tag]unlock.
iPoseProof (public_term_TPair with "H") as "(%t1 & %t2 & ->)".
rewrite public_TPair.
iDestruct "H" as "[H1 H2]".
iPoseProof (public_term_Tag with "H1") as "->".
by iExists t2.
Qed.

Lemma public_untag N (u u' : term) :
  PUB⟨u, u'⟩ ⊢
  match Spec.untag (Tag N) u, Spec.untag (Tag N) u' with
  | Some m, Some m' => PUB⟨m, m'⟩
  | None, None => True
  | _, _ => False
  end.
Proof.
iIntros "#Hu".
case: (Spec.untagP (Tag N) u) => [m ->|Hu].
- iDestruct (public_tag_term with "Hu") as %[m' ->].
  rewrite !Spec.tagK public_tag. by iDestruct "Hu" as "[_ ?]".
- case: (Spec.untagP (Tag N) u') => [m' ->|] //.
  iDestruct (public_term_tag with "Hu") as %[m ->].
  by case: (Hu m).
Qed.

Lemma public_to_list (m m' : term) :
  PUB⟨m, m'⟩ ⊢
  match Spec.to_list m, Spec.to_list m' with
  | Some ts, Some ts' => [∗ list] t; t' ∈ ts; ts', PUB⟨t, t'⟩
  | None, None => True
  | _, _ => False
  end.
Proof.
elim/term_ind': m m' => [n|a _ b IH|a|kt k _|k _ t _|t _|pt wf nf] m'; iIntros "#Hm".
2: { iDestruct (public_TPair_term with "Hm") as %(a' & b' & ->).
     rewrite public_TPair. iDestruct "Hm" as "[Ha Hb]".
     iPoseProof (IH with "Hb") as "Hb'" => /=.
     destruct (Spec.to_list b), (Spec.to_list b'); by iFrame "#". }
1: { iDestruct (public_TInt_term with "Hm") as %->.
     case: n => [|p|p] /=; [iEmpIntro | by iPureIntro..]. }
all: case e: (Spec.to_list m') => [ts'|] //; move/Spec.to_listK: e => ->.
all: case: ts' => [|t' ts']; rewrite [Spec.of_list]unlock /=.
all: by iDestruct "Hm" as "(_ & _ & [[]|(_ & [[]|[_ []]])])".
Qed.

Lemma public_to_list_length n m m' :
  PUB⟨m, m'⟩ ⊢
  ⌜Spec.to_list m = None ∧ Spec.to_list m' = None⌝ ∨
  ∃ ts ts', ⌜Spec.to_list m = Some ts ∧ Spec.to_list m' = Some ts'⌝ ∗
    (⌜length ts ≠ n ∧ length ts' ≠ n⌝ ∨
     ⌜length ts = n⌝ ∗ [∗ list] t; t' ∈ ts; ts', PUB⟨t, t'⟩).
Proof.
iIntros "#Hm". iPoseProof (public_to_list with "Hm") as "Hl".
destruct (Spec.to_list m) as [ts|], (Spec.to_list m') as [ts'|]; try done.
- iDestruct (big_sepL2_length with "Hl") as %Hlen.
  iRight. iExists ts, ts'. iSplit; first done.
  case: (decide (length ts = n)) => Hn.
  + iRight. by iSplit.
  + iLeft. iPureIntro. lia.
- by iLeft.
Qed.

Lemma public_of_list (ts ts' : list term) :
  ([∗ list] t; t' ∈ ts; ts', PUB⟨t, t'⟩) ⊢ PUB⟨Spec.of_list ts, Spec.of_list ts'⟩.
Proof.
rewrite [Spec.of_list]unlock.
elim: ts ts' => [|t ts IH] [|t' ts']; iIntros "H"; cbn [foldr];
  try by iDestruct (big_sepL2_length with "H") as %?.
- by rewrite public_TInt.
- rewrite big_sepL2_cons public_TPair. iDestruct "H" as "[Ht H]".
  iSplit; first done. by iApply IH.
Qed.

Lemma public_adec_key' (k k' : aenc_key) :
  PUB⟨k, k'⟩ ⊣⊢
  PUB⟨seed_of_aenc_key k, seed_of_aenc_key k'⟩ ∨
  (minted k ∧ minted_spec k' ∧
   publicly_linked k k' ∧
   linked (seed_of_aenc_key k) (seed_of_aenc_key k') ∧
   PUB⟨Spec.pkey k, Spec.pkey k'⟩).
Proof.
rewrite [term_of_aenc_key]unlock.
set s := seed_of_aenc_key k. set s' := seed_of_aenc_key k'.
rewrite -[Spec.pkey (TKey ADec s)]/(TKey AEnc s) -[Spec.pkey (TKey ADec s')]/(TKey AEnc s').
rewrite !minted_TKey !minted_spec_TKey public_TKey.
iSplit; [iIntros "#[_ ?]" | iIntros "#?"; iSplit]; done.
Qed.

Lemma public_aenc_key_term (k : aenc_key) (t' : term) :
  PUB⟨k, t'⟩ -∗
  ∃ (k' : aenc_key), ⌜t' = k'⌝.
Proof.
rewrite [term_of_aenc_key]unlock /=.
case: t' => /= *; iIntros "(_ & _ & [H|(_ & [H|[H _]])])";
  try (by iDestruct "H" as "[]").
all: iDestruct "H" as "[<- _]"; by iExists (AEncKey _).
Qed.

Lemma public_term_aenc_key (t : term) (k' : aenc_key) :
  PUB⟨t, k'⟩ -∗
  ∃ (k : aenc_key), ⌜t = k⌝.
Proof.
rewrite [term_of_aenc_key]unlock /=.
case: t => /= *; iIntros "(_ & _ & [H|(_ & [H|[_ H]])])";
  try (by iDestruct "H" as "[]").
all: iDestruct "H" as "[-> _]"; by iExists (AEncKey _).
Qed.

Lemma public_aenc_key (k k' : aenc_key) :
  PUB⟨Spec.pkey k, Spec.pkey k'⟩ ⊣⊢
  PUB⟨k, k'⟩ ∨
  (minted k ∧ minted_spec k' ∧
   publicly_linked (Spec.pkey k) (Spec.pkey k') ∧
   linked (seed_of_aenc_key k) (seed_of_aenc_key k')).
Proof.
rewrite [term_of_aenc_key]unlock.
set s := seed_of_aenc_key k. set s' := seed_of_aenc_key k'.
rewrite -[Spec.pkey (TKey ADec s)]/(TKey AEnc s) -[Spec.pkey (TKey ADec s')]/(TKey AEnc s').
rewrite !minted_TKey !minted_spec_TKey.
iSplit.
- iIntros "#H". iDestruct (public_TKey with "H") as "[_ [Hs|(? & ? & ? & ? & _)]]".
  + iLeft. iApply public_TKey. iSplit; first done. by iLeft.
  + iRight. by iFrame "#".
- iIntros "#[H|(? & ? & ? & ?)]".
  + iDestruct (public_TKey with "H") as "[_ [Hs|(_ & _ & _ & _ & ?)]]"; last done.
    iApply public_TKey. iSplit; first done. by iLeft.
  + iApply public_TKey. iSplit; first done. iRight. by iFrame "#".
Qed.

Lemma public_aenc_key_pkey_term (sk : aenc_key) (t' : term) :
  PUB⟨Spec.pkey sk, t'⟩ -∗
  ∃ (sk' : aenc_key), ⌜t' = Spec.pkey sk'⌝.
Proof.
rewrite /Spec.pkey [term_of_aenc_key]unlock /=.
case: t' => /= *; iIntros "(_ & _ & [H|(_ & [H|[H _]])])";
  try (by iDestruct "H" as "[]").
all: iDestruct "H" as "[<- _]"; by iExists (AEncKey _).
Qed.

Lemma public_term_aenc_key_pkey (t : term) (sk' : aenc_key) :
  PUB⟨t, Spec.pkey sk'⟩ -∗
  ∃ (sk : aenc_key), ⌜t = Spec.pkey sk⌝.
Proof.
rewrite /Spec.pkey [term_of_aenc_key]unlock /=.
case: t => /= *; iIntros "(_ & _ & [H|(_ & [H|[_ H]])])";
  try (by iDestruct "H" as "[]").
all: iDestruct "H" as "[-> _]"; by iExists (AEncKey _).
Qed.

End Constructors.

Section Ciphertexts.

Lemma public_TSeal k k' t t' :
  PUB⟨TSeal k t, TSeal k' t'⟩ ⊣⊢
  (PUB⟨k, k'⟩ ∧ PUB⟨t, t'⟩) ∨
  (minted (TSeal k t) ∧ minted_spec (TSeal k' t') ∧
   publicly_linked (TSeal k t) (TSeal k' t') ∧
   ((linked k k' ∧
     □ match k, k' with
       | TKey kt k1, TKey kt' k1' =>
         match kt, kt' with
         | Sign, Sign => PUB⟨TKey Verify k1, TKey Verify k1'⟩ ∧ PUB⟨t, t'⟩
         | AEnc, AEnc => PUB⟨t, t'⟩ ∨ linked t t'
         | SEnc, SEnc => True
         | _, _ => False
         end
       | _, _ => False
       end) ∨
    (opaque_l (TSeal k t) ∧ opaque_r (TSeal k' t')))).
Proof.
iSplit.
- iIntros "#H". iEval (rewrite /=) in "H".
  iDestruct "H" as "#(mk & mk' & [?|(? & [[? #Hbox]|?])])"; first by iLeft.
  + iRight. do 3 (iSplit; first done). iLeft. iSplit; first done. iModIntro.
    case: k => [n|a b|a|kt k1|k b|s|pt wf nf]; try done.
    case: k' => [n'|a' b'|a'|kt' k1'|k'' b'|s'|pt' wf' nf']; try done.
    rewrite minted_TSeal minted_spec_TSeal !minted_TKey !minted_spec_TKey.
    iDestruct "mk" as "[mk1 _]". iDestruct "mk'" as "[mk1' _]".
    case: kt; case: kt'; try done.
    iDestruct "Hbox" as "[Hv Ht]". iSplit; last done.
    iApply public_TKey. iSplit; first done.
    iDestruct "Hv" as "[?|[? ?]]"; [by iLeft | iRight; by iFrame "#"].
  + iRight. do 3 (iSplit; first done). by iRight.
- iIntros "#[[H1 H2]|(mk & mk' & Hl & [[? #Hbox]|Ho])]"; iEval (rewrite /=).
  + iPoseProof (public_minted with "H1") as "[? ?]".
    iPoseProof (public_minted with "H2") as "[? ?]".
    rewrite minted_TSeal minted_spec_TSeal.
    iSplit; first by iSplit. iSplit; first by iSplit. iLeft. by iSplit.
  + do 2 (iSplit; first done). iRight. iSplit; first done. iLeft.
    iSplit; first done. iModIntro.
    case: k => [n|a b|a|kt k1|k b|s|pt wf nf]; try done.
    case: k' => [n'|a' b'|a'|kt' k1'|k'' b'|s'|pt' wf' nf']; try done.
    rewrite minted_TSeal minted_spec_TSeal !minted_TKey !minted_spec_TKey.
    iDestruct "mk" as "[mk1 _]". iDestruct "mk'" as "[mk1' _]".
    case: kt; case: kt'; try done.
    iDestruct "Hbox" as "[Hv Ht]". iSplit; last done.
    iDestruct (public_TKey with "Hv") as "[_ [?|(_ & _ & ? & ? & _)]]";
      [by iLeft | iRight; by iFrame "#"].
  + do 2 (iSplit; first done). iRight. iSplit; first done. by iRight.
Qed.

Lemma public_TSeal_term k t (t' : term) :
  PUB⟨TSeal k t, t'⟩ -∗
  (∃ k' t1', ⌜t' = TSeal k' t1'⌝) ∨
  (publicly_linked (TSeal k t) t' ∧ opaque_l (TSeal k t) ∧ opaque_r t').
Proof.
case: t' => /= *; iIntros "(_ & _ & [H|(? & [H|[? ?]])])";
  try (by iDestruct "H" as "[]"); try (by iRight; iFrame).
all: iLeft; by iExists _, _.
Qed.

Lemma public_term_TSeal (t : term) k' t' :
  PUB⟨t, TSeal k' t'⟩ -∗
  (∃ k t1, ⌜t = TSeal k t1⌝) ∨
  (publicly_linked t (TSeal k' t') ∧ opaque_l t ∧ opaque_r (TSeal k' t')).
Proof.
case: t => /= *; iIntros "(_ & _ & [H|(? & [H|[? ?]])])";
  try (by iDestruct "H" as "[]"); try (by iRight; iFrame).
all: iLeft; by iExists _, _.
Qed.

Lemma public_enc (k k' : term) N t t' :
  PUB⟨k, k'⟩ -∗ PUB⟨t, t'⟩ -∗
  PUB⟨Spec.enc k (Tag N) t, Spec.enc k' (Tag N) t'⟩.
Proof.
iIntros "#Hk #Ht". rewrite /Spec.enc public_TSeal. iLeft.
iSplit; first done. rewrite public_tag. by iSplit.
Qed.

End Ciphertexts.

End PublicRules.
