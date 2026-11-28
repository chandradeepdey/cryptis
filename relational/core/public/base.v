(** * The relation [PUB] and its invariant

[PUB⟨t, t'⟩] says that the attacker cannot tell [t] in the left run apart
from [t'] in the right run.

- [Subterms]: the immediate parts of a term and chains of parts.
- [Relation]: two terms are related if they are built the same way from
  related parts, or if they are publicly linked and look alike to the
  attacker.
- [Invariant]: for a hidden term, the invariant holds back the parts on a
  chain down to a secret term, a nonce, or a linked term, and records that
  chain when the term enters the states map; a term becomes public only
  when nothing holds it back.  For a public ciphertext whose payload is
  hidden, the invariant holds its key back the same way. *)

From iris.algebra Require Import gmap gset.
From reloc Require Import reloc.
From cryptis Require Import cryptis.
From cryptis.hyper.core Require Import minted_spec term_meta_spec.
From cryptis.hyper.core.public Require Import state states.
Import State.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Public.

Context `{!relocG Σ, !publicGS Σ}.

Abbreviation iProp := (iProp Σ).
Abbreviation iPropO := (iPropO Σ).

Implicit Types t tsub tsup troot tprot t'sub t'sup t'root t'prot : term.
Implicit Types st : state.
Implicit Types states_l states_r : gmap term state.
Implicit Types P : term -> term -> iProp.

Section Subterms.

Inductive is_immediate_subterm : term → term → Prop :=
  | SubtermPairL t1 t2 : is_immediate_subterm t1 (TPair t1 t2)
  | SubtermPairR t1 t2 : is_immediate_subterm t2 (TPair t1 t2)
  | SubtermKey kt t1 : is_immediate_subterm t1 (TKey kt t1)
  | SubtermSealKey k t1 : is_immediate_subterm k (TSeal k t1)
  | SubtermSealBody k t1 : is_immediate_subterm t1 (TSeal k t1)
  | SubtermHash t1 : is_immediate_subterm t1 (THash t1).

Lemma is_immediate_subterm_aenc_key (sk : aenc_key) :
  is_immediate_subterm (seed_of_aenc_key sk) sk.
Proof. rewrite [term_of_aenc_key]unlock. exact: SubtermKey. Qed.

Lemma is_immediate_subterm_sign_key (sk : sign_key) :
  is_immediate_subterm (seed_of_sign_key sk) sk.
Proof. rewrite [term_of_sign_key]unlock. exact: SubtermKey. Qed.

Inductive subterm_path : term → list term → term → Prop :=
  | SubtermPathOne tsub t :
      is_immediate_subterm tsub t →
      subterm_path t [] tsub
  | SubtermPathStep tsub path troot t :
      is_immediate_subterm tsub t →
      subterm_path tsub path troot →
      subterm_path t (tsub :: path) troot.

Lemma is_immediate_subterm_lt tsub t :
  is_immediate_subterm tsub t → tsize tsub < tsize t.
Proof.
case => *;
  [ rewrite (tsize_eq (TPair _ _))
  | rewrite (tsize_eq (TPair _ _))
  | rewrite (tsize_eq (TKey _ _))
  | rewrite (tsize_eq (TSeal _ _))
  | rewrite (tsize_eq (TSeal _ _))
  | rewrite (tsize_eq (THash _)) ]; lia.
Qed.

Lemma subterm_path_lt t path troot :
  subterm_path t path troot → tsize troot < tsize t.
Proof.
elim => [?? /is_immediate_subterm_lt // | ???? /is_immediate_subterm_lt ? _ ?]; lia.
Qed.

End Subterms.

Section Relation.

Definition opaque_l t : iProp :=
  match t with
  | TNonce _ => True
  | THash t1 => secret_in_l t1
  | TSeal k t1 =>
    match k with
    | TKey AEnc s => secret_in_l (TKey ADec s) ∧ secret_in_l t1
    | TKey SEnc _ => secret_in_l k
    | _ => False
    end
  | _ => False
  end.

Definition opaque_r t' : iProp :=
  match t' with
  | TNonce _ => True
  | THash t1' => secret_in_r t1'
  | TSeal k' t1' =>
    match k' with
    | TKey AEnc s' => secret_in_r (TKey ADec s') ∧ secret_in_r t1'
    | TKey SEnc _ => secret_in_r k'
    | _ => False
    end
  | _ => False
  end.

#[global] Instance opaque_l_persistent t : Persistent (opaque_l t).
Proof. rewrite /opaque_l. apply _. Qed.

#[global] Instance opaque_r_persistent t' : Persistent (opaque_r t').
Proof. rewrite /opaque_r. apply _. Qed.

#[global] Instance opaque_l_timeless t : Timeless (opaque_l t).
Proof. rewrite /opaque_l. apply _. Qed.

#[global] Instance opaque_r_timeless t' : Timeless (opaque_r t').
Proof. rewrite /opaque_r. apply _. Qed.

Definition same_shape (R : term → term → iProp) t t' : iProp :=
  match t, t' with
  | TInt n, TInt n' => ⌜n = n'⌝
  | TPair t1 t2, TPair t1' t2' => R t1 t1' ∧ R t2 t2'
  | TKey kt t1, TKey kt' t1' => ⌜kt = kt'⌝ ∧ R t1 t1'
  | TSeal k t1, TSeal k' t1' => R k k' ∧ R t1 t1'
  | THash t1, THash t1' => R t1 t1'
  | _, _ => False
  end.

Definition linked_shape (R : term → term → iProp) t t' : iProp :=
  match t, t' with
  | TKey kt t1, TKey kt' t1' =>
    ⌜kt = kt'⌝ ∧ linked t1 t1' ∧
    (* [R (TKey AEnc t1) (TKey AEnc t1')] and [R (TKey Verify t1) (TKey Verify t1')],
       reduced to only the extra bits for the termination checker *)
    match kt with
    | ADec => publicly_linked (TKey AEnc t1) (TKey AEnc t1')
    | Sign => publicly_linked (TKey Verify t1) (TKey Verify t1')
    | _ => True
    end
  | TSeal k t1, TSeal k' t1' =>
    linked k k' ∧
    □ match k, k' with
      | TKey kt k1, TKey kt' k1' =>
        match kt, kt' with
        | Sign, Sign =>
          (* [R (TKey Verify k1) (TKey Verify k1')], inlined for the
             termination checker. *)
          (R k1 k1' ∨
           (publicly_linked (TKey Verify k1) (TKey Verify k1') ∧ linked k1 k1')) ∧
          R t1 t1'
        | AEnc, AEnc => R t1 t1' ∨ linked t1 t1'
        | SEnc, SEnc => True
        | _, _ => False
        end
      | _, _ => False
      end
  | THash t1, THash t1' => linked t1 t1'
  | _, _ => False
  end.

#[global] Instance same_shape_persistent R t t' :
  (∀ a b, Persistent (R a b)) → Persistent (same_shape R t t').
Proof. move=> ?. rewrite /same_shape. case: t; case: t' => *; apply _. Qed.

#[global] Instance linked_shape_persistent R t t' : Persistent (linked_shape R t t').
Proof. rewrite /linked_shape. case: t; case: t' => *; apply _. Qed.

Fixpoint public t t' : iProp :=
  minted t ∧ minted_spec t' ∧
  (same_shape public t t' ∨
   (publicly_linked t t' ∧
    (linked_shape public t t' ∨ (opaque_l t ∧ opaque_r t')))).

#[local] Notation "PUB⟨ a , b ⟩" := (public a b)
  (at level 0, no associativity, format "PUB⟨ a , b ⟩").

#[global] Instance public_persistent t t' : Persistent (PUB⟨t, t'⟩).
Proof. elim/term_ind': t t' => /=; rewrite /same_shape /linked_shape; apply _. Qed.

#[global] Instance public_timeless t t' : Timeless (PUB⟨t, t'⟩).
Proof.
elim/term_lt_ind: t t' => t IH t'.
case: t IH => [n|a b|a|kt s|k b|s|pt wf nf] IH /=; rewrite /same_shape /linked_shape;
  try apply _.
- have ? : ∀ t'', Timeless (PUB⟨a, t''⟩)
    by apply: IH; rewrite (tsize_eq (TPair _ _)); lia.
  have ? : ∀ t'', Timeless (PUB⟨b, t''⟩)
    by apply: IH; rewrite (tsize_eq (TPair _ _)); lia.
  apply _.
- have ? : ∀ t'', Timeless (PUB⟨s, t''⟩)
    by apply: IH; rewrite (tsize_eq (TKey _ _)); lia.
  apply _.
- have Hk : ∀ t'', Timeless (PUB⟨k, t''⟩)
    by apply: IH; rewrite (tsize_eq (TSeal _ _)); lia.
  have Hb : ∀ t'', Timeless (PUB⟨b, t''⟩)
    by apply: IH; rewrite (tsize_eq (TSeal _ _)); lia.
  case: k IH Hk => [n|a b'|a|kt s|k b'|s|pt wf nf] IH Hk; try apply _.
  have ? : ∀ t'', Timeless (PUB⟨s, t''⟩).
  { apply: IH. rewrite (tsize_eq (TSeal _ _)) (tsize_eq (TKey _ _)). lia. }
  apply _.
- have ? : ∀ t'', Timeless (PUB⟨s, t''⟩)
    by apply: IH; rewrite (tsize_eq (THash _)); lia.
  apply _.
Qed.

End Relation.

Section Invariant.

#[local] Notation "PUB⟨ a , b ⟩" := (public a b)
  (at level 0, no associativity, format "PUB⟨ a , b ⟩").

Definition protected_by_chain_l t path tprot : iProp :=
  ⌜subterm_path t path tprot⌝ ∗
  ([∗ list] t1 ∈ path, holds_subterm_l t t1) ∗
  (secret_in_l tprot ∨ (⌜is_nonce tprot⌝ ∨ ∃ t'prot, linked_in_l tprot t'prot) ∗ holds_subterm_l t tprot).

Definition protected_by_chain_r t' path t'prot : iProp :=
  ⌜subterm_path t' path t'prot⌝ ∗
  ([∗ list] t1' ∈ path, holds_subterm_r t' t1') ∗
  (secret_in_r t'prot ∨ (⌜is_nonce t'prot⌝ ∨ ∃ tprot, linked_in_r tprot t'prot) ∗ holds_subterm_r t' t'prot).

Definition protected_deposit_l t : iProp :=
  ⌜is_nonce t⌝ ∨ ∃ path tprot, protected_by_chain_l t path tprot.

Definition protected_deposit_r t' : iProp :=
  ⌜is_nonce t'⌝ ∨ ∃ path t'prot, protected_by_chain_r t' path t'prot.

Definition protects_deposit_l t : iProp :=
  ⌜is_nonce t⌝ ∨
  ∃ path tprot, protected_by_chain_l t path tprot ∗ protected_via_l t path tprot.

Definition protects_deposit_r t' : iProp :=
  ⌜is_nonce t'⌝ ∨
  ∃ path t'prot, protected_by_chain_r t' path t'prot ∗ protected_via_r t' path t'prot.

Definition public_deposit_l t t' : iProp :=
  match t, t' with
  | TSeal k t1, TSeal k' t1' =>
    match k with
    | TKey AEnc s =>
      (PUB⟨t1, t1'⟩ ∨ secret_in_l (TKey ADec s)) ∗ seal_release_l (TSeal k t1) ∨
      (∃ dk', linked_in_l (TKey ADec s) dk') ∗ holds_key_l t1 k
    | TKey SEnc s =>
      (PUB⟨t1, t1'⟩ ∨ secret_in_l (TKey SEnc s)) ∗ seal_release_l (TSeal k t1) ∨
      (∃ dk', linked_in_l (TKey SEnc s) dk') ∗ holds_key_l t1 k
    | _ => PUB⟨t1, t1'⟩
    end
  | TKey ADec s, _ => term_token (TKey AEnc s) (↑holdN)
  | TKey SEnc s, _ => term_token (TKey SEnc s) (↑holdN)
  | _, _ => True
  end.

Definition public_deposit_r t t' : iProp :=
  match t', t with
  | TSeal k' t1', TSeal k t1 =>
    match k' with
    | TKey AEnc s' =>
      (PUB⟨t1, t1'⟩ ∨ secret_in_r (TKey ADec s')) ∗ seal_release_r (TSeal k' t1') ∨
      (∃ dk, linked_in_r dk (TKey ADec s')) ∗ holds_key_r t1' k'
    | TKey SEnc s' =>
      (PUB⟨t1, t1'⟩ ∨ secret_in_r (TKey SEnc s')) ∗ seal_release_r (TSeal k' t1') ∨
      (∃ dk, linked_in_r dk (TKey SEnc s')) ∗ holds_key_r t1' k'
    | _ => PUB⟨t1, t1'⟩
    end
  | TKey ADec s', _ => term_token_spec (TKey AEnc s') (↑holdN)
  | TKey SEnc s', _ => term_token_spec (TKey SEnc s') (↑holdN)
  | _, _ => True
  end.

Definition public_states_l_deposits states_l : iProp :=
  [∗ map] t ↦ st ∈ states_l,
    match st with
    | PublicLink t' => public_deposit_l t t' ∗ prots_token_l t
    | _ => protects_deposit_l t
    end.

Definition public_states_r_deposits states_r : iProp :=
  [∗ map] t' ↦ st ∈ states_r,
    match st with
    | PublicLink t => public_deposit_r t t' ∗ prots_token_r t'
    | _ => protects_deposit_r t'
    end.

Definition public_states_deposits states_l states_r : iProp :=
  public_states_l_deposits states_l ∗ public_states_r_deposits states_r.

Definition public_PublicLink_l_consistent states_l : iProp :=
  ∀ t t', ⌜states_l !! t = Some (PublicLink t')⌝ → public t t'.

Definition public_PublicLink_r_consistent states_r : iProp :=
  ∀ t t', ⌜states_r !! t' = Some (PublicLink t)⌝ → public t t'.

Definition public_PublicLink_consistent states_l states_r : iProp :=
  public_PublicLink_l_consistent states_l ∗ public_PublicLink_r_consistent states_r.

Definition public_inv states_l states_r : iProp :=
  public_states_inv states_l states_r ∗
  public_states_deposits states_l states_r ∗
  public_PublicLink_consistent states_l states_r.

Definition public_ctx : iProp :=
  inv cryptisN (∃ states_l states_r, public_inv states_l states_r).

#[global] Instance protected_deposit_l_timeless t : Timeless (protected_deposit_l t).
Proof. rewrite /protected_deposit_l /protected_by_chain_l /holds_subterm_l. apply _. Qed.

#[global] Instance protected_deposit_r_timeless t' : Timeless (protected_deposit_r t').
Proof. rewrite /protected_deposit_r /protected_by_chain_r /holds_subterm_r. apply _. Qed.

#[global] Instance protects_deposit_l_timeless t : Timeless (protects_deposit_l t).
Proof. rewrite /protects_deposit_l /protected_by_chain_l /holds_subterm_l. apply _. Qed.

#[global] Instance protects_deposit_r_timeless t' : Timeless (protects_deposit_r t').
Proof. rewrite /protects_deposit_r /protected_by_chain_r /holds_subterm_r. apply _. Qed.

Lemma protects_deposit_protected_l t : protects_deposit_l t -∗ protected_deposit_l t.
Proof. iIntros "[?|(%path & %tprot & ? & _)]"; [by iLeft | iRight; by iExists _, _]. Qed.

Lemma protects_deposit_protected_r t' : protects_deposit_r t' -∗ protected_deposit_r t'.
Proof. iIntros "[?|(%path & %t'prot & ? & _)]"; [by iLeft | iRight; by iExists _, _]. Qed.

Lemma protects_deposit_chain_l t path tprot :
  ¬ is_nonce t →
  protected_via_l t path tprot -∗ protects_deposit_l t -∗
  protected_by_chain_l t path tprot.
Proof.
iIntros (Ht) "#via [%Hn|(%path1 & %tprot1 & prot & via1)]"; first by case: (Ht Hn).
by iDestruct (protected_via_l_agree with "via via1") as %[-> ->].
Qed.

Lemma protects_deposit_chain_r t' path t'prot :
  ¬ is_nonce t' →
  protected_via_r t' path t'prot -∗ protects_deposit_r t' -∗
  protected_by_chain_r t' path t'prot.
Proof.
iIntros (Ht) "#via [%Hn|(%path1 & %t'prot1 & prot & via1)]"; first by case: (Ht Hn).
by iDestruct (protected_via_r_agree with "via via1") as %[-> ->].
Qed.

#[global] Instance public_states_l_deposits_timeless states_l :
  Timeless (public_states_l_deposits states_l).
Proof.
apply big_sepM_timeless => t st.
rewrite /public_deposit_l /holds_key_l /seal_release_l /prots_token_l.
repeat case_match; apply _.
Qed.

#[global] Instance public_states_r_deposits_timeless states_r :
  Timeless (public_states_r_deposits states_r).
Proof.
apply big_sepM_timeless => t' st.
rewrite /public_deposit_r /holds_key_r /seal_release_r /prots_token_r.
repeat case_match; apply _.
Qed.

Definition hypercryptis_ctx : iProp :=
  term_meta_ctx ∗ term_meta_spec_ctx ∗ public_ctx.

#[global] Instance hypercryptis_ctx_has_term_meta_ctx : HasTermMetaCtx hypercryptis_ctx.
Proof. split; last apply _. by iIntros "#[H _]". Qed.

#[global] Instance hypercryptis_ctx_has_term_meta_spec_ctx : HasTermMetaSpecCtx hypercryptis_ctx.
Proof. split; last apply _. by iIntros "#[_ [H _]]". Qed.

End Invariant.

End Public.

Notation "PUB⟨ a , b ⟩" := (public a b)
  (at level 0, no associativity, format "PUB⟨ a , b ⟩").


Lemma publicGS_alloc `{!relocG Σ} E :
  publicGpreS Σ →
  ⊢ |={E}=> ∃ (H : publicGS Σ),
              hypercryptis_ctx.
Proof.
move=> [? ?]; iStartProof.
iMod term_metaGS_alloc as "[% #?]".
iMod term_meta_specGS_alloc as "[% #?]".
iMod (own_alloc (● (∅ : gmapUR term (authUR (optionUR stateR)))))
  as "[%public_states_l Hstates_l]"; first by apply auth_auth_valid.
iMod (own_alloc (● (∅ : gmapUR term (authUR (optionUR stateR)))))
  as "[%public_states_r Hstates_r]"; first by apply auth_auth_valid.
pose (Hpub := PublicGS _ _ _ public_states_l public_states_r).
iExists Hpub.
iMod (inv_alloc cryptisN _
        (∃ states_l states_r, public_inv states_l states_r)%I
        with "[Hstates_l Hstates_r]") as "#Hinv"; last by iFrame "#∗".
iModIntro. iExists ∅, ∅.
rewrite /public_inv /public_states_inv
        /public_states_l_auth /public_states_r_auth
        /public_states_deposits
        /public_states_l_deposits /public_states_r_deposits
        !fmap_empty !dom_empty_L !big_sepM_empty !big_sepS_empty.
iFrame. rewrite !left_id.
iSplit.
- iIntros (t t') "%Hcontra". by rewrite lookup_empty in Hcontra.
- iIntros (t t') "%Hcontra". by rewrite lookup_empty in Hcontra.
Qed.
