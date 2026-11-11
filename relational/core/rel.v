(** * The relation [PUB] and its invariant

[PUB⟨t, t'⟩] says that the attacker cannot tell [t] in the left run apart
from [t'] in the right run.  The invariant behind it keeps track of which
terms the two runs treat as the same, and which terms stay secret.

** Section [PublicRel]

- [Owners] says where the ghost state of a term lives.  A ciphertext lives on
  the seed of its key, under a namespace for the key and the payload, so that
  whoever holds the tokens of the seed decides how the runs treat the
  ciphertexts made with it, even the ones that anyone can compute.  Any other
  term lives on itself.  The part of these tokens that decides how the runs
  treat a term is its relational token; the never-sealed tokens of a seed
  hold the relational tokens of all the ciphertexts under its keys.
- [Map] records what is known about each term.
  - [linked t t'] means that the runs treat [t] and [t'] as the same term.
  - [publicly_linked t t'] means the same, and that the attacker may see
    them.
  - [secret_in_l t] means that the attacker never sees [t] in the left run.
- [Flow] records why a term stays hidden.  A term other than a nonce can be
  hidden only if one of its parts is hidden, for example the nonce inside it,
  or the key or the payload of a ciphertext.
- [Relation] defines [PUB].  Two terms are related if they are built the same
  way from related parts, or if they are publicly linked and either have the
  same shape with linked parts, which the attacker can only take apart in the
  same way in both runs, or are both opaque: a nonce, the hash of a secret, or
  a ciphertext that the attacker can neither make nor open.
- [Invariant] puts these together.

** Section [RelProperties]

- [Constructors] says what [PUB] means for each kind of term.  For a
  constructor [X], [publicly_related_X] covers two [X] terms, and
  [publicly_related_X_term] and [publicly_related_term_X] say what may be
  related to an [X] term.
- [Ciphertexts] does the same for ciphertexts.
- [Protection]: a hidden term is related to nothing, an opaque term is not
  built from related parts, and linked parts have the same partners as
  related ones.
- [Admission]: a term with an entry in the map has spent its map token.
- [PartBij]: a term is related to at most one term in the other run.
- [AttackerDecryption]: if the attacker tries to decrypt related terms with
  related keys, it succeeds in both runs or in neither, and the results are
  related.
- [HonestDecryption]: what an honest party gets when it decrypts with its
  own secret key, in each run.

Lemmas ending in [_fupd] are the ones to use.  The local ones they are built
from assume that the invariant is already open. *)

From iris.algebra Require Import gmap gset.
From reloc Require Import reloc.
From cryptis Require Import cryptis.
From cryptis.hyper.core Require Import minted_spec term_meta_spec.
From cryptis.hyper.core Require Import rel_state.
Import State.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation hypercryptisN := (cryptisN.@"hyper").
Abbreviation sealN := (hypercryptisN.@"seal").
Abbreviation termN := (hypercryptisN.@"term").

Class public_relGpreS Σ := Public_relGpreS {
  #[local] public_relGpreS_maps :: inG Σ (authUR (gmapUR term (authUR (optionUR stateR))));
  #[local] public_relGpreS_flow :: inG Σ (authUR (gmapUR term (authUR (gset_disjUR term))));
  #[local] public_relGpreS_term_meta :: term_metaGpreS Σ;
}.

Class public_relGS Σ := Public_relGS {
  #[global] maps_inG :: inG Σ (authUR (gmapUR term (authUR (optionUR stateR))));
  #[global] flow_inG :: inG Σ (authUR (gmapUR term (authUR (gset_disjUR term))));
  #[global] term_meta_inG :: term_metaGS Σ;
  #[global] term_meta_spec_inG :: term_meta_specGS Σ;
  public_rel_map_l : gname;
  public_rel_map_r : gname;
  public_rel_flow_l : gname;
  public_rel_flow_r : gname;
}.

Definition public_relΣ : gFunctors :=
  #[GFunctor (authUR (gmapUR term (authUR (optionUR stateR))));
    GFunctor (authUR (gmapUR term (authUR (gset_disjUR term))));
    term_metaΣ].

#[global] Instance subG_public_relGpreS Σ : subG public_relΣ Σ → public_relGpreS Σ.
Proof. solve_inG. Qed.

Section PublicRel.

Context `{!relocG Σ, !public_relGS Σ}.

Abbreviation iProp := (iProp Σ).
Abbreviation iPropO := (iPropO Σ).

Implicit Types t : term.
Implicit Types st : state.
Implicit Types pub_l pub_r : gmap term state.
Implicit Types flow_l flow_r : gmap term (gset term).
Implicit Types P : term -> term -> iProp.

Section Owners.

Definition seal_ns (k t : term) : namespace := sealN.@(k, t).

Definition rel_owner t : term :=
  match t with
  | TSeal (TKey _ s) _ => s
  | _ => t
  end.

Definition rel_ns t : namespace :=
  match t with
  | TSeal k t1 => seal_ns k t1
  | _ => termN
  end.

Definition rel_token_l t : iProp := term_token (rel_owner t) (↑rel_ns t).
Definition rel_token_r t' : iProp := term_token_spec (rel_owner t') (↑rel_ns t').

Definition map_token_l t : iProp := term_token (rel_owner t) (↑rel_ns t.@"map").
Definition map_token_r t' : iProp := term_token_spec (rel_owner t') (↑rel_ns t'.@"map").
Definition map_meta_l t : iProp := term_meta (rel_owner t) (rel_ns t.@"map") ().
Definition map_meta_r t' : iProp := term_meta_spec (rel_owner t') (rel_ns t'.@"map") ().

Definition flow_token_l t : iProp := term_token (rel_owner t) (↑rel_ns t.@"flow").
Definition flow_token_r t' : iProp := term_token_spec (rel_owner t') (↑rel_ns t'.@"flow").
Definition flow_meta_l t : iProp := term_meta (rel_owner t) (rel_ns t.@"flow") ().
Definition flow_meta_r t' : iProp := term_meta_spec (rel_owner t') (rel_ns t'.@"flow") ().

Definition never_sealed_under s s' E E' : iProp :=
  term_token s E ∗ term_token_spec s' E'.

#[global] Instance map_meta_l_persistent t : Persistent (map_meta_l t).
Proof. apply _. Qed.

#[global] Instance map_meta_r_persistent t' : Persistent (map_meta_r t').
Proof. apply _. Qed.

#[global] Instance flow_meta_l_persistent t : Persistent (flow_meta_l t).
Proof. apply _. Qed.

#[global] Instance flow_meta_r_persistent t' : Persistent (flow_meta_r t').
Proof. apply _. Qed.

Lemma rel_token_l_split t : rel_token_l t ⊢ map_token_l t ∗ flow_token_l t.
Proof.
rewrite /rel_token_l (term_token_difference _ (↑rel_ns t.@"map")); last solve_ndisj.
iIntros "[$ tok]". iApply (term_token_drop with "tok"). solve_ndisj.
Qed.

Lemma rel_token_r_split t' : rel_token_r t' ⊢ map_token_r t' ∗ flow_token_r t'.
Proof.
rewrite /rel_token_r (term_token_spec_difference _ (↑rel_ns t'.@"map")); last solve_ndisj.
iIntros "[$ tok]". iApply (term_token_spec_drop with "tok"). solve_ndisj.
Qed.

Lemma map_meta_l_set t : map_token_l t ==∗ map_meta_l t.
Proof. exact: term_meta_set. Qed.

Lemma map_meta_r_set t' : map_token_r t' ==∗ map_meta_r t'.
Proof. exact: term_meta_spec_set. Qed.

Lemma flow_meta_l_set t : flow_token_l t ==∗ flow_meta_l t.
Proof. exact: term_meta_set. Qed.

Lemma flow_meta_r_set t' : flow_token_r t' ==∗ flow_meta_r t'.
Proof. exact: term_meta_spec_set. Qed.

Lemma map_token_meta_l t : map_token_l t -∗ map_meta_l t -∗ False.
Proof. exact: term_meta_token. Qed.

Lemma map_token_meta_r t' : map_token_r t' -∗ map_meta_r t' -∗ False.
Proof. exact: term_meta_spec_token. Qed.

Lemma flow_token_meta_l t : flow_token_l t -∗ flow_meta_l t -∗ False.
Proof. exact: term_meta_token. Qed.

Lemma flow_token_meta_r t' : flow_token_r t' -∗ flow_meta_r t' -∗ False.
Proof. exact: term_meta_spec_token. Qed.

Lemma is_nonce_not_TSeal t : is_nonce t → ∀ k t1, t ≠ TSeal k t1.
Proof. by move=> /is_nonceP [a ->]. Qed.

Lemma term_token_rel_token_l t :
  (∀ k t1, t ≠ TSeal k t1) →
  term_token t ⊤ ⊢
  rel_token_l t ∗ term_token t (↑sealN) ∗
  term_token t (⊤ ∖ ↑hypercryptisN).
Proof.
move=> H. have -> : rel_token_l t = term_token t (↑termN).
{ by case: t H => // k t1 /(_ k t1). }
rewrite (term_token_difference t (↑hypercryptisN) ⊤) //.
rewrite (term_token_difference t (↑termN) (↑hypercryptisN));
  last solve_ndisj.
rewrite (term_token_difference t (↑sealN)
           (↑hypercryptisN ∖ ↑termN)); last solve_ndisj.
iIntros "[(term & seal & _) rest]". iFrame.
Qed.

Lemma term_token_rel_token_r t' :
  (∀ k t1, t' ≠ TSeal k t1) →
  term_token_spec t' ⊤ ⊢
  rel_token_r t' ∗ term_token_spec t' (↑sealN) ∗
  term_token_spec t' (⊤ ∖ ↑hypercryptisN).
Proof.
move=> H. have -> : rel_token_r t' = term_token_spec t' (↑termN).
{ by case: t' H => // k t1 /(_ k t1). }
rewrite (term_token_spec_difference t' (↑hypercryptisN) ⊤) //.
rewrite (term_token_spec_difference t' (↑termN)
           (↑hypercryptisN)); last solve_ndisj.
rewrite (term_token_spec_difference t' (↑sealN)
           (↑hypercryptisN ∖ ↑termN)); last solve_ndisj.
iIntros "[(term & seal & _) rest]". iFrame.
Qed.

Lemma never_sealed_under_rel_token kt s kt' s' t t' E E' :
  ↑seal_ns (TKey kt s) t ⊆ E →
  ↑seal_ns (TKey kt' s') t' ⊆ E' →
  never_sealed_under s s' E E' ⊣⊢
  rel_token_l (TSeal (TKey kt s) t) ∗ rel_token_r (TSeal (TKey kt' s') t') ∗
  never_sealed_under s s' (E ∖ ↑seal_ns (TKey kt s) t) (E' ∖ ↑seal_ns (TKey kt' s') t').
Proof.
move=> sub sub'.
rewrite /never_sealed_under /rel_token_l /rel_token_r /=.
rewrite (term_token_difference s _ E) // (term_token_spec_difference s' _ E') //.
iSplit; [iIntros "[[$ ?] [$ ?]]" | iIntros "(? & ? & ? & ?)"]; iFrame.
Qed.

End Owners.

Section Map.

Definition public_rel_map_l_auth pub_l : iProp :=
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) ∗
  [∗ map] t ↦ st ∈ pub_l, match st with
                            | Private _ => own public_rel_map_l (◯ {[ t := ●{#1/2} Some st ]})
                            | _ => emp
                            end.

Definition public_rel_map_r_auth pub_r : iProp :=
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) ∗
  [∗ map] t' ↦ st ∈ pub_r, match st with
                            | Private _ => own public_rel_map_r (◯ {[ t' := ●{#1/2} Some st ]})
                            | _ => emp
                            end.

Definition public_rel_map_inv pub_l pub_r : iProp :=
  public_rel_map_l_auth pub_l ∗
  public_rel_map_r_auth pub_r ∗
  ([∗ set] t ∈ dom pub_l, map_meta_l t) ∗
  ([∗ set] t' ∈ dom pub_r, map_meta_r t').

Definition pending_in_l t t' : iProp :=
  own public_rel_map_l (◯ {[ t := ●{#1/2} Some (Private t') ]}).

Definition pending_in_r t t' : iProp :=
  own public_rel_map_r (◯ {[ t' := ●{#1/2} Some (Private t) ]}).

Definition linked_in_l t t' : iProp :=
  own public_rel_map_l (◯ {[ t := ◯ Some (Private t') ]}).

#[global] Instance linked_in_l_persistent t t' : Persistent (linked_in_l t t').
Proof. apply _. Qed.

Definition linked_in_r t t' : iProp :=
  own public_rel_map_r (◯ {[ t' := ◯ Some (Private t) ]}).

#[global] Instance linked_in_r_persistent t t' : Persistent (linked_in_r t t').
Proof. apply _. Qed.

Definition linked t t' : iProp :=
  linked_in_l t t' ∧ linked_in_r t t'.

#[global] Instance linked_persistent t t' : Persistent (linked t t').
Proof. apply _. Qed.

Definition publicly_linked_in_l t t' : iProp :=
  own public_rel_map_l (◯ {[ t := ◯ Some (Public t') ]}).

#[global] Instance publicly_linked_in_l_persistent t t' : Persistent (publicly_linked_in_l t t').
Proof. apply _. Qed.

Definition publicly_linked_in_r t t' : iProp :=
  own public_rel_map_r (◯ {[ t' := ◯ Some (Public t) ]}).

#[global] Instance publicly_linked_in_r_persistent t t' : Persistent (publicly_linked_in_r t t').
Proof. apply _. Qed.

Definition publicly_linked t t' : iProp :=
  publicly_linked_in_l t t' ∧ publicly_linked_in_r t t'.

#[global] Instance publicly_linked_persistent t t' : Persistent (publicly_linked t t').
Proof. apply _. Qed.

Definition secret_in_l t : iProp :=
  own public_rel_map_l (◯ {[ t := ◯ Some Secret ]}).

#[global] Instance secret_in_l_persistent t : Persistent (secret_in_l t).
Proof. apply _. Qed.

Definition secret_in_r t' : iProp :=
  own public_rel_map_r (◯ {[ t' := ◯ Some Secret ]}).

#[global] Instance secret_in_r_persistent t' : Persistent (secret_in_r t').
Proof. apply _. Qed.

Lemma publicly_linked_in_l_linked_in_l t t' :
  publicly_linked_in_l t t' -∗ linked_in_l t t'.
Proof.
apply bi.entails_wand, own_mono, auth_frag_mono, singleton_included_mono, auth_frag_mono,
  Some_included_mono, Private_included_Public.
Qed.

Lemma publicly_linked_in_r_linked_in_r t t' :
  publicly_linked_in_r t t' -∗ linked_in_r t t'.
Proof.
apply bi.entails_wand, own_mono, auth_frag_mono, singleton_included_mono, auth_frag_mono,
  Some_included_mono, Private_included_Public.
Qed.

Lemma secret_in_l_linked_in_l t t' :
  secret_in_l t -∗ linked_in_l t t'.
Proof.
apply bi.entails_wand, own_mono, auth_frag_mono, singleton_included_mono, auth_frag_mono,
  Some_included_mono, Private_included_Secret.
Qed.

Lemma secret_in_r_linked_in_r t t' :
  secret_in_r t' -∗ linked_in_r t t'.
Proof.
apply bi.entails_wand, own_mono, auth_frag_mono, singleton_included_mono, auth_frag_mono,
  Some_included_mono, Private_included_Secret.
Qed.

Lemma publicly_linked_linked t t' :
  publicly_linked t t' -∗ linked t t'.
Proof.
iIntros "#[H1 H2]". iSplit.
- by iApply publicly_linked_in_l_linked_in_l.
- by iApply publicly_linked_in_r_linked_in_r.
Qed.

Lemma public_rel_map_l_fresh pub_l t :
  ([∗ set] t ∈ dom pub_l, map_meta_l t) -∗
  map_token_l t -∗
  ⌜pub_l !! t = None⌝.
Proof.
iIntros "Hmeta Htt".
destruct (pub_l !! t) eqn:Heq; last done.
iDestruct (big_sepS_elem_of _ _ t with "Hmeta") as "Hmeta_t"; first by apply elem_of_dom.
by iDestruct (map_token_meta_l with "Htt Hmeta_t") as "[]".
Qed.

Lemma public_rel_map_r_fresh pub_r t' :
  ([∗ set] t' ∈ dom pub_r, map_meta_r t') -∗
  map_token_r t' -∗
  ⌜pub_r !! t' = None⌝.
Proof.
iIntros "Hmeta Htts".
destruct (pub_r !! t') eqn:Heq; last done.
iDestruct (big_sepS_elem_of _ _ t' with "Hmeta") as "Hmeta_t"; first by apply elem_of_dom.
by iDestruct (map_token_meta_r with "Htts Hmeta_t") as "[]".
Qed.

Lemma public_rel_map_l_lookup pub_l t t' :
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  pending_in_l t t' -∗
  ⌜pub_l !! t = Some (Private t')⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl _].
apply singleton_included_l in Hincl as (? & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (pub_l !! t) as [st|] eqn:Heq.
- assert (●{#1 / 2} Some (Private t') ≼ ● Some st ⋅ ◯ Some st) as H.
  { by apply Some_included in Hincl as [H_eq | ?]=> //; rewrite H_eq. }
  apply auth_auth_dfrac_included in H as [_ Heq'].
  apply leibniz_equiv in Heq'. by simplify_eq.
- apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl.
Qed.

Lemma public_rel_map_r_lookup pub_r t t' :
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  pending_in_r t t' -∗
  ⌜pub_r !! t' = Some (Private t)⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl _].
apply singleton_included_l in Hincl as (? & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (pub_r !! t') as [st|] eqn:Heq.
- assert (●{#1 / 2} Some (Private t) ≼ ● Some st ⋅ ◯ Some st) as H.
  { by apply Some_included in Hincl as [H_eq | ?]=> //; rewrite H_eq. }
  apply auth_auth_dfrac_included in H as [_ Heq'].
  apply leibniz_equiv in Heq'. by simplify_eq.
- apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl.
Qed.

#[local] Lemma public_rel_map_l_lookup_frag pub_l t st :
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  own public_rel_map_l (◯ {[ t := ◯ Some st ]}) -∗
  ⌜∃ st1, pub_l !! t = Some st1 ∧ ✓ st1 ∧ st ≼ st1⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl Hval].
apply singleton_included_l in Hincl as (? & <- & Hincl).
rewrite lookup_fmap in Hincl.
specialize (Hval t). rewrite lookup_fmap in Hval.
destruct (pub_l !! t) as [st1|] eqn:Heq; last first.
{ apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl. }
exists st1. split; first done.
apply Some_included in Hincl as [Heq' | Hincl];
  first by inversion Heq' as [H _]; inversion H.
apply auth_frag_included in Hincl.
apply auth_both_valid_discrete in Hval as [_ Hval].
split; first by apply Some_valid.
exact: (proj1 (Some_included_total _ _) Hincl).
Qed.

#[local] Lemma public_rel_map_r_lookup_frag pub_r t' st :
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  own public_rel_map_r (◯ {[ t' := ◯ Some st ]}) -∗
  ⌜∃ st1, pub_r !! t' = Some st1 ∧ ✓ st1 ∧ st ≼ st1⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl Hval].
apply singleton_included_l in Hincl as (? & <- & Hincl).
rewrite lookup_fmap in Hincl.
specialize (Hval t'). rewrite lookup_fmap in Hval.
destruct (pub_r !! t') as [st1|] eqn:Heq; last first.
{ apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl. }
exists st1. split; first done.
apply Some_included in Hincl as [Heq' | Hincl];
  first by inversion Heq' as [H _]; inversion H.
apply auth_frag_included in Hincl.
apply auth_both_valid_discrete in Hval as [_ Hval].
split; first by apply Some_valid.
exact: (proj1 (Some_included_total _ _) Hincl).
Qed.

Lemma linked_in_l_lookup pub_l t t' :
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  linked_in_l t t' -∗
  ⌜pub_l !! t = Some (Private t') ∨
   pub_l !! t = Some Secret ∨
   pub_l !! t = Some (Public t')⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_rel_map_l_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by case: (Private_included Hval Hincl) => [->|[->|->]]; eauto.
Qed.

Lemma linked_in_r_lookup pub_r t t' :
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  linked_in_r t t' -∗
  ⌜pub_r !! t' = Some (Private t) ∨
   pub_r !! t' = Some Secret ∨
   pub_r !! t' = Some (Public t)⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_rel_map_r_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by case: (Private_included Hval Hincl) => [->|[->|->]]; eauto.
Qed.

Lemma publicly_linked_in_l_lookup pub_l t t' :
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  publicly_linked_in_l t t' -∗
  ⌜pub_l !! t = Some (Public t')⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_rel_map_l_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by rewrite (Public_included Hval Hincl).
Qed.

Lemma publicly_linked_in_r_lookup pub_r t t' :
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  publicly_linked_in_r t t' -∗
  ⌜pub_r !! t' = Some (Public t)⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_rel_map_r_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by rewrite (Public_included Hval Hincl).
Qed.

Lemma secret_in_l_lookup pub_l t :
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  secret_in_l t -∗
  ⌜pub_l !! t = Some Secret⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_rel_map_l_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by rewrite (Secret_included Hval Hincl).
Qed.

Lemma secret_in_r_lookup pub_r t' :
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  secret_in_r t' -∗
  ⌜pub_r !! t' = Some Secret⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_rel_map_r_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by rewrite (Secret_included Hval Hincl).
Qed.

Lemma publicly_linked_lookup_l pub_l t t' :
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  publicly_linked t t' -∗
  ⌜pub_l !! t = Some (Public t')⌝.
Proof.
iIntros "H1 [H2 _]".
by iApply (publicly_linked_in_l_lookup with "H1 H2").
Qed.

Lemma publicly_linked_lookup_r pub_r t t' :
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  publicly_linked t t' -∗
  ⌜pub_r !! t' = Some (Public t)⌝.
Proof.
iIntros "H1 [_ H2]".
by iApply (publicly_linked_in_r_lookup with "H1 H2").
Qed.

Lemma publicly_linked_in_l_agree t t1 t2 :
  publicly_linked_in_l t t1 -∗
  publicly_linked_in_l t t2 -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H". iPureIntro. move: H.
rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid.
rewrite -auth_frag_op auth_frag_valid -Some_op Some_valid.
exact: Public_Public_valid.
Qed.

Lemma publicly_linked_in_r_agree t' t1 t2 :
  publicly_linked_in_r t1 t' -∗
  publicly_linked_in_r t2 t' -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H". iPureIntro. move: H.
rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid.
rewrite -auth_frag_op auth_frag_valid -Some_op Some_valid.
exact: Public_Public_valid.
Qed.

Lemma linked_in_l_publicly_linked_in_l t t1 t2 :
  linked_in_l t t1 -∗
  publicly_linked_in_l t t2 -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H". iPureIntro. move: H.
rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid.
rewrite -auth_frag_op auth_frag_valid -Some_op Some_valid.
exact: Private_Public_valid.
Qed.

Lemma linked_in_r_publicly_linked_in_r t' t1 t2 :
  linked_in_r t1 t' -∗
  publicly_linked_in_r t2 t' -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H". iPureIntro. move: H.
rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid.
rewrite -auth_frag_op auth_frag_valid -Some_op Some_valid.
exact: Private_Public_valid.
Qed.

Lemma secret_in_l_publicly_linked_in_l t t' :
  secret_in_l t -∗
  publicly_linked_in_l t t' -∗
  False.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H". iPureIntro. move: H.
rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid.
rewrite -auth_frag_op auth_frag_valid -Some_op Some_valid.
exact: Secret_Public_valid.
Qed.

Lemma secret_in_r_publicly_linked_in_r t t' :
  secret_in_r t' -∗
  publicly_linked_in_r t t' -∗
  False.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H". iPureIntro. move: H.
rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid.
rewrite -auth_frag_op auth_frag_valid -Some_op Some_valid.
exact: Secret_Public_valid.
Qed.

Lemma publicly_linked_agree_l t t1 t2 :
  publicly_linked t t1 -∗
  publicly_linked t t2 -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "[H1 _] [H2 _]".
by iApply (publicly_linked_in_l_agree with "H1 H2").
Qed.

Lemma publicly_linked_agree_r t1 t2 t' :
  publicly_linked t1 t' -∗
  publicly_linked t2 t' -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "[_ H1] [_ H2]".
by iApply (publicly_linked_in_r_agree with "H1 H2").
Qed.

End Map.

Section Flow.

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

Definition public_rel_flow_l_auth flow_l : iProp :=
  own public_rel_flow_l (● ((λ ts, ● GSet ts ⋅ ◯ GSet ts) <$> flow_l)) ∗
  [∗ map] t ↦ ts ∈ flow_l,
    own public_rel_flow_l (◯ {[ t := ●{#1/2} (GSet ts) ]}).

Definition public_rel_flow_r_auth flow_r : iProp :=
  own public_rel_flow_r (● ((λ ts, ● GSet ts ⋅ ◯ GSet ts) <$> flow_r)) ∗
  [∗ map] t' ↦ ts ∈ flow_r,
    own public_rel_flow_r (◯ {[ t' := ●{#1/2} (GSet ts) ]}).

Definition public_rel_flow_inv flow_l flow_r : iProp :=
  public_rel_flow_l_auth flow_l ∗
  public_rel_flow_r_auth flow_r ∗
  ([∗ set] t ∈ dom flow_l, flow_meta_l t) ∗
  ([∗ set] t' ∈ dom flow_r, flow_meta_r t').

Definition protects_superterms_l t ts : iProp :=
  own public_rel_flow_l (◯ {[ t := ●{#1/2} (GSet ts) ]}).

Definition protected_by_subterm_l t tsub : iProp :=
  own public_rel_flow_l (◯ {[ tsub := ◯ (GSet {[ t ]}) ]}).

Definition protects_superterms_r t' ts : iProp :=
  own public_rel_flow_r (◯ {[ t' := ●{#1/2} (GSet ts) ]}).

Definition protected_by_subterm_r t' tsub : iProp :=
  own public_rel_flow_r (◯ {[ tsub := ◯ (GSet {[ t' ]}) ]}).

Lemma public_rel_flow_l_fresh flow_l t :
  ([∗ set] t' ∈ dom flow_l, flow_meta_l t') -∗
  flow_token_l t -∗
  ⌜flow_l !! t = None⌝.
Proof.
iIntros "Hmeta Htt".
destruct (flow_l !! t) eqn:Heq; last done.
iDestruct (big_sepS_elem_of _ _ t with "Hmeta") as "Hmeta_t"; first by apply elem_of_dom.
by iDestruct (flow_token_meta_l with "Htt Hmeta_t") as "[]".
Qed.

Lemma public_rel_flow_r_fresh flow_r t' :
  ([∗ set] t' ∈ dom flow_r, flow_meta_r t') -∗
  flow_token_r t' -∗
  ⌜flow_r !! t' = None⌝.
Proof.
iIntros "Hmeta Htts".
destruct (flow_r !! t') eqn:Heq; last done.
iDestruct (big_sepS_elem_of _ _ t' with "Hmeta") as "Hmeta_t"; first by apply elem_of_dom.
by iDestruct (flow_token_meta_r with "Htts Hmeta_t") as "[]".
Qed.

Lemma public_rel_flow_l_lookup flow_l t tsub :
  own public_rel_flow_l (● ((λ ts, ● GSet ts ⋅ ◯ GSet ts) <$> flow_l)) -∗
  protected_by_subterm_l t tsub -∗
  ⌜∃ ts, flow_l !! tsub = Some ts ∧ t ∈ ts⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl _].
apply singleton_included_l in Hincl as (y & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (flow_l !! tsub) as [ts|]; last first.
{ apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl. }
exists ts. split; first done.
apply Some_included in Hincl as [Heq | Hincl];
  first by inversion Heq as [H _]; inversion H.
apply auth_frag_included in Hincl.
apply gset_disj_included in Hincl. set_solver.
Qed.

Lemma public_rel_flow_r_lookup flow_r t' t'sub :
  own public_rel_flow_r (● ((λ ts, ● GSet ts ⋅ ◯ GSet ts) <$> flow_r)) -∗
  protected_by_subterm_r t' t'sub -∗
  ⌜∃ ts, flow_r !! t'sub = Some ts ∧ t' ∈ ts⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl _].
apply singleton_included_l in Hincl as (y & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (flow_r !! t'sub) as [ts|]; last first.
{ apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl. }
exists ts. split; first done.
apply Some_included in Hincl as [Heq | Hincl];
  first by inversion Heq as [H _]; inversion H.
apply auth_frag_included in Hincl.
apply gset_disj_included in Hincl. set_solver.
Qed.

Lemma public_rel_flow_l_lookup_2 flow_l t ts :
  own public_rel_flow_l (● ((λ ts, ● GSet ts ⋅ ◯ GSet ts) <$> flow_l)) -∗
  protects_superterms_l t ts -∗
  ⌜flow_l !! t = Some ts⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl _].
apply singleton_included_l in Hincl as (y & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (flow_l !! t) as [ts'|]; last first.
{ apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl. }
assert (●{#1 / 2} (GSet ts) ≼ ● (GSet ts') ⋅ ◯ (GSet ts')) as H.
{ by apply Some_included in Hincl as [H_eq | ?]=> //; rewrite H_eq. }
apply auth_auth_dfrac_included in H as [_ Heq].
by injection Heq as ->.
Qed.

Lemma public_rel_flow_r_lookup_2 flow_r t' ts :
  own public_rel_flow_r (● ((λ ts, ● GSet ts ⋅ ◯ GSet ts) <$> flow_r)) -∗
  protects_superterms_r t' ts -∗
  ⌜flow_r !! t' = Some ts⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl _].
apply singleton_included_l in Hincl as (y & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (flow_r !! t') as [ts'|]; last first.
{ apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl. }
assert (●{#1 / 2} (GSet ts) ≼ ● (GSet ts') ⋅ ◯ (GSet ts')) as H.
{ by apply Some_included in Hincl as [H_eq | ?]=> //; rewrite H_eq. }
apply auth_auth_dfrac_included in H as [_ Heq].
by injection Heq as ->.
Qed.

Lemma public_rel_flow_l_ne t tsub tsub1 :
  protected_by_subterm_l t tsub -∗
  protected_by_subterm_l t tsub1 -∗
  ⌜tsub ≠ tsub1⌝.
Proof.
iIntros "Hprot Hprot1".
iIntros (->).
iCombine "Hprot Hprot1" gives "%Hvalid". iPureIntro.
rewrite -auth_frag_op singleton_op -auth_frag_op in Hvalid.
rewrite auth_frag_valid singleton_valid auth_frag_valid gset_disj_valid_op in Hvalid.
set_solver.
Qed.

Lemma public_rel_flow_r_ne t' t'sub t'sub1 :
  protected_by_subterm_r t' t'sub -∗
  protected_by_subterm_r t' t'sub1 -∗
  ⌜t'sub ≠ t'sub1⌝.
Proof.
iIntros "Hprot Hprot1".
iIntros (->).
iPoseProof (own_valid_2 with "Hprot Hprot1") as "%Hvalid".
iPureIntro.
rewrite -auth_frag_op singleton_op -auth_frag_op in Hvalid.
rewrite auth_frag_valid singleton_valid auth_frag_valid gset_disj_valid_op in Hvalid.
set_solver.
Qed.

End Flow.

Section Relation.

Definition opaque_l t : iProp :=
  match t with
  | TNonce _ => True
  | THash t1 => secret_in_l t1
  | TSeal k t1 =>
    match k with
    | TKey AEnc s => secret_in_l s ∧ secret_in_l t1
    | TKey SEnc s => secret_in_l s
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
    | TKey AEnc s' => secret_in_r s' ∧ secret_in_r t1'
    | TKey SEnc s' => secret_in_r s'
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
    ⌜kt = kt'⌝ ∧ match kt with AEnc | Verify => linked t1 t1' | _ => False end
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
        | AEnc, AEnc => (R k1 k1' → R t1 t1') ∧ (R t1 t1' ∨ linked t1 t1')
        | SEnc, SEnc => R k1 k1' → R t1 t1'
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

Fixpoint publicly_related t t' : iProp :=
  minted t ∧ minted_spec t' ∧
  (same_shape publicly_related t t' ∨
   (publicly_linked t t' ∧
    (linked_shape publicly_related t t' ∨ (opaque_l t ∧ opaque_r t')))).

#[local] Notation "PUB⟨ a , b ⟩" := (publicly_related a b)
  (at level 0, no associativity, format "PUB⟨ a , b ⟩").

Lemma publicly_related_unfold t t' :
  PUB⟨t, t'⟩ ⊣⊢
  minted t ∧ minted_spec t' ∧
  (same_shape publicly_related t t' ∨
   (publicly_linked t t' ∧
    (linked_shape publicly_related t t' ∨ (opaque_l t ∧ opaque_r t')))).
Proof. by case: t. Qed.

#[global] Instance publicly_related_persistent t t' : Persistent (PUB⟨t, t'⟩).
Proof. elim/term_ind': t t' => /=; rewrite /same_shape /linked_shape; apply _. Qed.

#[global] Instance publicly_related_timeless t t' : Timeless (PUB⟨t, t'⟩).
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

Definition public_rel_Private_l_protected pub_l flow_l : Prop :=
  ∀ t st, pub_l !! t = Some st → not_Public st →
    is_nonce t ∨ (∃ tsub ts1, flow_l !! tsub = Some ts1 ∧ t ∈ ts1).

Definition public_rel_Private_r_protected pub_r flow_r : Prop :=
  ∀ t' st, pub_r !! t' = Some st → not_Public st →
    is_nonce t' ∨ (∃ t'sub ts1, flow_r !! t'sub = Some ts1 ∧ t' ∈ ts1).

Definition public_rel_Private_protected pub_l pub_r flow_l flow_r : Prop :=
  public_rel_Private_l_protected pub_l flow_l ∧
  public_rel_Private_r_protected pub_r flow_r.

Definition public_rel_Public_l_consistent pub_l : iProp :=
  ∀ t t', ⌜pub_l !! t = Some (Public t')⌝ → publicly_related t t'.

Definition public_rel_Public_r_consistent pub_r : iProp :=
  ∀ t t', ⌜pub_r !! t' = Some (Public t)⌝ → publicly_related t t'.

Definition public_rel_Public_consistent pub_l pub_r : iProp :=
  public_rel_Public_l_consistent pub_l ∗ public_rel_Public_r_consistent pub_r.

Definition public_rel_flow_l_consistent pub_l flow_l : Prop :=
  ∀ t ts, flow_l !! t = Some ts → ts ≠ ∅ →
    set_Forall (is_immediate_subterm t) ts ∧
    (is_nonce t ∨ (∃ tsub ts1, flow_l !! tsub = Some ts1 ∧ t ∈ ts1)) ∧
    ((pub_l !! t = None) ∨ (∃ st, pub_l !! t = Some st ∧ not_Public st)).

Definition public_rel_flow_r_consistent pub_r flow_r : Prop :=
  ∀ t' ts, flow_r !! t' = Some ts → ts ≠ ∅ →
    set_Forall (is_immediate_subterm t') ts ∧
    (is_nonce t' ∨ (∃ t'sub ts1, flow_r !! t'sub = Some ts1 ∧ t' ∈ ts1)) ∧
    ((pub_r !! t' = None) ∨ (∃ st, pub_r !! t' = Some st ∧ not_Public st)).

Definition public_rel_flow_consistent pub_l pub_r flow_l flow_r : Prop :=
  public_rel_flow_l_consistent pub_l flow_l ∧
  public_rel_flow_r_consistent pub_r flow_r.

Definition public_rel_inv pub_l pub_r flow_l flow_r : iProp :=
  public_rel_map_inv pub_l pub_r ∗
  public_rel_flow_inv flow_l flow_r ∗
  ⌜public_rel_Private_protected pub_l pub_r flow_l flow_r⌝ ∗
  public_rel_Public_consistent pub_l pub_r ∗
  ⌜public_rel_flow_consistent pub_l pub_r flow_l flow_r⌝.

Definition public_rel_ctx : iProp :=
  inv cryptisN (∃ pub_l pub_r flow_l flow_r, public_rel_inv pub_l pub_r flow_l flow_r).

Definition cryptis_rel_ctx : iProp :=
  term_meta_ctx ∗ term_meta_spec_ctx ∗ public_rel_ctx.

#[global] Instance cryptis_rel_ctx_has_term_meta_ctx : HasTermMetaCtx cryptis_rel_ctx.
Proof. split; last apply _. by iIntros "#[H _]". Qed.

#[global] Instance cryptis_rel_ctx_has_term_meta_spec_ctx : HasTermMetaSpecCtx cryptis_rel_ctx.
Proof. split; last apply _. by iIntros "#[_ [H _]]". Qed.

End Invariant.

End PublicRel.

Notation "PUB⟨ a , b ⟩" := (publicly_related a b)
  (at level 0, no associativity, format "PUB⟨ a , b ⟩").


Lemma public_relGS_alloc `{!relocG Σ} E :
  public_relGpreS Σ →
  ⊢ |={E}=> ∃ (H : public_relGS Σ),
              cryptis_rel_ctx.
Proof.
move=> ?; iStartProof.
iMod term_metaGS_alloc as "[% #?]".
iMod term_meta_specGS_alloc as "[% #?]".
iMod (own_alloc (● (∅ : gmapUR term (authUR (optionUR stateR)))))
  as "[%public_rel_map_l Hmap_l]"; first by apply auth_auth_valid.
iMod (own_alloc (● (∅ : gmapUR term (authUR (optionUR stateR)))))
  as "[%public_rel_map_r Hmap_r]"; first by apply auth_auth_valid.
iMod (own_alloc (● (∅ : gmapUR term (authUR (gset_disjUR term)))))
  as "[%public_rel_flow_l Hflow_l]"; first by apply auth_auth_valid.
iMod (own_alloc (● (∅ : gmapUR term (authUR (gset_disjUR term)))))
  as "[%public_rel_flow_r Hflow_r]"; first by apply auth_auth_valid.
pose (Hpub := Public_relGS _ _ _ _
                public_rel_map_l public_rel_map_r
                public_rel_flow_l public_rel_flow_r).
iExists Hpub.
iMod (inv_alloc cryptisN _
        (∃ pub_l pub_r flow_l flow_r, public_rel_inv pub_l pub_r flow_l flow_r)%I
        with "[Hmap_l Hmap_r Hflow_l Hflow_r]") as "#Hinv"; last by iFrame "#∗".
iModIntro. iExists ∅, ∅, ∅, ∅.
rewrite /public_rel_inv /public_rel_map_inv /public_rel_flow_inv
        /public_rel_map_l_auth /public_rel_map_r_auth
        /public_rel_flow_l_auth /public_rel_flow_r_auth
        !fmap_empty !dom_empty_L !big_sepM_empty !big_sepS_empty.
iFrame. rewrite !left_id.
iSplit; [|iSplit; [iSplit|]].
- iPureIntro. split; move=> t ts; by rewrite lookup_empty => ?.
- iIntros (t t') "%Hcontra". by rewrite lookup_empty in Hcontra.
- iIntros (t t') "%Hcontra". by rewrite lookup_empty in Hcontra.
- iPureIntro. split; move=> t ts; by rewrite lookup_empty => ?.
Qed.

Section RelProperties.

Context `{!relocG Σ, !public_relGS Σ}.

Abbreviation iProp := (iProp Σ).
Abbreviation iPropO := (iPropO Σ).

Implicit Types t : term.
Implicit Types st : state.
Implicit Types pub_l pub_r : gmap term state.
Implicit Types flow_l flow_r : gmap term (gset term).
Implicit Types P : term -> term -> iProp.

Section Constructors.

Lemma publicly_related_minted t t' :
  PUB⟨t, t'⟩ ⊢ minted t ∗ minted_spec t'.
Proof. rewrite publicly_related_unfold. iIntros "(#? & #? & _)". by iFrame "#". Qed.

Lemma publicly_related_cases t t' :
  PUB⟨t, t'⟩ -∗
  same_shape publicly_related t t' ∨
  (publicly_linked t t' ∧
   (linked_shape publicly_related t t' ∨ (opaque_l t ∧ opaque_r t'))).
Proof. rewrite publicly_related_unfold. by iIntros "(_ & _ & ?)". Qed.

Lemma publicly_related_opaque t t' :
  minted t -∗ minted_spec t' -∗ publicly_linked t t' -∗
  opaque_l t -∗ opaque_r t' -∗ PUB⟨t, t'⟩.
Proof.
iIntros "#? #? #? #? #?". rewrite publicly_related_unfold.
do 2 (iSplit; first done). iRight. iSplit; first done. iRight. by iSplit.
Qed.

Lemma publicly_related_TInt n n' :
  PUB⟨TInt n, TInt n'⟩ ⊣⊢ ⌜n = n'⌝.
Proof.
rewrite /= minted_TInt minted_spec_TInt. iSplit.
- by iIntros "(_ & _ & [?|(_ & [[]|[[] _]])])".
- iIntros "->". do 2 (iSplit; first done). by iLeft.
Qed.

Lemma publicly_related_TInt_term n (t' : term) :
  PUB⟨TInt n, t'⟩ -∗ ⌜t' = TInt n⌝.
Proof.
case: t' => /= *; iIntros "(_ & _ & [H|(_ & [H|[H _]])])";
  try (by iDestruct "H" as "[]").
by iDestruct "H" as %->.
Qed.

Lemma publicly_related_term_TInt (t : term) n :
  PUB⟨t, TInt n⟩ -∗ ⌜t = TInt n⌝.
Proof.
case: t => /= *; iIntros "(_ & _ & [H|(_ & [H|[_ H]])])";
  try (by iDestruct "H" as "[]").
by iDestruct "H" as %->.
Qed.

Lemma publicly_related_TPair t1 t2 t1' t2' :
  PUB⟨TPair t1 t2, TPair t1' t2'⟩ ⊣⊢
  PUB⟨t1, t1'⟩ ∧ PUB⟨t2, t2'⟩.
Proof.
rewrite /= minted_TPair minted_spec_TPair. iSplit.
- by iIntros "(_ & _ & [?|(_ & [[]|[[] _]])])".
- iIntros "#[H1 H2]".
  iPoseProof (publicly_related_minted with "H1") as "[? ?]".
  iPoseProof (publicly_related_minted with "H2") as "[? ?]".
  iSplit; first by iSplit. iSplit; first by iSplit. iLeft. by iSplit.
Qed.

Lemma publicly_related_TPair_term t1 t2 (t' : term) :
  PUB⟨TPair t1 t2, t'⟩ -∗
  ∃ t1' t2', ⌜t' = TPair t1' t2'⌝.
Proof.
case: t' => /= *; iIntros "(_ & _ & [H|(_ & [H|[H _]])])";
  try (by iDestruct "H" as "[]").
by iExists _, _.
Qed.

Lemma publicly_related_term_TPair (t : term) t1' t2' :
  PUB⟨t, TPair t1' t2'⟩ -∗
  ∃ t1 t2, ⌜t = TPair t1 t2⌝.
Proof.
case: t => /= *; iIntros "(_ & _ & [H|(_ & [H|[_ H]])])";
  try (by iDestruct "H" as "[]").
by iExists _, _.
Qed.

Lemma publicly_related_TNonce a a' :
  PUB⟨TNonce a, TNonce a'⟩ ⊣⊢
  minted (TNonce a) ∧ minted_spec (TNonce a') ∧
  publicly_linked (TNonce a) (TNonce a').
Proof.
rewrite /=. iSplit.
- iIntros "#(? & ? & [[]|[? _]])". by do 2 (iSplit; first done).
- iIntros "#(? & ? & ?)". do 2 (iSplit; first done).
  iRight. iSplit; first done. iRight. by iSplit.
Qed.

Lemma publicly_related_TNonce_term a (t' : term) :
  PUB⟨TNonce a, t'⟩ -∗ publicly_linked (TNonce a) t'.
Proof. rewrite /=. by iIntros "(_ & _ & [[]|[? _]])". Qed.

Lemma publicly_related_term_TNonce (t : term) a' :
  PUB⟨t, TNonce a'⟩ -∗ publicly_linked t (TNonce a').
Proof. case: t => /= *; by iIntros "(_ & _ & [[]|[? _]])". Qed.

Lemma publicly_related_nonce t t' :
  is_nonce t → is_nonce t' →
  PUB⟨t, t'⟩ ⊣⊢ minted t ∧ minted_spec t' ∧ publicly_linked t t'.
Proof. move=> /is_nonceP [a ->] /is_nonceP [a' ->]. exact: publicly_related_TNonce. Qed.

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
  | AEnc | Verify =>
    PUB⟨t, t'⟩ ∨
    (minted t ∧ minted_spec t' ∧
     publicly_linked (TKey kt t) (TKey kt' t') ∧ linked t t')
  | _ => PUB⟨t, t'⟩
  end.
Proof.
rewrite /= minted_TKey minted_spec_TKey. iSplit.
- iIntros "#(? & ? & [[-> H]|(? & [[-> H]|[[] _]])])"; iSplit; try done;
    case: kt' => /=; try done; try (by iLeft); try (by iDestruct "H" as "[]");
    iRight; by do 3 (iSplit; first done).
- iIntros "#(-> & H)".
  case: kt' => /=.
  1,4: iDestruct "H" as "[H|(? & ? & ? & ?)]";
       [ iPoseProof (publicly_related_minted with "H") as "[? ?]";
         do 2 (iSplit; first done); iLeft; by iSplit
       | do 2 (iSplit; first done); iRight; iSplit; first done; iLeft; by iSplit ].
  all: iPoseProof (publicly_related_minted with "H") as "[? ?]";
       do 2 (iSplit; first done); iLeft; by iSplit.
Qed.

Lemma publicly_related_TKey_term kt t (t' : term) :
  PUB⟨TKey kt t, t'⟩ -∗ ∃ t1', ⌜t' = TKey kt t1'⌝.
Proof.
case: t' => /= *; iIntros "(_ & _ & [H|(_ & [H|[H _]])])";
  try (by iDestruct "H" as "[]").
all: iDestruct "H" as "[-> _]"; by iExists _.
Qed.

Lemma publicly_related_term_TKey (t : term) kt' t' :
  PUB⟨t, TKey kt' t'⟩ -∗ ∃ t1, ⌜t = TKey kt' t1⌝.
Proof.
case: t => /= *; iIntros "(_ & _ & [H|(_ & [H|[_ H]])])";
  try (by iDestruct "H" as "[]").
all: iDestruct "H" as "[-> _]"; by iExists _.
Qed.

Lemma publicly_related_pkey t t' :
  PUB⟨t, t'⟩ -∗ PUB⟨Spec.pkey t, Spec.pkey t'⟩.
Proof.
iIntros "#H".
case ek: (Spec.to_key t) => [[kt s]|]; last first.
{ case ek': (Spec.to_key t') => [[kt' s']|].
  { have -> : t' = TKey kt' s' by case: t' ek' => // ?? [-> ->].
    iDestruct (publicly_related_term_TKey with "H") as %[s0 ->].
    by rewrite /= in ek. }
  have -> : Spec.pkey t = t by case: t ek => //= - [].
  have -> : Spec.pkey t' = t' by case: t' ek' => //= - [].
  done. }
have {ek} -> : t = TKey kt s by case: t ek => // ?? [-> ->].
iDestruct (publicly_related_TKey_term with "H") as %[s' ->].
rewrite publicly_related_TKey. iDestruct "H" as "[_ H]".
case: kt.
- by rewrite -[Spec.pkey (TKey AEnc s)]/(TKey AEnc s)
             -[Spec.pkey (TKey AEnc s')]/(TKey AEnc s')
             publicly_related_TKey; iSplit.
- rewrite -[Spec.pkey (TKey ADec s)]/(TKey AEnc s)
          -[Spec.pkey (TKey ADec s')]/(TKey AEnc s')
          publicly_related_TKey. iSplit; first done. by iLeft.
- rewrite -[Spec.pkey (TKey Sign s)]/(TKey Verify s)
          -[Spec.pkey (TKey Sign s')]/(TKey Verify s')
          publicly_related_TKey. iSplit; first done. by iLeft.
- by rewrite -[Spec.pkey (TKey Verify s)]/(TKey Verify s)
             -[Spec.pkey (TKey Verify s')]/(TKey Verify s')
             publicly_related_TKey; iSplit.
- by rewrite -[Spec.pkey (TKey SEnc s)]/(TKey SEnc s)
             -[Spec.pkey (TKey SEnc s')]/(TKey SEnc s')
             publicly_related_TKey; iSplit.
Qed.

Lemma publicly_related_has_key_type kt t t' :
  PUB⟨t, t'⟩ ⊢ ⌜Spec.has_key_type kt t = Spec.has_key_type kt t'⌝.
Proof.
iIntros "#H". rewrite /Spec.has_key_type.
case: (Spec.is_keyP t) => [kt0 s ->|Ht].
- by iDestruct (publicly_related_TKey_term with "H") as %[s' ->].
- case: (Spec.is_keyP t') => [kt1 s' ->|] //.
  iDestruct (publicly_related_term_TKey with "H") as %[s ->].
  by case: (Ht kt1 s).
Qed.

Lemma publicly_related_THash t t' :
  PUB⟨THash t, THash t'⟩ ⊣⊢
  PUB⟨t, t'⟩ ∨
  (minted t ∧ minted_spec t' ∧
   publicly_linked (THash t) (THash t') ∧
   (linked t t' ∨ (secret_in_l t ∧ secret_in_r t'))).
Proof.
rewrite /= minted_THash minted_spec_THash. iSplit.
- iIntros "#(? & ? & [?|(? & ?)])"; [by iLeft | iRight; by do 3 (iSplit; first done)].
- iIntros "#[H|(? & ? & ? & ?)]";
    last by (do 2 (iSplit; first done); iRight; iSplit).
  iPoseProof (publicly_related_minted with "H") as "[? ?]".
  do 2 (iSplit; first done). by iLeft.
Qed.

Lemma publicly_related_THash_term t (t' : term) :
  PUB⟨THash t, t'⟩ -∗
  (∃ t1', ⌜t' = THash t1'⌝) ∨
  (publicly_linked (THash t) t' ∧ secret_in_l t ∧ opaque_r t').
Proof.
case: t' => /= *; iIntros "(_ & _ & [H|(? & [H|[? ?]])])";
  try (by iDestruct "H" as "[]"); try (by iRight; iFrame).
all: iLeft; by iExists _.
Qed.

Lemma publicly_related_term_THash (t : term) t' :
  PUB⟨t, THash t'⟩ -∗
  (∃ t1, ⌜t = THash t1⌝) ∨
  (publicly_linked t (THash t') ∧ opaque_l t ∧ secret_in_r t').
Proof.
case: t => /= *; iIntros "(_ & _ & [H|(? & [H|[? ?]])])";
  try (by iDestruct "H" as "[]"); try (by iRight; iFrame).
all: iLeft; by iExists _.
Qed.

Lemma publicly_related_Tag N N' : PUB⟨Tag N, Tag N'⟩ ⊣⊢ ⌜N = N'⌝.
Proof.
rewrite [Tag]unlock publicly_related_TInt. iSplit.
- iIntros "%H". injection H as H. by apply encode_inj in H.
- iIntros "->". done.
Qed.

Lemma publicly_related_Tag_term N (t' : term) :
  PUB⟨Tag N, t'⟩ -∗
  ⌜t' = Tag N⌝.
Proof.
iIntros "#H".
rewrite [Tag]unlock.
by iPoseProof (publicly_related_TInt_term with "H") as "->".
Qed.

Lemma publicly_related_term_Tag (t : term) N' :
  PUB⟨t, Tag N'⟩ -∗
  ⌜t = Tag N'⌝.
Proof.
iIntros "#H".
rewrite [Tag]unlock.
by iPoseProof (publicly_related_term_TInt with "H") as "->".
Qed.

Lemma publicly_related_tag N N' t t' :
  PUB⟨Spec.tag (Tag N) t, Spec.tag (Tag N') t'⟩ ⊣⊢
  ⌜N = N'⌝ ∧ PUB⟨t, t'⟩.
Proof.
by rewrite [Spec.tag]unlock publicly_related_TPair publicly_related_Tag.
Qed.

Lemma publicly_related_tag_term N t (t' : term) :
  PUB⟨Spec.tag (Tag N) t, t'⟩ -∗
  ∃ t1', ⌜t' = Spec.tag (Tag N) t1'⌝.
Proof.
iIntros "#H".
rewrite [Spec.tag]unlock.
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
rewrite [Spec.tag]unlock.
iPoseProof (publicly_related_term_TPair with "H") as "(%t1 & %t2 & ->)".
rewrite publicly_related_TPair.
iDestruct "H" as "[H1 H2]".
iPoseProof (publicly_related_term_Tag with "H1") as "->".
by iExists t2.
Qed.

Lemma publicly_related_untag N (u u' : term) :
  PUB⟨u, u'⟩ ⊢
  match Spec.untag (Tag N) u, Spec.untag (Tag N) u' with
  | Some m, Some m' => PUB⟨m, m'⟩
  | None, None => True
  | _, _ => False
  end.
Proof.
iIntros "#Hu".
case: (Spec.untagP (Tag N) u) => [m ->|Hu].
- iDestruct (publicly_related_tag_term with "Hu") as %[m' ->].
  rewrite !Spec.tagK publicly_related_tag. by iDestruct "Hu" as "[_ ?]".
- case: (Spec.untagP (Tag N) u') => [m' ->|] //.
  iDestruct (publicly_related_term_tag with "Hu") as %[m ->].
  by case: (Hu m).
Qed.

Lemma publicly_related_to_list (m m' : term) :
  PUB⟨m, m'⟩ ⊢
  match Spec.to_list m, Spec.to_list m' with
  | Some ts, Some ts' => [∗ list] t; t' ∈ ts; ts', PUB⟨t, t'⟩
  | None, None => True
  | _, _ => False
  end.
Proof.
elim/term_ind': m m' => [n|a _ b IH|a|kt k _|k _ t _|t _|pt wf nf] m'; iIntros "#Hm".
2: { iDestruct (publicly_related_TPair_term with "Hm") as %(a' & b' & ->).
     rewrite publicly_related_TPair. iDestruct "Hm" as "[Ha Hb]".
     iPoseProof (IH with "Hb") as "Hb'" => /=.
     destruct (Spec.to_list b), (Spec.to_list b'); by iFrame "#". }
1: { iDestruct (publicly_related_TInt_term with "Hm") as %->.
     case: n => [|p|p] /=; [iEmpIntro | by iPureIntro..]. }
all: case e: (Spec.to_list m') => [ts'|] //; move/Spec.to_listK: e => ->.
all: case: ts' => [|t' ts']; rewrite [Spec.of_list]unlock /=.
all: by iDestruct "Hm" as "(_ & _ & [[]|(_ & [[]|[_ []]])])".
Qed.

Lemma publicly_related_to_list_length n m m' :
  PUB⟨m, m'⟩ ⊢
  ⌜Spec.to_list m = None ∧ Spec.to_list m' = None⌝ ∨
  ∃ ts ts', ⌜Spec.to_list m = Some ts ∧ Spec.to_list m' = Some ts'⌝ ∗
    (⌜length ts ≠ n ∧ length ts' ≠ n⌝ ∨
     ⌜length ts = n⌝ ∗ [∗ list] t; t' ∈ ts; ts', PUB⟨t, t'⟩).
Proof.
iIntros "#Hm". iPoseProof (publicly_related_to_list with "Hm") as "Hl".
destruct (Spec.to_list m) as [ts|], (Spec.to_list m') as [ts'|]; try done.
- iDestruct (big_sepL2_length with "Hl") as %Hlen.
  iRight. iExists ts, ts'. iSplit; first done.
  case: (decide (length ts = n)) => Hn.
  + iRight. by iSplit.
  + iLeft. iPureIntro. lia.
- by iLeft.
Qed.

Lemma publicly_related_of_list (ts ts' : list term) :
  ([∗ list] t; t' ∈ ts; ts', PUB⟨t, t'⟩) ⊢ PUB⟨Spec.of_list ts, Spec.of_list ts'⟩.
Proof.
rewrite [Spec.of_list]unlock.
elim: ts ts' => [|t ts IH] [|t' ts']; iIntros "H"; cbn [foldr];
  try by iDestruct (big_sepL2_length with "H") as %?.
- by rewrite publicly_related_TInt.
- rewrite big_sepL2_cons publicly_related_TPair. iDestruct "H" as "[Ht H]".
  iSplit; first done. by iApply IH.
Qed.

Lemma publicly_related_adec_key' (k k' : aenc_key) :
  PUB⟨k, k'⟩ ⊣⊢
  PUB⟨seed_of_aenc_key k, seed_of_aenc_key k'⟩.
Proof.
rewrite [term_of_aenc_key]unlock /= minted_TKey minted_spec_TKey. iSplit.
- by iIntros "(_ & _ & [[_ ?]|(_ & [[_ []]|[[] _]])])".
- iIntros "#H". iPoseProof (publicly_related_minted with "H") as "[? ?]".
  do 2 (iSplit; first done). iLeft. by iSplit.
Qed.

Lemma publicly_related_aenc_key_term (k : aenc_key) (t' : term) :
  PUB⟨k, t'⟩ -∗
  ∃ (k' : aenc_key), ⌜t' = k'⌝.
Proof.
rewrite [term_of_aenc_key]unlock /=.
case: t' => /= *; iIntros "(_ & _ & [H|(_ & [H|[H _]])])";
  try (by iDestruct "H" as "[]").
all: iDestruct "H" as "[<- _]"; by iExists (AEncKey _).
Qed.

Lemma publicly_related_term_aenc_key (t : term) (k' : aenc_key) :
  PUB⟨t, k'⟩ -∗
  ∃ (k : aenc_key), ⌜t = k⌝.
Proof.
rewrite [term_of_aenc_key]unlock /=.
case: t => /= *; iIntros "(_ & _ & [H|(_ & [H|[_ H]])])";
  try (by iDestruct "H" as "[]").
all: iDestruct "H" as "[-> _]"; by iExists (AEncKey _).
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
- iIntros "#(? & ? & [[_ ?]|(? & [[_ ?]|[[] _]])])";
    [by iLeft | iRight; by do 3 (iSplit; first done)].
- iIntros "#[H|(? & ? & ? & ?)]".
  + iPoseProof (publicly_related_minted with "H") as "[? ?]".
    do 2 (iSplit; first done). iLeft. by iSplit.
  + do 2 (iSplit; first done). iRight. iSplit; first done. iLeft. by iSplit.
Qed.

Lemma publicly_related_aenc_key_pkey_term (sk : aenc_key) (t' : term) :
  PUB⟨Spec.pkey sk, t'⟩ -∗
  ∃ (sk' : aenc_key), ⌜t' = Spec.pkey sk'⌝.
Proof.
rewrite /Spec.pkey [term_of_aenc_key]unlock /=.
case: t' => /= *; iIntros "(_ & _ & [H|(_ & [H|[H _]])])";
  try (by iDestruct "H" as "[]").
all: iDestruct "H" as "[<- _]"; by iExists (AEncKey _).
Qed.

Lemma publicly_related_term_aenc_key_pkey (t : term) (sk' : aenc_key) :
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

Lemma publicly_related_TSeal k k' t t' :
  PUB⟨TSeal k t, TSeal k' t'⟩ ⊣⊢
  (PUB⟨k, k'⟩ ∧ PUB⟨t, t'⟩) ∨
  (minted (TSeal k t) ∧ minted_spec (TSeal k' t') ∧
   publicly_linked (TSeal k t) (TSeal k' t') ∧
   ((linked k k' ∧
     □ match k, k' with
       | TKey kt k1, TKey kt' k1' =>
         match kt, kt' with
         | Sign, Sign => PUB⟨TKey Verify k1, TKey Verify k1'⟩ ∧ PUB⟨t, t'⟩
         | AEnc, AEnc => (PUB⟨k1, k1'⟩ → PUB⟨t, t'⟩) ∧ (PUB⟨t, t'⟩ ∨ linked t t')
         | SEnc, SEnc => PUB⟨k1, k1'⟩ → PUB⟨t, t'⟩
         | _, _ => False
         end
       | _, _ => False
       end) ∨
    (opaque_l (TSeal k t) ∧ opaque_r (TSeal k' t')))).
Proof.
rewrite publicly_related_unfold /same_shape /linked_shape. cbv beta iota.
iSplit.
- iIntros "#(mk & mk' & [?|(? & [[? #Hbox]|?])])"; first by iLeft.
  + iRight. do 3 (iSplit; first done). iLeft. iSplit; first done. iModIntro.
    case: k => [n|a b|a|kt k1|k b|s|pt wf nf]; try done.
    case: k' => [n'|a' b'|a'|kt' k1'|k'' b'|s'|pt' wf' nf']; try done.
    case: kt; case: kt'; try done.
    iDestruct "Hbox" as "(Hv & Ht)". iFrame "Ht".
    rewrite minted_TSeal minted_spec_TSeal !minted_TKey !minted_spec_TKey.
    iDestruct "mk" as "[mk1 _]". iDestruct "mk'" as "[mk1' _]".
    iApply publicly_related_TKey. iSplit; first done.
    iDestruct "Hv" as "[?|[? ?]]"; [by iLeft | iRight; by do 3 (iSplit; first done)].
  + iRight. do 3 (iSplit; first done). by iRight.
- iIntros "#[[H1 H2]|(mk & mk' & Hl & [[? #Hbox]|Ho])]".
  + iPoseProof (publicly_related_minted with "H1") as "[? ?]".
    iPoseProof (publicly_related_minted with "H2") as "[? ?]".
    rewrite minted_TSeal minted_spec_TSeal.
    iSplit; first by iSplit. iSplit; first by iSplit. iLeft. by iSplit.
  + do 2 (iSplit; first done). iRight. iSplit; first done. iLeft.
    iSplit; first done. iModIntro.
    case: k => [n|a b|a|kt k1|k b|s|pt wf nf]; try done.
    case: k' => [n'|a' b'|a'|kt' k1'|k'' b'|s'|pt' wf' nf']; try done.
    case: kt; case: kt'; try done.
    iDestruct "Hbox" as "(Hv & Ht)". iFrame "Ht".
    iDestruct (publicly_related_TKey with "Hv") as "[_ [?|(_ & _ & ? & ?)]]";
      [by iLeft | iRight; by iSplit].
  + do 2 (iSplit; first done). iRight. iSplit; first done. by iRight.
Qed.

Lemma publicly_related_TSeal_term k t (t' : term) :
  PUB⟨TSeal k t, t'⟩ -∗
  (∃ k' t1', ⌜t' = TSeal k' t1'⌝) ∨
  (publicly_linked (TSeal k t) t' ∧ opaque_l (TSeal k t) ∧ opaque_r t').
Proof.
case: t' => /= *; iIntros "(_ & _ & [H|(? & [H|[? ?]])])";
  try (by iDestruct "H" as "[]"); try (by iRight; iFrame).
all: iLeft; by iExists _, _.
Qed.

Lemma publicly_related_term_TSeal (t : term) k' t' :
  PUB⟨t, TSeal k' t'⟩ -∗
  (∃ k t1, ⌜t = TSeal k t1⌝) ∨
  (publicly_linked t (TSeal k' t') ∧ opaque_l t ∧ opaque_r (TSeal k' t')).
Proof.
case: t => /= *; iIntros "(_ & _ & [H|(? & [H|[? ?]])])";
  try (by iDestruct "H" as "[]"); try (by iRight; iFrame).
all: iLeft; by iExists _, _.
Qed.

Lemma publicly_related_enc (k k' : term) N t t' :
  PUB⟨k, k'⟩ -∗ PUB⟨t, t'⟩ -∗
  PUB⟨Spec.enc k (Tag N) t, Spec.enc k' (Tag N) t'⟩.
Proof.
iIntros "#Hk #Ht". rewrite /Spec.enc publicly_related_TSeal. iLeft.
iSplit; first done. rewrite publicly_related_tag. by iSplit.
Qed.

End Ciphertexts.

Section Protection.

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
  case: (public_rel_protected_inv_l HPriv Hcons Hprot) => HnotPub Hsub;
  iDestruct (publicly_related_cases with "Hpub") as "[Hs|[Hl _]]";
  try (iDestruct (publicly_linked_lookup_l with "Hauth Hl") as %Hlookup;
       by case: (HnotPub _ Hlookup));
  case: t' => /= *; try (by iDestruct "Hs" as "[]");
  case: Hsub => [[]|[tsub [Hsub Hprot']]]; try (by inversion Hsub).
- iDestruct "Hs" as "[Ha Hb]". inversion Hsub; subst.
  + iApply (IHa Hprot' with "Hauth Ha").
  + iApply (IHb Hprot' with "Hauth Hb").
- iDestruct "Hs" as "[_ Hs]". inversion Hsub; subst.
  iApply (IH Hprot' with "Hauth Hs").
- iDestruct "Hs" as "[Hk Hb]". inversion Hsub; subst.
  + iApply (IHk Hprot' with "Hauth Hk").
  + iApply (IHb Hprot' with "Hauth Hb").
- inversion Hsub; subst. iApply (IH Hprot' with "Hauth Hs").
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
  case: (public_rel_protected_inv_r HPriv Hcons Hprot) => HnotPub Hsub;
  iDestruct (publicly_related_cases with "Hpub") as "[Hs|[Hl _]]";
  try (iDestruct (publicly_linked_lookup_r with "Hauth Hl") as %Hlookup;
       by case: (HnotPub _ Hlookup));
  case: t => /= *; try (by iDestruct "Hs" as "[]");
  case: Hsub => [[]|[tsub [Hsub Hprot']]]; try (by inversion Hsub).
- iDestruct "Hs" as "[Ha Hb]". inversion Hsub; subst.
  + iApply (IHa Hprot' with "Hauth Ha").
  + iApply (IHb Hprot' with "Hauth Hb").
- iDestruct "Hs" as "[_ Hs]". inversion Hsub; subst.
  iApply (IH Hprot' with "Hauth Hs").
- iDestruct "Hs" as "[Hk Hb]". inversion Hsub; subst.
  + iApply (IHk Hprot' with "Hauth Hk").
  + iApply (IHb Hprot' with "Hauth Hb").
- inversion Hsub; subst. iApply (IH Hprot' with "Hauth Hs").
Qed.

#[local] Lemma secret_in_l_publicly_related pub_l flow_l {t t'} :
  public_rel_Private_l_protected pub_l flow_l →
  public_rel_flow_l_consistent pub_l flow_l →
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  secret_in_l t -∗ PUB⟨t, t'⟩ -∗ False.
Proof.
move=> HPriv Hcons. iIntros "Hmap Hs Ht".
iDestruct (secret_in_l_lookup with "Hmap Hs") as %Hsec.
by iApply (publicly_related_protected_l HPriv Hcons
             (or_introl (ex_intro _ _ (conj Hsec I))) with "Hmap Ht").
Qed.

#[local] Lemma secret_in_r_publicly_related pub_r flow_r {t t'} :
  public_rel_Private_r_protected pub_r flow_r →
  public_rel_flow_r_consistent pub_r flow_r →
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  secret_in_r t' -∗ PUB⟨t, t'⟩ -∗ False.
Proof.
move=> HPriv Hcons. iIntros "Hmap Hs Ht".
iDestruct (secret_in_r_lookup with "Hmap Hs") as %Hsec.
by iApply (publicly_related_protected_r HPriv Hcons
             (or_introl (ex_intro _ _ (conj Hsec I))) with "Hmap Ht").
Qed.

Lemma secret_in_l_publicly_related_fupd E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗ secret_in_l t -∗ PUB⟨t, t'⟩ ={E}=∗ False.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Hs #Ht".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (([Hmap_l _] & _ & _ & _) & _ & [%HPriv_l _] & _ &
                   [%Hflow_l_cons _]))".
by iDestruct (secret_in_l_publicly_related HPriv_l Hflow_l_cons
                with "Hmap_l Hs Ht") as "[]".
Qed.

Lemma secret_in_r_publicly_related_fupd E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗ secret_in_r t' -∗ PUB⟨t, t'⟩ ={E}=∗ False.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Hs #Ht".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ((_ & [Hmap_r _] & _ & _) & _ & [_ %HPriv_r] & _ &
                   [_ %Hflow_r_cons]))".
by iDestruct (secret_in_r_publicly_related HPriv_r Hflow_r_cons
                with "Hmap_r Hs Ht") as "[]".
Qed.

#[local] Lemma publicly_related_linked_in_l pub_l flow_l :
  public_rel_Private_l_protected pub_l flow_l →
  public_rel_flow_l_consistent pub_l flow_l →
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  public_rel_Public_l_consistent pub_l -∗
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

#[local] Lemma publicly_related_linked_in_r pub_r flow_r :
  public_rel_Private_r_protected pub_r flow_r →
  public_rel_flow_r_consistent pub_r flow_r →
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  public_rel_Public_r_consistent pub_r -∗
  ∀ t1 t2 t', PUB⟨t1, t'⟩ -∗ linked_in_r t2 t' -∗ PUB⟨t2, t'⟩.
Proof.
move=> HPriv Hcons. iIntros "Hauth Hrel" (t1 t2 t') "#H1 #H2".
iDestruct (linked_in_r_lookup with "Hauth H2") as %[Hpriv|[Hpriv|Hpub]].
- by iPoseProof (publicly_related_protected_r HPriv Hcons (or_introl (ex_intro _ _ (conj Hpriv I)))
                  with "Hauth H1") as "[]".
- by iPoseProof (publicly_related_protected_r HPriv Hcons (or_introl (ex_intro _ _ (conj Hpriv I)))
                  with "Hauth H1") as "[]".
- by iApply ("Hrel" with "[//]").
Qed.

#[local] Lemma publicly_related_linked_key_l pub_l flow_l {kt s k_t'} :
  public_rel_Private_l_protected pub_l flow_l →
  public_rel_flow_l_consistent pub_l flow_l →
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  public_rel_Public_l_consistent pub_l -∗
  linked_in_l (TKey kt s) k_t' -∗
  PUB⟨TKey kt s, k_t'⟩ ∨ (∀ s', PUB⟨s, s'⟩ -∗ False).
Proof.
move=> HPriv_l Hflow_l_cons. iIntros "Hmap_l Hpub_consistent #Hlink".
iDestruct (linked_in_l_lookup with "Hmap_l Hlink") as %Hlookup.
have Hcase :
    (∃ st, pub_l !! TKey kt s = Some st ∧ not_Public st) ∨
    pub_l !! TKey kt s = Some (Public k_t').
{ case: Hlookup => [H|[H|H]]; [left|left|by right]; eexists; (split; [exact H|exact I]). }
case: Hcase => [Hprot|Hpub].
- iRight. iIntros (s') "#Hs".
  case: (public_rel_protected_inv_l HPriv_l Hflow_l_cons (or_introl Hprot))
    => _ [//|[tsub [Hsub Hprot']]].
  inversion Hsub; subst.
  by iApply (publicly_related_protected_l HPriv_l Hflow_l_cons Hprot'
               with "Hmap_l Hs").
- iLeft. by iApply "Hpub_consistent".
Qed.

#[local] Lemma publicly_related_linked_key_r pub_r flow_r {k_t kt' s'} :
  public_rel_Private_r_protected pub_r flow_r →
  public_rel_flow_r_consistent pub_r flow_r →
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  public_rel_Public_r_consistent pub_r -∗
  linked_in_r k_t (TKey kt' s') -∗
  PUB⟨k_t, TKey kt' s'⟩ ∨ (∀ s, PUB⟨s, s'⟩ -∗ False).
Proof.
move=> HPriv_r Hflow_r_cons. iIntros "Hmap_r Hpub_consistent #Hlink".
iDestruct (linked_in_r_lookup with "Hmap_r Hlink") as %Hlookup.
have Hcase :
    (∃ st, pub_r !! TKey kt' s' = Some st ∧ not_Public st) ∨
    pub_r !! TKey kt' s' = Some (Public k_t).
{ case: Hlookup => [H|[H|H]]; [left|left|by right]; eexists; (split; [exact H|exact I]). }
case: Hcase => [Hprot|Hpub].
- iRight. iIntros (s) "#Hs".
  case: (public_rel_protected_inv_r HPriv_r Hflow_r_cons (or_introl Hprot))
    => _ [//|[t'sub [Hsub Hprot']]].
  inversion Hsub; subst.
  by iApply (publicly_related_protected_r HPriv_r Hflow_r_cons Hprot'
               with "Hmap_r Hs").
- iLeft. by iApply ("Hpub_consistent" with "[//]").
Qed.

#[local] Lemma opaque_l_same_shape pub_l flow_l {t t'} :
  public_rel_Private_l_protected pub_l flow_l →
  public_rel_flow_l_consistent pub_l flow_l →
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  opaque_l t -∗ same_shape publicly_related t t' -∗ False.
Proof.
move=> HPriv Hcons.
case: t => [n|a b|a|kt s|k b|s|pt wf nf]; case: t' => /= *;
  iIntros "Hmap #Ho #Hs"; try (by iDestruct "Ho" as "[]"); try (by iDestruct "Hs" as "[]").
- iDestruct "Hs" as "[Hk Hb]".
  case: k => [?|? ?|?|kt s|? ?|?|? ? ?]; try (by iDestruct "Ho" as "[]").
  case: kt; try (by iDestruct "Ho" as "[]").
  + iDestruct "Ho" as "[_ Ho]".
    by iApply (secret_in_l_publicly_related HPriv Hcons with "Hmap Ho Hb").
  + iDestruct (publicly_related_TKey_term with "Hk") as %[s' ->].
    rewrite publicly_related_TKey. iDestruct "Hk" as "[_ Hk]".
    by iApply (secret_in_l_publicly_related HPriv Hcons with "Hmap Ho Hk").
- by iApply (secret_in_l_publicly_related HPriv Hcons with "Hmap Ho Hs").
Qed.

#[local] Lemma opaque_r_same_shape pub_r flow_r {t t'} :
  public_rel_Private_r_protected pub_r flow_r →
  public_rel_flow_r_consistent pub_r flow_r →
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  opaque_r t' -∗ same_shape publicly_related t t' -∗ False.
Proof.
move=> HPriv Hcons.
case: t' => [n|a b|a|kt s|k b|s|pt wf nf]; case: t => /= *;
  iIntros "Hmap #Ho #Hs"; try (by iDestruct "Ho" as "[]"); try (by iDestruct "Hs" as "[]").
- iDestruct "Hs" as "[Hk Hb]".
  case: k => [?|? ?|?|kt s|? ?|?|? ? ?]; try (by iDestruct "Ho" as "[]").
  case: kt; try (by iDestruct "Ho" as "[]").
  + iDestruct "Ho" as "[_ Ho]".
    by iApply (secret_in_r_publicly_related HPriv Hcons with "Hmap Ho Hb").
  + iDestruct (publicly_related_term_TKey with "Hk") as %[s' ->].
    rewrite publicly_related_TKey. iDestruct "Hk" as "[_ Hk]".
    by iApply (secret_in_r_publicly_related HPriv Hcons with "Hmap Ho Hk").
- by iApply (secret_in_r_publicly_related HPriv Hcons with "Hmap Ho Hs").
Qed.

#[local] Lemma linked_shape_same_shape_l pub_l flow_l {t t1' t2'} :
  public_rel_Private_l_protected pub_l flow_l →
  public_rel_flow_l_consistent pub_l flow_l →
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  public_rel_Public_l_consistent pub_l -∗
  same_shape publicly_related t t1' -∗
  linked_shape publicly_related t t2' -∗
  same_shape publicly_related t t2'.
Proof.
move=> HPriv Hcons.
case: t => [n|a b|a|kt s|k b|s|pt wf nf];
  case: t2' => [n2|a2 b2|a2|kt2 s2|k2 b2|s2|pt2 wf2 nf2] /=;
  iIntros "Hmap #Hrel #Hs #Hl"; try (by iDestruct "Hl" as "[]");
  case: t1' => /= *; try (by iDestruct "Hs" as "[]").
- iDestruct "Hs" as "[_ Hs]". iDestruct "Hl" as "[<- Hl]". iSplit; first done.
  case: kt; try (by iDestruct "Hl" as "[]");
    iDestruct "Hl" as "[Hl _]";
    by iApply (publicly_related_linked_in_l HPriv Hcons with "Hmap Hrel Hs Hl").
- iDestruct "Hs" as "[Hk Hb]". iDestruct "Hl" as "[[Hkl _] #Hl]".
  iPoseProof (publicly_related_linked_in_l HPriv Hcons with "Hmap Hrel Hk Hkl") as "#Hk2".
  iSplit; first done.
  case: k => [?|? ?|?|kt s|? ?|?|? ? ?]; try (by iDestruct "Hl" as "[]").
  case: k2 => [?|? ?|?|kt' s'|? ?|?|? ? ?]; try (by iDestruct "Hl" as "[]").
  case: kt; case: kt'; try (by iDestruct "Hl" as "[]").
  + iDestruct "Hl" as "[_ Hb2]".
    iDestruct "Hb2" as "[Hb2|[Hb2 _]]"; first done.
    by iApply (publicly_related_linked_in_l HPriv Hcons with "Hmap Hrel Hb Hb2").
  + by iDestruct "Hl" as "[_ Hb2]".
  + iApply "Hl". rewrite publicly_related_TKey. by iDestruct "Hk2" as "[_ ?]".
- iDestruct "Hl" as "[Hl _]".
  by iApply (publicly_related_linked_in_l HPriv Hcons with "Hmap Hrel Hs Hl").
Qed.

#[local] Lemma linked_shape_same_shape_r pub_r flow_r {t1 t2 t'} :
  public_rel_Private_r_protected pub_r flow_r →
  public_rel_flow_r_consistent pub_r flow_r →
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  public_rel_Public_r_consistent pub_r -∗
  same_shape publicly_related t1 t' -∗
  linked_shape publicly_related t2 t' -∗
  same_shape publicly_related t2 t'.
Proof.
move=> HPriv Hcons.
case: t' => [n|a b|a|kt s|k b|s|pt wf nf];
  case: t2 => [n2|a2 b2|a2|kt2 s2|k2 b2|s2|pt2 wf2 nf2] /=;
  iIntros "Hmap #Hrel #Hs #Hl"; try (by iDestruct "Hl" as "[]");
  case: t1 => /= *; try (by iDestruct "Hs" as "[]").
- iDestruct "Hs" as "[_ Hs]". iDestruct "Hl" as "[%Heq Hl]". subst kt2. iSplit; first done.
  case: kt; try (by iDestruct "Hl" as "[]");
    iDestruct "Hl" as "[_ Hl]";
    by iApply (publicly_related_linked_in_r HPriv Hcons with "Hmap Hrel Hs Hl").
- iDestruct "Hs" as "[Hk Hb]". iDestruct "Hl" as "[[_ Hkl] #Hl]".
  iPoseProof (publicly_related_linked_in_r HPriv Hcons with "Hmap Hrel Hk Hkl") as "#Hk2".
  iSplit; first done.
  case: k2 => [?|? ?|?|kt' s'|? ?|?|? ? ?]; try (by iDestruct "Hl" as "[]").
  case: k => [?|? ?|?|kt s|? ?|?|? ? ?]; try (by iDestruct "Hl" as "[]").
  case: kt; case: kt'; try (by iDestruct "Hl" as "[]").
  + iDestruct "Hl" as "[_ Hb2]".
    iDestruct "Hb2" as "[Hb2|[_ Hb2]]"; first done.
    by iApply (publicly_related_linked_in_r HPriv Hcons with "Hmap Hrel Hb Hb2").
  + by iDestruct "Hl" as "[_ Hb2]".
  + iApply "Hl". rewrite publicly_related_TKey. by iDestruct "Hk2" as "[_ ?]".
- iDestruct "Hl" as "[_ Hl]".
  by iApply (publicly_related_linked_in_r HPriv Hcons with "Hmap Hrel Hs Hl").
Qed.

End Protection.

Section Admission.

Lemma linked_in_l_map_token_fupd E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗ linked_in_l t t' -∗ map_token_l t ={E}=∗ False.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Hl tok".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r & ([Hmap_l _] & _ & Hmeta & _) & _)".
iDestruct (linked_in_l_lookup with "Hmap_l Hl") as %Hlookup.
iDestruct (public_rel_map_l_fresh with "Hmeta tok") as %Hfresh.
exfalso. rewrite Hfresh in Hlookup. by case: Hlookup => [|[|]].
Qed.

Lemma linked_in_r_map_token_fupd E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗ linked_in_r t t' -∗ map_token_r t' ={E}=∗ False.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Hl tok".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r & (_ & [Hmap_r _] & _ & Hmeta) & _)".
iDestruct (linked_in_r_lookup with "Hmap_r Hl") as %Hlookup.
iDestruct (public_rel_map_r_fresh with "Hmeta tok") as %Hfresh.
exfalso. rewrite Hfresh in Hlookup. by case: Hlookup => [|[|]].
Qed.

End Admission.

Section PartBij.

#[local] Lemma publicly_related_part_bij_1_shape pub_l flow_l {t t1' t2'} :
  public_rel_Private_l_protected pub_l flow_l →
  public_rel_flow_l_consistent pub_l flow_l →
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  public_rel_Public_l_consistent pub_l -∗
  PUB⟨t, t1'⟩ -∗
  PUB⟨t, t2'⟩ -∗
  ⌜t1' = t2'⌝ ∨
  (same_shape publicly_related t t1' ∧ same_shape publicly_related t t2').
Proof.
move=> HPriv Hcons. iIntros "Hmap #Hrel #H1 #H2".
iDestruct (publicly_related_cases with "H1") as "[Hs1|(Hl1 & [Hk1|[Ho1 _]])]";
iDestruct (publicly_related_cases with "H2") as "[Hs2|(Hl2 & [Hk2|[Ho2 _]])]";
  try (iLeft; by iApply (publicly_linked_agree_l with "Hl1 Hl2")).
- iRight. by iSplit.
- iRight. iSplit; first done.
  by iApply (linked_shape_same_shape_l HPriv Hcons with "Hmap Hrel Hs1 Hk2").
- by iDestruct (opaque_l_same_shape HPriv Hcons with "Hmap Ho2 Hs1") as "[]".
- iRight. iSplit; last done.
  by iApply (linked_shape_same_shape_l HPriv Hcons with "Hmap Hrel Hs2 Hk1").
- by iDestruct (opaque_l_same_shape HPriv Hcons with "Hmap Ho1 Hs2") as "[]".
Qed.

#[local] Lemma publicly_related_part_bij_2_shape pub_r flow_r {t1 t2 t'} :
  public_rel_Private_r_protected pub_r flow_r →
  public_rel_flow_r_consistent pub_r flow_r →
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  public_rel_Public_r_consistent pub_r -∗
  PUB⟨t1, t'⟩ -∗
  PUB⟨t2, t'⟩ -∗
  ⌜t1 = t2⌝ ∨
  (same_shape publicly_related t1 t' ∧ same_shape publicly_related t2 t').
Proof.
move=> HPriv Hcons. iIntros "Hmap #Hrel #H1 #H2".
iDestruct (publicly_related_cases with "H1") as "[Hs1|(Hl1 & [Hk1|[_ Ho1]])]";
iDestruct (publicly_related_cases with "H2") as "[Hs2|(Hl2 & [Hk2|[_ Ho2]])]";
  try (iLeft; by iApply (publicly_linked_agree_r with "Hl1 Hl2")).
- iRight. by iSplit.
- iRight. iSplit; first done.
  by iApply (linked_shape_same_shape_r HPriv Hcons with "Hmap Hrel Hs1 Hk2").
- by iDestruct (opaque_r_same_shape HPriv Hcons with "Hmap Ho2 Hs1") as "[]".
- iRight. iSplit; last done.
  by iApply (linked_shape_same_shape_r HPriv Hcons with "Hmap Hrel Hs2 Hk1").
- by iDestruct (opaque_r_same_shape HPriv Hcons with "Hmap Ho1 Hs2") as "[]".
Qed.

#[local] Lemma publicly_related_part_bij_1_auth pub_l flow_l {t t1' t2'} :
  public_rel_Private_l_protected pub_l flow_l →
  public_rel_flow_l_consistent pub_l flow_l →
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  public_rel_Public_l_consistent pub_l -∗
  PUB⟨t, t1'⟩ -∗
  PUB⟨t, t2'⟩ -∗
  ⌜t1' = t2'⌝.
Proof.
move=> HPriv_l Hflow_l_cons. iIntros "Hmap_l Hpub_consistent #H1 #H2".
iInduction t as [n|a b|a|kt s|k b|s|pt wf nf] "IH" using term_ind' forall (t1' t2') "H1 H2";
  iDestruct (publicly_related_part_bij_1_shape HPriv_l Hflow_l_cons
               with "Hmap_l Hpub_consistent H1 H2") as "#Hc";
  iDestruct "Hc" as "[%|[Hs1 Hs2]]"; try done;
  case: t1' => /= *; try (by iDestruct "Hs1" as "[]");
  case: t2' => /= *; try (by iDestruct "Hs2" as "[]").
- iDestruct "Hs1" as %->. by iDestruct "Hs2" as %->.
- iDestruct "Hs1" as "[Ha1 Hb1]". iDestruct "Hs2" as "[Ha2 Hb2]".
  iDestruct ("IH" with "Hmap_l Hpub_consistent Ha1 Ha2") as %->.
  by iDestruct ("IH1" with "Hmap_l Hpub_consistent Hb1 Hb2") as %->.
- iDestruct "Hs1" as "[<- Hs1]". iDestruct "Hs2" as "[<- Hs2]".
  by iDestruct ("IH" with "Hmap_l Hpub_consistent Hs1 Hs2") as %->.
- iDestruct "Hs1" as "[Hk1 Hb1]". iDestruct "Hs2" as "[Hk2 Hb2]".
  iDestruct ("IH" with "Hmap_l Hpub_consistent Hk1 Hk2") as %->.
  by iDestruct ("IH1" with "Hmap_l Hpub_consistent Hb1 Hb2") as %->.
- by iDestruct ("IH" with "Hmap_l Hpub_consistent Hs1 Hs2") as %->.
Qed.

#[local] Lemma publicly_related_part_bij_1_open pub_l pub_r flow_l flow_r t t1' t2' :
  public_rel_inv pub_l pub_r flow_l flow_r -∗
  PUB⟨t, t1'⟩ -∗
  PUB⟨t, t2'⟩ -∗
  ⌜t1' = t2'⌝.
Proof.
iIntros "(([Hmap_l _] & _ & _ & _) & _ & [%HPriv_l _] & [Hpub_consistent _] &
          [%Hflow_l_cons _]) #H1 #H2".
by iApply (publicly_related_part_bij_1_auth HPriv_l Hflow_l_cons
            with "Hmap_l Hpub_consistent H1 H2").
Qed.

Lemma publicly_related_part_bij_1_fupd E t t1' t2' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  PUB⟨t, t1'⟩ -∗
  PUB⟨t, t2'⟩ -∗
  |={E}=> ⌜t1' = t2'⌝.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #H1 #H2".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r & Hbody)".
iDestruct (publicly_related_part_bij_1_open with "Hbody H1 H2") as %Heq.
iModIntro. iSplitL; last done.
iModIntro. iExists pub_l, pub_r, flow_l, flow_r. iFrame.
Qed.

#[local] Lemma publicly_related_part_bij_2_auth pub_r flow_r {t1 t2 t'} :
  public_rel_Private_r_protected pub_r flow_r →
  public_rel_flow_r_consistent pub_r flow_r →
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  public_rel_Public_r_consistent pub_r -∗
  PUB⟨t1, t'⟩ -∗
  PUB⟨t2, t'⟩ -∗
  ⌜t1 = t2⌝.
Proof.
move=> HPriv_r Hflow_r_cons. iIntros "Hmap_r Hpub_consistent #H1 #H2".
iInduction t' as [n'|a' b'|a'|kt' s'|k' b'|s'|pt' wf' nf'] "IH" using term_ind' forall (t1 t2) "H1 H2";
  iDestruct (publicly_related_part_bij_2_shape HPriv_r Hflow_r_cons
               with "Hmap_r Hpub_consistent H1 H2") as "#Hc";
  iDestruct "Hc" as "[%|[Hs1 Hs2]]"; try done;
  case: t1 => /= *; try (by iDestruct "Hs1" as "[]");
  case: t2 => /= *; try (by iDestruct "Hs2" as "[]").
- iDestruct "Hs1" as %->. by iDestruct "Hs2" as %->.
- iDestruct "Hs1" as "[Ha1 Hb1]". iDestruct "Hs2" as "[Ha2 Hb2]".
  iDestruct ("IH" with "Hmap_r Hpub_consistent Ha1 Ha2") as %->.
  by iDestruct ("IH1" with "Hmap_r Hpub_consistent Hb1 Hb2") as %->.
- iDestruct "Hs1" as "[-> Hs1]". iDestruct "Hs2" as "[-> Hs2]".
  by iDestruct ("IH" with "Hmap_r Hpub_consistent Hs1 Hs2") as %->.
- iDestruct "Hs1" as "[Hk1 Hb1]". iDestruct "Hs2" as "[Hk2 Hb2]".
  iDestruct ("IH" with "Hmap_r Hpub_consistent Hk1 Hk2") as %->.
  by iDestruct ("IH1" with "Hmap_r Hpub_consistent Hb1 Hb2") as %->.
- by iDestruct ("IH" with "Hmap_r Hpub_consistent Hs1 Hs2") as %->.
Qed.

#[local] Lemma publicly_related_part_bij_2_open pub_l pub_r flow_l flow_r t1 t2 t' :
  public_rel_inv pub_l pub_r flow_l flow_r -∗
  PUB⟨t1, t'⟩ -∗
  PUB⟨t2, t'⟩ -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "((_ & [Hmap_r _] & _ & _) & _ & [_ %HPriv_r] & [_ Hpub_consistent_r] &
          [_ %Hflow_r_cons]) #H1 #H2".
by iApply (publicly_related_part_bij_2_auth HPriv_r Hflow_r_cons
            with "Hmap_r Hpub_consistent_r H1 H2").
Qed.

Lemma publicly_related_part_bij_2_fupd E t1 t2 t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  PUB⟨t1, t'⟩ -∗
  PUB⟨t2, t'⟩ -∗
  |={E}=> ⌜t1 = t2⌝.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #H1 #H2".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r & Hbody)".
iDestruct (publicly_related_part_bij_2_open with "Hbody H1 H2") as %Heq.
iModIntro. iSplitL; last done.
iModIntro. iExists pub_l, pub_r, flow_l, flow_r. iFrame.
Qed.

Lemma publicly_related_part_bij E t t' :
  ↑cryptisN ⊆ E →
  (∀ t1', cryptis_rel_ctx -∗ PUB⟨t, t'⟩ -∗ PUB⟨t, t1'⟩ -∗ |={E}=> ⌜t' = t1'⌝) ∧
  (∀ t1, cryptis_rel_ctx -∗ PUB⟨t, t'⟩ -∗ PUB⟨t1, t'⟩ -∗ |={E}=> ⌜t = t1⌝).
Proof.
move=> HE. split.
- move=> t1'. exact: publicly_related_part_bij_1_fupd.
- move=> t1. exact: publicly_related_part_bij_2_fupd.
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
{ iMod (publicly_related_part_bij_1_fupd with "Hctx Ht1 Ht2") as %->; first done.
  by iPureIntro. }
destruct (decide (t1' = t2')) as [->|Hne'].
{ iMod (publicly_related_part_bij_2_fupd with "Hctx Ht1 Ht2") as %->; first done.
  by iPureIntro. }
iPureIntro. tauto.
Qed.

End PartBij.

Section AttackerDecryption.

#[local] Lemma publicly_related_open_auth pub_l flow_l {k k' t t' t1 t1'} :
  public_rel_Private_l_protected pub_l flow_l →
  public_rel_flow_l_consistent pub_l flow_l →
  Spec.open k t = Some t1 →
  Spec.open k' t' = Some t1' →
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  PUB⟨t1, t1'⟩.
Proof.
move=> HPriv Hcons. rewrite /Spec.open.
case: t => // k_t t.
case: t' => // k_t' t'.
case: decide => // k_t_k [<-].
case: decide => // k_t_k' [<-].
iIntros "Hmap #Hk #Ht".
case: k_t k_t' => // kt k1 [] // kt' k1' in k_t_k k_t_k' *.
case: kt k_t_k => // - [<-]; case: kt' k_t_k' => // - [<-].
all: try (rewrite publicly_related_TKey; by iDestruct "Hk" as "[% _]").
all: iDestruct (publicly_related_TSeal with "Ht") as "[[_ Ht1]|(_ & _ & _ & [[_ #Hrest]|[Ho _]])]";
  first done.
all: try iSimpl in "Ho"; try iSimpl in "Hrest".
all: iDestruct (publicly_related_TKey with "Hk") as "[_ Hk']"; iSimpl in "Hk'".
- iDestruct "Hrest" as "[Hrest _]". by iApply "Hrest".
- iDestruct "Ho" as "[Ho _]".
  by iDestruct (secret_in_l_publicly_related HPriv Hcons with "Hmap Ho Hk'") as "[]".
- by iDestruct "Hrest" as "[_ ?]".
- by iDestruct "Ho" as "[]".
- by iApply "Hrest".
- by iDestruct (secret_in_l_publicly_related HPriv Hcons with "Hmap Ho Hk'") as "[]".
Qed.

#[local] Lemma publicly_related_open_inv {pub_l pub_r flow_l flow_r k k' t t' t1 t1'} :
  Spec.open k t = Some t1 →
  Spec.open k' t' = Some t1' →
  public_rel_inv pub_l pub_r flow_l flow_r -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  PUB⟨t1, t1'⟩.
Proof.
iIntros (Ho Ho') "(([Hmap_l _] & _ & _ & _) & _ & [%HPriv_l _] & _ & [%Hflow_l_cons _]) #Hk #Ht".
by iApply (publicly_related_open_auth HPriv_l Hflow_l_cons Ho Ho' with "Hmap_l Hk Ht").
Qed.

Lemma publicly_related_open E k k' t t' t1 t1' :
  ↑cryptisN ⊆ E →
  Spec.open k t = Some t1 →
  Spec.open k' t' = Some t1' →
  cryptis_rel_ctx -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ ={E}=∗
  PUB⟨t1, t1'⟩.
Proof.
iIntros (HE Ho Ho') "#(_ & _ & Hinv) #Hk #Ht".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r & Hbody)".
iDestruct (publicly_related_open_inv Ho Ho' with "Hbody Hk Ht") as "#Ht1".
iModIntro. iSplitL; last done.
iModIntro. iExists pub_l, pub_r, flow_l, flow_r. iFrame.
Qed.

#[local] Lemma publicly_related_linked_in_l_agree pub_l flow_l {t t1' t2'} :
  public_rel_Private_l_protected pub_l flow_l →
  public_rel_flow_l_consistent pub_l flow_l →
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  public_rel_Public_l_consistent pub_l -∗
  PUB⟨t, t1'⟩ -∗
  linked_in_l t t2' -∗
  ⌜t1' = t2'⌝.
Proof.
move=> HPriv_l Hflow_l_cons. iIntros "Hmap_l Hpub_consistent #H1 #H2".
iPoseProof (publicly_related_linked_in_l HPriv_l Hflow_l_cons
              with "Hmap_l Hpub_consistent H1 H2") as "#H3".
by iApply (publicly_related_part_bij_1_auth HPriv_l Hflow_l_cons
             with "Hmap_l Hpub_consistent H1 H3").
Qed.

#[local] Lemma publicly_related_linked_in_r_agree pub_r flow_r {t1 t2 t'} :
  public_rel_Private_r_protected pub_r flow_r →
  public_rel_flow_r_consistent pub_r flow_r →
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  public_rel_Public_r_consistent pub_r -∗
  PUB⟨t1, t'⟩ -∗
  linked_in_r t2 t' -∗
  ⌜t1 = t2⌝.
Proof.
move=> HPriv_r Hflow_r_cons. iIntros "Hmap_r Hpub_consistent #H1 #H2".
iPoseProof (publicly_related_linked_in_r HPriv_r Hflow_r_cons
              with "Hmap_r Hpub_consistent H1 H2") as "#H3".
by iApply (publicly_related_part_bij_2_auth HPriv_r Hflow_r_cons
             with "Hmap_r Hpub_consistent H1 H3").
Qed.

#[local] Lemma publicly_related_seed_agree_l pub_l flow_l {s s1 s2} :
  public_rel_Private_l_protected pub_l flow_l →
  public_rel_flow_l_consistent pub_l flow_l →
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  public_rel_Public_l_consistent pub_l -∗
  PUB⟨s, s1⟩ -∗
  (PUB⟨s, s2⟩ ∨ linked s s2) -∗
  ⌜s1 = s2⌝.
Proof.
move=> HPriv_l Hflow_l_cons. iIntros "Hmap_l Hpub_consistent #H1 #[H2|[H2 _]]".
- by iApply (publicly_related_part_bij_1_auth HPriv_l Hflow_l_cons
               with "Hmap_l Hpub_consistent H1 H2").
- by iApply (publicly_related_linked_in_l_agree HPriv_l Hflow_l_cons
               with "Hmap_l Hpub_consistent H1 H2").
Qed.

#[local] Lemma publicly_related_seed_agree_r pub_r flow_r {s1 s2 s'} :
  public_rel_Private_r_protected pub_r flow_r →
  public_rel_flow_r_consistent pub_r flow_r →
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  public_rel_Public_r_consistent pub_r -∗
  PUB⟨s1, s'⟩ -∗
  (PUB⟨s2, s'⟩ ∨ linked s2 s') -∗
  ⌜s1 = s2⌝.
Proof.
move=> HPriv_r Hflow_r_cons. iIntros "Hmap_r Hpub_consistent #H1 #[H2|[_ H2]]".
- by iApply (publicly_related_part_bij_2_auth HPriv_r Hflow_r_cons
               with "Hmap_r Hpub_consistent H1 H2").
- by iApply (publicly_related_linked_in_r_agree HPriv_r Hflow_r_cons
               with "Hmap_r Hpub_consistent H1 H2").
Qed.

#[local] Lemma publicly_related_TSeal_Sign_linked s b k_t' b' :
  PUB⟨TSeal (TKey Sign s) b, TSeal k_t' b'⟩ -∗
  PUB⟨TKey Sign s, k_t'⟩ ∨
  (∃ s', ⌜k_t' = TKey Sign s'⌝ ∧ PUB⟨TKey Verify s, TKey Verify s'⟩).
Proof.
rewrite publicly_related_TSeal.
iIntros "#[[H _]|(_ & _ & _ & [[_ Hbox]|[Ho _]])]"; first by iLeft.
- iRight. case: k_t' => [?|? ?|?|kt' s'|? ?|?|? ? ?]; try by iDestruct "Hbox" as "[]".
  case: kt'; try by iDestruct "Hbox" as "[]".
  iDestruct "Hbox" as "[Hv _]". iExists s'. by iSplit.
- iSimpl in "Ho". by iDestruct "Ho" as "[]".
Qed.

#[local] Lemma publicly_related_TSeal_Sign_linked_r k_t b s' b' :
  PUB⟨TSeal k_t b, TSeal (TKey Sign s') b'⟩ -∗
  PUB⟨k_t, TKey Sign s'⟩ ∨
  (∃ s, ⌜k_t = TKey Sign s⌝ ∧ PUB⟨TKey Verify s, TKey Verify s'⟩).
Proof.
rewrite publicly_related_TSeal.
iIntros "#[[H _]|(_ & _ & _ & [[_ Hbox]|[_ Ho]])]"; first by iLeft.
- iRight. case: k_t => [?|? ?|?|kt s|? ?|?|? ? ?]; try by iDestruct "Hbox" as "[]".
  case: kt; try by iDestruct "Hbox" as "[]".
  iDestruct "Hbox" as "[Hv _]". iExists s. by iSplit.
- iSimpl in "Ho". by iDestruct "Ho" as "[]".
Qed.

#[local] Lemma publicly_related_open_l_auth pub_l flow_l {k k' t t' t1} :
  public_rel_Private_l_protected pub_l flow_l →
  public_rel_flow_l_consistent pub_l flow_l →
  Spec.open k t = Some t1 →
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  public_rel_Public_l_consistent pub_l -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  ⌜is_Some (Spec.open k' t')⌝.
Proof.
move=> HPriv_l Hflow_l_cons.
rewrite {1}/Spec.open. case: t => // k_t b.
case: decide => // Hkey _.
move: Hkey; rewrite /Spec.open_key /Spec.to_key.
case: k_t => // kt s Hkey.
have Hdone : ∀ kt' s' b', Spec.open_key (TKey kt' s') = Some k' →
  is_Some (Spec.open k' (TSeal (TKey kt' s') b')).
{ move=> kt' s' b' Hk'. rewrite /Spec.open decide_True //. }
case: kt Hkey => // - [<-] {k}; iIntros "Hmap_l Hpub_consistent #Hk #Ht";
  iDestruct (publicly_related_TKey_term with "Hk") as %[s'' ->];
  iDestruct (publicly_related_TSeal_term with "Ht") as "[(%k_t' & %b' & ->)|(_ & Hsec & _)]".
- (* Asymmetric encryption, [t'] is a ciphertext. *)
  rewrite publicly_related_TKey. iDestruct "Hk" as "[_ #Hs]".
  iAssert (PUB⟨TKey AEnc s, k_t'⟩) as "#Hkk".
  { iDestruct (publicly_related_TSeal with "Ht") as "[[Hkk _]|(_ & _ & _ & [[[Hlink _] _]|[Ho _]])]";
      first done.
    - iDestruct (publicly_related_linked_key_l HPriv_l Hflow_l_cons
                   with "Hmap_l Hpub_consistent Hlink") as "[Hkk|Hno]"; first done.
      by iDestruct ("Hno" with "Hs") as "[]".
    - iSimpl in "Ho". iDestruct "Ho" as "[Ho _]".
      by iDestruct (secret_in_l_publicly_related HPriv_l Hflow_l_cons
                      with "Hmap_l Ho Hs") as "[]". }
  iDestruct (publicly_related_TKey_term with "Hkk") as %[s' ->].
  rewrite publicly_related_TKey. iDestruct "Hkk" as "[_ Hkk]".
  iAssert (PUB⟨s, s'⟩ ∨ linked s s')%I as "#Hkk'".
  { iDestruct "Hkk" as "[?|(_ & _ & _ & ?)]"; by [iLeft|iRight]. }
  iDestruct (publicly_related_seed_agree_l HPriv_l Hflow_l_cons
               with "Hmap_l Hpub_consistent Hs Hkk'") as %<-.
  iPureIntro. by apply: Hdone.
- (* Asymmetric encryption, [t'] is not a ciphertext: impossible. *)
  rewrite publicly_related_TKey. iDestruct "Hk" as "[_ #Hs]".
  iSimpl in "Hsec". iDestruct "Hsec" as "[Hsec _]". iExFalso.
  by iApply (secret_in_l_publicly_related HPriv_l Hflow_l_cons with "Hmap_l Hsec Hs").
- (* Signature, [t'] is a ciphertext. *)
  iDestruct (publicly_related_TSeal_Sign_linked with "Ht") as "[Hkk|(%s' & -> & Hv)]".
  + iDestruct (publicly_related_TKey_term with "Hkk") as %[s' ->].
    rewrite !publicly_related_TKey. iDestruct "Hkk" as "[_ #Hkk]".
    iAssert (PUB⟨s, s''⟩ ∨ linked s s'')%I as "#Hs".
    { iDestruct "Hk" as "[_ [?|(_ & _ & _ & ?)]]"; by [iLeft|iRight]. }
    iDestruct (publicly_related_seed_agree_l HPriv_l Hflow_l_cons
                 with "Hmap_l Hpub_consistent Hkk Hs") as %<-.
    iPureIntro. by apply: Hdone.
  + iDestruct (publicly_related_part_bij_1_auth HPriv_l Hflow_l_cons
                 with "Hmap_l Hpub_consistent Hv Hk") as %[= <-].
    iPureIntro. by apply: Hdone.
- (* Signature, [t'] is not a ciphertext: impossible. *)
  iSimpl in "Hsec". by iDestruct "Hsec" as "[]".
- (* Symmetric encryption, [t'] is a ciphertext. *)
  rewrite publicly_related_TKey. iDestruct "Hk" as "[_ #Hs]".
  iAssert (PUB⟨TKey SEnc s, k_t'⟩) as "#Hkk".
  { iDestruct (publicly_related_TSeal with "Ht") as "[[Hkk _]|(_ & _ & _ & [[[Hlink _] _]|[Ho _]])]";
      first done.
    - iDestruct (publicly_related_linked_key_l HPriv_l Hflow_l_cons
                   with "Hmap_l Hpub_consistent Hlink") as "[Hkk|Hno]"; first done.
      by iDestruct ("Hno" with "Hs") as "[]".
    - iSimpl in "Ho".
      by iDestruct (secret_in_l_publicly_related HPriv_l Hflow_l_cons
                      with "Hmap_l Ho Hs") as "[]". }
  iDestruct (publicly_related_TKey_term with "Hkk") as %[s' ->].
  rewrite publicly_related_TKey. iDestruct "Hkk" as "[_ Hkk]".
  iDestruct (publicly_related_part_bij_1_auth HPriv_l Hflow_l_cons
               with "Hmap_l Hpub_consistent Hs Hkk") as %<-.
  iPureIntro. by apply: Hdone.
- (* Symmetric encryption, [t'] is not a ciphertext: impossible. *)
  rewrite publicly_related_TKey. iDestruct "Hk" as "[_ #Hs]". iExFalso.
  iSimpl in "Hsec".
  by iApply (secret_in_l_publicly_related HPriv_l Hflow_l_cons with "Hmap_l Hsec Hs").
Qed.

#[local] Lemma publicly_related_open_r_auth pub_r flow_r {k k' t t' t1'} :
  public_rel_Private_r_protected pub_r flow_r →
  public_rel_flow_r_consistent pub_r flow_r →
  Spec.open k' t' = Some t1' →
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  public_rel_Public_r_consistent pub_r -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  ⌜is_Some (Spec.open k t)⌝.
Proof.
move=> HPriv_r Hflow_r_cons.
rewrite {1}/Spec.open. case: t' => // k_t' b'.
case: decide => // Hkey _.
move: Hkey; rewrite /Spec.open_key /Spec.to_key.
case: k_t' => // kt' s' Hkey.
have Hdone : ∀ kt s b, Spec.open_key (TKey kt s) = Some k →
  is_Some (Spec.open k (TSeal (TKey kt s) b)).
{ move=> kt s b Hk. rewrite /Spec.open decide_True //. }
case: kt' Hkey => // - [<-] {k'}; iIntros "Hmap_r Hpub_consistent #Hk #Ht";
  iDestruct (publicly_related_term_TKey with "Hk") as %[s'' ->];
  iDestruct (publicly_related_term_TSeal with "Ht") as "[(%k_t & %b & ->)|(_ & _ & Hsec)]".
- rewrite publicly_related_TKey. iDestruct "Hk" as "[_ #Hs]".
  iAssert (PUB⟨k_t, TKey AEnc s'⟩) as "#Hkk".
  { iDestruct (publicly_related_TSeal with "Ht") as "[[Hkk _]|(_ & _ & _ & [[[_ Hlink] _]|[_ Ho]])]";
      first done.
    - iDestruct (publicly_related_linked_key_r HPriv_r Hflow_r_cons
                   with "Hmap_r Hpub_consistent Hlink") as "[Hkk|Hno]"; first done.
      by iDestruct ("Hno" with "Hs") as "[]".
    - iSimpl in "Ho". iDestruct "Ho" as "[Ho _]".
      by iDestruct (secret_in_r_publicly_related HPriv_r Hflow_r_cons
                      with "Hmap_r Ho Hs") as "[]". }
  iDestruct (publicly_related_term_TKey with "Hkk") as %[s ->].
  rewrite publicly_related_TKey. iDestruct "Hkk" as "[_ Hkk]".
  iAssert (PUB⟨s, s'⟩ ∨ linked s s')%I as "#Hkk'".
  { iDestruct "Hkk" as "[?|(_ & _ & _ & ?)]"; by [iLeft|iRight]. }
  iDestruct (publicly_related_seed_agree_r HPriv_r Hflow_r_cons
               with "Hmap_r Hpub_consistent Hs Hkk'") as %<-.
  iPureIntro. by apply: Hdone.
- rewrite publicly_related_TKey. iDestruct "Hk" as "[_ #Hs]".
  iSimpl in "Hsec". iDestruct "Hsec" as "[Hsec _]". iExFalso.
  by iApply (secret_in_r_publicly_related HPriv_r Hflow_r_cons with "Hmap_r Hsec Hs").
- iDestruct (publicly_related_TSeal_Sign_linked_r with "Ht") as "[Hkk|(%s & -> & Hv)]".
  + iDestruct (publicly_related_term_TKey with "Hkk") as %[s ->].
    rewrite !publicly_related_TKey. iDestruct "Hkk" as "[_ #Hkk]".
    iAssert (PUB⟨s'', s'⟩ ∨ linked s'' s')%I as "#Hs".
    { iDestruct "Hk" as "[_ [?|(_ & _ & _ & ?)]]"; by [iLeft|iRight]. }
    iDestruct (publicly_related_seed_agree_r HPriv_r Hflow_r_cons
                 with "Hmap_r Hpub_consistent Hkk Hs") as %<-.
    iPureIntro. by apply: Hdone.
  + iDestruct (publicly_related_part_bij_2_auth HPriv_r Hflow_r_cons
                 with "Hmap_r Hpub_consistent Hv Hk") as %[= <-].
    iPureIntro. by apply: Hdone.
- iSimpl in "Hsec". by iDestruct "Hsec" as "[]".
- rewrite publicly_related_TKey. iDestruct "Hk" as "[_ #Hs]".
  iAssert (PUB⟨k_t, TKey SEnc s'⟩) as "#Hkk".
  { iDestruct (publicly_related_TSeal with "Ht") as "[[Hkk _]|(_ & _ & _ & [[[_ Hlink] _]|[_ Ho]])]";
      first done.
    - iDestruct (publicly_related_linked_key_r HPriv_r Hflow_r_cons
                   with "Hmap_r Hpub_consistent Hlink") as "[Hkk|Hno]"; first done.
      by iDestruct ("Hno" with "Hs") as "[]".
    - iSimpl in "Ho".
      by iDestruct (secret_in_r_publicly_related HPriv_r Hflow_r_cons
                      with "Hmap_r Ho Hs") as "[]". }
  iDestruct (publicly_related_term_TKey with "Hkk") as %[s ->].
  rewrite publicly_related_TKey. iDestruct "Hkk" as "[_ Hkk]".
  iDestruct (publicly_related_part_bij_2_auth HPriv_r Hflow_r_cons
               with "Hmap_r Hpub_consistent Hs Hkk") as %<-.
  iPureIntro. by apply: Hdone.
- rewrite publicly_related_TKey. iDestruct "Hk" as "[_ #Hs]". iExFalso.
  iSimpl in "Hsec".
  by iApply (secret_in_r_publicly_related HPriv_r Hflow_r_cons with "Hmap_r Hsec Hs").
Qed.

#[local] Lemma publicly_related_open_open pub_l pub_r flow_l flow_r k k' t t' :
  public_rel_inv pub_l pub_r flow_l flow_r -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  ⌜is_Some (Spec.open k t) ↔ is_Some (Spec.open k' t')⌝.
Proof.
iIntros "(([Hmap_l _] & [Hmap_r _] & _ & _) & _ & [%HPriv_l %HPriv_r] &
          [Hpub_consistent Hpub_consistent_r] & [%Hflow_l_cons %Hflow_r_cons]) #Hk #Ht".
iSplit.
- iIntros "%Hopen". case: Hopen => t1 Hopen.
  by iApply (publicly_related_open_l_auth HPriv_l Hflow_l_cons Hopen
               with "Hmap_l Hpub_consistent Hk Ht").
- iIntros "%Hopen". case: Hopen => t1' Hopen.
  by iApply (publicly_related_open_r_auth HPriv_r Hflow_r_cons Hopen
               with "Hmap_r Hpub_consistent_r Hk Ht").
Qed.

Lemma publicly_related_open_fupd E k k' t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  |={E}=> ⌜is_Some (Spec.open k t) ↔ is_Some (Spec.open k' t')⌝.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Hk #Ht".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r & Hbody)".
iDestruct (publicly_related_open_open with "Hbody Hk Ht") as %Hiff.
iModIntro. iSplitL; last done.
iModIntro. iExists pub_l, pub_r, flow_l, flow_r. iFrame.
Qed.

End AttackerDecryption.

Section HonestDecryption.

Lemma publicly_related_open_aenc_fupd E (sk sk' : aenc_key) t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  PUB⟨Spec.pkey sk, Spec.pkey sk'⟩ -∗
  publicly_linked (Spec.pkey sk) (Spec.pkey sk') -∗
  PUB⟨t, t'⟩ ={E}=∗
  match Spec.open sk t, Spec.open sk' t' with
  | Some u, Some u' => PUB⟨u, u'⟩ ∨ publicly_linked t t'
  | Some u, None =>
    publicly_linked t t' ∧ secret_in_l (seed_of_aenc_key sk) ∧ secret_in_l u
  | None, Some u' =>
    publicly_linked t t' ∧ secret_in_r (seed_of_aenc_key sk') ∧ secret_in_r u'
  | None, None => True
  end.
Proof.
move=> HE. case: sk sk' => [sA] [sA'].
rewrite [term_of_aenc_key]unlock.
rewrite -[Spec.pkey (TKey ADec sA)]/(TKey AEnc sA).
rewrite -[Spec.pkey (TKey ADec sA')]/(TKey AEnc sA').
iIntros "#Hctx #Hpk #[Hlink_l Hlink_r] #Ht".
case eL: (Spec.open (TKey ADec sA) t) => [u|];
case eR: (Spec.open (TKey ADec sA') t') => [u'|]; iSimpl.
- move/Spec.open_aenc_Some: (eL) => ?; subst t.
  move/Spec.open_aenc_Some: (eR) => ?; subst t'.
  iDestruct (publicly_related_TSeal with "Ht") as "[[_ Hu]|(_ & _ & Hl & _)]";
    iModIntro; by [iLeft|iRight].
- move/Spec.open_aenc_Some: (eL) => ?; subst t.
  iDestruct (publicly_related_TSeal_term with "Ht") as "[(%k' & %u' & ->)|(Hl & Ho & _)]";
    last by iModIntro; iSimpl in "Ho"; iFrame "#".
  have Hk' : k' ≠ TKey AEnc sA'.
  { move=> ?; subst k'.
    have := proj2 (Spec.open_aenc_Some sA' (TSeal (TKey AEnc sA') u') u') eq_refl.
    by rewrite eR. }
  iDestruct (publicly_related_TSeal with "Ht") as "[[Hk _]|(_ & _ & Hl & [[[Hkl _] _]|[Ho _]])]".
  + iMod (publicly_related_part_bij' with "Hctx Hpk Hk") as %Hiff; first done.
    by case: Hk'; symmetry; apply Hiff.
  + iDestruct (linked_in_l_publicly_linked_in_l with "Hkl Hlink_l") as %?.
    by case: Hk'; congruence.
  + iModIntro. iSimpl in "Ho". iFrame "#".
- move/Spec.open_aenc_Some: (eR) => ?; subst t'.
  iDestruct (publicly_related_term_TSeal with "Ht") as "[(%k & %u & ->)|(Hl & _ & Ho)]";
    last by iModIntro; iSimpl in "Ho"; iFrame "#".
  have Hk : k ≠ TKey AEnc sA.
  { move=> ?; subst k.
    have := proj2 (Spec.open_aenc_Some sA (TSeal (TKey AEnc sA) u) u) eq_refl.
    by rewrite eL. }
  iDestruct (publicly_related_TSeal with "Ht") as "[[Hk _]|(_ & _ & Hl & [[[_ Hkr] _]|[_ Ho]])]".
  + iMod (publicly_related_part_bij' with "Hctx Hk Hpk") as %Hiff; first done.
    by case: Hk; apply Hiff.
  + iDestruct (linked_in_r_publicly_linked_in_r with "Hkr Hlink_r") as %?.
    by case: Hk; congruence.
  + iModIntro. iSimpl in "Ho". iFrame "#".
- by iModIntro.
Qed.

Lemma publicly_related_open_senc_fupd E (k k' : senc_key) t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  secret_in_l (seed_of_senc_key k) -∗
  secret_in_r (seed_of_senc_key k') -∗
  PUB⟨t, t'⟩ ={E}=∗
  ⌜is_Some (Spec.open k t) ∨ is_Some (Spec.open k' t')⌝ → publicly_linked t t'.
Proof.
move=> HE. case: k k' => [s] [s'].
rewrite [term_of_senc_key]unlock /=.
iIntros "#Hctx #Hs #Hs' #Ht".
iDestruct (publicly_related_cases with "Ht") as "[Hsh|[Hl _]]"; last by iModIntro; iIntros.
case eL: (Spec.open (TKey SEnc s) t) => [u|].
{ move/Spec.open_senc_Some: (eL) => ?; subst t.
  case: t' => [?|? ?|?|? ?|k1 u1|?|? ? ?]; iSimpl in "Hsh"; try by iDestruct "Hsh" as "[]".
  iDestruct "Hsh" as "[Hk _]".
  iDestruct (publicly_related_TKey_term with "Hk") as %[s1 ->].
  iDestruct (publicly_related_TKey with "Hk") as "[_ Hk']".
  by iMod (secret_in_l_publicly_related_fupd with "Hctx Hs Hk'") as "[]". }
case eR: (Spec.open (TKey SEnc s') t') => [u'|].
{ move/Spec.open_senc_Some: (eR) => ?; subst t'. clear eL.
  case: t => [?|? ?|?|? ?|k1 u1|?|? ? ?]; iSimpl in "Hsh"; try by iDestruct "Hsh" as "[]".
  iDestruct "Hsh" as "[Hk _]".
  iDestruct (publicly_related_term_TKey with "Hk") as %[s1 ->].
  iDestruct (publicly_related_TKey with "Hk") as "[_ Hk']".
  by iMod (secret_in_r_publicly_related_fupd with "Hctx Hs' Hk'") as "[]". }
iModIntro. iIntros ([[? ?]|[? ?]]); congruence.
Qed.

End HonestDecryption.

End RelProperties.
