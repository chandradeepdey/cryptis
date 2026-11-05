(** * The relation [PUB] and its invariant

[PUB⟨t, t'⟩] says that the attacker cannot tell [t] in the left run apart
from [t'] in the right run.  The invariant behind it keeps track of which
terms the two runs treat as the same, and which terms stay secret.

** Section [PublicRel]

- [Map] records what is known about each term.
  - [linked t t'] means that the runs treat [t] and [t'] as the same term.
  - [publicly_linked t t'] means the same, and that the attacker may see
    them.
  - [secret_in_l t] means that the attacker never sees [t] in the left run.
- [Flow] records why a term stays hidden.  A term other than a nonce can be
  hidden only if one of its parts is hidden, for example the nonce inside it.
- [Seals] records, on the seed of each key, the ciphertexts made with it
  and their partners in the other run.
- [Relation] defines [PUB].  Two terms are related if they are built the
  same way from related parts, if they are publicly linked, or if they are
  sealed as a pair.
- [Invariant] puts these together.

** Section [RelProperties]

- [Constructors] says what [PUB] means for each kind of term.  For a
  constructor [X], [publicly_related_X] covers two [X] terms, and
  [publicly_related_X_term] and [publicly_related_term_X] say what may be
  related to an [X] term.
- [Ciphertexts] does the same for ciphertexts.
- [Protection]: a hidden term is related to nothing.
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
From cryptis.hyper.core Require Export rel_state.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
  ([∗ set] t ∈ dom pub_l, term_meta t (cryptisN.@"public_rel".@"map") ()) ∗
  ([∗ set] t' ∈ dom pub_r, term_meta_spec t' (cryptisN.@"public_rel".@"map") ()).

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
  ([∗ set] t ∈ dom pub_l, term_meta t (cryptisN.@"public_rel".@"map") ()) -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  ⌜pub_l !! t = None⌝.
Proof.
iIntros "Hmeta Htt".
destruct (pub_l !! t) eqn:Heq; last done.
iDestruct (big_sepS_elem_of _ _ t with "Hmeta") as "Hmeta_t"; first by apply elem_of_dom.
by iDestruct (term_meta_token with "Htt Hmeta_t") as "[]".
Qed.

Lemma public_rel_map_r_fresh pub_r t' :
  ([∗ set] t' ∈ dom pub_r, term_meta_spec t' (cryptisN.@"public_rel".@"map") ()) -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  ⌜pub_r !! t' = None⌝.
Proof.
iIntros "Hmeta Htts".
destruct (pub_r !! t') eqn:Heq; last done.
iDestruct (big_sepS_elem_of _ _ t' with "Hmeta") as "Hmeta_t"; first by apply elem_of_dom.
by iDestruct (term_meta_spec_token with "Htts Hmeta_t") as "[]".
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
  ([∗ set] t ∈ dom flow_l, term_meta t (cryptisN.@"public_rel".@"flow") ()) ∗
  ([∗ set] t' ∈ dom flow_r, term_meta_spec t' (cryptisN.@"public_rel".@"flow") ()).

Definition protects_superterms_l t ts : iProp :=
  own public_rel_flow_l (◯ {[ t := ●{#1/2} (GSet ts) ]}).

Definition protected_by_subterm_l t tsub : iProp :=
  own public_rel_flow_l (◯ {[ tsub := ◯ (GSet {[ t ]}) ]}).

Definition protects_superterms_r t' ts : iProp :=
  own public_rel_flow_r (◯ {[ t' := ●{#1/2} (GSet ts) ]}).

Definition protected_by_subterm_r t' tsub : iProp :=
  own public_rel_flow_r (◯ {[ tsub := ◯ (GSet {[ t' ]}) ]}).

Lemma public_rel_flow_l_fresh flow_l t :
  ([∗ set] t' ∈ dom flow_l, term_meta t' (cryptisN.@"public_rel".@"flow") ()) -∗
  term_token t (↑cryptisN.@"public_rel".@"flow") -∗
  ⌜flow_l !! t = None⌝.
Proof.
iIntros "Hmeta Htt".
destruct (flow_l !! t) eqn:Heq; last done.
iDestruct (big_sepS_elem_of _ _ t with "Hmeta") as "Hmeta_t"; first by apply elem_of_dom.
by iDestruct (term_meta_token with "Htt Hmeta_t") as "[]".
Qed.

Lemma public_rel_flow_r_fresh flow_r t' :
  ([∗ set] t' ∈ dom flow_r, term_meta_spec t' (cryptisN.@"public_rel".@"flow") ()) -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"flow") -∗
  ⌜flow_r !! t' = None⌝.
Proof.
iIntros "Hmeta Htts".
destruct (flow_r !! t') eqn:Heq; last done.
iDestruct (big_sepS_elem_of _ _ t' with "Hmeta") as "Hmeta_t"; first by apply elem_of_dom.
by iDestruct (term_meta_spec_token with "Htts Hmeta_t") as "[]".
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

Section Seals.

Implicit Types (k : term) (s : term).

Definition seal_ns (k t : term) : namespace := cryptisN.@"public_rel".@"seal".@(k, t).

Definition sealed_under_l k t t' : iProp :=
  match k with
  | TKey _ s => term_meta s (seal_ns k t) t'
  | _ => False
  end.

Definition sealed_under_r k' t' t : iProp :=
  match k' with
  | TKey _ s' => term_meta_spec s' (seal_ns k' t') t
  | _ => False
  end.

#[global] Instance sealed_under_l_persistent k t t' : Persistent (sealed_under_l k t t').
Proof. case: k => *; apply _. Qed.

#[global] Instance sealed_under_r_persistent k' t' t : Persistent (sealed_under_r k' t' t).
Proof. case: k' => *; apply _. Qed.

#[global] Instance sealed_under_l_timeless k t t' : Timeless (sealed_under_l k t t').
Proof. case: k => *; apply _. Qed.

#[global] Instance sealed_under_r_timeless k' t' t : Timeless (sealed_under_r k' t' t).
Proof. case: k' => *; apply _. Qed.

Definition sealed_under k k' t t' : iProp :=
  sealed_under_l k t (TSeal k' t') ∧ sealed_under_r k' t' (TSeal k t).

Definition never_sealed_under s s' E E' : iProp :=
  term_token s E ∗ term_token_spec s' E'.

Lemma sealed_under_l_agree k t t1' t2' :
  sealed_under_l k t t1' -∗ sealed_under_l k t t2' -∗ ⌜t1' = t2'⌝.
Proof.
case: k => *; try by iIntros "[]".
iIntros "#H1 #H2". by iApply (term_meta_agree with "H1 H2").
Qed.

Lemma sealed_under_r_agree k' t' t1 t2 :
  sealed_under_r k' t' t1 -∗ sealed_under_r k' t' t2 -∗ ⌜t1 = t2⌝.
Proof.
case: k' => *; try by iIntros "[]".
iIntros "#H1 #H2". by iApply (term_meta_spec_agree with "H1 H2").
Qed.

Lemma sealed_under_l_set E kt s t t' :
  ↑seal_ns (TKey kt s) t ⊆ E →
  term_token s E ==∗
  sealed_under_l (TKey kt s) t t' ∗ term_token s (E ∖ ↑seal_ns (TKey kt s) t).
Proof. move=> sub. by iApply term_meta_set'. Qed.

Lemma sealed_under_r_set E kt s' t' t :
  ↑seal_ns (TKey kt s') t' ⊆ E →
  term_token_spec s' E ==∗
  sealed_under_r (TKey kt s') t' t ∗ term_token_spec s' (E ∖ ↑seal_ns (TKey kt s') t').
Proof. move=> sub. by iApply term_meta_spec_set'. Qed.

Lemma sealed_under_l_token E kt s t t' :
  ↑seal_ns (TKey kt s) t ⊆ E →
  term_token s E -∗ sealed_under_l (TKey kt s) t t' -∗ False.
Proof. move=> sub. iIntros "tok #rec". by iDestruct (term_meta_token with "tok rec") as "[]". Qed.

Lemma sealed_under_r_token E kt s' t' t :
  ↑seal_ns (TKey kt s') t' ⊆ E →
  term_token_spec s' E -∗ sealed_under_r (TKey kt s') t' t -∗ False.
Proof. move=> sub. iIntros "tok #rec". by iDestruct (term_meta_spec_token with "tok rec") as "[]". Qed.

Lemma sealed_under_set kt s kt' s' t t' Ek Ek' :
  ↑seal_ns (TKey kt s) t ⊆ Ek →
  ↑seal_ns (TKey kt' s') t' ⊆ Ek' →
  never_sealed_under s s' Ek Ek' ==∗
  sealed_under (TKey kt s) (TKey kt' s') t t' ∗
  never_sealed_under s s' (Ek ∖ ↑seal_ns (TKey kt s) t) (Ek' ∖ ↑seal_ns (TKey kt' s') t').
Proof.
iIntros (sub sub') "[tok tok']".
iMod (sealed_under_l_set (TSeal (TKey kt' s') t') sub with "tok") as "[#Hl $]".
iMod (sealed_under_r_set (TSeal (TKey kt s) t) sub' with "tok'") as "[#Hr $]".
iModIntro. by iSplit.
Qed.

Lemma aenc_key_pkey (sk : aenc_key) : Spec.pkey sk = TKey AEnc (seed_of_aenc_key sk).
Proof. by case: sk => s; rewrite [term_of_aenc_key]unlock. Qed.

Lemma senc_key_TKey (k : senc_key) : (k : term) = TKey SEnc (seed_of_senc_key k).
Proof. by case: k => s; rewrite [term_of_senc_key]unlock. Qed.

Lemma sign_key_TKey (sk : sign_key) : (sk : term) = TKey Sign (seed_of_sign_key sk).
Proof. by case: sk => s; rewrite [term_of_sign_key]unlock. Qed.

End Seals.

Section Relation.

Fixpoint publicly_related t t' : iProp :=
  minted t ∧ minted_spec t' ∧
  match t, t' with
  | TInt n, TInt n' => ⌜n = n'⌝
  | TPair t1 t2, TPair t1' t2' => publicly_related t1 t1' ∧ publicly_related t2 t2'
  | TNonce a, TNonce a' => publicly_linked t t'
  | TKey kt t1, TKey kt' t1' => ⌜kt = kt'⌝ ∧
    match kt with
    | AEnc => publicly_related t1 t1' ∨
              (publicly_linked t t' ∧ linked t1 t1')
    | ADec => publicly_related t1 t1'
    | Sign => publicly_related t1 t1'
    | Verify => publicly_related t1 t1' ∨
                (publicly_linked t t' ∧ linked t1 t1')
    | SEnc => publicly_related t1 t1'
    end
  | TSeal k t1, TSeal k' t1' =>
    (publicly_related k k' ∧ publicly_related t1 t1') ∨
    (sealed_under k k' t1 t1' ∧
     □ (match k, k' with
        | TKey kt k1, TKey kt' k1' =>
          match kt, kt' with
          | Sign, Sign =>
            linked k k' ∧
            (* PUB⟨TKey Verify k1, TKey Verify k1'⟩, inlined for the
               termination checker. *)
            (publicly_related k1 k1' ∨
             (publicly_linked (TKey Verify k1) (TKey Verify k1') ∧ linked k1 k1')) ∧
            publicly_related t1 t1'
          | AEnc, AEnc =>
            linked k k' ∧
            (publicly_related k1 k1' → publicly_related t1 t1') ∧
            (publicly_related t1 t1' ∨ linked t1 t1')
          | SEnc, SEnc =>
            linked k k' ∧ (publicly_related k1 k1' → publicly_related t1 t1')
          | AEnc, SEnc => secret_in_l k1 ∧ secret_in_l t1 ∧ secret_in_r k1'
          | SEnc, AEnc => secret_in_l k1 ∧ secret_in_r k1' ∧ secret_in_r t1'
          | _, _ => False
          end
        | _, _ => False
        end))
  | THash t1, THash t1' => publicly_related t1 t1' ∨
    (publicly_linked t t' ∧ linked t1 t1')
  | TNonce a, TSeal k' t1' =>
    publicly_linked_in_l t t' ∧ sealed_under_r k' t1' t ∧
    (match k' with
    | TKey AEnc s' => secret_in_r s' ∧ secret_in_r t1'
    | TKey SEnc s' => secret_in_r s'
    | _ => False
    end)
  | TSeal k t1, TNonce a' =>
    sealed_under_l k t1 t' ∧ publicly_linked_in_r t t' ∧
    (match k with
    | TKey AEnc s => secret_in_l s ∧ secret_in_l t1
    | TKey SEnc s => secret_in_l s
    | _ => False
    end)
  | TNonce a, THash t1' => publicly_linked t t' ∧ secret_in_r t1'
  | THash t1, TNonce a' => publicly_linked t t' ∧ secret_in_l t1
  | TSeal k t1, THash t1' =>
    sealed_under_l k t1 t' ∧ publicly_linked_in_r t t' ∧ secret_in_r t1' ∧
    (match k with
    | TKey AEnc s => secret_in_l s ∧ secret_in_l t1
    | TKey SEnc s => secret_in_l s
    | _ => False
    end)
  | THash t1, TSeal k' t1' =>
    publicly_linked_in_l t t' ∧ sealed_under_r k' t1' t ∧ secret_in_l t1 ∧
    (match k' with
    | TKey AEnc s' => secret_in_r s' ∧ secret_in_r t1'
    | TKey SEnc s' => secret_in_r s'
    | _ => False
    end)
  | _, _ =>
      False
  end.

#[local] Notation "PUB⟨ a , b ⟩" := (publicly_related a b)
  (at level 0, no associativity, format "PUB⟨ a , b ⟩").

#[global] Instance publicly_related_persistent t t' : Persistent (PUB⟨t, t'⟩).
Proof. elim/term_ind': t t' => /=; apply _. Qed.

#[global] Instance publicly_related_timeless t t' : Timeless (PUB⟨t, t'⟩).
Proof.
elim/term_lt_ind: t t' => t IH t'.
case: t IH => [n|a b|a|kt s|k b|s|pt wf nf] IH /=; try apply _.
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
  PUB⟨TNonce a, t'⟩ -∗ publicly_linked_in_l (TNonce a) t'.
Proof.
case: t' => /= *; try by iIntros "(_ & _ & [])".
- by iIntros "(_ & _ & [? _])".
- by iIntros "(_ & _ & ? & _)".
- by iIntros "(_ & _ & [? _] & _)".
Qed.

Lemma publicly_related_term_TNonce (t : term) a' :
  PUB⟨t, TNonce a'⟩ -∗ publicly_linked_in_r t (TNonce a').
Proof.
case: t => /= *; try by iIntros "(_ & _ & [])".
- by iIntros "(_ & _ & [_ ?])".
- by iIntros "(_ & _ & _ & ? & _)".
- by iIntros "(_ & _ & [_ ?] & _)".
Qed.

Lemma publicly_related_nonce t t' :
  is_nonce t → is_nonce t' →
  PUB⟨t, t'⟩ ⊣⊢ minted t ∧ minted_spec t' ∧ publicly_linked t t'.
Proof. by move=> /is_nonceP [a ->] /is_nonceP [a' ->]. Qed.

Lemma publicly_related_nonce_term t t' :
  is_nonce t → PUB⟨t, t'⟩ -∗ publicly_linked_in_l t t'.
Proof. move=> /is_nonceP [a ->]. exact: publicly_related_TNonce_term. Qed.

Lemma publicly_related_term_nonce t t' :
  is_nonce t' → PUB⟨t, t'⟩ -∗ publicly_linked_in_r t t'.
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

Lemma publicly_related_TKey_term kt t (t' : term) :
  PUB⟨TKey kt t, t'⟩ -∗ ∃ t1', ⌜t' = TKey kt t1'⌝.
Proof.
case: t' => /= *; try by iIntros "(_ & _ & [])".
iIntros "(_ & _ & <- & _)". by eauto.
Qed.

Lemma publicly_related_term_TKey (t : term) kt' t' :
  PUB⟨t, TKey kt' t'⟩ -∗ ∃ t1, ⌜t = TKey kt' t1⌝.
Proof.
case: t => /= *; try by iIntros "(_ & _ & [])".
iIntros "(_ & _ & -> & _)". by eauto.
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
   publicly_linked (THash t) (THash t') ∧ linked t t').
Proof.
rewrite /= minted_THash minted_spec_THash. iSplit.
- iIntros "#(? & ? & [?|(? & ?)])";
    [by iLeft | iRight; by do 3 (iSplit; first done)].
- iIntros "#[H|(? & ? & ? & ?)]";
    last by (do 2 (iSplit; first done); iRight; iSplit; first done).
  iPoseProof (publicly_related_minted with "H") as "[? ?]".
  do 2 (iSplit; first done). by iLeft.
Qed.

Lemma publicly_related_THash_term t (t' : term) :
  PUB⟨THash t, t'⟩ -∗
  (∃ t1', ⌜t' = THash t1'⌝) ∨
  (publicly_linked_in_l (THash t) t' ∧ secret_in_l t).
Proof.
case: t' => /= *; try by iIntros "(_ & _ & [])".
- iIntros "(_ & _ & [? _] & ?)". iRight. by iSplit.
- iIntros "(_ & _ & ? & _ & ? & _)". iRight. by iSplit.
- iIntros "_". iLeft. by eauto.
Qed.

Lemma publicly_related_term_THash (t : term) t' :
  PUB⟨t, THash t'⟩ -∗
  (∃ t1, ⌜t = THash t1⌝) ∨
  (publicly_linked_in_r t (THash t') ∧ secret_in_r t').
Proof.
case: t => /= *; try by iIntros "(_ & _ & [])".
- iIntros "(_ & _ & [_ ?] & ?)". iRight. by iSplit.
- iIntros "(_ & _ & _ & ? & ? & _)". iRight. by iSplit.
- iIntros "_". iLeft. by eauto.
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
all: by iDestruct "Hm" as "(_ & _ & [])".
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

End Constructors.

Section Ciphertexts.

Lemma publicly_related_TSeal k k' t t' :
  PUB⟨TSeal k t, TSeal k' t'⟩ ⊣⊢
  (PUB⟨k, k'⟩ ∧ PUB⟨t, t'⟩) ∨
  (minted (TSeal k t) ∧ minted_spec (TSeal k' t') ∧
   sealed_under k k' t t' ∧
   □ (match k, k' with
      | TKey kt k1, TKey kt' k1' =>
        match kt, kt' with
        | Sign, Sign =>
          linked k k' ∧ PUB⟨TKey Verify k1, TKey Verify k1'⟩ ∧ PUB⟨t, t'⟩
        | AEnc, AEnc =>
          linked k k' ∧ (PUB⟨k1, k1'⟩ → PUB⟨t, t'⟩) ∧ (PUB⟨t, t'⟩ ∨ linked t t')
        | SEnc, SEnc => linked k k' ∧ (PUB⟨k1, k1'⟩ → PUB⟨t, t'⟩)
        | AEnc, SEnc => secret_in_l k1 ∧ secret_in_l t ∧ secret_in_r k1'
        | SEnc, AEnc => secret_in_l k1 ∧ secret_in_r k1' ∧ secret_in_r t'
        | _, _ => False
        end
      | _, _ => False
      end)).
Proof.
rewrite /=. iSplit.
- iIntros "#(mk & mk' & [?|(? & #Hbox)])"; first by iLeft.
  iRight. do 3 (iSplit; first done). iModIntro.
  case: k => [n|a b|a|kt k1|k b|s|pt wf nf]; try done.
  case: k' => [n'|a' b'|a'|kt' k1'|k'' b'|s'|pt' wf' nf']; try done.
  case: kt; case: kt'; try done.
  iDestruct "Hbox" as "(Hl & Hv & Ht)". iFrame "Hl Ht".
  rewrite minted_TSeal minted_spec_TSeal !minted_TKey !minted_spec_TKey.
  iDestruct "mk" as "[mk1 _]". iDestruct "mk'" as "[mk1' _]".
  by do 3 (iSplit; first done).
- iIntros "#[[H1 H2]|(mk & mk' & ? & #Hbox)]".
  { iPoseProof (publicly_related_minted with "H1") as "[? ?]".
    iPoseProof (publicly_related_minted with "H2") as "[? ?]".
    rewrite minted_TSeal minted_spec_TSeal.
    iSplit; first by iSplit. iSplit; first by iSplit. iLeft. by iSplit. }
  do 2 (iSplit; first done). iRight. iSplit; first done. iModIntro.
  case: k => [n|a b|a|kt k1|k b|s|pt wf nf]; try done.
  case: k' => [n'|a' b'|a'|kt' k1'|k'' b'|s'|pt' wf' nf']; try done.
  case: kt; case: kt'; try done.
  iDestruct "Hbox" as "(Hl & (_ & _ & _ & Hv) & Ht)". by iFrame "#".
Qed.

Lemma publicly_related_TSeal_term k t (t' : term) :
  PUB⟨TSeal k t, t'⟩ -∗
  (∃ k' t1', ⌜t' = TSeal k' t1'⌝) ∨
  (sealed_under_l k t t' ∧
   (match k with
   | TKey AEnc s => secret_in_l s ∧ secret_in_l t
   | TKey SEnc s => secret_in_l s
   | _ => False
   end)).
Proof.
case: t' => /= *; try by iIntros "(_ & _ & [])".
- iIntros "(_ & _ & ? & _ & ?)". iRight. by iSplit.
- iIntros "_". iLeft. by eauto.
- iIntros "(_ & _ & ? & _ & _ & ?)". iRight. by iSplit.
Qed.

Lemma publicly_related_term_TSeal (t : term) k' t' :
  PUB⟨t, TSeal k' t'⟩ -∗
  (∃ k t1, ⌜t = TSeal k t1⌝) ∨
  (sealed_under_r k' t' t ∧
   (match k' with
   | TKey AEnc s' => secret_in_r s' ∧ secret_in_r t'
   | TKey SEnc s' => secret_in_r s'
   | _ => False
   end)).
Proof.
case: t => /= *; try by iIntros "(_ & _ & [])".
- iIntros "(_ & _ & _ & ? & ?)". iRight. by iSplit.
- iIntros "_". iLeft. by eauto.
- iIntros "(_ & _ & _ & ? & _ & ?)". iRight. by iSplit.
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
  case: (public_rel_protected_inv_l HPriv Hcons Hprot) => HnotPub Hsub.
- case: Hsub => [[]|[tsub [Hsub _]]] //. by inversion Hsub.
- iDestruct (publicly_related_TPair_term with "Hpub") as %(a' & b' & ->).
  rewrite publicly_related_TPair. iDestruct "Hpub" as "[Ha Hb]".
  case: Hsub => [[]|[tsub [Hsub Hprot']]] //.
  inversion Hsub; subst.
  + iApply (IHa Hprot' with "Hauth Ha").
  + iApply (IHb Hprot' with "Hauth Hb").
- iDestruct (publicly_related_TNonce_term with "Hpub") as "Hel".
  iDestruct (publicly_linked_in_l_lookup with "Hauth Hel") as %Hlookup.
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
- case: Hsub => [[]|[tsub [Hsub _]]] //. by inversion Hsub.
- iDestruct (publicly_related_THash_term with "Hpub") as "[(%s' & ->)|[Hel _]]".
  + case: Hsub => [[]|[tsub [Hsub Hprot']]] //.
    inversion Hsub; subst.
    rewrite publicly_related_THash.
    iDestruct "Hpub" as "[Hpub|(_ & _ & Hel & _)]";
      first by iApply (IH Hprot' with "Hauth Hpub").
    iDestruct (publicly_linked_lookup_l with "Hauth Hel") as %Hlookup.
    by case: (HnotPub _ Hlookup).
  + iDestruct (publicly_linked_in_l_lookup with "Hauth Hel") as %Hlookup.
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
  iDestruct (publicly_linked_in_r_lookup with "Hauth Hel") as %Hlookup.
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
- case: Hsub => [[]|[t'sub [Hsub _]]] //. by inversion Hsub.
- iDestruct (publicly_related_term_THash with "Hpub") as "[(%s1 & ->)|[Hel _]]".
  + case: Hsub => [[]|[t'sub [Hsub Hprot']]] //.
    inversion Hsub; subst.
    rewrite publicly_related_THash.
    iDestruct "Hpub" as "[Hpub|(_ & _ & Hel & _)]";
      first by iApply (IH Hprot' with "Hauth Hpub").
    iDestruct (publicly_linked_lookup_r with "Hauth Hel") as %Hlookup.
    by case: (HnotPub _ Hlookup).
  + iDestruct (publicly_linked_in_r_lookup with "Hauth Hel") as %Hlookup.
    by case: (HnotPub _ Hlookup).
- by case: t => /= *; iDestruct "Hpub" as "(_ & _ & [])".
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

#[local] Lemma publicly_related_TSeal_secret_l pub_l flow_l {k b k' b'} :
  public_rel_Private_l_protected pub_l flow_l →
  public_rel_flow_l_consistent pub_l flow_l →
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  (match k with
   | TKey AEnc s => secret_in_l s ∧ secret_in_l b
   | TKey SEnc s => secret_in_l s
   | _ => False
   end) -∗
  PUB⟨k, k'⟩ -∗ PUB⟨b, b'⟩ -∗ False.
Proof.
move=> HPriv Hcons. iIntros "Hmap Hs #Hk #Hb".
case: k => [?|? ?|?|kt s|? ?|?|? ? ?]; try by iDestruct "Hs" as "[]".
case: kt; try by iDestruct "Hs" as "[]".
- iDestruct "Hs" as "[_ Hs]".
  by iApply (secret_in_l_publicly_related HPriv Hcons with "Hmap Hs Hb").
- iDestruct (publicly_related_TKey_term with "Hk") as %[s' ->].
  rewrite publicly_related_TKey. iDestruct "Hk" as "[_ Hk']".
  by iApply (secret_in_l_publicly_related HPriv Hcons with "Hmap Hs Hk'").
Qed.

#[local] Lemma publicly_related_TSeal_secret_r pub_r flow_r {k b k' b'} :
  public_rel_Private_r_protected pub_r flow_r →
  public_rel_flow_r_consistent pub_r flow_r →
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  (match k' with
   | TKey AEnc s' => secret_in_r s' ∧ secret_in_r b'
   | TKey SEnc s' => secret_in_r s'
   | _ => False
   end) -∗
  PUB⟨k, k'⟩ -∗ PUB⟨b, b'⟩ -∗ False.
Proof.
move=> HPriv Hcons. iIntros "Hmap Hs #Hk #Hb".
case: k' => [?|? ?|?|kt s'|? ?|?|? ? ?]; try by iDestruct "Hs" as "[]".
case: kt; try by iDestruct "Hs" as "[]".
- iDestruct "Hs" as "[_ Hs]".
  by iApply (secret_in_r_publicly_related HPriv Hcons with "Hmap Hs Hb").
- iDestruct (publicly_related_term_TKey with "Hk") as %[s ->].
  rewrite publicly_related_TKey. iDestruct "Hk" as "[_ Hk']".
  by iApply (secret_in_r_publicly_related HPriv Hcons with "Hmap Hs Hk'").
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

#[local] Lemma publicly_related_TSeal_parts_l pub_l flow_l {k b k1' b1' k2' b2'} :
  public_rel_Private_l_protected pub_l flow_l →
  public_rel_flow_l_consistent pub_l flow_l →
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  public_rel_Public_l_consistent pub_l -∗
  PUB⟨k, k1'⟩ -∗ PUB⟨b, b1'⟩ -∗ PUB⟨TSeal k b, TSeal k2' b2'⟩ -∗
  PUB⟨k, k2'⟩ ∧ PUB⟨b, b2'⟩.
Proof.
move=> HPriv Hcons. iIntros "Hmap #Hrel #Hk #Hb #Ht".
rewrite publicly_related_TSeal.
iDestruct "Ht" as "[[? ?]|(_ & _ & _ & #Hpl)]"; first by iSplit.
case: k => [?|? ?|?|kt s|? ?|?|? ? ?]; try by iDestruct "Hpl" as "[]".
case: k2' => [?|? ?|?|kt' s'|? ?|?|? ? ?]; try by iDestruct "Hpl" as "[]".
case: kt; case: kt'; try by iDestruct "Hpl" as "[]".
all: try (iDestruct "Hpl" as "(_ & Hs & _)";
          by iDestruct (secret_in_l_publicly_related HPriv Hcons with "Hmap Hs Hb") as "[]").
all: try (iDestruct "Hpl" as "(Hs & _)";
          iDestruct (publicly_related_TKey_term with "Hk") as %[? ->];
          rewrite publicly_related_TKey; iDestruct "Hk" as "[_ Hk']";
          by iDestruct (secret_in_l_publicly_related HPriv Hcons with "Hmap Hs Hk'") as "[]").
- iDestruct "Hpl" as "([Hl _] & Himpl & Hb2)".
  iPoseProof (publicly_related_linked_in_l HPriv Hcons with "Hmap Hrel Hk Hl") as "#Hk2".
  iSplit; first done.
  iDestruct "Hb2" as "[Hb2|[Hb2 _]]"; first done.
  by iApply (publicly_related_linked_in_l HPriv Hcons with "Hmap Hrel Hb Hb2").
- iDestruct "Hpl" as "([Hl _] & _ & Hb2)".
  iPoseProof (publicly_related_linked_in_l HPriv Hcons with "Hmap Hrel Hk Hl") as "#Hk2".
  by iSplit.
- iDestruct "Hpl" as "([Hl _] & Himpl)".
  iPoseProof (publicly_related_linked_in_l HPriv Hcons with "Hmap Hrel Hk Hl") as "#Hk2".
  iSplit; first done. iApply "Himpl".
  rewrite publicly_related_TKey. by iDestruct "Hk2" as "[_ ?]".
Qed.

#[local] Lemma publicly_related_TSeal_parts_r pub_r flow_r {k b k' b' k1 b1} :
  public_rel_Private_r_protected pub_r flow_r →
  public_rel_flow_r_consistent pub_r flow_r →
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  public_rel_Public_r_consistent pub_r -∗
  PUB⟨k1, k'⟩ -∗ PUB⟨b1, b'⟩ -∗ PUB⟨TSeal k b, TSeal k' b'⟩ -∗
  PUB⟨k, k'⟩ ∧ PUB⟨b, b'⟩.
Proof.
move=> HPriv Hcons. iIntros "Hmap #Hrel #Hk #Hb #Ht".
rewrite publicly_related_TSeal.
iDestruct "Ht" as "[[? ?]|(_ & _ & _ & #Hpl)]"; first by iSplit.
case: k => [?|? ?|?|kt s|? ?|?|? ? ?]; try by iDestruct "Hpl" as "[]".
case: k' => [?|? ?|?|kt' s'|? ?|?|? ? ?]; try by iDestruct "Hpl" as "[]".
case: kt; case: kt'; try by iDestruct "Hpl" as "[]".
all: try (iDestruct "Hpl" as "(_ & _ & Hs)";
          by iDestruct (secret_in_r_publicly_related HPriv Hcons with "Hmap Hs Hb") as "[]").
all: try (iDestruct "Hpl" as "(_ & _ & Hs)";
          iDestruct (publicly_related_term_TKey with "Hk") as %[? ->];
          rewrite publicly_related_TKey; iDestruct "Hk" as "[_ Hk']";
          by iDestruct (secret_in_r_publicly_related HPriv Hcons with "Hmap Hs Hk'") as "[]").
- iDestruct "Hpl" as "([_ Hl] & Himpl & Hb2)".
  iPoseProof (publicly_related_linked_in_r HPriv Hcons with "Hmap Hrel Hk Hl") as "#Hk2".
  iSplit; first done.
  iDestruct "Hb2" as "[Hb2|[_ Hb2]]"; first done.
  by iApply (publicly_related_linked_in_r HPriv Hcons with "Hmap Hrel Hb Hb2").
- iDestruct "Hpl" as "([_ Hl] & _ & Hb2)".
  iPoseProof (publicly_related_linked_in_r HPriv Hcons with "Hmap Hrel Hk Hl") as "#Hk2".
  by iSplit.
- iDestruct "Hpl" as "([_ Hl] & Himpl)".
  iPoseProof (publicly_related_linked_in_r HPriv Hcons with "Hmap Hrel Hk Hl") as "#Hk2".
  iSplit; first done. iApply "Himpl".
  rewrite publicly_related_TKey. by iDestruct "Hk2" as "[_ ?]".
Qed.

End Protection.

Section PartBij.

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
  by iApply (publicly_linked_in_l_agree with "Hel1 Hel2").
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
- iDestruct (publicly_related_TSeal_term with "H1") as "[(%k1' & %b1' & ->)|[Hs1 Hsec1]]";
  iDestruct (publicly_related_TSeal_term with "H2") as "[(%k2' & %b2' & ->)|[Hs2 Hsec2]]".
  + iDestruct (publicly_related_TSeal with "H1") as "[[Hk1 Hb1]|(_ & _ & [Hs1 _] & _)]";
    iDestruct (publicly_related_TSeal with "H2") as "[[Hk2 Hb2]|(_ & _ & [Hs2 _] & _)]".
    * iDestruct ("IH" with "Hmap_l Hpub_consistent Hk1 Hk2") as %->.
      by iDestruct ("IH1" with "Hmap_l Hpub_consistent Hb1 Hb2") as %->.
    * iDestruct (publicly_related_TSeal_parts_l HPriv_l Hflow_l_cons
                   with "Hmap_l Hpub_consistent Hk1 Hb1 H2") as "#[Hk2 Hb2]".
      iDestruct ("IH" with "Hmap_l Hpub_consistent Hk1 Hk2") as %->.
      by iDestruct ("IH1" with "Hmap_l Hpub_consistent Hb1 Hb2") as %->.
    * iDestruct (publicly_related_TSeal_parts_l HPriv_l Hflow_l_cons
                   with "Hmap_l Hpub_consistent Hk2 Hb2 H1") as "#[Hk1 Hb1]".
      iDestruct ("IH" with "Hmap_l Hpub_consistent Hk1 Hk2") as %->.
      by iDestruct ("IH1" with "Hmap_l Hpub_consistent Hb1 Hb2") as %->.
    * by iDestruct (sealed_under_l_agree with "Hs1 Hs2") as %?.
  + rewrite publicly_related_TSeal.
    iDestruct "H1" as "[[Hk1 Hb1]|(_ & _ & [Hs1 _] & _)]".
    * by iDestruct (publicly_related_TSeal_secret_l HPriv_l Hflow_l_cons
                      with "Hmap_l Hsec2 Hk1 Hb1") as "[]".
    * by iDestruct (sealed_under_l_agree with "Hs1 Hs2") as %?.
  + rewrite publicly_related_TSeal.
    iDestruct "H2" as "[[Hk2 Hb2]|(_ & _ & [Hs2 _] & _)]".
    * by iDestruct (publicly_related_TSeal_secret_l HPriv_l Hflow_l_cons
                      with "Hmap_l Hsec1 Hk2 Hb2") as "[]".
    * by iDestruct (sealed_under_l_agree with "Hs1 Hs2") as %?.
  + by iDestruct (sealed_under_l_agree with "Hs1 Hs2") as %?.
- iDestruct (publicly_related_THash_term with "H1") as "[(%s1' & ->)|[Hel1 Hsecret]]";
  iDestruct (publicly_related_THash_term with "H2") as "[(%s2' & ->)|[Hel2 Hsecret']]".
  + rewrite !publicly_related_THash.
    iDestruct "H1" as "[H1|(_ & _ & Hel1 & [Hpriv1 _])]";
    iDestruct "H2" as "[H2|(_ & _ & Hel2 & [Hpriv2 _])]".
    * by iDestruct ("IH" with "Hmap_l Hpub_consistent H1 H2") as %->.
    * iPoseProof (publicly_related_linked_in_l HPriv_l Hflow_l_cons
                    with "Hmap_l Hpub_consistent H1 Hpriv2") as "#H2".
      by iDestruct ("IH" with "Hmap_l Hpub_consistent H1 H2") as %->.
    * iPoseProof (publicly_related_linked_in_l HPriv_l Hflow_l_cons
                    with "Hmap_l Hpub_consistent H2 Hpriv1") as "#H1".
      by iDestruct ("IH" with "Hmap_l Hpub_consistent H1 H2") as %->.
    * iDestruct (publicly_linked_agree_l with "Hel1 Hel2") as %Heq.
      by injection Heq as ->.
  + iDestruct (secret_in_l_lookup with "Hmap_l Hsecret'") as %Hs.
    rewrite publicly_related_THash.
    iDestruct "H1" as "[H1|(_ & _ & Hel1 & _)]".
    * by iPoseProof (publicly_related_protected_l HPriv_l Hflow_l_cons
                      (or_introl (ex_intro _ _ (conj Hs I))) with "Hmap_l H1") as "[]".
    * iDestruct "Hel1" as "[Hel1 _]". by iApply (publicly_linked_in_l_agree with "Hel1 Hel2").
  + iDestruct (secret_in_l_lookup with "Hmap_l Hsecret") as %Hs.
    rewrite publicly_related_THash.
    iDestruct "H2" as "[H2|(_ & _ & Hel2 & _)]".
    * by iPoseProof (publicly_related_protected_l HPriv_l Hflow_l_cons
                      (or_introl (ex_intro _ _ (conj Hs I))) with "Hmap_l H2") as "[]".
    * iDestruct "Hel2" as "[Hel2 _]". by iApply (publicly_linked_in_l_agree with "Hel1 Hel2").
  + by iApply (publicly_linked_in_l_agree with "Hel1 Hel2").
- by iDestruct "H1" as "(_ & _ & [])".
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
  by iApply (publicly_linked_in_r_agree with "Hel1 Hel2").
- case: t1 => /= *; try by iDestruct "H1" as "(_ & _ & [])".
  case: t2 => /= *; try by iDestruct "H2" as "(_ & _ & [])".
  iDestruct "H1" as "(_ & _ & -> & H1)". iDestruct "H2" as "(_ & _ & -> & H2)".
  destruct kt';
    try (by iDestruct ("IH" with "Hmap_r Hpub_consistent H1 H2") as %->);
    iDestruct "H1" as "[H1|[Hel1 [_ Hpriv1]]]";
    iDestruct "H2" as "[H2|[Hel2 [_ Hpriv2]]]";
    first
      [ by iDestruct ("IH" with "Hmap_r Hpub_consistent H1 H2") as %->
      | iPoseProof (publicly_related_linked_in_r HPriv_r Hflow_r_cons
                      with "Hmap_r Hpub_consistent H1 Hpriv2") as "#H2";
        by iDestruct ("IH" with "Hmap_r Hpub_consistent H1 H2") as %->
      | iPoseProof (publicly_related_linked_in_r HPriv_r Hflow_r_cons
                      with "Hmap_r Hpub_consistent H2 Hpriv1") as "#H1";
        by iDestruct ("IH" with "Hmap_r Hpub_consistent H1 H2") as %->
      | by (iDestruct (publicly_linked_agree_r with "Hel1 Hel2") as %Heq;
            injection Heq as ->) ].
- iDestruct (publicly_related_term_TSeal with "H1") as "[(%k1 & %b1 & ->)|[Hs1 Hsec1]]";
  iDestruct (publicly_related_term_TSeal with "H2") as "[(%k2 & %b2 & ->)|[Hs2 Hsec2]]".
  + iDestruct (publicly_related_TSeal with "H1") as "[[Hk1 Hb1]|(_ & _ & [_ Hs1] & _)]";
    iDestruct (publicly_related_TSeal with "H2") as "[[Hk2 Hb2]|(_ & _ & [_ Hs2] & _)]".
    * iDestruct ("IH" with "Hmap_r Hpub_consistent Hk1 Hk2") as %->.
      by iDestruct ("IH1" with "Hmap_r Hpub_consistent Hb1 Hb2") as %->.
    * iDestruct (publicly_related_TSeal_parts_r HPriv_r Hflow_r_cons
                   with "Hmap_r Hpub_consistent Hk1 Hb1 H2") as "#[Hk2 Hb2]".
      iDestruct ("IH" with "Hmap_r Hpub_consistent Hk1 Hk2") as %->.
      by iDestruct ("IH1" with "Hmap_r Hpub_consistent Hb1 Hb2") as %->.
    * iDestruct (publicly_related_TSeal_parts_r HPriv_r Hflow_r_cons
                   with "Hmap_r Hpub_consistent Hk2 Hb2 H1") as "#[Hk1 Hb1]".
      iDestruct ("IH" with "Hmap_r Hpub_consistent Hk1 Hk2") as %->.
      by iDestruct ("IH1" with "Hmap_r Hpub_consistent Hb1 Hb2") as %->.
    * by iDestruct (sealed_under_r_agree with "Hs1 Hs2") as %?.
  + rewrite publicly_related_TSeal.
    iDestruct "H1" as "[[Hk1 Hb1]|(_ & _ & [_ Hs1] & _)]".
    * by iDestruct (publicly_related_TSeal_secret_r HPriv_r Hflow_r_cons
                      with "Hmap_r Hsec2 Hk1 Hb1") as "[]".
    * by iDestruct (sealed_under_r_agree with "Hs1 Hs2") as %?.
  + rewrite publicly_related_TSeal.
    iDestruct "H2" as "[[Hk2 Hb2]|(_ & _ & [_ Hs2] & _)]".
    * by iDestruct (publicly_related_TSeal_secret_r HPriv_r Hflow_r_cons
                      with "Hmap_r Hsec1 Hk2 Hb2") as "[]".
    * by iDestruct (sealed_under_r_agree with "Hs1 Hs2") as %?.
  + by iDestruct (sealed_under_r_agree with "Hs1 Hs2") as %?.
- iDestruct (publicly_related_term_THash with "H1") as "[(%s1 & ->)|[Hel1 Hsecret]]";
  iDestruct (publicly_related_term_THash with "H2") as "[(%s2 & ->)|[Hel2 Hsecret']]".
  + rewrite !publicly_related_THash.
    iDestruct "H1" as "[H1|(_ & _ & Hel1 & [_ Hpriv1])]";
    iDestruct "H2" as "[H2|(_ & _ & Hel2 & [_ Hpriv2])]".
    * by iDestruct ("IH" with "Hmap_r Hpub_consistent H1 H2") as %->.
    * iPoseProof (publicly_related_linked_in_r HPriv_r Hflow_r_cons
                    with "Hmap_r Hpub_consistent H1 Hpriv2") as "#H2".
      by iDestruct ("IH" with "Hmap_r Hpub_consistent H1 H2") as %->.
    * iPoseProof (publicly_related_linked_in_r HPriv_r Hflow_r_cons
                    with "Hmap_r Hpub_consistent H2 Hpriv1") as "#H1".
      by iDestruct ("IH" with "Hmap_r Hpub_consistent H1 H2") as %->.
    * iDestruct (publicly_linked_agree_r with "Hel1 Hel2") as %Heq.
      by injection Heq as ->.
  + iDestruct (secret_in_r_lookup with "Hmap_r Hsecret'") as %Hs.
    rewrite publicly_related_THash.
    iDestruct "H1" as "[H1|(_ & _ & Hel1 & _)]".
    * by iPoseProof (publicly_related_protected_r HPriv_r Hflow_r_cons
                      (or_introl (ex_intro _ _ (conj Hs I))) with "Hmap_r H1") as "[]".
    * iDestruct "Hel1" as "[_ Hel1]". by iApply (publicly_linked_in_r_agree with "Hel1 Hel2").
  + iDestruct (secret_in_r_lookup with "Hmap_r Hsecret") as %Hs.
    rewrite publicly_related_THash.
    iDestruct "H2" as "[H2|(_ & _ & Hel2 & _)]".
    * by iPoseProof (publicly_related_protected_r HPriv_r Hflow_r_cons
                      (or_introl (ex_intro _ _ (conj Hs I))) with "Hmap_r H2") as "[]".
    * iDestruct "Hel2" as "[_ Hel2]". by iApply (publicly_linked_in_r_agree with "Hel1 Hel2").
  + by iApply (publicly_linked_in_r_agree with "Hel1 Hel2").
- by case: t1 => /= *; iDestruct "H1" as "(_ & _ & [])".
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
iIntros "#Hk #[[_ Ht]|(_ & _ & _ & #Hrest)]"; first done.
case: k_t k_t' => // kt k1 [] // kt' k1' in k_t_k k_t_k' *.
case: kt k_t_k => // - [<-]; case: kt' k_t_k' => // - [<-]; iSimpl in "Hrest".
all: try (rewrite publicly_related_TKey; by iDestruct "Hk" as "[% _]").
- iDestruct "Hrest" as "(_ & Hrest & _)". iApply "Hrest". rewrite publicly_related_TKey.
  by iDestruct "Hk" as "[??]".
- by iDestruct "Hrest" as "(_ & _ & ?)".
- iDestruct "Hrest" as "(_ & Hrest)". iApply "Hrest". rewrite publicly_related_TKey.
  by iDestruct "Hk" as "[??]".
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
iIntros "#[[H _]|(_ & _ & _ & Hbox)]"; first by iLeft.
iRight. case: k_t' => [?|? ?|?|kt' s'|? ?|?|? ? ?]; try by iDestruct "Hbox" as "[]".
case: kt'; try by iDestruct "Hbox" as "[]".
iDestruct "Hbox" as "(_ & Hv & _)". iExists s'. by iSplit.
Qed.

#[local] Lemma publicly_related_TSeal_Sign_linked_r k_t b s' b' :
  PUB⟨TSeal k_t b, TSeal (TKey Sign s') b'⟩ -∗
  PUB⟨k_t, TKey Sign s'⟩ ∨
  (∃ s, ⌜k_t = TKey Sign s⌝ ∧ PUB⟨TKey Verify s, TKey Verify s'⟩).
Proof.
rewrite publicly_related_TSeal.
iIntros "#[[H _]|(_ & _ & _ & Hbox)]"; first by iLeft.
iRight. case: k_t => [?|? ?|?|kt s|? ?|?|? ? ?]; try by iDestruct "Hbox" as "[]".
case: kt; try by iDestruct "Hbox" as "[]".
iDestruct "Hbox" as "(_ & Hv & _)". iExists s. by iSplit.
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
  iDestruct (publicly_related_TSeal_term with "Ht") as "[(%k_t' & %b' & ->)|[_ Hsec]]".
- (* Asymmetric encryption, [t'] is a ciphertext. *)
  rewrite publicly_related_TKey. iDestruct "Hk" as "[_ #Hs]".
  iAssert (PUB⟨TKey AEnc s, k_t'⟩) as "#Hkk".
  { rewrite publicly_related_TSeal.
    iDestruct "Ht" as "[[Hkk _]|(_ & _ & _ & #Hbox)]"; first done.
    case: k_t' => [?|? ?|?|kt' s'|? ?|?|? ? ?]; try by iDestruct "Hbox" as "[]".
    case: kt'; try by iDestruct "Hbox" as "[]".
    - iDestruct "Hbox" as "([Hlink _] & _)".
      iDestruct (publicly_related_linked_key_l HPriv_l Hflow_l_cons
                   with "Hmap_l Hpub_consistent Hlink") as "[Hkk|Hno]"; first done.
      by iDestruct ("Hno" with "Hs") as "[]".
    - iDestruct "Hbox" as "(Hsec & _)".
      by iDestruct (secret_in_l_publicly_related HPriv_l Hflow_l_cons
                      with "Hmap_l Hsec Hs") as "[]". }
  iDestruct (publicly_related_TKey_term with "Hkk") as %[s' ->].
  rewrite publicly_related_TKey. iDestruct "Hkk" as "[_ Hkk]".
  iAssert (PUB⟨s, s'⟩ ∨ linked s s')%I as "#Hkk'".
  { iDestruct "Hkk" as "[?|(_ & _ & _ & ?)]"; by [iLeft|iRight]. }
  iDestruct (publicly_related_seed_agree_l HPriv_l Hflow_l_cons
               with "Hmap_l Hpub_consistent Hs Hkk'") as %<-.
  iPureIntro. by apply: Hdone.
- (* Asymmetric encryption, [t'] is not a ciphertext: impossible. *)
  rewrite publicly_related_TKey. iDestruct "Hk" as "[_ #Hs]".
  iDestruct "Hsec" as "[Hsec _]". iExFalso.
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
  by iDestruct "Hsec" as "[]".
- (* Symmetric encryption, [t'] is a ciphertext. *)
  rewrite publicly_related_TKey. iDestruct "Hk" as "[_ #Hs]".
  iAssert (PUB⟨TKey SEnc s, k_t'⟩) as "#Hkk".
  { rewrite publicly_related_TSeal.
    iDestruct "Ht" as "[[Hkk _]|(_ & _ & _ & #Hbox)]"; first done.
    case: k_t' => [?|? ?|?|kt' s'|? ?|?|? ? ?]; try by iDestruct "Hbox" as "[]".
    case: kt'; try by iDestruct "Hbox" as "[]".
    - iDestruct "Hbox" as "[Hsec _]".
      by iDestruct (secret_in_l_publicly_related HPriv_l Hflow_l_cons
                      with "Hmap_l Hsec Hs") as "[]".
    - iDestruct "Hbox" as "([Hlink _] & _)".
      iDestruct (publicly_related_linked_key_l HPriv_l Hflow_l_cons
                   with "Hmap_l Hpub_consistent Hlink") as "[Hkk|Hno]"; first done.
      by iDestruct ("Hno" with "Hs") as "[]". }
  iDestruct (publicly_related_TKey_term with "Hkk") as %[s' ->].
  rewrite publicly_related_TKey. iDestruct "Hkk" as "[_ Hkk]".
  iDestruct (publicly_related_part_bij_1_auth HPriv_l Hflow_l_cons
               with "Hmap_l Hpub_consistent Hs Hkk") as %<-.
  iPureIntro. by apply: Hdone.
- (* Symmetric encryption, [t'] is not a ciphertext: impossible. *)
  rewrite publicly_related_TKey. iDestruct "Hk" as "[_ #Hs]". iExFalso.
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
  iDestruct (publicly_related_term_TSeal with "Ht") as "[(%k_t & %b & ->)|[_ Hsec]]".
- rewrite publicly_related_TKey. iDestruct "Hk" as "[_ #Hs]".
  iAssert (PUB⟨k_t, TKey AEnc s'⟩) as "#Hkk".
  { rewrite publicly_related_TSeal.
    iDestruct "Ht" as "[[Hkk _]|(_ & _ & _ & #Hbox)]"; first done.
    case: k_t => [?|? ?|?|kt s|? ?|?|? ? ?]; try by iDestruct "Hbox" as "[]".
    case: kt; try by iDestruct "Hbox" as "[]".
    - iDestruct "Hbox" as "([_ Hlink] & _)".
      iDestruct (publicly_related_linked_key_r HPriv_r Hflow_r_cons
                   with "Hmap_r Hpub_consistent Hlink") as "[Hkk|Hno]"; first done.
      by iDestruct ("Hno" with "Hs") as "[]".
    - iDestruct "Hbox" as "(_ & Hsec & _)".
      by iDestruct (secret_in_r_publicly_related HPriv_r Hflow_r_cons
                      with "Hmap_r Hsec Hs") as "[]". }
  iDestruct (publicly_related_term_TKey with "Hkk") as %[s ->].
  rewrite publicly_related_TKey. iDestruct "Hkk" as "[_ Hkk]".
  iAssert (PUB⟨s, s'⟩ ∨ linked s s')%I as "#Hkk'".
  { iDestruct "Hkk" as "[?|(_ & _ & _ & ?)]"; by [iLeft|iRight]. }
  iDestruct (publicly_related_seed_agree_r HPriv_r Hflow_r_cons
               with "Hmap_r Hpub_consistent Hs Hkk'") as %<-.
  iPureIntro. by apply: Hdone.
- rewrite publicly_related_TKey. iDestruct "Hk" as "[_ #Hs]".
  iDestruct "Hsec" as "[Hsec _]". iExFalso.
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
- by iDestruct "Hsec" as "[]".
- rewrite publicly_related_TKey. iDestruct "Hk" as "[_ #Hs]".
  iAssert (PUB⟨k_t, TKey SEnc s'⟩) as "#Hkk".
  { rewrite publicly_related_TSeal.
    iDestruct "Ht" as "[[Hkk _]|(_ & _ & _ & #Hbox)]"; first done.
    case: k_t => [?|? ?|?|kt s|? ?|?|? ? ?]; try by iDestruct "Hbox" as "[]".
    case: kt; try by iDestruct "Hbox" as "[]".
    - iDestruct "Hbox" as "(_ & _ & Hsec)".
      by iDestruct (secret_in_r_publicly_related HPriv_r Hflow_r_cons
                      with "Hmap_r Hsec Hs") as "[]".
    - iDestruct "Hbox" as "([_ Hlink] & _)".
      iDestruct (publicly_related_linked_key_r HPriv_r Hflow_r_cons
                   with "Hmap_r Hpub_consistent Hlink") as "[Hkk|Hno]"; first done.
      by iDestruct ("Hno" with "Hs") as "[]". }
  iDestruct (publicly_related_term_TKey with "Hkk") as %[s ->].
  rewrite publicly_related_TKey. iDestruct "Hkk" as "[_ Hkk]".
  iDestruct (publicly_related_part_bij_2_auth HPriv_r Hflow_r_cons
               with "Hmap_r Hpub_consistent Hs Hkk") as %<-.
  iPureIntro. by apply: Hdone.
- rewrite publicly_related_TKey. iDestruct "Hk" as "[_ #Hs]". iExFalso.
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
  | Some u, Some u' =>
    PUB⟨u, u'⟩ ∨ sealed_under (Spec.pkey sk) (Spec.pkey sk') u u'
  | Some u, None =>
    sealed_under_l (Spec.pkey sk) u t' ∧ secret_in_l (seed_of_aenc_key sk) ∧ secret_in_l u
  | None, Some u' =>
    sealed_under_r (Spec.pkey sk') u' t ∧ secret_in_r (seed_of_aenc_key sk') ∧ secret_in_r u'
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
  iDestruct (publicly_related_TSeal with "Ht") as "[[_ Hu]|(_ & _ & Hsu & _)]";
    iModIntro; by [iLeft|iRight].
- move/Spec.open_aenc_Some: (eL) => ?; subst t.
  iDestruct (publicly_related_TSeal_term with "Ht") as "[(%k' & %u' & ->)|?]";
    last by iModIntro.
  have Hk' : k' ≠ TKey AEnc sA'.
  { move=> ?; subst k'.
    have := proj2 (Spec.open_aenc_Some sA' (TSeal (TKey AEnc sA') u') u') eq_refl.
    by rewrite eR. }
  rewrite publicly_related_TSeal.
  iDestruct "Ht" as "[[Hk _]|(_ & _ & [Hsu _] & #Hbox)]".
  + iMod (publicly_related_part_bij' with "Hctx Hpk Hk") as %Hiff; first done.
    by case: Hk'; symmetry; apply Hiff.
  + clear eR. case: k' Hk' => [?|? ?|?|kt' s'|? ?|?|? ? ?] Hk'; try by iDestruct "Hbox" as "[]".
    case: kt' Hk' => Hk'; try by iDestruct "Hbox" as "[]".
    * iDestruct "Hbox" as "([Hkl _] & _)".
      iDestruct (linked_in_l_publicly_linked_in_l with "Hkl Hlink_l") as %?.
      by case: Hk'; congruence.
    * iDestruct "Hbox" as "(Hs & Hu & _)". iModIntro. by iFrame "Hsu Hs Hu".
- move/Spec.open_aenc_Some: (eR) => ?; subst t'.
  iDestruct (publicly_related_term_TSeal with "Ht") as "[(%k & %u & ->)|?]";
    last by iModIntro.
  have Hk : k ≠ TKey AEnc sA.
  { move=> ?; subst k.
    have := proj2 (Spec.open_aenc_Some sA (TSeal (TKey AEnc sA) u) u) eq_refl.
    by rewrite eL. }
  rewrite publicly_related_TSeal.
  iDestruct "Ht" as "[[Hk _]|(_ & _ & [_ Hsu] & #Hbox)]".
  + iMod (publicly_related_part_bij' with "Hctx Hk Hpk") as %Hiff; first done.
    by case: Hk; apply Hiff.
  + clear eL. case: k Hk => [?|? ?|?|kt s|? ?|?|? ? ?] Hk; try by iDestruct "Hbox" as "[]".
    case: kt Hk => Hk; try by iDestruct "Hbox" as "[]".
    * iDestruct "Hbox" as "([_ Hkr] & _)".
      iDestruct (linked_in_r_publicly_linked_in_r with "Hkr Hlink_r") as %?.
      by case: Hk; congruence.
    * iDestruct "Hbox" as "(_ & Hs & Hu)". iModIntro. by iFrame "Hsu Hs Hu".
- by iModIntro.
Qed.

Lemma publicly_related_open_senc_fupd E (k k' : senc_key) t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  secret_in_l (seed_of_senc_key k) -∗
  secret_in_r (seed_of_senc_key k') -∗
  PUB⟨t, t'⟩ ={E}=∗
  match Spec.open k t, Spec.open k' t' with
  | Some u, Some u' => sealed_under k k' u u'
  | Some u, None => sealed_under_l k u t'
  | None, Some u' => sealed_under_r k' u' t
  | None, None => True
  end.
Proof.
move=> HE. case: k k' => [s] [s'].
rewrite [term_of_senc_key]unlock /=.
iIntros "#Hctx #Hs #Hs' #Ht".
case eL: (Spec.open (TKey SEnc s) t) => [u|];
case eR: (Spec.open (TKey SEnc s') t') => [u'|]; iSimpl.
- move/Spec.open_senc_Some: (eL) => ?; subst t.
  move/Spec.open_senc_Some: (eR) => ?; subst t'.
  iDestruct (publicly_related_TSeal with "Ht") as "[[Hk _]|(_ & _ & Hsu & _)]";
    last by iModIntro.
  rewrite publicly_related_TKey. iDestruct "Hk" as "[_ Hk]".
  by iMod (secret_in_l_publicly_related_fupd with "Hctx Hs Hk") as "[]".
- move/Spec.open_senc_Some: (eL) => ?; subst t.
  iDestruct (publicly_related_TSeal_term with "Ht") as "[(%k'' & %u'' & ->)|[? _]]";
    last by iModIntro.
  iDestruct (publicly_related_TSeal with "Ht") as "[[Hk _]|(_ & _ & [Hsu _] & _)]";
    last by iModIntro.
  iDestruct (publicly_related_TKey_term with "Hk") as %[s'' ->].
  rewrite publicly_related_TKey. iDestruct "Hk" as "[_ Hk]".
  by iMod (secret_in_l_publicly_related_fupd with "Hctx Hs Hk") as "[]".
- move/Spec.open_senc_Some: (eR) => ?; subst t'.
  iDestruct (publicly_related_term_TSeal with "Ht") as "[(%k0 & %u0 & ->)|[? _]]";
    last by iModIntro.
  iDestruct (publicly_related_TSeal with "Ht") as "[[Hk _]|(_ & _ & [_ Hsu] & _)]";
    last by iModIntro.
  iDestruct (publicly_related_term_TKey with "Hk") as %[s0 ->].
  rewrite publicly_related_TKey. iDestruct "Hk" as "[_ Hk]".
  by iMod (secret_in_r_publicly_related_fupd with "Hctx Hs' Hk") as "[]".
- by iModIntro.
Qed.

End HonestDecryption.

End RelProperties.
