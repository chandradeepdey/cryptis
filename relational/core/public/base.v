(** * The relation [PUB] and its invariant

[PUB⟨t, t'⟩] says that the attacker cannot tell [t] in the left run apart
from [t'] in the right run.

** Section [Public]

- [Tokens]: the ghost state of a term.  A ciphertext keeps it on its key,
  so that whoever owns the key decides how its ciphertexts are treated.
  Any other term keeps it on itself.
- [States]: whether the runs treat two terms as the same ([linked]),
  whether the attacker may see them too ([publicly_linked]), and whether a
  term stays secret ([secret_in_l]).
- [Subterms]: the parts of a term, and chains of parts.
- [Relation]: two terms are related if they are built the same way from
  related parts, or if they are publicly linked and look alike to the
  attacker.
- [Invariant]: a hidden term holds back the parts on a chain down to a
  secret term, a nonce or a linked term, and a term becomes public only
  when nothing holds it back.  A hidden term records the chain it is
  protected via when it enters the states map, so that whoever knows the
  record can later tell which parts it holds back.  A public ciphertext
  whose payload is hidden
  holds its key back the same way.

** Section [PublicProperties]

- [Constructors] and [Ciphertexts]: what may be related to each kind of
  term.
- [Protection]: a hidden term is related to nothing.
- [Release]: once a key is public, its ciphertexts have related payloads.
- [Admission]: a term in the states map has used up its states token.
- [PartBij]: a term is related to at most one term in the other run.
- [AttackerDecryption]: decrypting related terms with related keys
  succeeds in both runs or in neither, with related results.
- [HonestDecryption]: what an honest party gets when it decrypts with its
  own key.

Lemmas ending in [_fupd] open the invariant themselves. *)

From iris.algebra Require Import gmap gset.
From reloc Require Import reloc.
From cryptis Require Import cryptis.
From cryptis.hyper.core Require Import minted_spec term_meta_spec.
From cryptis.hyper.core.public Require Import state.
Import State.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation hypercryptisN := (cryptisN.@"hyper").
Abbreviation sealN := (hypercryptisN.@"seal").
Abbreviation termN := (hypercryptisN.@"term").
Abbreviation holdN := (hypercryptisN.@"hold").

Class publicGpreS Σ := PublicGPreS {
  #[local] publicGpreS_states :: inG Σ (authUR (gmapUR term (authUR (optionUR stateR))));
  #[local] publicGpreS_term_meta :: term_metaGpreS Σ;
}.

Class publicGS Σ := PublicGS {
  #[global] public_states_inG :: inG Σ (authUR (gmapUR term (authUR (optionUR stateR))));
  #[global] public_term_meta_inG :: term_metaGS Σ;
  #[global] public_term_meta_spec_inG :: term_meta_specGS Σ;
  public_states_l : gname;
  public_states_r : gname;
}.

Definition publicΣ : gFunctors :=
  #[GFunctor (authUR (gmapUR term (authUR (optionUR stateR))));
    term_metaΣ].

#[global] Instance subG_publicGpreS Σ : subG publicΣ Σ → publicGpreS Σ.
Proof. solve_inG. Qed.

Section Public.

Context `{!relocG Σ, !publicGS Σ}.

Abbreviation iProp := (iProp Σ).
Abbreviation iPropO := (iPropO Σ).

Implicit Types t tsub tsup troot tprot t'sub t'sup t'root t'prot : term.
Implicit Types st : state.
Implicit Types states_l states_r : gmap term state.
Implicit Types P : term -> term -> iProp.

Section Tokens.

Definition seal_namespace (t : term) : namespace := sealN.@t.

Definition home_of_term t : term * namespace :=
  match t with
  | TSeal k t1 => (k, seal_namespace t1)
  | _ => (t, termN)
  end.

Definition public_token_l t : iProp := term_token (home_of_term t).1 (↑(home_of_term t).2).
Definition public_token_r t' : iProp := term_token_spec (home_of_term t').1 (↑(home_of_term t').2).

Definition never_sealed_under k k' E E' : iProp :=
  term_token k E ∗ term_token_spec k' E'.

Definition states_token_l t : iProp := term_token (home_of_term t).1 (↑(home_of_term t).2.@"states").
Definition states_token_r t' : iProp := term_token_spec (home_of_term t').1 (↑(home_of_term t').2.@"states").
Definition states_meta_l t : iProp := term_meta (home_of_term t).1 ((home_of_term t).2.@"states".@"in") ().
Definition states_meta_r t' : iProp := term_meta_spec (home_of_term t').1 ((home_of_term t').2.@"states".@"in") ().
Definition protected_via_l t (path : list term) tprot : iProp :=
  term_meta (home_of_term t).1 ((home_of_term t).2.@"states".@"via") (path, tprot).
Definition protected_via_r t' (path : list term) t'prot : iProp :=
  term_meta_spec (home_of_term t').1 ((home_of_term t').2.@"states".@"via") (path, t'prot).

Definition prots_token_l t : iProp := term_token (home_of_term t).1 (↑(home_of_term t).2.@"prots").
Definition prots_token_r t' : iProp := term_token_spec (home_of_term t').1 (↑(home_of_term t').2.@"prots").

Definition holds_subterm_l t tsub : iProp :=
  term_token (home_of_term tsub).1 (↑(home_of_term tsub).2.@"prots".@t).
Definition holds_subterm_r t' t'sub : iProp :=
  term_token_spec (home_of_term t'sub).1 (↑(home_of_term t'sub).2.@"prots".@t').

Definition seal_release_l t : iProp := term_token (home_of_term t).1 (↑(home_of_term t).2.@"release").
Definition seal_release_r t' : iProp := term_token_spec (home_of_term t').1 (↑(home_of_term t').2.@"release").

Definition holds_key_l t k : iProp := term_token k (↑holdN.@t).
Definition holds_key_r t' k' : iProp := term_token_spec k' (↑holdN.@t').

#[global] Instance protected_via_l_persistent t path tprot :
  Persistent (protected_via_l t path tprot).
Proof. apply _. Qed.

#[global] Instance protected_via_r_persistent t' path t'prot :
  Persistent (protected_via_r t' path t'prot).
Proof. apply _. Qed.

#[global] Instance states_meta_l_persistent t : Persistent (states_meta_l t).
Proof. apply _. Qed.

#[global] Instance states_meta_r_persistent t' : Persistent (states_meta_r t').
Proof. apply _. Qed.

Lemma public_token_l_split t :
  public_token_l t ⊢ states_token_l t ∗ prots_token_l t ∗ seal_release_l t.
Proof.
rewrite /public_token_l (term_token_difference _ (↑(home_of_term t).2.@"states")); last solve_ndisj.
iIntros "[$ tok]".
rewrite (term_token_difference _ (↑(home_of_term t).2.@"prots") (_ ∖ _)); last solve_ndisj.
iDestruct "tok" as "[$ tok]". iApply (term_token_drop with "tok"). solve_ndisj.
Qed.

Lemma public_token_r_split t' :
  public_token_r t' ⊢ states_token_r t' ∗ prots_token_r t' ∗ seal_release_r t'.
Proof.
rewrite /public_token_r (term_token_spec_difference _ (↑(home_of_term t').2.@"states")); last solve_ndisj.
iIntros "[$ tok]".
rewrite (term_token_spec_difference _ (↑(home_of_term t').2.@"prots") (_ ∖ _)); last solve_ndisj.
iDestruct "tok" as "[$ tok]". iApply (term_token_spec_drop with "tok"). solve_ndisj.
Qed.

Lemma states_meta_l_set t : states_token_l t ==∗ states_meta_l t.
Proof. iIntros "tok". iApply (term_meta_set with "tok"). solve_ndisj. Qed.

Lemma states_meta_r_set t' : states_token_r t' ==∗ states_meta_r t'.
Proof. iIntros "tok". iApply (term_meta_spec_set with "tok"). solve_ndisj. Qed.

Lemma protected_via_l_set t path tprot :
  states_token_l t ==∗ states_meta_l t ∗ protected_via_l t path tprot.
Proof.
iIntros "tok".
iMod (term_meta_set' (N:=(home_of_term t).2.@"states".@"in") () with "tok") as "[$ tok]";
  first solve_ndisj.
iApply (term_meta_set with "tok"). solve_ndisj.
Qed.

Lemma protected_via_r_set t' path t'prot :
  states_token_r t' ==∗ states_meta_r t' ∗ protected_via_r t' path t'prot.
Proof.
iIntros "tok".
iMod (term_meta_spec_set' (N:=(home_of_term t').2.@"states".@"in") () with "tok")
  as "[$ tok]"; first solve_ndisj.
iApply (term_meta_spec_set with "tok"). solve_ndisj.
Qed.

Lemma protected_via_l_agree t path1 tprot1 path2 tprot2 :
  protected_via_l t path1 tprot1 -∗ protected_via_l t path2 tprot2 -∗
  ⌜path1 = path2 ∧ tprot1 = tprot2⌝.
Proof.
iIntros "H1 H2". by iDestruct (term_meta_agree with "H1 H2") as %[= -> ->].
Qed.

Lemma protected_via_r_agree t' path1 t'prot1 path2 t'prot2 :
  protected_via_r t' path1 t'prot1 -∗ protected_via_r t' path2 t'prot2 -∗
  ⌜path1 = path2 ∧ t'prot1 = t'prot2⌝.
Proof.
iIntros "H1 H2". by iDestruct (term_meta_spec_agree with "H1 H2") as %[= -> ->].
Qed.

Lemma states_token_meta_l t : states_token_l t -∗ states_meta_l t -∗ False.
Proof. iIntros "tok meta". iApply (term_meta_token with "tok meta"). solve_ndisj. Qed.

Lemma states_token_meta_r t' : states_token_r t' -∗ states_meta_r t' -∗ False.
Proof. iIntros "tok meta". iApply (term_meta_spec_token with "tok meta"). solve_ndisj. Qed.

Lemma prots_token_holds_subterm_l t tsub : prots_token_l tsub -∗ holds_subterm_l t tsub -∗ False.
Proof.
iIntros "tok hold". iDestruct (term_token_disj with "tok hold") as %Hdisj.
have : ↑(home_of_term tsub).2.@"prots".@t ⊆ (↑(home_of_term tsub).2.@"prots" : coPset)
  by solve_ndisj.
pose proof (nclose_non_empty ((home_of_term tsub).2.@"prots".@t)). set_solver.
Qed.

Lemma prots_token_holds_subterm_r t' t'sub : prots_token_r t'sub -∗ holds_subterm_r t' t'sub -∗ False.
Proof.
iIntros "tok hold". iDestruct (term_token_spec_disj with "tok hold") as %Hdisj.
have : ↑(home_of_term t'sub).2.@"prots".@t' ⊆ (↑(home_of_term t'sub).2.@"prots" : coPset)
  by solve_ndisj.
pose proof (nclose_non_empty ((home_of_term t'sub).2.@"prots".@t')). set_solver.
Qed.

Lemma term_token_public_token_l t :
  (∀ k t1, t ≠ TSeal k t1) →
  term_token t ⊤ ⊢
  public_token_l t ∗ term_token t (↑sealN) ∗ term_token t (↑holdN) ∗
  term_token t (⊤ ∖ ↑hypercryptisN).
Proof.
move=> H. have -> : public_token_l t = term_token t (↑termN).
{ by case: t H => // k t1 /(_ k t1). }
rewrite (term_token_difference t (↑hypercryptisN) ⊤) //.
rewrite (term_token_difference t (↑termN) (↑hypercryptisN));
  last solve_ndisj.
rewrite (term_token_difference t (↑sealN)
           (↑hypercryptisN ∖ ↑termN)); last solve_ndisj.
rewrite (term_token_difference t (↑holdN)
           (↑hypercryptisN ∖ ↑termN ∖ ↑sealN)); last solve_ndisj.
iIntros "[(term & seal & rel & _) rest]". iFrame.
Qed.

Lemma term_token_public_token_r t' :
  (∀ k t1, t' ≠ TSeal k t1) →
  term_token_spec t' ⊤ ⊢
  public_token_r t' ∗ term_token_spec t' (↑sealN) ∗ term_token_spec t' (↑holdN) ∗
  term_token_spec t' (⊤ ∖ ↑hypercryptisN).
Proof.
move=> H. have -> : public_token_r t' = term_token_spec t' (↑termN).
{ by case: t' H => // k t1 /(_ k t1). }
rewrite (term_token_spec_difference t' (↑hypercryptisN) ⊤) //.
rewrite (term_token_spec_difference t' (↑termN)
           (↑hypercryptisN)); last solve_ndisj.
rewrite (term_token_spec_difference t' (↑sealN)
           (↑hypercryptisN ∖ ↑termN)); last solve_ndisj.
rewrite (term_token_spec_difference t' (↑holdN)
           (↑hypercryptisN ∖ ↑termN ∖ ↑sealN)); last solve_ndisj.
iIntros "[(term & seal & rel & _) rest]". iFrame.
Qed.

Lemma never_sealed_under_public_token k k' t t' E E' :
  ↑seal_namespace t ⊆ E →
  ↑seal_namespace t' ⊆ E' →
  never_sealed_under k k' E E' ⊣⊢
  public_token_l (TSeal k t) ∗ public_token_r (TSeal k' t') ∗
  never_sealed_under k k' (E ∖ ↑seal_namespace t) (E' ∖ ↑seal_namespace t').
Proof.
move=> sub sub'.
rewrite /never_sealed_under /public_token_l /public_token_r /=.
rewrite (term_token_difference k _ E) // (term_token_spec_difference k' _ E') //.
iSplit; [iIntros "[[$ ?] [$ ?]]" | iIntros "(? & ? & ? & ?)"]; iFrame.
Qed.

End Tokens.

Section States.

Definition public_states_l_auth states_l : iProp :=
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) ∗
  [∗ map] t ↦ st ∈ states_l, match st with
                            | Pending _ => own public_states_l (◯ {[ t := ●{#1/2} Some st ]})
                            | _ => emp
                            end.

Definition public_states_r_auth states_r : iProp :=
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) ∗
  [∗ map] t' ↦ st ∈ states_r, match st with
                            | Pending _ => own public_states_r (◯ {[ t' := ●{#1/2} Some st ]})
                            | _ => emp
                            end.

Definition public_states_inv states_l states_r : iProp :=
  public_states_l_auth states_l ∗
  public_states_r_auth states_r ∗
  ([∗ set] t ∈ dom states_l, states_meta_l t) ∗
  ([∗ set] t' ∈ dom states_r, states_meta_r t').

Definition pending_in_l t t' : iProp :=
  own public_states_l (◯ {[ t := ●{#1/2} Some (Pending t') ]}).

Definition pending_in_r t t' : iProp :=
  own public_states_r (◯ {[ t' := ●{#1/2} Some (Pending t) ]}).

Definition linked_in_l t t' : iProp :=
  own public_states_l (◯ {[ t := ◯ Some (Pending t') ]}).

#[global] Instance linked_in_l_persistent t t' : Persistent (linked_in_l t t').
Proof. apply _. Qed.

Definition linked_in_r t t' : iProp :=
  own public_states_r (◯ {[ t' := ◯ Some (Pending t) ]}).

#[global] Instance linked_in_r_persistent t t' : Persistent (linked_in_r t t').
Proof. apply _. Qed.

Definition linked t t' : iProp :=
  linked_in_l t t' ∧ linked_in_r t t'.

#[global] Instance linked_persistent t t' : Persistent (linked t t').
Proof. apply _. Qed.

Definition publicly_linked_in_l t t' : iProp :=
  own public_states_l (◯ {[ t := ◯ Some (PublicLink t') ]}).

#[global] Instance publicly_linked_in_l_persistent t t' : Persistent (publicly_linked_in_l t t').
Proof. apply _. Qed.

Definition publicly_linked_in_r t t' : iProp :=
  own public_states_r (◯ {[ t' := ◯ Some (PublicLink t) ]}).

#[global] Instance publicly_linked_in_r_persistent t t' : Persistent (publicly_linked_in_r t t').
Proof. apply _. Qed.

Definition publicly_linked t t' : iProp :=
  publicly_linked_in_l t t' ∧ publicly_linked_in_r t t'.

#[global] Instance publicly_linked_persistent t t' : Persistent (publicly_linked t t').
Proof. apply _. Qed.

Definition secret_in_l t : iProp :=
  own public_states_l (◯ {[ t := ◯ Some Secret ]}).

#[global] Instance secret_in_l_persistent t : Persistent (secret_in_l t).
Proof. apply _. Qed.

Definition secret_in_r t' : iProp :=
  own public_states_r (◯ {[ t' := ◯ Some Secret ]}).

#[global] Instance secret_in_r_persistent t' : Persistent (secret_in_r t').
Proof. apply _. Qed.

Lemma publicly_linked_in_l_linked_in_l t t' :
  publicly_linked_in_l t t' -∗ linked_in_l t t'.
Proof.
apply bi.entails_wand, own_mono, auth_frag_mono, singleton_included_mono, auth_frag_mono,
  Some_included_mono, Pending_included_PublicLink.
Qed.

Lemma publicly_linked_in_r_linked_in_r t t' :
  publicly_linked_in_r t t' -∗ linked_in_r t t'.
Proof.
apply bi.entails_wand, own_mono, auth_frag_mono, singleton_included_mono, auth_frag_mono,
  Some_included_mono, Pending_included_PublicLink.
Qed.

Lemma secret_in_l_linked_in_l t t' :
  secret_in_l t -∗ linked_in_l t t'.
Proof.
apply bi.entails_wand, own_mono, auth_frag_mono, singleton_included_mono, auth_frag_mono,
  Some_included_mono, Pending_included_Secret.
Qed.

Lemma secret_in_r_linked_in_r t t' :
  secret_in_r t' -∗ linked_in_r t t'.
Proof.
apply bi.entails_wand, own_mono, auth_frag_mono, singleton_included_mono, auth_frag_mono,
  Some_included_mono, Pending_included_Secret.
Qed.

Lemma secret_in_linked t t' :
  secret_in_l t -∗ secret_in_r t' -∗ linked t t'.
Proof.
iIntros "#? #?".
iSplit; [by iApply secret_in_l_linked_in_l | by iApply secret_in_r_linked_in_r].
Qed.

Lemma publicly_linked_linked t t' :
  publicly_linked t t' -∗ linked t t'.
Proof.
iIntros "#[H1 H2]". iSplit.
- by iApply publicly_linked_in_l_linked_in_l.
- by iApply publicly_linked_in_r_linked_in_r.
Qed.

Lemma public_states_l_fresh states_l t :
  ([∗ set] t ∈ dom states_l, states_meta_l t) -∗
  states_token_l t -∗
  ⌜states_l !! t = None⌝.
Proof.
iIntros "Hmeta Htt".
destruct (states_l !! t) eqn:Heq; last done.
iDestruct (big_sepS_elem_of _ _ t with "Hmeta") as "Hmeta_t"; first by apply elem_of_dom.
by iDestruct (states_token_meta_l with "Htt Hmeta_t") as "[]".
Qed.

Lemma public_states_r_fresh states_r t' :
  ([∗ set] t' ∈ dom states_r, states_meta_r t') -∗
  states_token_r t' -∗
  ⌜states_r !! t' = None⌝.
Proof.
iIntros "Hmeta Htts".
destruct (states_r !! t') eqn:Heq; last done.
iDestruct (big_sepS_elem_of _ _ t' with "Hmeta") as "Hmeta_t"; first by apply elem_of_dom.
by iDestruct (states_token_meta_r with "Htts Hmeta_t") as "[]".
Qed.

Lemma public_states_l_lookup states_l t t' :
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  pending_in_l t t' -∗
  ⌜states_l !! t = Some (Pending t')⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl _].
apply singleton_included_l in Hincl as (? & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (states_l !! t) as [st|] eqn:Heq.
- assert (●{#1 / 2} Some (Pending t') ≼ ● Some st ⋅ ◯ Some st) as H.
  { by apply Some_included in Hincl as [H_eq | ?]=> //; rewrite H_eq. }
  apply auth_auth_dfrac_included in H as [_ Heq'].
  apply leibniz_equiv in Heq'. by simplify_eq.
- apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl.
Qed.

Lemma public_states_r_lookup states_r t t' :
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  pending_in_r t t' -∗
  ⌜states_r !! t' = Some (Pending t)⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl _].
apply singleton_included_l in Hincl as (? & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (states_r !! t') as [st|] eqn:Heq.
- assert (●{#1 / 2} Some (Pending t) ≼ ● Some st ⋅ ◯ Some st) as H.
  { by apply Some_included in Hincl as [H_eq | ?]=> //; rewrite H_eq. }
  apply auth_auth_dfrac_included in H as [_ Heq'].
  apply leibniz_equiv in Heq'. by simplify_eq.
- apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl.
Qed.

#[local] Lemma public_states_l_lookup_frag states_l t st :
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  own public_states_l (◯ {[ t := ◯ Some st ]}) -∗
  ⌜∃ st1, states_l !! t = Some st1 ∧ ✓ st1 ∧ st ≼ st1⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl Hval].
apply singleton_included_l in Hincl as (? & <- & Hincl).
rewrite lookup_fmap in Hincl.
specialize (Hval t). rewrite lookup_fmap in Hval.
destruct (states_l !! t) as [st1|] eqn:Heq; last first.
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

#[local] Lemma public_states_r_lookup_frag states_r t' st :
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  own public_states_r (◯ {[ t' := ◯ Some st ]}) -∗
  ⌜∃ st1, states_r !! t' = Some st1 ∧ ✓ st1 ∧ st ≼ st1⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl Hval].
apply singleton_included_l in Hincl as (? & <- & Hincl).
rewrite lookup_fmap in Hincl.
specialize (Hval t'). rewrite lookup_fmap in Hval.
destruct (states_r !! t') as [st1|] eqn:Heq; last first.
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

Lemma linked_in_l_lookup states_l t t' :
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  linked_in_l t t' -∗
  ⌜states_l !! t = Some (Pending t') ∨
   states_l !! t = Some Secret ∨
   states_l !! t = Some (PublicLink t')⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_states_l_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by case: (Pending_included Hval Hincl) => [->|[->|->]]; eauto.
Qed.

Lemma linked_in_r_lookup states_r t t' :
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  linked_in_r t t' -∗
  ⌜states_r !! t' = Some (Pending t) ∨
   states_r !! t' = Some Secret ∨
   states_r !! t' = Some (PublicLink t)⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_states_r_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by case: (Pending_included Hval Hincl) => [->|[->|->]]; eauto.
Qed.

Lemma publicly_linked_in_l_lookup states_l t t' :
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  publicly_linked_in_l t t' -∗
  ⌜states_l !! t = Some (PublicLink t')⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_states_l_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by rewrite (PublicLink_included Hval Hincl).
Qed.

Lemma publicly_linked_in_r_lookup states_r t t' :
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  publicly_linked_in_r t t' -∗
  ⌜states_r !! t' = Some (PublicLink t)⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_states_r_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by rewrite (PublicLink_included Hval Hincl).
Qed.

Lemma secret_in_l_lookup states_l t :
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  secret_in_l t -∗
  ⌜states_l !! t = Some Secret⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_states_l_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by rewrite (Secret_included Hval Hincl).
Qed.

Lemma secret_in_r_lookup states_r t' :
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  secret_in_r t' -∗
  ⌜states_r !! t' = Some Secret⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_states_r_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by rewrite (Secret_included Hval Hincl).
Qed.

Lemma publicly_linked_lookup_l states_l t t' :
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  publicly_linked t t' -∗
  ⌜states_l !! t = Some (PublicLink t')⌝.
Proof.
iIntros "H1 [H2 _]".
by iApply (publicly_linked_in_l_lookup with "H1 H2").
Qed.

Lemma publicly_linked_lookup_r states_r t t' :
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  publicly_linked t t' -∗
  ⌜states_r !! t' = Some (PublicLink t)⌝.
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
exact: PublicLink_PublicLink_valid.
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
exact: PublicLink_PublicLink_valid.
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
exact: Pending_PublicLink_valid.
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
exact: Pending_PublicLink_valid.
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
exact: Secret_PublicLink_valid.
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
exact: Secret_PublicLink_valid.
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

End States.

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
move=> ?; iStartProof.
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

Section PublicProperties.

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

Section Protection.

#[local] Lemma same_shape_immediate_subterm_l {t1 t t'} :
  is_immediate_subterm t1 t →
  same_shape public t t' -∗ ∃ t1', PUB⟨t1, t1'⟩.
Proof.
move=> Himm.
destruct Himm; case: t' => /= *; iIntros "#Hs"; try by iDestruct "Hs" as "[]".
- iDestruct "Hs" as "[H _]". by iExists _.
- iDestruct "Hs" as "[_ H]". by iExists _.
- iDestruct "Hs" as "[_ H]". by iExists _.
- iDestruct "Hs" as "[H _]". by iExists _.
- iDestruct "Hs" as "[_ H]". by iExists _.
- by iExists _.
Qed.

#[local] Lemma same_shape_immediate_subterm_r {t1' t t'} :
  is_immediate_subterm t1' t' →
  same_shape public t t' -∗ ∃ t1, PUB⟨t1, t1'⟩.
Proof.
move=> Himm.
destruct Himm; case: t => /= *; iIntros "#Hs"; try by iDestruct "Hs" as "[]".
- iDestruct "Hs" as "[H _]". by iExists _.
- iDestruct "Hs" as "[_ H]". by iExists _.
- iDestruct "Hs" as "[_ H]". by iExists _.
- iDestruct "Hs" as "[H _]". by iExists _.
- iDestruct "Hs" as "[_ H]". by iExists _.
- by iExists _.
Qed.

#[local] Lemma subterm_path_public_l states_l m tsup t path troot :
  tsize t ≤ tsize tsup →
  (∀ x, tsize x < tsize tsup → m !! x = states_l !! x) →
  subterm_path t path troot →
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  public_states_l_deposits m -∗
  ([∗ list] t1 ∈ path, holds_subterm_l tsup t1) -∗
  ∀ t', same_shape public t t' -∗ ∃ t'root, PUB⟨troot, t'root⟩.
Proof.
move=> Hle Hagree Hpath.
elim: Hpath Hle => [troot1 t1 Himm Hle | tsub path1 troot1 t1 Himm Hpath1 IH Hle].
- iIntros "_ _ _ %t' #Hs". by iApply (same_shape_immediate_subterm_l Himm).
- iIntros "Hauth Hdeps [Hhold Hrest] %t' #Hs".
  iDestruct (same_shape_immediate_subterm_l Himm with "Hs") as "[%t'sub #Htsub]".
  have Hlt1 := is_immediate_subterm_lt Himm.
  iDestruct (public_cases with "Htsub") as "[Hs1|[Hl1 _]]".
  + iApply (IH ltac:(lia) with "Hauth Hdeps Hrest Hs1").
  + iDestruct (publicly_linked_lookup_l with "Hauth Hl1") as %Hpl.
    have Hm1 : m !! tsub = Some (PublicLink t'sub) by rewrite Hagree; last lia.
    iDestruct (big_sepM_lookup _ _ _ _ Hm1 with "Hdeps") as "[_ Hprots]".
    by iDestruct (prots_token_holds_subterm_l with "Hprots Hhold") as "[]".
Qed.

#[local] Lemma subterm_path_public_r states_r m t'sup t' path t'root :
  tsize t' ≤ tsize t'sup →
  (∀ x, tsize x < tsize t'sup → m !! x = states_r !! x) →
  subterm_path t' path t'root →
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  public_states_r_deposits m -∗
  ([∗ list] t1' ∈ path, holds_subterm_r t'sup t1') -∗
  ∀ t, same_shape public t t' -∗ ∃ troot, PUB⟨troot, t'root⟩.
Proof.
move=> Hle Hagree Hpath.
elim: Hpath Hle => [t'root1 t'1 Himm Hle | t'sub path1 t'root1 t'1 Himm Hpath1 IH Hle].
- iIntros "_ _ _ %t #Hs". by iApply (same_shape_immediate_subterm_r Himm).
- iIntros "Hauth Hdeps [Hhold Hrest] %t #Hs".
  iDestruct (same_shape_immediate_subterm_r Himm with "Hs") as "[%tsub #Htsub]".
  have Hlt1 := is_immediate_subterm_lt Himm.
  iDestruct (public_cases with "Htsub") as "[Hs1|[Hl1 _]]".
  + iApply (IH ltac:(lia) with "Hauth Hdeps Hrest Hs1").
  + iDestruct (publicly_linked_lookup_r with "Hauth Hl1") as %Hpl.
    have Hm1 : m !! t'sub = Some (PublicLink tsub) by rewrite Hagree; last lia.
    iDestruct (big_sepM_lookup _ _ _ _ Hm1 with "Hdeps") as "[_ Hprots]".
    by iDestruct (prots_token_holds_subterm_r with "Hprots Hhold") as "[]".
Qed.

#[local] Lemma public_protected_l states_l m t :
  (∀ x, tsize x ≤ tsize t → m !! x = states_l !! x) →
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  public_states_l_deposits m -∗
  ∀ st, ⌜states_l !! t = Some st ∧ not_PublicLink st⌝ →
  ∀ t', PUB⟨t, t'⟩ -∗ False.
Proof.
elim/term_lt_ind: t m => t IH m Hagree.
iIntros "Hauth Hdeps" (st [Hst Hnotpub] t') "#Hpub".
iDestruct (public_cases with "Hpub") as "[Hs|[Hl _]]"; last first.
{ iDestruct (publicly_linked_lookup_l with "Hauth Hl") as %Hpl.
  by rewrite Hst in Hpl; case: Hpl Hnotpub => -> []. }
have Hm : m !! t = Some st by rewrite Hagree.
iDestruct (big_sepM_delete _ _ t _ Hm with "Hdeps") as "[Ht Hdeps]".
have -> : (match st with
           | PublicLink t' => public_deposit_l t t' ∗ prots_token_l t
           | _ => protects_deposit_l t
           end)%I = protects_deposit_l t by case: (st) Hnotpub.
iDestruct "Ht" as "[%Hnonce|(%path & %troot & (%Hpath & Hpath & Hroot) & _)]".
{ move/is_nonceP: Hnonce => [a ->].
  by case: t' => /= *; iDestruct "Hs" as "[]". }
have Hagree_lt : ∀ x, tsize x < tsize t → delete t m !! x = states_l !! x.
{ move=> x Hx. rewrite lookup_delete_ne; [apply Hagree; lia | move=> ?; subst x; lia]. }
iDestruct (subterm_path_public_l (Nat.le_refl _) Hagree_lt Hpath
             with "Hauth Hdeps Hpath Hs") as "[%t'root #Hpub_root]".
have Hlt := subterm_path_lt Hpath.
have Hagree_root : ∀ x, tsize x ≤ tsize troot → delete t m !! x = states_l !! x.
{ move=> x Hx. apply Hagree_lt. lia. }
iDestruct "Hroot" as "[#Hsec|[[%Hnonce|[%t'root2 #Hlink]] Hhold]]".
- iDestruct (secret_in_l_lookup with "Hauth Hsec") as %Hsec.
  by iApply (IH troot Hlt (delete t m) Hagree_root with "Hauth Hdeps [] Hpub_root").
- iDestruct (public_nonce_term _ Hnonce with "Hpub_root") as "#Hl".
  iDestruct (publicly_linked_lookup_l with "Hauth Hl") as %Hst'.
  have Hm' : delete t m !! troot = Some (PublicLink t'root) by rewrite Hagree_root.
  iDestruct (big_sepM_lookup _ _ _ _ Hm' with "Hdeps") as "[_ Hprots]".
  by iDestruct (prots_token_holds_subterm_l with "Hprots Hhold") as "[]".
- iDestruct (linked_in_l_lookup with "Hauth Hlink") as %[Hst'|[Hst'|Hst']];
    try by iApply (IH troot Hlt (delete t m) Hagree_root with "Hauth Hdeps [] Hpub_root").
  have Hm' : delete t m !! troot = Some (PublicLink t'root2) by rewrite Hagree_root.
  iDestruct (big_sepM_lookup _ _ _ _ Hm' with "Hdeps") as "[_ Hprots]".
  by iDestruct (prots_token_holds_subterm_l with "Hprots Hhold") as "[]".
Qed.

#[local] Lemma public_protected_r states_r m t' :
  (∀ x, tsize x ≤ tsize t' → m !! x = states_r !! x) →
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  public_states_r_deposits m -∗
  ∀ st, ⌜states_r !! t' = Some st ∧ not_PublicLink st⌝ →
  ∀ t, PUB⟨t, t'⟩ -∗ False.
Proof.
elim/term_lt_ind: t' m => t' IH m Hagree.
iIntros "Hauth Hdeps" (st [Hst Hnotpub] t) "#Hpub".
iDestruct (public_cases with "Hpub") as "[Hs|[Hl _]]"; last first.
{ iDestruct (publicly_linked_lookup_r with "Hauth Hl") as %Hpl.
  by rewrite Hst in Hpl; case: Hpl Hnotpub => -> []. }
have Hm : m !! t' = Some st by rewrite Hagree.
iDestruct (big_sepM_delete _ _ t' _ Hm with "Hdeps") as "[Ht Hdeps]".
have -> : (match st with
           | PublicLink t => public_deposit_r t t' ∗ prots_token_r t'
           | _ => protects_deposit_r t'
           end)%I = protects_deposit_r t' by case: (st) Hnotpub.
iDestruct "Ht" as "[%Hnonce|(%path & %t'root & (%Hpath & Hpath & Hroot) & _)]".
{ move/is_nonceP: Hnonce => [a' ->].
  by case: t => /= *; iDestruct "Hs" as "[]". }
have Hagree_lt : ∀ x, tsize x < tsize t' → delete t' m !! x = states_r !! x.
{ move=> x Hx. rewrite lookup_delete_ne; [apply Hagree; lia | move=> ?; subst x; lia]. }
iDestruct (subterm_path_public_r (Nat.le_refl _) Hagree_lt Hpath
             with "Hauth Hdeps Hpath Hs") as "[%troot #Hpub_root]".
have Hlt := subterm_path_lt Hpath.
have Hagree_root : ∀ x, tsize x ≤ tsize t'root → delete t' m !! x = states_r !! x.
{ move=> x Hx. apply Hagree_lt. lia. }
iDestruct "Hroot" as "[#Hsec|[[%Hnonce|[%troot2 #Hlink]] Hhold]]".
- iDestruct (secret_in_r_lookup with "Hauth Hsec") as %Hsec.
  by iApply (IH t'root Hlt (delete t' m) Hagree_root with "Hauth Hdeps [] Hpub_root").
- iDestruct (public_term_nonce _ Hnonce with "Hpub_root") as "#Hl".
  iDestruct (publicly_linked_lookup_r with "Hauth Hl") as %Hst'.
  have Hm' : delete t' m !! t'root = Some (PublicLink troot) by rewrite Hagree_root.
  iDestruct (big_sepM_lookup _ _ _ _ Hm' with "Hdeps") as "[_ Hprots]".
  by iDestruct (prots_token_holds_subterm_r with "Hprots Hhold") as "[]".
- iDestruct (linked_in_r_lookup with "Hauth Hlink") as %[Hst'|[Hst'|Hst']];
    try by iApply (IH t'root Hlt (delete t' m) Hagree_root with "Hauth Hdeps [] Hpub_root").
  have Hm' : delete t' m !! t'root = Some (PublicLink troot2) by rewrite Hagree_root.
  iDestruct (big_sepM_lookup _ _ _ _ Hm' with "Hdeps") as "[_ Hprots]".
  by iDestruct (prots_token_holds_subterm_r with "Hprots Hhold") as "[]".
Qed.

#[local] Lemma secret_in_l_public states_l {t t'} :
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  public_states_l_deposits states_l -∗
  secret_in_l t -∗ PUB⟨t, t'⟩ -∗ False.
Proof.
iIntros "Hstates Hdeps Hs Ht".
iDestruct (secret_in_l_lookup with "Hstates Hs") as %Hsec.
by iApply (public_protected_l (λ _ _, eq_refl) with "Hstates Hdeps [] Ht").
Qed.

#[local] Lemma secret_in_r_public states_r {t t'} :
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  public_states_r_deposits states_r -∗
  secret_in_r t' -∗ PUB⟨t, t'⟩ -∗ False.
Proof.
iIntros "Hstates Hdeps Hs Ht".
iDestruct (secret_in_r_lookup with "Hstates Hs") as %Hsec.
by iApply (public_protected_r (λ _ _, eq_refl) with "Hstates Hdeps [] Ht").
Qed.

Lemma secret_in_l_public_fupd E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗ secret_in_l t -∗ PUB⟨t, t'⟩ ={E}=∗ False.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Hs #Ht".
iInv "Hinv" as ">(%states_l & %states_r & ([Hstates_l _] & _) & [Hdeps _] & _)".
by iDestruct (secret_in_l_public with "Hstates_l Hdeps Hs Ht") as "[]".
Qed.

Lemma secret_in_r_public_fupd E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗ secret_in_r t' -∗ PUB⟨t, t'⟩ ={E}=∗ False.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Hs #Ht".
iInv "Hinv" as ">(%states_l & %states_r & (_ & [Hstates_r _] & _) & [_ Hdeps] & _)".
by iDestruct (secret_in_r_public with "Hstates_r Hdeps Hs Ht") as "[]".
Qed.

End Protection.

Section Release.

#[local] Lemma public_TSeal_l_open states_l {k t k' t' dk dk'} :
  match k with
  | TKey AEnc s => dk = TKey ADec s
  | TKey SEnc s => dk = TKey SEnc s
  | _ => False
  end →
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  public_states_l_deposits states_l -∗
  publicly_linked_in_l (TSeal k t) (TSeal k' t') -∗
  PUB⟨dk, dk'⟩ -∗
  PUB⟨t, t'⟩.
Proof.
move=> Hk. iIntros "Hstates Hprot #Hl #Hdk".
iDestruct (publicly_linked_in_l_lookup with "Hstates Hl") as %Hc.
iDestruct (big_sepM_delete _ _ _ _ Hc with "Hprot") as "[[He _] Hprot]".
have Hagree : ∀ x, tsize x ≤ tsize dk → delete (TSeal k t) states_l !! x = states_l !! x.
{ move=> x Hx. rewrite lookup_delete_ne //. move=> ?; subst x.
  case: (k) Hk Hx => // - [] // s -> Hx;
    rewrite (tsize_eq (TSeal _ _)) !tsize_eq in Hx; lia. }
case: k Hk Hc Hagree => // - [] // s -> Hc Hagree; iSimpl in "He";
  iDestruct "He" as "[[[?|Hsec] _]|[[%x Hlink] Htok]]"; try done.
all: try by iDestruct (secret_in_l_lookup with "Hstates Hsec") as %Hsec;
       iDestruct (public_protected_l Hagree with "Hstates Hprot [] Hdk") as "[]".
all: iDestruct (linked_in_l_lookup with "Hstates Hlink") as %[Hst|[Hst|Hst]];
  try by iDestruct (public_protected_l Hagree with "Hstates Hprot [] Hdk") as "[]".
all: match type of Hc with _ !! ?c = _ =>
       have Hst' := Hst; rewrite -(lookup_delete_ne _ c) // in Hst' end.
all: iDestruct (big_sepM_lookup _ _ _ _ Hst' with "Hprot") as "[Hfull _]".
all: iSimpl in "Hfull"; iDestruct (term_token_disj with "Hfull Htok") as %Hdisj.
all: exfalso; have Hsub : ↑holdN.@t ⊆ (↑holdN : coPset) by solve_ndisj.
all: pose proof (nclose_non_empty (holdN.@t)); set_solver.
Qed.

#[local] Lemma public_TSeal_r_open states_r {k t k' t' dk dk'} :
  match k' with
  | TKey AEnc s => dk' = TKey ADec s
  | TKey SEnc s => dk' = TKey SEnc s
  | _ => False
  end →
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  public_states_r_deposits states_r -∗
  publicly_linked_in_r (TSeal k t) (TSeal k' t') -∗
  PUB⟨dk, dk'⟩ -∗
  PUB⟨t, t'⟩.
Proof.
move=> Hk. iIntros "Hstates Hprot #Hl #Hdk".
iDestruct (publicly_linked_in_r_lookup with "Hstates Hl") as %Hc.
iDestruct (big_sepM_delete _ _ _ _ Hc with "Hprot") as "[[He _] Hprot]".
have Hagree : ∀ x, tsize x ≤ tsize dk' → delete (TSeal k' t') states_r !! x = states_r !! x.
{ move=> x Hx. rewrite lookup_delete_ne //. move=> ?; subst x.
  case: (k') Hk Hx => // - [] // s -> Hx;
    rewrite (tsize_eq (TSeal _ _)) !tsize_eq in Hx; lia. }
case: k' Hk Hc Hagree => // - [] // s -> Hc Hagree; iSimpl in "He";
  iDestruct "He" as "[[[?|Hsec] _]|[[%x Hlink] Htok]]"; try done.
all: try by iDestruct (secret_in_r_lookup with "Hstates Hsec") as %Hsec;
       iDestruct (public_protected_r Hagree with "Hstates Hprot [] Hdk") as "[]".
all: iDestruct (linked_in_r_lookup with "Hstates Hlink") as %[Hst|[Hst|Hst]];
  try by iDestruct (public_protected_r Hagree with "Hstates Hprot [] Hdk") as "[]".
all: match type of Hc with _ !! ?c = _ =>
       have Hst' := Hst; rewrite -(lookup_delete_ne _ c) // in Hst' end.
all: iDestruct (big_sepM_lookup _ _ _ _ Hst' with "Hprot") as "[Hfull _]".
all: iSimpl in "Hfull"; iDestruct (term_token_spec_disj with "Hfull Htok") as %Hdisj.
all: exfalso; have Hsub : ↑holdN.@t' ⊆ (↑holdN : coPset) by solve_ndisj.
all: pose proof (nclose_non_empty (holdN.@t')); set_solver.
Qed.

Lemma public_TSeal_release_AEnc_hold_l_fupd E s t k' t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  PUB⟨t, t'⟩ -∗
  seal_release_l (TSeal (TKey AEnc s) t) -∗
  publicly_linked_in_l (TSeal (TKey AEnc s) t) (TSeal k' t') ={E}=∗
  holds_key_l t (TKey AEnc s).
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Ht Hseal #Hl".
iInv "Hinv" as ">(%states_l & %states_r &
                  ([Hstates_l Hstates_l_frag] & Hstates_rest) &
                  [Hpublic_deposit_l Hpublic_deposit_r] & Hrest)".
iDestruct (publicly_linked_in_l_lookup with "Hstates_l Hl") as %Hc.
iDestruct (big_sepM_delete _ _ _ _ Hc with "Hpublic_deposit_l") as "[[He Hprots] Hothers]".
iAssert (holds_key_l t (TKey AEnc s) ∗ public_states_l_deposits states_l)%I
  with "[He Hprots Hothers Hseal]" as "[Hkey Hpublic_deposit_l]".
{ rewrite /public_states_l_deposits (big_sepM_delete _ states_l _ _ Hc).
  iFrame "Hothers Hprots".
  iSimpl in "He"; iSimpl; iDestruct "He" as "[[_ Hseal']|[_ Hkey]]".
  - iDestruct (term_token_disj with "Hseal Hseal'") as %Hdisj; exfalso;
      pose proof (nclose_non_empty (seal_namespace t.@"release")); set_solver.
  - iFrame "Hkey"; iLeft; iFrame "Hseal"; by iLeft. }
iModIntro. iSplitR "Hkey"; last done.
iModIntro. iExists states_l, states_r. iFrame.
Qed.

Lemma public_TSeal_release_AEnc_hold_r_fupd E s' t' k t :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  PUB⟨t, t'⟩ -∗
  seal_release_r (TSeal (TKey AEnc s') t') -∗
  publicly_linked_in_r (TSeal k t) (TSeal (TKey AEnc s') t') ={E}=∗
  holds_key_r t' (TKey AEnc s').
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Ht Hseal #Hl".
iInv "Hinv" as ">(%states_l & %states_r &
                  (Hstates_l & [Hstates_r Hstates_r_frag] & Hstates_rest) &
                  [Hpublic_deposit_l Hpublic_deposit_r] & Hrest)".
iDestruct (publicly_linked_in_r_lookup with "Hstates_r Hl") as %Hc.
iDestruct (big_sepM_delete _ _ _ _ Hc with "Hpublic_deposit_r") as "[[He Hprots] Hothers]".
iAssert (holds_key_r t' (TKey AEnc s') ∗ public_states_r_deposits states_r)%I
  with "[He Hprots Hothers Hseal]" as "[Hkey Hpublic_deposit_r]".
{ rewrite /public_states_r_deposits (big_sepM_delete _ states_r _ _ Hc).
  iFrame "Hothers Hprots".
  iSimpl in "He"; iSimpl; iDestruct "He" as "[[_ Hseal']|[_ Hkey]]".
  - iDestruct (term_token_spec_disj with "Hseal Hseal'") as %Hdisj; exfalso;
      pose proof (nclose_non_empty (seal_namespace t'.@"release")); set_solver.
  - iFrame "Hkey"; iLeft; iFrame "Hseal"; by iLeft. }
iModIntro. iSplitR "Hkey"; last done.
iModIntro. iExists states_l, states_r. iFrame.
Qed.

Lemma public_TSeal_release_SEnc_hold_l_fupd E s t k' t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  PUB⟨t, t'⟩ -∗
  seal_release_l (TSeal (TKey SEnc s) t) -∗
  publicly_linked_in_l (TSeal (TKey SEnc s) t) (TSeal k' t') ={E}=∗
  holds_key_l t (TKey SEnc s).
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Ht Hseal #Hl".
iInv "Hinv" as ">(%states_l & %states_r &
                  ([Hstates_l Hstates_l_frag] & Hstates_rest) &
                  [Hpublic_deposit_l Hpublic_deposit_r] & Hrest)".
iDestruct (publicly_linked_in_l_lookup with "Hstates_l Hl") as %Hc.
iDestruct (big_sepM_delete _ _ _ _ Hc with "Hpublic_deposit_l") as "[[He Hprots] Hothers]".
iAssert (holds_key_l t (TKey SEnc s) ∗ public_states_l_deposits states_l)%I
  with "[He Hprots Hothers Hseal]" as "[Hkey Hpublic_deposit_l]".
{ rewrite /public_states_l_deposits (big_sepM_delete _ states_l _ _ Hc).
  iFrame "Hothers Hprots".
  iSimpl in "He"; iSimpl; iDestruct "He" as "[[_ Hseal']|[_ Hkey]]".
  - iDestruct (term_token_disj with "Hseal Hseal'") as %Hdisj; exfalso;
      pose proof (nclose_non_empty (seal_namespace t.@"release")); set_solver.
  - iFrame "Hkey"; iLeft; iFrame "Hseal"; by iLeft. }
iModIntro. iSplitR "Hkey"; last done.
iModIntro. iExists states_l, states_r. iFrame.
Qed.

Lemma public_TSeal_release_SEnc_hold_r_fupd E s' t' k t :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  PUB⟨t, t'⟩ -∗
  seal_release_r (TSeal (TKey SEnc s') t') -∗
  publicly_linked_in_r (TSeal k t) (TSeal (TKey SEnc s') t') ={E}=∗
  holds_key_r t' (TKey SEnc s').
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Ht Hseal #Hl".
iInv "Hinv" as ">(%states_l & %states_r &
                  (Hstates_l & [Hstates_r Hstates_r_frag] & Hstates_rest) &
                  [Hpublic_deposit_l Hpublic_deposit_r] & Hrest)".
iDestruct (publicly_linked_in_r_lookup with "Hstates_r Hl") as %Hc.
iDestruct (big_sepM_delete _ _ _ _ Hc with "Hpublic_deposit_r") as "[[He Hprots] Hothers]".
iAssert (holds_key_r t' (TKey SEnc s') ∗ public_states_r_deposits states_r)%I
  with "[He Hprots Hothers Hseal]" as "[Hkey Hpublic_deposit_r]".
{ rewrite /public_states_r_deposits (big_sepM_delete _ states_r _ _ Hc).
  iFrame "Hothers Hprots".
  iSimpl in "He"; iSimpl; iDestruct "He" as "[[_ Hseal']|[_ Hkey]]".
  - iDestruct (term_token_spec_disj with "Hseal Hseal'") as %Hdisj; exfalso;
      pose proof (nclose_non_empty (seal_namespace t'.@"release")); set_solver.
  - iFrame "Hkey"; iLeft; iFrame "Hseal"; by iLeft. }
iModIntro. iSplitR "Hkey"; last done.
iModIntro. iExists states_l, states_r. iFrame.
Qed.

End Release.

Section LinkedShape.

#[local] Lemma public_linked_in_l states_l :
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  public_states_l_deposits states_l -∗
  public_PublicLink_l_consistent states_l -∗
  ∀ t t1' t2', PUB⟨t, t1'⟩ -∗ linked_in_l t t2' -∗ PUB⟨t, t2'⟩.
Proof.
iIntros "Hauth Hdeps HPublicLink_consistent" (t t1' t2') "#H1 #H2".
iDestruct (linked_in_l_lookup with "Hauth H2") as %[HPending_t|[HPending_t|HPublicLink_t]].
- by iPoseProof (public_protected_l (λ _ _, eq_refl) with "Hauth Hdeps [] H1") as "[]".
- by iPoseProof (public_protected_l (λ _ _, eq_refl) with "Hauth Hdeps [] H1") as "[]".
- by iApply ("HPublicLink_consistent" with "[//]").
Qed.

#[local] Lemma public_linked_in_r states_r :
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  public_states_r_deposits states_r -∗
  public_PublicLink_r_consistent states_r -∗
  ∀ t1 t2 t', PUB⟨t1, t'⟩ -∗ linked_in_r t2 t' -∗ PUB⟨t2, t'⟩.
Proof.
iIntros "Hauth Hdeps HPublicLink_consistent" (t1 t2 t') "#H1 #H2".
iDestruct (linked_in_r_lookup with "Hauth H2") as %[HPending_t|[HPending_t|HPublicLink_t]].
- by iPoseProof (public_protected_r (λ _ _, eq_refl) with "Hauth Hdeps [] H1") as "[]".
- by iPoseProof (public_protected_r (λ _ _, eq_refl) with "Hauth Hdeps [] H1") as "[]".
- by iApply ("HPublicLink_consistent" with "[//]").
Qed.

#[local] Lemma opaque_l_same_shape states_l {t t'} :
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  public_states_l_deposits states_l -∗
  opaque_l t -∗ same_shape public t t' -∗ False.
Proof.
case: t => [n|a b|a|kt s|k b|s|pt wf nf]; case: t' => /= *;
  iIntros "Hstates Hdeps #Ho #Hs"; try (by iDestruct "Ho" as "[]"); try (by iDestruct "Hs" as "[]").
- iDestruct "Hs" as "[Hk Hb]".
  case: k => [?|? ?|?|kt s|? ?|?|? ? ?]; try (by iDestruct "Ho" as "[]").
  case: kt; try (by iDestruct "Ho" as "[]").
  + iDestruct "Ho" as "[_ Ho]".
    by iApply (secret_in_l_public with "Hstates Hdeps Ho Hb").
  + by iApply (secret_in_l_public with "Hstates Hdeps Ho Hk").
- by iApply (secret_in_l_public with "Hstates Hdeps Ho Hs").
Qed.

#[local] Lemma opaque_r_same_shape states_r {t t'} :
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  public_states_r_deposits states_r -∗
  opaque_r t' -∗ same_shape public t t' -∗ False.
Proof.
case: t' => [n|a b|a|kt s|k b|s|pt wf nf]; case: t => /= *;
  iIntros "Hstates Hdeps #Ho #Hs"; try (by iDestruct "Ho" as "[]"); try (by iDestruct "Hs" as "[]").
- iDestruct "Hs" as "[Hk Hb]".
  case: k => [?|? ?|?|kt s|? ?|?|? ? ?]; try (by iDestruct "Ho" as "[]").
  case: kt; try (by iDestruct "Ho" as "[]").
  + iDestruct "Ho" as "[_ Ho]".
    by iApply (secret_in_r_public with "Hstates Hdeps Ho Hb").
  + by iApply (secret_in_r_public with "Hstates Hdeps Ho Hk").
- by iApply (secret_in_r_public with "Hstates Hdeps Ho Hs").
Qed.

#[local] Lemma linked_shape_same_shape_l states_l {t t1' t2'} :
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  public_PublicLink_l_consistent states_l -∗
  public_states_l_deposits states_l -∗
  publicly_linked t t2' -∗
  same_shape public t t1' -∗
  linked_shape public t t2' -∗
  same_shape public t t2'.
Proof.
case: t => [n|a b|a|kt s|k b|s|pt wf nf];
  case: t2' => [n2|a2 b2|a2|kt2 s2|k2 b2|s2|pt2 wf2 nf2] /=;
  iIntros "Hstates #HPublicLink_consistent Hprot #Hpl #Hs #Hl"; try (by iDestruct "Hl" as "[]");
  case: t1' => /= *; try (by iDestruct "Hs" as "[]").
- iDestruct "Hs" as "[_ Hs]". iDestruct "Hl" as "(<- & [Hl _] & _)". iSplit; first done.
  by iApply (public_linked_in_l with "Hstates Hprot HPublicLink_consistent Hs Hl").
- iDestruct "Hs" as "[Hk Hb]". iDestruct "Hl" as "[[Hkl _] #Hl]".
  iPoseProof (public_linked_in_l with "Hstates Hprot HPublicLink_consistent Hk Hkl") as "#Hk2".
  iSplit; first done.
  case: k => [?|? ?|?|kt s|? ?|?|? ? ?]; try (by iDestruct "Hl" as "[]").
  case: k2 => [?|? ?|?|kt' s'|? ?|?|? ? ?]; try (by iDestruct "Hl" as "[]").
  case: kt; case: kt'; try (by iDestruct "Hl" as "[]").
  + iDestruct "Hl" as "[Hb2|[Hb2 _]]"; first done.
    by iApply (public_linked_in_l with "Hstates Hprot HPublicLink_consistent Hb Hb2").
  + by iDestruct "Hl" as "[_ Hb2]".
  + iDestruct "Hpl" as "[Hpl _]".
    by iApply (public_TSeal_l_open with "Hstates Hprot Hpl Hk2").
- iDestruct "Hl" as "[Hl _]".
  by iApply (public_linked_in_l with "Hstates Hprot HPublicLink_consistent Hs Hl").
Qed.

#[local] Lemma linked_shape_same_shape_r states_r {t1 t2 t'} :
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  public_PublicLink_r_consistent states_r -∗
  public_states_r_deposits states_r -∗
  publicly_linked t2 t' -∗
  same_shape public t1 t' -∗
  linked_shape public t2 t' -∗
  same_shape public t2 t'.
Proof.
case: t' => [n|a b|a|kt s|k b|s|pt wf nf];
  case: t2 => [n2|a2 b2|a2|kt2 s2|k2 b2|s2|pt2 wf2 nf2] /=;
  iIntros "Hstates #HPublicLink_consistent Hprot #Hpl #Hs #Hl"; try (by iDestruct "Hl" as "[]");
  case: t1 => /= *; try (by iDestruct "Hs" as "[]").
- iDestruct "Hs" as "[_ Hs]". iDestruct "Hl" as "(%Heq & [_ Hl] & _)". subst kt2. iSplit; first done.
  by iApply (public_linked_in_r with "Hstates Hprot HPublicLink_consistent Hs Hl").
- iDestruct "Hs" as "[Hk Hb]". iDestruct "Hl" as "[[_ Hkl] #Hl]".
  iPoseProof (public_linked_in_r with "Hstates Hprot HPublicLink_consistent Hk Hkl") as "#Hk2".
  iSplit; first done.
  case: k2 => [?|? ?|?|kt' s'|? ?|?|? ? ?]; try (by iDestruct "Hl" as "[]").
  case: k => [?|? ?|?|kt s|? ?|?|? ? ?]; try (by iDestruct "Hl" as "[]").
  case: kt; case: kt'; try (by iDestruct "Hl" as "[]").
  + iDestruct "Hl" as "[Hb2|[_ Hb2]]"; first done.
    by iApply (public_linked_in_r with "Hstates Hprot HPublicLink_consistent Hb Hb2").
  + by iDestruct "Hl" as "[_ Hb2]".
  + iDestruct "Hpl" as "[_ Hpl]".
    by iApply (public_TSeal_r_open with "Hstates Hprot Hpl Hk2").
- iDestruct "Hl" as "[_ Hl]".
  by iApply (public_linked_in_r with "Hstates Hprot HPublicLink_consistent Hs Hl").
Qed.

End LinkedShape.

Section Admission.

Lemma linked_in_l_states_token_fupd E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗ linked_in_l t t' -∗ states_token_l t ={E}=∗ False.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Hl tok".
iInv "Hinv" as ">(%states_l & %states_r & ([Hstates_l _] & _ & Hmeta & _) & _)".
iDestruct (linked_in_l_lookup with "Hstates_l Hl") as %Hlookup.
iDestruct (public_states_l_fresh with "Hmeta tok") as %Hfresh.
exfalso. rewrite Hfresh in Hlookup. by case: Hlookup => [|[|]].
Qed.

Lemma linked_in_r_states_token_fupd E t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗ linked_in_r t t' -∗ states_token_r t' ={E}=∗ False.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Hl tok".
iInv "Hinv" as ">(%states_l & %states_r & (_ & [Hstates_r _] & _ & Hmeta) & _)".
iDestruct (linked_in_r_lookup with "Hstates_r Hl") as %Hlookup.
iDestruct (public_states_r_fresh with "Hmeta tok") as %Hfresh.
exfalso. rewrite Hfresh in Hlookup. by case: Hlookup => [|[|]].
Qed.

End Admission.

Section PartBij.

#[local] Lemma public_part_bij_1_shape states_l {t t1' t2'} :
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  public_PublicLink_l_consistent states_l -∗
  public_states_l_deposits states_l -∗
  PUB⟨t, t1'⟩ -∗
  PUB⟨t, t2'⟩ -∗
  ⌜t1' = t2'⌝ ∨
  (same_shape public t t1' ∧ same_shape public t t2').
Proof.
iIntros "Hstates #HPublicLink_consistent Hprot #H1 #H2".
iDestruct (public_cases with "H1") as "[Hs1|(Hl1 & [Hk1|[Ho1 _]])]";
iDestruct (public_cases with "H2") as "[Hs2|(Hl2 & [Hk2|[Ho2 _]])]";
  try (iLeft; by iApply (publicly_linked_agree_l with "Hl1 Hl2")).
- iRight. by iSplit.
- iRight. iSplit; first done.
  by iApply (linked_shape_same_shape_l with "Hstates HPublicLink_consistent Hprot Hl2 Hs1 Hk2").
- by iDestruct (opaque_l_same_shape with "Hstates Hprot Ho2 Hs1") as "[]".
- iRight. iSplit; last done.
  by iApply (linked_shape_same_shape_l with "Hstates HPublicLink_consistent Hprot Hl1 Hs2 Hk1").
- by iDestruct (opaque_l_same_shape with "Hstates Hprot Ho1 Hs2") as "[]".
Qed.

#[local] Lemma public_part_bij_2_shape states_r {t1 t2 t'} :
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  public_PublicLink_r_consistent states_r -∗
  public_states_r_deposits states_r -∗
  PUB⟨t1, t'⟩ -∗
  PUB⟨t2, t'⟩ -∗
  ⌜t1 = t2⌝ ∨
  (same_shape public t1 t' ∧ same_shape public t2 t').
Proof.
iIntros "Hstates #HPublicLink_consistent Hprot #H1 #H2".
iDestruct (public_cases with "H1") as "[Hs1|(Hl1 & [Hk1|[_ Ho1]])]";
iDestruct (public_cases with "H2") as "[Hs2|(Hl2 & [Hk2|[_ Ho2]])]";
  try (iLeft; by iApply (publicly_linked_agree_r with "Hl1 Hl2")).
- iRight. by iSplit.
- iRight. iSplit; first done.
  by iApply (linked_shape_same_shape_r with "Hstates HPublicLink_consistent Hprot Hl2 Hs1 Hk2").
- by iDestruct (opaque_r_same_shape with "Hstates Hprot Ho2 Hs1") as "[]".
- iRight. iSplit; last done.
  by iApply (linked_shape_same_shape_r with "Hstates HPublicLink_consistent Hprot Hl1 Hs2 Hk1").
- by iDestruct (opaque_r_same_shape with "Hstates Hprot Ho1 Hs2") as "[]".
Qed.

#[local] Lemma public_part_bij_1_auth states_l {t t1' t2'} :
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  public_PublicLink_l_consistent states_l -∗
  public_states_l_deposits states_l -∗
  PUB⟨t, t1'⟩ -∗
  PUB⟨t, t2'⟩ -∗
  ⌜t1' = t2'⌝.
Proof.
iIntros "Hstates_l HPublicLink_consistent Hprot #H1 #H2".
iInduction t as [n|a b|a|kt s|k b|s|pt wf nf] "IH" using term_ind' forall (t1' t2') "H1 H2";
  iDestruct (public_part_bij_1_shape
               with "Hstates_l HPublicLink_consistent Hprot H1 H2") as "#Hc";
  iDestruct "Hc" as "[%|[Hs1 Hs2]]"; try done;
  case: t1' => /= *; try (by iDestruct "Hs1" as "[]");
  case: t2' => /= *; try (by iDestruct "Hs2" as "[]").
- iDestruct "Hs1" as %->. by iDestruct "Hs2" as %->.
- iDestruct "Hs1" as "[Ha1 Hb1]". iDestruct "Hs2" as "[Ha2 Hb2]".
  iDestruct ("IH" with "Hstates_l HPublicLink_consistent Hprot Ha1 Ha2") as %->.
  by iDestruct ("IH1" with "Hstates_l HPublicLink_consistent Hprot Hb1 Hb2") as %->.
- iDestruct "Hs1" as "[<- Hs1]". iDestruct "Hs2" as "[<- Hs2]".
  by iDestruct ("IH" with "Hstates_l HPublicLink_consistent Hprot Hs1 Hs2") as %->.
- iDestruct "Hs1" as "[Hk1 Hb1]". iDestruct "Hs2" as "[Hk2 Hb2]".
  iDestruct ("IH" with "Hstates_l HPublicLink_consistent Hprot Hk1 Hk2") as %->.
  by iDestruct ("IH1" with "Hstates_l HPublicLink_consistent Hprot Hb1 Hb2") as %->.
- by iDestruct ("IH" with "Hstates_l HPublicLink_consistent Hprot Hs1 Hs2") as %->.
Qed.

#[local] Lemma public_part_bij_1_open states_l states_r t t1' t2' :
  public_inv states_l states_r -∗
  PUB⟨t, t1'⟩ -∗
  PUB⟨t, t2'⟩ -∗
  ⌜t1' = t2'⌝.
Proof.
iIntros "(([Hstates_l _] & _) & [Hprot _] & [HPublicLink_consistent _]) #H1 #H2".
by iApply (public_part_bij_1_auth with "Hstates_l HPublicLink_consistent Hprot H1 H2").
Qed.

Lemma public_part_bij_1_fupd E t t1' t2' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  PUB⟨t, t1'⟩ -∗
  PUB⟨t, t2'⟩ -∗
  |={E}=> ⌜t1' = t2'⌝.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #H1 #H2".
iInv "Hinv" as ">(%states_l & %states_r & Hbody)".
iDestruct (public_part_bij_1_open with "Hbody H1 H2") as %Heq.
iModIntro. iSplitL; last done.
iModIntro. iExists states_l, states_r. iFrame.
Qed.

#[local] Lemma public_part_bij_2_auth states_r {t1 t2 t'} :
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  public_PublicLink_r_consistent states_r -∗
  public_states_r_deposits states_r -∗
  PUB⟨t1, t'⟩ -∗
  PUB⟨t2, t'⟩ -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "Hstates_r HPublicLink_consistent Hprot #H1 #H2".
iInduction t' as [n'|a' b'|a'|kt' s'|k' b'|s'|pt' wf' nf'] "IH" using term_ind' forall (t1 t2) "H1 H2";
  iDestruct (public_part_bij_2_shape
               with "Hstates_r HPublicLink_consistent Hprot H1 H2") as "#Hc";
  iDestruct "Hc" as "[%|[Hs1 Hs2]]"; try done;
  case: t1 => /= *; try (by iDestruct "Hs1" as "[]");
  case: t2 => /= *; try (by iDestruct "Hs2" as "[]").
- iDestruct "Hs1" as %->. by iDestruct "Hs2" as %->.
- iDestruct "Hs1" as "[Ha1 Hb1]". iDestruct "Hs2" as "[Ha2 Hb2]".
  iDestruct ("IH" with "Hstates_r HPublicLink_consistent Hprot Ha1 Ha2") as %->.
  by iDestruct ("IH1" with "Hstates_r HPublicLink_consistent Hprot Hb1 Hb2") as %->.
- iDestruct "Hs1" as "[-> Hs1]". iDestruct "Hs2" as "[-> Hs2]".
  by iDestruct ("IH" with "Hstates_r HPublicLink_consistent Hprot Hs1 Hs2") as %->.
- iDestruct "Hs1" as "[Hk1 Hb1]". iDestruct "Hs2" as "[Hk2 Hb2]".
  iDestruct ("IH" with "Hstates_r HPublicLink_consistent Hprot Hk1 Hk2") as %->.
  by iDestruct ("IH1" with "Hstates_r HPublicLink_consistent Hprot Hb1 Hb2") as %->.
- by iDestruct ("IH" with "Hstates_r HPublicLink_consistent Hprot Hs1 Hs2") as %->.
Qed.

#[local] Lemma public_part_bij_2_open states_l states_r t1 t2 t' :
  public_inv states_l states_r -∗
  PUB⟨t1, t'⟩ -∗
  PUB⟨t2, t'⟩ -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "((_ & [Hstates_r _] & _) & [_ Hprot] & [_ HPublicLink_consistent_r]) #H1 #H2".
by iApply (public_part_bij_2_auth with "Hstates_r HPublicLink_consistent_r Hprot H1 H2").
Qed.

Lemma public_part_bij_2_fupd E t1 t2 t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  PUB⟨t1, t'⟩ -∗
  PUB⟨t2, t'⟩ -∗
  |={E}=> ⌜t1 = t2⌝.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #H1 #H2".
iInv "Hinv" as ">(%states_l & %states_r & Hbody)".
iDestruct (public_part_bij_2_open with "Hbody H1 H2") as %Heq.
iModIntro. iSplitL; last done.
iModIntro. iExists states_l, states_r. iFrame.
Qed.

Lemma public_part_bij E t t' :
  ↑cryptisN ⊆ E →
  (∀ t1', hypercryptis_ctx -∗ PUB⟨t, t'⟩ -∗ PUB⟨t, t1'⟩ -∗ |={E}=> ⌜t' = t1'⌝) ∧
  (∀ t1, hypercryptis_ctx -∗ PUB⟨t, t'⟩ -∗ PUB⟨t1, t'⟩ -∗ |={E}=> ⌜t = t1⌝).
Proof.
move=> HE. split.
- move=> t1'. exact: public_part_bij_1_fupd.
- move=> t1. exact: public_part_bij_2_fupd.
Qed.

Lemma public_part_bij' E t1 t1' t2 t2' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  PUB⟨t1, t1'⟩ -∗
  PUB⟨t2, t2'⟩ -∗
  |={E}=> ⌜t1 = t2 ↔ t1' = t2'⌝.
Proof.
iIntros (HE) "#Hctx #Ht1 #Ht2".
destruct (decide (t1 = t2)) as [->|Hne].
{ iMod (public_part_bij_1_fupd with "Hctx Ht1 Ht2") as %->; first done.
  by iPureIntro. }
destruct (decide (t1' = t2')) as [->|Hne'].
{ iMod (public_part_bij_2_fupd with "Hctx Ht1 Ht2") as %->; first done.
  by iPureIntro. }
iPureIntro. tauto.
Qed.

End PartBij.

Section AttackerDecryption.

#[local] Lemma public_open_auth {states_l k k' t t' t1 t1'} :
  Spec.open k t = Some t1 →
  Spec.open k' t' = Some t1' →
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  public_states_l_deposits states_l -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  PUB⟨t1, t1'⟩.
Proof.
rewrite /Spec.open.
case: t => // k_t t.
case: t' => // k_t' t'.
case: decide => // k_t_k [<-].
case: decide => // k_t_k' [<-].
iIntros "Hstates Hprot #Hk #Ht".
case: k_t k_t' => // kt k1 [] // kt' k1' in k_t_k k_t_k' *.
case: kt k_t_k => // - [<-]; case: kt' k_t_k' => // - [<-].
all: try (rewrite public_TKey; by iDestruct "Hk" as "[% _]").
all: iDestruct (public_TSeal with "Ht") as "[[_ Ht1]|(_ & _ & [Hl _] & [[_ #Hrest]|[Ho _]])]";
  first done.
all: try iSimpl in "Ho"; try iSimpl in "Hrest".
- by iApply (public_TSeal_l_open with "Hstates Hprot Hl Hk").
- iDestruct "Ho" as "[Ho _]".
  by iDestruct (secret_in_l_public with "Hstates Hprot Ho Hk") as "[]".
- by iDestruct "Hrest" as "[_ ?]".
- by iDestruct "Ho" as "[]".
- by iApply (public_TSeal_l_open with "Hstates Hprot Hl Hk").
- by iDestruct (secret_in_l_public with "Hstates Hprot Ho Hk") as "[]".
Qed.

#[local] Lemma public_open_inv {states_l states_r k k' t t' t1 t1'} :
  Spec.open k t = Some t1 →
  Spec.open k' t' = Some t1' →
  public_inv states_l states_r -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  PUB⟨t1, t1'⟩.
Proof.
iIntros (Ho Ho') "(([Hstates_l _] & _) & [Hprot _] & _) #Hk #Ht".
by iApply (public_open_auth Ho Ho' with "Hstates_l Hprot Hk Ht").
Qed.

Lemma public_open E k k' t t' t1 t1' :
  ↑cryptisN ⊆ E →
  Spec.open k t = Some t1 →
  Spec.open k' t' = Some t1' →
  hypercryptis_ctx -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ ={E}=∗
  PUB⟨t1, t1'⟩.
Proof.
iIntros (HE Ho Ho') "#(_ & _ & Hinv) #Hk #Ht".
iInv "Hinv" as ">(%states_l & %states_r & Hbody)".
iDestruct (public_open_inv Ho Ho' with "Hbody Hk Ht") as "#Ht1".
iModIntro. iSplitL; last done.
iModIntro. iExists states_l, states_r. iFrame.
Qed.

#[local] Lemma public_TSeal_key_l states_l {k b k' b' k1'} :
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  public_states_l_deposits states_l -∗
  public_PublicLink_l_consistent states_l -∗
  PUB⟨TSeal k b, TSeal k' b'⟩ -∗
  PUB⟨k, k1'⟩ -∗
  PUB⟨k, k'⟩ ∨ opaque_l (TSeal k b).
Proof.
iIntros "Hstates Hdeps #HPublicLink_consistent #Ht #Hk".
iDestruct (public_TSeal with "Ht") as "[[? _]|(_ & _ & _ & [[[Hlink _] _]|[? _]])]".
- by iLeft.
- iLeft.
  by iApply (public_linked_in_l with "Hstates Hdeps HPublicLink_consistent Hk Hlink").
- by iRight.
Qed.

#[local] Lemma public_TSeal_key_r states_r {k b k' b' k1} :
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  public_states_r_deposits states_r -∗
  public_PublicLink_r_consistent states_r -∗
  PUB⟨TSeal k b, TSeal k' b'⟩ -∗
  PUB⟨k1, k'⟩ -∗
  PUB⟨k, k'⟩ ∨ opaque_r (TSeal k' b').
Proof.
iIntros "Hstates Hdeps #HPublicLink_consistent #Ht #Hk".
iDestruct (public_TSeal with "Ht") as "[[? _]|(_ & _ & _ & [[[_ Hlink] _]|[_ ?]])]".
- by iLeft.
- iLeft.
  by iApply (public_linked_in_r with "Hstates Hdeps HPublicLink_consistent Hk Hlink").
- by iRight.
Qed.

#[local] Lemma public_open_l_auth {states_l k k' t t' t1} :
  Spec.open k t = Some t1 →
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  public_PublicLink_l_consistent states_l -∗
  public_states_l_deposits states_l -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  ⌜is_Some (Spec.open k' t')⌝.
Proof.
rewrite {1}/Spec.open. case: t => // k_t b.
case: decide => // Hkey _.
move: Hkey; rewrite /Spec.open_key /Spec.to_key.
case: k_t => // kt s Hkey.
have Hdone : ∀ kt' s' b', Spec.open_key (TKey kt' s') = Some k' →
  is_Some (Spec.open k' (TSeal (TKey kt' s') b')).
{ move=> kt' s' b' Hk'. rewrite /Spec.open decide_True //. }
case: kt Hkey => // - [<-] {k}; iIntros "Hstates_l HPublicLink_consistent Hprot #Hk #Ht";
  iDestruct (public_TKey_term with "Hk") as %[s'' ->];
  iDestruct (public_TSeal_term with "Ht") as "[(%k_t' & %b' & ->)|(_ & Hsec & _)]".
- (* Asymmetric encryption, [t'] is a ciphertext. *)
  iAssert (PUB⟨TKey AEnc s, TKey AEnc s''⟩) as "#Hpk"; first by iApply (public_pkey with "Hk").
  iAssert (PUB⟨TKey AEnc s, k_t'⟩ ∨ opaque_l (TSeal (TKey AEnc s) b))%I as "#[Hkk|Ho]".
  { by iApply (public_TSeal_key_l with "Hstates_l Hprot HPublicLink_consistent Ht Hpk"). }
  + iDestruct (public_part_bij_1_auth
                 with "Hstates_l HPublicLink_consistent Hprot Hpk Hkk") as %<-.
    iPureIntro. by apply: Hdone.
  + iSimpl in "Ho". iDestruct "Ho" as "[Ho _]". iExFalso.
    by iApply (secret_in_l_public with "Hstates_l Hprot Ho Hk").
- (* Asymmetric encryption, [t'] is not a ciphertext: impossible. *)
  iSimpl in "Hsec". iDestruct "Hsec" as "[Hsec _]". iExFalso.
  by iApply (secret_in_l_public with "Hstates_l Hprot Hsec Hk").
- (* Signature, [t'] is a ciphertext. *)
  iDestruct (public_TSeal with "Ht") as "[[Hkk _]|(_ & _ & _ & [[_ Hbox]|[Ho _]])]".
  + iDestruct (public_TKey_term with "Hkk") as %[s' ->].
    iAssert (PUB⟨TKey Verify s, TKey Verify s'⟩) as "#Hv";
      first by iApply (public_pkey with "Hkk").
    iDestruct (public_part_bij_1_auth
                 with "Hstates_l HPublicLink_consistent Hprot Hv Hk") as %[= <-].
    iPureIntro. by apply: Hdone.
  + case: k_t' => [?|? ?|?|kt' s'|? ?|?|? ? ?]; try by iDestruct "Hbox" as "[]".
    case: kt'; try by iDestruct "Hbox" as "[]".
    iDestruct "Hbox" as "[Hv _]".
    iDestruct (public_part_bij_1_auth
                 with "Hstates_l HPublicLink_consistent Hprot Hv Hk") as %[= <-].
    iPureIntro. by apply: Hdone.
  + iSimpl in "Ho". by iDestruct "Ho" as "[]".
- (* Signature, [t'] is not a ciphertext: impossible. *)
  iSimpl in "Hsec". by iDestruct "Hsec" as "[]".
- (* Symmetric encryption, [t'] is a ciphertext. *)
  iAssert (PUB⟨TKey SEnc s, k_t'⟩ ∨ opaque_l (TSeal (TKey SEnc s) b))%I as "#[Hkk|Ho]".
  { by iApply (public_TSeal_key_l with "Hstates_l Hprot HPublicLink_consistent Ht Hk"). }
  + iDestruct (public_part_bij_1_auth
                 with "Hstates_l HPublicLink_consistent Hprot Hk Hkk") as %<-.
    iPureIntro. by apply: Hdone.
  + iSimpl in "Ho". iExFalso.
    by iApply (secret_in_l_public with "Hstates_l Hprot Ho Hk").
- (* Symmetric encryption, [t'] is not a ciphertext: impossible. *)
  iSimpl in "Hsec". iExFalso.
  by iApply (secret_in_l_public with "Hstates_l Hprot Hsec Hk").
Qed.

#[local] Lemma public_open_r_auth {states_r k k' t t' t1'} :
  Spec.open k' t' = Some t1' →
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  public_PublicLink_r_consistent states_r -∗
  public_states_r_deposits states_r -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  ⌜is_Some (Spec.open k t)⌝.
Proof.
rewrite {1}/Spec.open. case: t' => // k_t' b'.
case: decide => // Hkey _.
move: Hkey; rewrite /Spec.open_key /Spec.to_key.
case: k_t' => // kt' s' Hkey.
have Hdone : ∀ kt s b, Spec.open_key (TKey kt s) = Some k →
  is_Some (Spec.open k (TSeal (TKey kt s) b)).
{ move=> kt s b Hk. rewrite /Spec.open decide_True //. }
case: kt' Hkey => // - [<-] {k'}; iIntros "Hstates_r HPublicLink_consistent Hprot #Hk #Ht";
  iDestruct (public_term_TKey with "Hk") as %[s'' ->];
  iDestruct (public_term_TSeal with "Ht") as "[(%k_t & %b & ->)|(_ & _ & Hsec)]".
- iAssert (PUB⟨TKey AEnc s'', TKey AEnc s'⟩) as "#Hpk"; first by iApply (public_pkey with "Hk").
  iAssert (PUB⟨k_t, TKey AEnc s'⟩ ∨ opaque_r (TSeal (TKey AEnc s') b'))%I as "#[Hkk|Ho]".
  { by iApply (public_TSeal_key_r with "Hstates_r Hprot HPublicLink_consistent Ht Hpk"). }
  + iDestruct (public_part_bij_2_auth
                 with "Hstates_r HPublicLink_consistent Hprot Hpk Hkk") as %<-.
    iPureIntro. by apply: Hdone.
  + iSimpl in "Ho". iDestruct "Ho" as "[Ho _]". iExFalso.
    by iApply (secret_in_r_public with "Hstates_r Hprot Ho Hk").
- iSimpl in "Hsec". iDestruct "Hsec" as "[Hsec _]". iExFalso.
  by iApply (secret_in_r_public with "Hstates_r Hprot Hsec Hk").
- iDestruct (public_TSeal with "Ht") as "[[Hkk _]|(_ & _ & _ & [[_ Hbox]|[_ Ho]])]".
  + iDestruct (public_term_TKey with "Hkk") as %[s ->].
    iAssert (PUB⟨TKey Verify s, TKey Verify s'⟩) as "#Hv";
      first by iApply (public_pkey with "Hkk").
    iDestruct (public_part_bij_2_auth
                 with "Hstates_r HPublicLink_consistent Hprot Hv Hk") as %[= <-].
    iPureIntro. by apply: Hdone.
  + case: k_t => [?|? ?|?|kt s|? ?|?|? ? ?]; try by iDestruct "Hbox" as "[]".
    case: kt; try by iDestruct "Hbox" as "[]".
    iDestruct "Hbox" as "[Hv _]".
    iDestruct (public_part_bij_2_auth
                 with "Hstates_r HPublicLink_consistent Hprot Hv Hk") as %[= <-].
    iPureIntro. by apply: Hdone.
  + iSimpl in "Ho". by iDestruct "Ho" as "[]".
- iSimpl in "Hsec". by iDestruct "Hsec" as "[]".
- iAssert (PUB⟨k_t, TKey SEnc s'⟩ ∨ opaque_r (TSeal (TKey SEnc s') b'))%I as "#[Hkk|Ho]".
  { by iApply (public_TSeal_key_r with "Hstates_r Hprot HPublicLink_consistent Ht Hk"). }
  + iDestruct (public_part_bij_2_auth
                 with "Hstates_r HPublicLink_consistent Hprot Hk Hkk") as %<-.
    iPureIntro. by apply: Hdone.
  + iSimpl in "Ho". iExFalso.
    by iApply (secret_in_r_public with "Hstates_r Hprot Ho Hk").
- iSimpl in "Hsec". iExFalso.
  by iApply (secret_in_r_public with "Hstates_r Hprot Hsec Hk").
Qed.

#[local] Lemma public_open_open states_l states_r k k' t t' :
  public_inv states_l states_r -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  ⌜is_Some (Spec.open k t) ↔ is_Some (Spec.open k' t')⌝.
Proof.
iIntros "(([Hstates_l _] & [Hstates_r _] & _) & [Hprot_l Hprot_r] &
          [HPublicLink_consistent HPublicLink_consistent_r]) #Hk #Ht".
iSplit.
- iIntros "%Hopen". case: Hopen => t1 Hopen.
  by iApply (public_open_l_auth Hopen with "Hstates_l HPublicLink_consistent Hprot_l Hk Ht").
- iIntros "%Hopen". case: Hopen => t1' Hopen.
  by iApply (public_open_r_auth Hopen with "Hstates_r HPublicLink_consistent_r Hprot_r Hk Ht").
Qed.

Lemma public_open_fupd E k k' t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  |={E}=> ⌜is_Some (Spec.open k t) ↔ is_Some (Spec.open k' t')⌝.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Hk #Ht".
iInv "Hinv" as ">(%states_l & %states_r & Hbody)".
iDestruct (public_open_open with "Hbody Hk Ht") as %Hiff.
iModIntro. iSplitL; last done.
iModIntro. iExists states_l, states_r. iFrame.
Qed.

End AttackerDecryption.

Section HonestDecryption.

Lemma public_open_aenc_fupd E (sk sk' : aenc_key) t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  PUB⟨Spec.pkey sk, Spec.pkey sk'⟩ -∗
  publicly_linked (Spec.pkey sk) (Spec.pkey sk') -∗
  PUB⟨t, t'⟩ ={E}=∗
  match Spec.open sk t, Spec.open sk' t' with
  | Some u, Some u' => PUB⟨u, u'⟩ ∨ publicly_linked t t'
  | Some u, None =>
    publicly_linked t t' ∧ secret_in_l sk ∧ secret_in_l u
  | None, Some u' =>
    publicly_linked t t' ∧ secret_in_r sk' ∧ secret_in_r u'
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
  iDestruct (public_TSeal with "Ht") as "[[_ Hu]|(_ & _ & Hl & _)]";
    iModIntro; by [iLeft|iRight].
- move/Spec.open_aenc_Some: (eL) => ?; subst t.
  iDestruct (public_TSeal_term with "Ht") as "[(%k' & %u' & ->)|(Hl & Ho & _)]";
    last by iModIntro; iSimpl in "Ho"; iFrame "#".
  have Hk' : k' ≠ TKey AEnc sA'.
  { move=> ?; subst k'.
    have := proj2 (Spec.open_aenc_Some sA' (TSeal (TKey AEnc sA') u') u') eq_refl.
    by rewrite eR. }
  iDestruct (public_TSeal with "Ht") as "[[Hk _]|(_ & _ & Hl & [[[Hkl _] _]|[Ho _]])]".
  + iMod (public_part_bij' with "Hctx Hpk Hk") as %Hiff; first done.
    by case: Hk'; symmetry; apply Hiff.
  + iDestruct (linked_in_l_publicly_linked_in_l with "Hkl Hlink_l") as %?.
    by case: Hk'; congruence.
  + iModIntro. iSimpl in "Ho". iFrame "#".
- move/Spec.open_aenc_Some: (eR) => ?; subst t'.
  iDestruct (public_term_TSeal with "Ht") as "[(%k & %u & ->)|(Hl & _ & Ho)]";
    last by iModIntro; iSimpl in "Ho"; iFrame "#".
  have Hk : k ≠ TKey AEnc sA.
  { move=> ?; subst k.
    have := proj2 (Spec.open_aenc_Some sA (TSeal (TKey AEnc sA) u) u) eq_refl.
    by rewrite eL. }
  iDestruct (public_TSeal with "Ht") as "[[Hk _]|(_ & _ & Hl & [[[_ Hkr] _]|[_ Ho]])]".
  + iMod (public_part_bij' with "Hctx Hk Hpk") as %Hiff; first done.
    by case: Hk; apply Hiff.
  + iDestruct (linked_in_r_publicly_linked_in_r with "Hkr Hlink_r") as %?.
    by case: Hk; congruence.
  + iModIntro. iSimpl in "Ho". iFrame "#".
- by iModIntro.
Qed.

Lemma public_open_senc_fupd E (k k' : senc_key) t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  secret_in_l k -∗
  secret_in_r k' -∗
  PUB⟨t, t'⟩ ={E}=∗
  ⌜is_Some (Spec.open k t) ∨ is_Some (Spec.open k' t')⌝ → publicly_linked t t'.
Proof.
move=> HE. case: k k' => [s] [s'].
rewrite [term_of_senc_key]unlock /=.
iIntros "#Hctx #Hs #Hs' #Ht".
iDestruct (public_cases with "Ht") as "[Hsh|[Hl _]]"; last by iModIntro; iIntros.
case eL: (Spec.open (TKey SEnc s) t) => [u|].
{ move/Spec.open_senc_Some: (eL) => ?; subst t.
  case: t' => [?|? ?|?|? ?|k1 u1|?|? ? ?]; iSimpl in "Hsh"; try by iDestruct "Hsh" as "[]".
  iDestruct "Hsh" as "[Hk _]".
  by iMod (secret_in_l_public_fupd with "Hctx Hs Hk") as "[]". }
case eR: (Spec.open (TKey SEnc s') t') => [u'|].
{ move/Spec.open_senc_Some: (eR) => ?; subst t'. clear eL.
  case: t => [?|? ?|?|? ?|k1 u1|?|? ? ?]; iSimpl in "Hsh"; try by iDestruct "Hsh" as "[]".
  iDestruct "Hsh" as "[Hk _]".
  by iMod (secret_in_r_public_fupd with "Hctx Hs' Hk") as "[]". }
iModIntro. iIntros ([[? ?]|[? ?]]); congruence.
Qed.

End HonestDecryption.

End PublicProperties.
