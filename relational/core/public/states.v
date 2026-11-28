(** * Ghost state for [PUB]

- [Tokens]: per-term tokens and metadata records.  For a ciphertext, the
  invariant keeps these on its key, so whoever holds the key's tokens
  controls how its ciphertexts are treated; for any other term, it keeps
  them on the term itself.
- [States]: the authoritative state maps for both runs, and the persistent
  fragments recording whether two terms are linked, publicly linked, or
  secret. *)

From iris.algebra Require Import gmap gset.
From reloc Require Import reloc.
From cryptis Require Import cryptis.
From cryptis.hyper.core Require Import term_meta_spec.
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

Section PublicStates.

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

Definition never_sealed_under_l k E : iProp := term_token k E.
Definition never_sealed_under_r k' E' : iProp := term_token_spec k' E'.

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

Lemma never_sealed_under_public_token_l k t E :
  ↑seal_namespace t ⊆ E →
  never_sealed_under_l k E ⊣⊢
  public_token_l (TSeal k t) ∗ never_sealed_under_l k (E ∖ ↑seal_namespace t).
Proof.
move=> sub. rewrite /never_sealed_under_l /public_token_l /=.
by rewrite (term_token_difference k _ E).
Qed.

Lemma never_sealed_under_public_token_r k' t' E' :
  ↑seal_namespace t' ⊆ E' →
  never_sealed_under_r k' E' ⊣⊢
  public_token_r (TSeal k' t') ∗ never_sealed_under_r k' (E' ∖ ↑seal_namespace t').
Proof.
move=> sub'. rewrite /never_sealed_under_r /public_token_r /=.
by rewrite (term_token_spec_difference k' _ E').
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

End PublicStates.
