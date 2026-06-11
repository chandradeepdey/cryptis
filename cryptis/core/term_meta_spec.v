From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list reservation_map excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis.lib Require Import gmeta nown saved_prop.
From cryptis.core Require Import term minted.

From cryptis.core Require Import term_meta.
From reloc Require Import reloc.
From cryptis.core Require Import minted_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Existing Instance term_meta_meta.
#[local] Existing Instance term_meta_names.

Class term_meta_specGS Σ : Type := TermMetaSpecGS {
  #[global] term_meta_spec_inG  :: term_metaGpreS Σ;
  term_meta_spec_name : gname;
}.

Section TermMetaSpec.

Context `{!relocG Σ}.
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).

Definition term_meta_spec_inv `{!term_meta_specGS Σ} : iProp :=
  ∃ names : gmap term gname,
    own term_meta_spec_name (● ((to_agree <$> names) : gmap _ _)) ∗
    [∗ set] t ∈ dom names, minted_spec t.

Definition term_meta_spec_ctx `{!term_meta_specGS Σ} : iProp :=
  inv (nroot.@"cryptis".@"meta") term_meta_spec_inv.

Lemma term_meta_specGS_alloc E :
  term_metaGpreS Σ →
  ⊢ |={E}=> ∃ (H : term_meta_specGS Σ), term_meta_spec_ctx.
Proof.
move=> ?; iStartProof.
iMod (own_alloc (● (∅ : gmap term (agree gname)))) as (γ_names) "names_auth".
  by apply auth_auth_valid.
pose (H := TermMetaSpecGS _ γ_names).
iExists H. iApply inv_alloc.
iExists ∅. rewrite fmap_empty /=. iFrame.
by rewrite dom_empty_L big_sepS_empty.
Qed.

Context `{!term_meta_specGS Σ}.

Global Instance term_meta_spec_inv_timeless : Timeless term_meta_spec_inv.
Proof. rewrite /term_meta_spec_inv. apply _. Qed.

#[global]
Instance term_meta_spec_ctx_persistent : Persistent term_meta_spec_ctx.
Proof. apply _. Qed.

Class HasTermMetaSpecCtx (ctx : iProp) := {
  has_term_meta_spec_ctx : ctx ⊢ term_meta_spec_ctx;
  has_term_meta_spec_ctx_persistent : Persistent ctx;
}.

Local Existing Instance has_term_meta_spec_ctx_persistent.

Definition term_spec_name t γ : iProp :=
  minted_spec t ∗
  own term_meta_spec_name (◯ {[t := to_agree γ]}).

Global Instance term_spec_name_persistent t γ : Persistent (term_spec_name t γ).
Proof. apply _. Qed.

Global Instance term_spec_name_timeless t γ : Timeless (term_spec_name t γ).
Proof. apply _. Qed.

Lemma term_spec_name_agree t γ1 γ2 :
  term_spec_name t γ1 -∗
  term_spec_name t γ2 -∗
  ⌜γ1 = γ2⌝.
Proof.
iIntros "[_ name1] [_ name2]".
iPoseProof (own_valid_2 with "name1 name2") as "%valid".
rewrite -auth_frag_op auth_frag_valid in valid.
move/(_ t): valid.
rewrite lookup_op !lookup_singleton_eq -Some_op Some_valid.
by move=> /to_agree_op_inv_L ->.
Qed.

Lemma term_spec_name_minted_spec t γ : term_spec_name t γ -∗ minted_spec t.
Proof. by iIntros "[? _]". Qed.

Definition term_token_spec_def t E : iProp :=
  ∃ γ, term_spec_name t γ ∗ gmeta_token γ E.
Definition term_token_spec_aux : seal term_token_spec_def. by eexists. Qed.
Definition term_token_spec := unseal term_token_spec_aux.
Lemma term_token_spec_unseal : term_token_spec = term_token_spec_def.
Proof. exact: seal_eq. Qed.

Definition term_meta_spec_def `{Countable L} t N (x : L) : iProp :=
  ∃ γ, term_spec_name t γ ∗ gmeta γ N x.
Definition term_meta_spec_aux : seal (@term_meta_spec_def). by eexists. Qed.
Definition term_meta_spec := unseal term_meta_spec_aux.
Lemma term_meta_spec_unseal : @term_meta_spec = @term_meta_spec_def.
Proof. exact: seal_eq. Qed.
Arguments term_meta_spec {L _ _} t N x.

Lemma term_token_spec_minted_spec t E : term_token_spec t E -∗ minted_spec t.
Proof.
rewrite term_token_spec_unseal. iIntros "(%γ & #name & _)".
by iApply term_spec_name_minted_spec.
Qed.

Lemma term_meta_spec_minted_spec `{Countable L} t N (x : L) :
  term_meta_spec t N x -∗ minted_spec t.
Proof.
rewrite term_meta_spec_unseal. iIntros "(%γ & #name & _)".
by iApply term_spec_name_minted_spec.
Qed.

Global Instance term_token_spec_timeless t E : Timeless (term_token_spec t E).
Proof. rewrite term_token_spec_unseal. apply _. Qed.

Global Instance term_meta_spec_timeless `{Countable L} t N (x : L) :
  Timeless (term_meta_spec t N x).
Proof. rewrite term_meta_spec_unseal. apply _. Qed.

Global Instance term_meta_spec_persistent `{Countable L} t N (x : L) :
  Persistent (term_meta_spec t N x).
Proof. rewrite term_meta_spec_unseal. apply _. Qed.

Lemma term_token_spec_drop E1 E2 t :
  E1 ⊆ E2 → term_token_spec t E2 -∗ term_token_spec t E1.
Proof.
rewrite term_token_spec_unseal.
iIntros "% (%γ & #name & token)".
iExists γ. iSplit => //. by iApply gmeta_token_drop.
Qed.

Lemma term_token_spec_disj E1 E2 t :
  term_token_spec t E1 -∗ term_token_spec t E2 -∗ ⌜E1 ## E2⌝.
Proof.
rewrite term_token_spec_unseal.
iIntros "(% & #name1 & token1) (% & #name2 & token2)".
iPoseProof (term_spec_name_agree with "name1 name2") as "<-".
iApply (gmeta_token_disj with "token1 token2").
Qed.

Lemma term_token_spec_difference t E1 E2 :
  E1 ⊆ E2 → term_token_spec t E2 ⊣⊢ term_token_spec t E1 ∗ term_token_spec t (E2 ∖ E1).
Proof.
rewrite term_token_spec_unseal.
move=> sub. iSplit.
- iIntros "(% & #name & token)".
  rewrite (gmeta_token_difference _ _ _ sub).
  iDestruct "token" as "[token1 token2]".
  by iSplitL "token1"; iExists _; iFrame.
- iIntros "[(% & #name1 & token1) (% & #name2 & token2)]".
  iPoseProof (term_spec_name_agree with "name1 name2") as "<-".
  iExists _; iSplit => //.
  rewrite (gmeta_token_difference _ _ _ sub). by iFrame.
Qed.

Lemma term_meta_spec_token `{Countable L} t (x : L) N E :
  ↑N ⊆ E → term_token_spec t E -∗ term_meta_spec t N x -∗ False.
Proof.
rewrite term_token_spec_unseal term_meta_spec_unseal => sub.
iIntros "(% & #name1 & token) (% & #name2 & #meta_spec)".
iPoseProof (term_spec_name_agree with "name1 name2") as "<-".
by iApply (gmeta_gmeta_token with "token meta_spec").
Qed.

Lemma term_meta_spec_set' `{Countable L} N (x : L) E t :
  ↑N ⊆ E → term_token_spec t E ==∗ term_meta_spec t N x ∗ term_token_spec t (E ∖ ↑N).
Proof.
rewrite term_token_spec_unseal term_meta_spec_unseal.
iIntros "%sub (%γ & #name & token)".
iMod (gmeta_set' _ _ _ x sub with "token") as "[#meta_spec token]".
iModIntro.
by iSplit; iExists _; iSplit => //.
Qed.

Lemma term_meta_spec_set `{Countable L} N (x : L) E t :
  ↑N ⊆ E → term_token_spec t E ==∗ term_meta_spec t N x.
Proof.
iIntros "%sub token".
iMod (term_meta_spec_set' x _ sub with "token") as "[#meta_spec token]".
by iModIntro.
Qed.

Lemma term_meta_spec_agree `{Countable L} t N (x1 x2 : L) :
  term_meta_spec t N x1 -∗ term_meta_spec t N x2 -∗ ⌜x1 = x2⌝.
Proof.
rewrite term_meta_spec_unseal.
iIntros "(% & #name1 & #meta_spec1) (% & #name2 & #meta_spec2)".
iPoseProof (term_spec_name_agree with "name1 name2") as "<-".
iApply (gmeta_agree with "meta_spec1 meta_spec2").
Qed.

Lemma term_token_spec_switch t N' Q : ⊢ switch (term_token_spec t (↑N')) Q.
Proof.
iExists (term_meta_spec t N' ()). iSplit; iModIntro.
- iIntros "[token #meta_spec]".
  by iDestruct (term_meta_spec_token with "token meta_spec") as "[]".
- iIntros "token".
  by iMod (term_meta_spec_set () with "token") as "#meta_spec".
Qed.

Section TermOwnSpec.

Definition term_own_spec_def `{inG Σ A} t N (x : A) : iProp :=
  ∃ γ, term_spec_name t γ ∗ nown γ N x.
Definition term_own_spec_aux : seal (@term_own_spec_def). by eexists. Qed.
Definition term_own_spec := unseal (@term_own_spec_aux).
Lemma term_own_spec_unseal : @term_own_spec = @term_own_spec_def.
Proof. exact: seal_eq. Qed.
Arguments term_own_spec {A _} t N x.

Context `{inG Σ A}.

Lemma term_own_spec_alloc t N {E} (a : A) :
  ↑N ⊆ E → ✓ a → term_token_spec t E ==∗ term_own_spec t N a ∗ term_token_spec t (E ∖ ↑N).
Proof.
rewrite term_own_spec_unseal term_token_spec_unseal.
iIntros "%sub %val (% & #name & token)".
iMod (nown_alloc _ _ sub val with "token") as "[own token]".
iModIntro.
by iSplitL "own"; iExists _; iFrame.
Qed.

Lemma term_token_spec_own t N E (a : A) :
  ↑N ⊆ E → term_token_spec t E -∗ term_own_spec t N a -∗ False.
Proof.
rewrite term_own_spec_unseal term_token_spec_unseal.
iIntros "%sub (%γ & #name & token) (%γ' & #name' & own)" .
iPoseProof (term_spec_name_agree with "name name'") as "->".
by iApply (nown_token with "token own").
Qed.

Lemma term_own_spec_valid t N (a : A) : term_own_spec t N a -∗ ✓ a.
Proof.
rewrite term_own_spec_unseal.
iIntros "(%γ' & #own_γ & own)". iApply (nown_valid with "own").
Qed.

Lemma term_own_spec_valid_2 t N (a1 a2 : A) :
  term_own_spec t N a1 -∗ term_own_spec t N a2 -∗ ✓ (a1 ⋅ a2).
Proof.
rewrite term_own_spec_unseal.
iIntros "(%γ1 & #own_γ1 & own1) (%γ2 & #own_γ2 & own2)".
iPoseProof (term_spec_name_agree with "own_γ1 own_γ2") as "<-".
by iApply (nown_valid_2 with "own1 own2").
Qed.

Lemma term_own_spec_update t N (a a' : A) :
  a ~~> a' → term_own_spec t N a ==∗ term_own_spec t N a'.
Proof.
rewrite term_own_spec_unseal.
iIntros (?) "(%γ' & #? & own)".
iMod (nown_update with "own") as "own"; eauto.
iModIntro. iExists γ'. eauto.
Qed.

#[global]
Instance term_own_spec_core_persistent t N (a : A) :
  CoreId a → Persistent (term_own_spec t N a).
Proof. rewrite term_own_spec_unseal. apply _. Qed.

#[global]
Instance term_own_spec_timeless t N (a : A) :
  Discrete a → Timeless (term_own_spec t N a).
Proof. rewrite term_own_spec_unseal. apply _. Qed.

#[global]
Instance term_own_spec_ne t N : NonExpansive (@term_own_spec A _ t N).
Proof. rewrite term_own_spec_unseal. solve_proper. Qed.

#[global]
Instance term_own_spec_proper t N : Proper ((≡) ==> (≡)) (@term_own_spec A _ t N).
Proof. rewrite term_own_spec_unseal. solve_proper. Qed.

Lemma term_own_spec_op t N (a1 a2 : A) :
  term_own_spec t N (a1 ⋅ a2) ⊣⊢ term_own_spec t N a1 ∗ term_own_spec t N a2.
Proof.
rewrite term_own_spec_unseal.
iSplit.
- iIntros "(%γ' & #? & [own1 own2])".
  by iSplitL "own1"; iExists γ'; iSplit.
- iIntros "[(%γ1 & #own_γ1 & own1) (%γ2 & #own_γ2 & own2)]".
  iPoseProof (term_spec_name_agree with "own_γ1 own_γ2") as "<-".
  iExists γ1. iSplit => //. by iSplitL "own1".
Qed.

#[global]
Instance from_sep_term_own_spec t N (a b1 b2 : A) :
  IsOp a b1 b2 → FromSep (term_own_spec t N a) (term_own_spec t N b1) (term_own_spec t N b2).
Proof.
by rewrite /IsOp /FromSep => ->; rewrite term_own_spec_op.
Qed.

#[global]
Instance combine_sep_as_term_own_spec t N (a b1 b2 : A) :
  IsOp a b1 b2 → CombineSepAs (term_own_spec t N b1) (term_own_spec t N b2) (term_own_spec t N a).
Proof. exact: from_sep_term_own_spec. Qed.

#[global]
Instance into_sep_term_own_spec t N (a b1 b2 : A) :
  IsOp a b1 b2 → IntoSep (term_own_spec t N a) (term_own_spec t N b1) (term_own_spec t N b2).
Proof.
by rewrite /IsOp /IntoSep => ->; rewrite term_own_spec_op.
Qed.

#[global]
Instance combine_sep_gives_term_own_spec t N (a1 a2 : A) :
  CombineSepGives (term_own_spec t N a1) (term_own_spec t N a2) (✓ (a1 ⋅ a2)).
Proof.
rewrite /CombineSepGives. iIntros "[H1 H2]".
by iPoseProof (term_own_spec_valid_2 with "H1 H2") as "#?".
Qed.

Lemma term_own_spec_mono t N (a1 a2 : A) : a1 ≼ a2 → term_own_spec t N a2 -∗ term_own_spec t N a1.
Proof.
case => ? ->.
rewrite term_own_spec_op.
by iIntros "[??]".
Qed.

Lemma term_own_spec_update_2 t N (a1 a2 a' : A) :
  a1 ⋅ a2 ~~> a' →
  term_own_spec t N a1 -∗
  term_own_spec t N a2 ==∗
  term_own_spec t N a'.
Proof.
iIntros "% H1 H2".
iMod (term_own_spec_update with "[H1 H2]") as "H" => //.
by iSplitL "H1".
Qed.

End TermOwnSpec.

#[global] Typeclasses Opaque term_own_spec.

Lemma term_token_spec_alloc_aux (T : gset term) (P Q : iProp) E :
  (∀ t, ⌜t ∈ T⌝ -∗ P -∗ minted_spec t -∗ False) -∗
  (∀ t, ⌜t ∈ T⌝ -∗ Q -∗ minted_spec t) -∗
  (P ∧ |={E}=> Q) -∗
  term_meta_spec_inv ={E}=∗
  term_meta_spec_inv ∗ Q ∗ [∗ set] t ∈ T, term_token_spec t ⊤.
Proof.
assert (∀ names : gmap term gname,
  dom names ## T →
  own term_meta_spec_name (● ((to_agree <$> names) : gmap term _)) ==∗
  ∃ names' : gmap term gname,
  ⌜dom names' = dom names ∪ T⌝ ∗
  own term_meta_spec_name (● ((to_agree <$> names') : gmap term _)) ∗
  [∗ set] t ∈ T, minted_spec t -∗ term_token_spec t ⊤) as names_alloc.
{ induction T as [|t T fresh IH] using set_ind_L.
  - iIntros "%names _ own !>". iExists names.
    by rewrite right_id_L big_sepS_empty; iFrame.
  - iIntros "%names %dis own".
    have t_names : t ∉ dom names by set_solver.
    have {}dis : dom names ## T by set_solver.
    iMod gmeta_token_alloc as "(%γ & token)".
    iMod (own_update with "own") as "[own frag]".
    { eapply auth_update_alloc.
      apply (alloc_singleton_local_update _ t (to_agree γ)) => //.
      by rewrite lookup_fmap (_ : names !! t = None) // -not_elem_of_dom. }
    rewrite -fmap_insert.
    have {}dis: dom (<[t := γ]>names) ## T.
      rewrite dom_insert; set_solver.
    iMod (IH _ dis with "own") as "(%names' & %dom_names' & own & tokens)".
    iModIntro. iExists names'. iFrame.
    rewrite dom_names' dom_insert_L. iSplit; first by iPureIntro; set_solver.
    rewrite big_sepS_union; last by set_solver.
    iFrame. rewrite big_sepS_singleton.
    iIntros "#m_t". rewrite term_token_spec_unseal. iExists γ. by iFrame. }
iIntros "PE QE PQ (%names & own & #minted_spec_names)".
iAssert (⌜dom names ## T⌝)%I as "%dis".
{ rewrite elem_of_disjoint. iIntros "%t %t_names %t_T".
  rewrite big_sepS_delete //. iDestruct "minted_spec_names" as "[minted_spec_t _]".
  iDestruct "PQ" as "[P _]".
  iApply ("PE" with "[//] P minted_spec_t"). }
iMod (names_alloc _ dis with "own") as "(%names' & %dom_names & own & tokens)".
iDestruct "PQ" as "[_ >Q]".
iAssert ([∗ set] t ∈ T, minted_spec t)%I as "#minted_spec_T".
{ rewrite (big_sepS_forall _ T). iIntros "%t %t_T".
  by iApply ("QE" with "[//] Q"). }
iCombine "minted_spec_T tokens" as "tokens". rewrite -big_sepS_sep.
iModIntro. iFrame. iSplit.
- rewrite dom_names big_sepS_union //. by iSplit.
- iApply (big_sepS_impl with "tokens").
  iIntros "!> %t _ [#m_t token]". by iApply "token".
Qed.

Variable ctx: iProp.

Context `{!HasTermMetaSpecCtx ctx}.

Lemma term_token_spec_alloc (T : gset term) (P Q : iProp) E :
  ↑nroot.@"cryptis".@"meta" ⊆ E →
  ctx -∗
  (∀ t, ⌜t ∈ T⌝ -∗ P -∗ minted_spec t -∗ False) -∗
  (∀ t, ⌜t ∈ T⌝ -∗ Q -∗ minted_spec t) -∗
  (P ∧ |={E ∖ ↑nroot.@"cryptis".@"meta"}=> Q) ={E}=∗
  Q ∗ [∗ set] t ∈ T, term_token_spec t ⊤.
Proof.
iIntros "%sub ctx H1 H2 H3".
iPoseProof (has_term_meta_spec_ctx with "ctx") as "{ctx} #ctx".
iInv "ctx" as ">inv" => //.
iMod (term_token_spec_alloc_aux with "H1 H2 H3 inv") as "(inv & post & token)".
iModIntro. by iFrame.
Qed.

End TermMetaSpec.

Arguments term_token_spec {Σ _ _} t E.
Arguments term_meta_spec {Σ _ _ L _ _} t N x.
Arguments term_meta_spec_set {Σ _ _ _ _ _} N x E t.
Arguments term_token_spec_difference {Σ _ _} t E1 E2.
Arguments term_token_spec_drop {Σ _ _} E1 E2 t.
Arguments term_spec_name {Σ _ _} t γ.
Arguments term_own_spec {Σ _ _ A _} t N x.
Arguments term_own_spec_alloc {Σ _ _ A _ t} N {_} a.
Arguments term_own_spec_update {Σ _ _ A _ t N a} a'.

Section TermPropSpec.

Context `{!relocG Σ, !term_meta_specGS Σ, !savedPropG Σ}.

Definition term_prop_spec t N : iProp Σ :=
  ∃ P : iProp Σ, term_own_spec t N (saved_prop DfracDiscarded P) ∧ ▷ P.

Lemma term_prop_spec_alloc t N P E :
  ↑N ⊆ E →
  term_token_spec t E ==∗
  □ (term_prop_spec t N ↔ ▷ P) ∗
  term_token_spec t (E ∖ ↑N).
Proof.
iIntros "%sub token".
iMod (term_own_spec_alloc N (saved_prop DfracDiscarded P) with "token")
  as "[#own alloc]" => //.
iFrame. iIntros "!> !>". iSplit.
- iIntros "(%Q & #own' & HQ)".
  iPoseProof (term_own_spec_valid_2 with "own own'") as "#valid".
  rewrite saved_prop_op_validI.
  iDestruct "valid" as "[_ valid]". iNext.
  by iRewrite "valid".
- iIntros "HP". iExists P. by eauto.
Qed.

Lemma term_token_spec_prop t N E :
  ↑N ⊆ E → term_token_spec t E -∗ term_prop_spec t N -∗ False.
Proof.
iIntros "%sub token (%P & #own & HP)".
by iApply (term_token_spec_own with "token own").
Qed.

End TermPropSpec.

Section TermPredSpec.

Context {A : Type} `{!relocG Σ, !term_meta_specGS Σ, !savedPredG Σ A}.

Implicit Types (φ : A → iProp Σ) (x : A).

Definition term_pred_spec t N x : iProp Σ :=
  ∃ φ, term_own_spec t N (saved_pred DfracDiscarded φ) ∧ ▷ φ x.

Lemma term_pred_spec_alloc t N E φ :
  ↑N ⊆ E →
  term_token_spec t E ==∗
  □ (∀ x, term_pred_spec t N x ↔ ▷ φ x) ∗
  term_token_spec t (E ∖ ↑N).
Proof.
iIntros "%sub token".
iMod (term_own_spec_alloc N (saved_pred DfracDiscarded φ) with "token")
  as "[#own alloc]" => //.
iFrame. iIntros "!> !> %x". iSplit.
- iIntros "(%Ψ & #own' & HΨ)".
  iPoseProof (term_own_spec_valid_2 with "own own'") as "#valid".
  rewrite saved_pred_op_validI.
  iDestruct "valid" as "[_ #valid]". iSpecialize ("valid" $! x). iNext.
  by iRewrite "valid".
- iIntros "Hφ". iExists φ. by eauto.
Qed.

Lemma term_token_spec_pred t N E x :
  ↑N ⊆ E → term_token_spec t E -∗ term_pred_spec t N x -∗ False.
Proof.
iIntros "%sub token (%φ & #own & Hφ)".
by iApply (term_token_spec_own with "token own").
Qed.

End TermPredSpec.
