(** * Protection, admission, and partial bijection for [PUB]

- [Protection]: a hidden or secret term is related to nothing.
- [Release]: once a key is public, its publicly linked ciphertexts have
  related payloads.
- [Admission]: a term in the states map has used up its states token.
- [PartBij]: a term is related to at most one term in the other run.

Lemmas ending in [_fupd] open the invariant themselves. *)

From iris.algebra Require Import gmap gset.
From reloc Require Import reloc.
From cryptis Require Import cryptis.
From cryptis.hyper.core Require Import minted_spec term_meta_spec.
From cryptis.hyper.core.public Require Import state states base rules.
Import State.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicBijection.

Context `{!relocG Σ, !publicGS Σ}.

Abbreviation iProp := (iProp Σ).
Abbreviation iPropO := (iPropO Σ).

Implicit Types t tsub tsup troot tprot t'sub t'sup t'root t'prot : term.
Implicit Types st : state.
Implicit Types states_l states_r : gmap term state.
Implicit Types P : term -> term -> iProp.

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

Lemma secret_in_l_public states_l {t t'} :
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  public_states_l_deposits states_l -∗
  secret_in_l t -∗ PUB⟨t, t'⟩ -∗ False.
Proof.
iIntros "Hstates Hdeps Hs Ht".
iDestruct (secret_in_l_lookup with "Hstates Hs") as %Hsec.
by iApply (public_protected_l (λ _ _, eq_refl) with "Hstates Hdeps [] Ht").
Qed.

Lemma secret_in_r_public states_r {t t'} :
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

Lemma public_TSeal_l_open states_l {k t k' t' dk dk'} :
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

Lemma public_TSeal_r_open states_r {k t k' t' dk dk'} :
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

End Release.

Section LinkedShape.

Lemma public_linked_in_l states_l :
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

Lemma public_linked_in_r states_r :
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

Lemma public_part_bij_1_auth states_l {t t1' t2'} :
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

Lemma public_part_bij_2_auth states_r {t1 t2 t'} :
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

End PublicBijection.
