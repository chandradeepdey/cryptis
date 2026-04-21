From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list excl.
From iris.algebra Require Import functions.
From iris.algebra.lib Require Import gset_bij mono_list.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib gmeta nown.
From cryptis.core Require Import term minted public.

From reloc Require Import reloc.
From cryptis.core Require Import minted_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class public_relGpreS Σ := Public_relGpreS {
  #[local] public_relGpreS_trace :: inG Σ (mono_listUR (term * term)%type);
  #[local] public_relGpreS_pub :: inG Σ (gset_bijUR term term);
  #[local] public_relGpreS_priv :: inG Σ (authUR (gset_disjUR (term * term)));
  #[local] public_relGpreS_flow_l :: inG Σ (authUR (gset_disjUR (term *  term)));
  #[local] public_relGpreS_flow_r :: inG Σ (authUR (gset_disjUR (term *  term)));
}.

Class public_relGS Σ := Public_relGS {
  #[local] public_rel_inG :: public_relGpreS Σ;
  public_rel_trace_name  : gname;
  public_rel_pub_name  : gname;
  public_rel_priv_name  : gname;
  public_rel_flow_l_name  : gname;
  public_rel_flow_r_name  : gname;
}.

Definition public_relΣ : gFunctors :=
  #[GFunctor (authUR (gset_disjUR (term * term)));
    GFunctor (authUR (gset_disjUR (term * term)));
    GFunctor (authUR (gset_disjUR (term * term)));
    GFunctor (mono_listUR (term * term)%type);
    GFunctor (gset_bijUR term term)].

Global Instance subG_public_relGpreS Σ : subG public_relΣ Σ → public_relGpreS Σ.
Proof. solve_inG. Qed.

Implicit Types (tr: list (term * term)) (pub priv flow_l flow_r: gset (term * term)).
Inductive dolev_yao tr : term -> term -> Prop :=
  | dy_in t1 t2 : (t1, t2) ∈ tr -> dolev_yao tr t1 t2
  | dy_int n : dolev_yao tr (TInt n) (TInt n)
  | dy_pair t1a t1b t2a t2b : dolev_yao tr t1a t2a -> dolev_yao tr t1b t2b -> dolev_yao tr (TPair t1a t1b) (TPair t2a t2b)
  | dy_fst t1a t1b t2a t2b : dolev_yao tr (TPair t1a t1b) (TPair t2a t2b) -> dolev_yao tr t1a t2a
  | dy_snd t1a t1b t2a t2b : dolev_yao tr (TPair t1a t1b) (TPair t2a t2b) -> dolev_yao tr t1b t2b
  | dy_hash t1 t2 : dolev_yao tr t1 t2 -> dolev_yao tr (THash t1) (THash t2)
  | dy_key kt t1 t2 : dolev_yao tr t1 t2 -> dolev_yao tr (TKey kt t1) (TKey kt t2)
  | dy_seal k1 k2 t1 t2 : dolev_yao tr k1 k2 -> dolev_yao tr t1 t2 -> dolev_yao tr (TSeal k1 t1) (TSeal k2 t2)
  | dy_unseal k1 k2 t1 t1' t2 t2' : dolev_yao tr k1 k2 -> dolev_yao tr t1 t2 -> Spec.open k1 t1 = Some t1' -> Spec.open k2 t2 = Some t2' -> dolev_yao tr t1' t2'.

Definition dolev_yao_consistent tr :=
  (∀ t1 t1' t2 t2', dolev_yao tr t1 t1' -> dolev_yao tr t2 t2' ->
    t1 = t2 <-> t1' = t2') ∧
  (∀ t1 t2, dolev_yao tr t1 t2 -> Spec.to_int t1 = Spec.to_int t2) ∧
  (∀ t1 t2, dolev_yao tr t1 t2 ->
    is_Some (Spec.untuple t1) <-> is_Some (Spec.untuple t2)) ∧
  (∀ t1 t1' t2 t2', dolev_yao tr t1 t1' -> dolev_yao tr t2 t2' ->
    is_Some (Spec.open t1 t2) <-> is_Some (Spec.open t1' t2')) ∧
  (∀ t1 t2, dolev_yao tr t1 t2 -> Spec.is_key t1 = Spec.is_key t2).

Definition tables_consistent tr pub priv flow_l flow_r :=
  gset_bijective pub ∧
  gset_bijective priv ∧
  (* pub and priv cannot contain the same term *)
  (∀ t1 t2 t2', (t1, t2) ∈ pub → (t1, t2') ∈ priv → False) ∧
  (∀ t1 t1' t2, (t1, t2) ∈ pub → (t1', t2) ∈ priv → False) ∧
  (* pub is an extension of the trace, but not the full Dolev-Yao closure *)
  (∀ t1 t2, (t1, t2) ∈ tr → (t1, t2) ∈ pub) ∧
  (∀ t1 t2, (t1, t2) ∈ pub → dolev_yao tr t1 t2) ∧
  (* priv restricts what can become publicly related eventually *)
  (∀ t1 t2 t2', (t1, t2) ∈ priv → dolev_yao tr t1 t2' → t2 = t2') ∧
  (∀ t1 t1' t2, (t1, t2) ∈ priv → dolev_yao tr t1' t2 → t1 = t1') ∧
  (* flow must be consistent with pub *)
  (∀ t1 t1' t2, (t1, t1') ∈ flow_l → (t1, t2) ∈ pub → ∃ t2', (t1', t2') ∈ pub) ∧
  (∀ t1 t2 t2', (t2, t2') ∈ flow_r → (t1, t2) ∈ pub → ∃ t1', (t1', t2') ∈ pub).

Section Rel.

Context `{!relocG Σ, !public_relGS Σ, !publicGS Σ}.

Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).

Definition public_rel_trace_auth (trace: list (term * term)) : iProp :=
  own public_rel_trace_name (●ML trace).

Definition public_rel_pub_auth (pub: gset (term * term)) : iProp :=
  own public_rel_pub_name (gset_bij_auth (DfracOwn 1) pub).

Definition public_rel_priv_auth (priv: gset (term * term)) : iProp :=
  own public_rel_priv_name (● (GSet priv)).

Definition public_rel_flow_l_auth (flow_l: gset (term * term)) : iProp :=
  own public_rel_flow_l_name (● (GSet flow_l)).

Definition public_rel_flow_r_auth (flow_r: gset (term * term)) : iProp :=
  own public_rel_flow_l_name (● (GSet flow_r)).

Definition cryptis_rel_N := nroot .@ "cryptis_rel".

(* to be addressed- probably should not have existentials *)
Definition cryptis_rel_inv : iProp :=
  ∃ tr pub priv flow_l flow_r,
      public_rel_trace_auth tr ∗
      public_rel_pub_auth pub ∗
      public_rel_priv_auth priv ∗
      public_rel_flow_l_auth flow_l ∗
      public_rel_flow_r_auth flow_r ∗
    ⌜dolev_yao_consistent tr ∧ tables_consistent tr pub priv flow_l flow_r⌝.


Definition nonce_rel_auth R : iProp :=
  nown public_term_part_bij_name (nroot.@"nonce")
    (gset_bij_auth (DfracOwn 1) R).

Definition nonce_rel_frag t1 t2 : iProp :=
  nown public_term_part_bij_name (nroot.@"nonce")
    (gset_bij_elem t1 t2) ∗
    minted_spec t1 ∗ minted t2.

Lemma nonce_rel_alloc t1 t2 R :
  (∀ t2', (t1, t2') ∉ R) → (∀ t1', (t1', t2) ∉ R) →
  minted_spec t1 ∗ minted t2 ∗
  nonce_rel_auth R ==∗
  nonce_rel_auth ({[(t1, t2)]} ∪ R) ∗
  nonce_rel_frag t1 t2.
Proof.
iIntros "%fresh1 %fresh2 (mt1 & mt2 & own)".
iMod (nown_update with "own") as "own".
apply: gset_bij_auth_extend => //=.
iDestruct "own" as "[auth #frag]".
rewrite -gset_op view_frag_op nown_op.
iDestruct "frag" as "[#frag1 #frag2]".
iModIntro. iFrame "#". iFrame.
iCombine "frag1 frag2" as "#frag".
rewrite /nonce_rel_auth /gset_bij_auth nown_op.
by iFrame "#".
Qed.

Fixpoint public t1 t2 : iProp :=
  match t1, t2 with
  | TInt n1, TInt n2 => ⌜n1 = n2⌝
  | TPair t11 t12, TPair t21 t22 =>
      public t11 t21 ∧ public t12 t22
  | TNonce _, TNonce _ => nonce_rel_frag t1 t2
  | TKey kt1 t1, TKey kt2 t2 =>
      False (* FIXME *)
  | TSeal k1 t1, TSeal k2 t2 =>
      ⌜k1 = k2⌝ ∧ enc_rel_frag k1 t1 t2
  | THash _, THash _ =>
      False (* FIXME *)
  | TExpN' _ _ _, TExpN' _ _ _ =>
      False (* FIXME *)
  | _, _ =>
      False (* WIP *)
  end.

Lemma public_TSeal k R t1 t2 :
  (∀ t2', (t1, t2') ∉ R) → (∀ t1', (t1', t2) ∉ R) →
  enc_rel_auth k R ==∗
  enc_rel_auth k ({[(t1, t2)]} ∪ R) ∗
  public (TSeal k t1) (TSeal k t2).
Proof.
iIntros "%fresh1 %fresh2 H●".
iMod (enc_rel_alloc _ fresh1 fresh2 with "H●") as "[H● H◯]".
by iFrame.
Qed.

Lemma public_TNonce R (t1 t2: loc) :
  (∀ t2', (TNonce t1, t2') ∉ R) → (∀ t1', (t1', TNonce t2) ∉ R) →
  minted_spec (TNonce t1) ∗ minted (TNonce t2) ∗
  nonce_rel_auth R ==∗
  nonce_rel_auth ({[((TNonce t1), (TNonce t2))]} ∪ R) ∗
  public (TNonce t1) (TNonce t2).
Proof.
  iIntros "%fresh1 %fresh2 (#Ht1 & #Ht2 & H●)".
  iMod (nonce_rel_alloc fresh1 fresh2 with "[H●]") as "[H● H◯]".
  - by iFrame "#".
  by iFrame.
Qed.

End Rel.
