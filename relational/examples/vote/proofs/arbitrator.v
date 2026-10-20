(** The arbitrator: the model of its slot list and tally, the one-sided
    specs of its pure steps, and the relational proofs of ballot collection
    and of the published result. *)

From cryptis Require Import lib cryptis primitives.
From cryptis.lib Require Import avl.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.core Require Import minted_spec term_meta_spec rel rel_inv_updates.
From cryptis.hyper.primitives Require Import simple_spec comp_spec with_cryptis_spec attacker_spec.
From cryptis.hyper.lib Require Import avl_spec.
From cryptis.hyper.examples.vote Require Import impl.
From cryptis.hyper.examples.vote.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Arbitrator.

Context `{!relocG Σ, !public_relGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (skT : aenc_key) (skV : sign_key).
Implicit Types (votes cands : list Z) (ks : list sign_key).
Implicit Types (st : list (option (term * term))).

(** * Model *)

Definition slot_empty (p : term * option term) : bool :=
  match p.2 with None => true | Some _ => false end.

Definition vote_of skT (t : term) : option Z :=
  match Spec.dec skT (Tag (voteN.@"vote")) t with
  | Some pl =>
    match Spec.untuple pl with Some q => Spec.to_int q.2 | None => None end
  | None => None
  end.

Definition incr (k : Z) (t : AVL.tree) : AVL.tree :=
  AVL.insert k (default 0%Z (AVL.lookup k t) + 1)%Z t.

Definition tally_step skT (p : term * option term) (t : AVL.tree) : AVL.tree :=
  match p.2 with
  | Some ct => match vote_of skT ct with Some k => incr k t | None => t end
  | None => t
  end.

Definition seed cands : AVL.tree := foldr (λ k t, AVL.insert k 0%Z t) AVL.Leaf cands.

Definition pair_of (p : Z * Z) : term := TPair (TInt p.1) (TInt p.2).

Definition result (t : AVL.tree) : term := Spec.of_list (map pair_of (AVL.to_list t)).

Definition slots_l (pks : list term) st : list (term * option term) :=
  zip pks (map (fmap fst) st).

Definition slots_r (pks : list term) st : list (term * option term) :=
  zip pks (map (fmap snd) st).

Fixpoint slots_ok skT skT' votes votes' st {struct st} : Prop :=
  match st, votes, votes' with
  | [], _, _ => True
  | o :: st, v :: votes, v' :: votes' =>
    match o with
    | None => True
    | Some (ct, ct') =>
      ∃ n n', ct = ballot_ct skT n (TInt v) ∧ ct' = ballot_ct skT' n' (TInt v')
    end ∧ slots_ok skT skT' votes votes' st
  | _, _, _ => False
  end.

(** * Pure facts about slots and tallies *)

Lemma slots_ok_replicate skT skT' votes votes' (n : nat) :
  length votes = n → length votes' = n →
  slots_ok skT skT' votes votes' (replicate n None).
Proof.
elim: n votes votes' => [|n IH] [|v votes] [|v' votes'] //= [Hl] [Hl'].
split; first done. exact: IH.
Qed.

Lemma zip_replicate_None (f : term * term → term) (pks : list term) :
  zip pks (map (fmap f) (replicate (length pks) None)) = map (λ pk, (pk, None)) pks.
Proof. by elim: pks => [|pk pks IH] //=; rewrite IH. Qed.

Lemma find_slot_empty_None (f : term * term → term) (pks : list term) st :
  length pks = length st →
  find slot_empty (zip pks (map (fmap f) st)) = None ↔ Forall is_Some st.
Proof.
elim: pks st => [|pk pks IH] [|o st] //= [Hlen].
case: o => [p|] /=; last by split; [discriminate | move=> /Forall_cons [[? ?] _]; discriminate].
rewrite IH // Forall_cons. split; [by split; eauto | by case].
Qed.

Lemma vote_of_ballot skT n (v : Z) : vote_of skT (ballot_ct skT n (TInt v)) = Some v.
Proof. by rewrite /vote_of /ballot_ct /Spec.enc dec_aenc. Qed.

Lemma tally_slots_l_eq skT skT' ks votes votes' st acc :
  length st = length ks → length votes = length ks →
  slots_ok skT skT' votes votes' st → Forall is_Some st →
  foldr (tally_step skT) acc (slots_l (pkeys ks) st) = foldr incr acc votes.
Proof.
elim: st ks votes votes' acc => [|o st IH] [|sk ks] [|v votes] votes' acc //= [Hst] [Hv].
case: votes' => [|v' votes'] //= [Ho Hok] /Forall_cons [Hsome Hall].
case: o Ho Hsome => [[ct ct'] [n [n' [-> ->]]] _|_ []] //=.
rewrite /tally_step /= vote_of_ballot -/(slots_l (pkeys ks) st).
by rewrite (IH ks votes votes' acc Hst Hv Hok Hall).
Qed.

Lemma tally_slots_r_eq skT skT' ks' votes votes' st acc :
  length st = length ks' → length votes' = length ks' →
  slots_ok skT skT' votes votes' st → Forall is_Some st →
  foldr (tally_step skT') acc (slots_r (pkeys ks') st) = foldr incr acc votes'.
Proof.
elim: st ks' votes votes' acc => [|o st IH] [|sk ks'] votes [|v' votes'] acc //= [Hst] [Hv'].
case: votes => [|v votes] //= [Ho Hok] /Forall_cons [Hsome Hall].
case: o Ho Hsome => [[ct ct'] [n [n' [-> ->]]] _|_ []] //=.
rewrite /tally_step /= vote_of_ballot -/(slots_r (pkeys ks') st).
by rewrite (IH ks' votes votes' acc Hst Hv' Hok Hall).
Qed.

Definition incr_map (k : Z) (m : gmap Z Z) : gmap Z Z :=
  <[k := (default 0%Z (m !! k) + 1)%Z]> m.

Lemma bst_seed cands : AVL.bst (seed cands).
Proof.
elim: cands => [|k cands IH] /=; [exact: AVL.bst_leaf | exact: AVL.bst_insert].
Qed.

Lemma to_map_foldr_incr s vs :
  AVL.bst s →
  AVL.bst (foldr incr s vs) ∧
  AVL.to_map (foldr incr s vs) = foldr incr_map (AVL.to_map s) vs.
Proof.
elim: vs => [|v vs IH] //= Hs. move: IH => /(_ Hs) [Hb E]. split.
- exact: AVL.bst_insert.
- by rewrite /incr /incr_map AVL.to_map_insert // AVL.lookup_to_map // E.
Qed.

Lemma incr_map_comm a b m : incr_map a (incr_map b m) = incr_map b (incr_map a m).
Proof.
rewrite /incr_map. case: (decide (a = b)) => [->|ne] //.
rewrite !lookup_insert_ne // (insert_insert _ a b) decide_False //.
Qed.

#[local] Instance incr_map_proper x : Proper ((=) ==> (=)) (incr_map x).
Proof. by move=> ?? ->. Qed.

Lemma foldr_incr_map_perm m vs vs' :
  vs ≡ₚ vs' → foldr incr_map m vs = foldr incr_map m vs'.
Proof.
apply: (foldr_permutation (=) incr_map m) => j1 a1 j2 a2 b _ _ _.
exact: incr_map_comm.
Qed.

Lemma pkeys_zip ks votes :
  length ks ≤ length votes →
  map (λ p : sign_key * Z, Spec.pkey (p.1 : term)) (zip ks votes) = pkeys ks.
Proof.
elim: ks votes => [|sk ks IH] [|v votes] //= Hlen; first lia.
rewrite IH //. lia.
Qed.

(** * Public terms *)

Lemma pub_pair_terms (l : list (Z * Z)) :
  ⊢ PUB⟨Spec.of_list (map pair_of l), Spec.of_list (map pair_of l)⟩.
Proof.
rewrite [Spec.of_list]unlock. elim: l => [|[k v] l IH].
- rewrite -[foldr _ _ _]/(TInt 0) publicly_related_TInt. by iPureIntro.
- rewrite -[foldr TPair (TInt 0) (map pair_of ((k, v) :: l))]
          /(TPair (pair_of (k, v)) (foldr TPair (TInt 0) (map pair_of l))).
  rewrite publicly_related_TPair. iSplit; last by iApply IH.
  rewrite /pair_of publicly_related_TPair !publicly_related_TInt. by iSplit; iPureIntro.
Qed.

(** * One-sided steps of the arbitrator *)

Lemma rel_tally_vote_l K e skT p t Ψ :
  (REL fill K (repr (tally_step skT p t) : expr) << e : Ψ) -∗
  REL fill K (tally_vote skT (repr p) (repr t)) << e : Ψ.
Proof.
iIntros "post". rewrite /tally_vote /tally_step.
case: p => [pk [ct|]] /=; rel_pures_l; last by iApply "post".
rel_apply_l rel_adec'_l. iModIntro. iSplit; last first.
{ iIntros (Hnone). rewrite /vote_of Hnone. rel_pures_l. by iApply "post". }
iIntros (pl _ Hdec). rewrite /vote_of Hdec. rel_pures_l.
rel_apply_l rel_untuple_l.
case: (Spec.untuple pl) => [[q1 q2]|] /=; rel_pures_l; last by iApply "post".
rel_apply_l rel_to_int_l.
case: (Spec.to_int q2) => [k|] /=; rel_pures_l; last by iApply "post".
rel_apply_l rel_avl_lookup_l. rewrite /incr.
case: (AVL.lookup k t) => [n|] /=; rel_pures_l; by rel_apply_l rel_avl_insert_l.
Qed.

Lemma rel_tally_vote_r K e skT p t Ψ :
  (REL e << fill K (repr (tally_step skT p t) : expr) : Ψ) -∗
  REL e << fill K (tally_vote skT (repr p) (repr t)) : Ψ.
Proof.
iIntros "post". rewrite /tally_vote /tally_step.
case: p => [pk [ct|]] /=; rel_pures_r; last by iApply "post".
rel_apply_r rel_adec'_r. iSplit; last first.
{ iIntros (Hnone). rewrite /vote_of Hnone. rel_pures_r. by iApply "post". }
iIntros (pl _ Hdec). rewrite /vote_of Hdec. rel_pures_r.
rel_apply_r rel_untuple_r.
case: (Spec.untuple pl) => [[q1 q2]|] /=; rel_pures_r; last by iApply "post".
rel_apply_r rel_to_int_r.
case: (Spec.to_int q2) => [k|] /=; rel_pures_r; last by iApply "post".
rel_apply_r rel_avl_lookup_r. rewrite /incr.
case: (AVL.lookup k t) => [n|] /=; rel_pures_r; by rel_apply_r rel_avl_insert_r.
Qed.

Lemma rel_tally_slots_l K e skT (slots : list (term * option term)) t Ψ :
  (REL fill K (repr (foldr (tally_step skT) t slots) : expr) << e : Ψ) -∗
  REL fill K (tally_slots skT (repr slots) (repr t)) << e : Ψ.
Proof.
rewrite /= [@repr_list]unlock.
elim: slots K => [|p slots IH] K /=; iIntros "post"; rel_rec_l; rel_pures_l;
  first by iApply "post".
rel_bind_l (tally_slots _ _ _). iApply IH. rewrite /=. rel_pures_l.
by iApply rel_tally_vote_l.
Qed.

Lemma rel_tally_slots_r K e skT (slots : list (term * option term)) t Ψ :
  (REL e << fill K (repr (foldr (tally_step skT) t slots) : expr) : Ψ) -∗
  REL e << fill K (tally_slots skT (repr slots) (repr t)) : Ψ.
Proof.
rewrite /= [@repr_list]unlock.
elim: slots K => [|p slots IH] K /=; iIntros "post"; rel_rec_r; rel_pures_r;
  first by iApply "post".
rel_bind_r (tally_slots _ _ _). iApply IH. rewrite /=. rel_pures_r.
by iApply rel_tally_vote_r.
Qed.

Lemma rel_seed_l K e cands Ψ :
  (REL fill K (repr (seed cands) : expr) << e : Ψ) -∗
  REL fill K (seed_candidates (repr cands)) << e : Ψ.
Proof.
iIntros "post". rewrite /seed_candidates. rel_pures_l.
iApply (rel_foldr_list_l _ _ _ (λ k t, AVL.insert k 0%Z t) _ cands AVL.Leaf with "post").
move=> K' k t _. iIntros "post". rel_pures_l. by rel_apply_l rel_avl_insert_l.
Qed.

Lemma rel_seed_r K e cands Ψ :
  (REL e << fill K (repr (seed cands) : expr) : Ψ) -∗
  REL e << fill K (seed_candidates (repr cands)) : Ψ.
Proof.
iIntros "post". rewrite /seed_candidates. rel_pures_r.
iApply (rel_foldr_list_r _ _ _ (λ k t, AVL.insert k 0%Z t) _ cands AVL.Leaf with "post");
  first solve_ndisj.
move=> K' k t _. iIntros "post". rel_pures_r. by rel_apply_r rel_avl_insert_r.
Qed.

Lemma rel_result_l K e t Ψ :
  (REL fill K (result t : expr) << e : Ψ) -∗
  REL fill K (term_of_list (map_list pair_term (avl_to_list (repr t)))) << e : Ψ.
Proof.
iIntros "post". rel_apply_l rel_avl_to_list_l.
rel_bind_l (map_list _ _).
iApply (rel_map_list_l _ _ _ pair_of pair_term (AVL.to_list t) with "[post]").
- move=> K' [k v] _. iIntros "post". rewrite /pair_term /=. rel_pures_l.
  rel_apply_l rel_tint_l. rel_pures_l. rel_apply_l rel_tint_l. by rel_apply_l rel_tuple_l.
- rewrite /=. by rel_apply_l rel_term_of_list_l.
Qed.

Lemma rel_result_r K e t Ψ :
  (REL e << fill K (result t : expr) : Ψ) -∗
  REL e << fill K (term_of_list (map_list pair_term (avl_to_list (repr t)))) : Ψ.
Proof.
iIntros "post". rel_apply_r rel_avl_to_list_r.
rel_bind_r (map_list _ _).
iApply (rel_map_list_r _ _ _ pair_of pair_term (AVL.to_list t) with "[post]");
  first solve_ndisj.
- move=> K' [k v] _. iIntros "post". rewrite /pair_term /=. rel_pures_r.
  rel_apply_r rel_tint_r. rel_pures_r. rel_apply_r rel_tint_r. by rel_apply_r rel_tuple_r.
- rewrite /=. by rel_apply_r rel_term_of_list_r.
Qed.

Lemma rel_init_slots_l K e (pks : list term) Ψ :
  (REL fill K (repr (slots_l pks (replicate (length pks) None)) : expr) << e : Ψ) -∗
  REL fill K (map_list (λ: "pk", ("pk", NONE))%V (repr pks)) << e : Ψ.
Proof.
iIntros "post". rewrite /slots_l zip_replicate_None.
iApply (rel_map_list_l _ _ _ (λ pk, (pk, None)) _ pks with "post").
move=> K' pk _. iIntros "post". rel_pures_l. by iApply "post".
Qed.

Lemma rel_init_slots_r K e (pks : list term) Ψ :
  (REL e << fill K (repr (slots_r pks (replicate (length pks) None)) : expr) : Ψ) -∗
  REL e << fill K (map_list (λ: "pk", ("pk", NONE))%V (repr pks)) : Ψ.
Proof.
iIntros "post". rewrite /slots_r zip_replicate_None.
iApply (rel_map_list_r _ _ _ (λ pk, (pk, None)) _ pks with "post"); first solve_ndisj.
move=> K' pk _. iIntros "post". rel_pures_r. by iApply "post".
Qed.

Lemma rel_find_empty_l K e (slots : list (term * option term)) Ψ :
  (REL fill K (repr (find slot_empty slots) : expr) << e : Ψ) -∗
  REL fill K (find_list is_empty_slot (repr slots)) << e : Ψ.
Proof.
iIntros "post".
iApply (rel_find_list_l _ _ _ slot_empty is_empty_slot slots with "post").
move=> K' [pk o] _. iIntros "post". rewrite /is_empty_slot /=. rel_pures_l.
case: o => [ct|] /=; rel_pures_l; by iApply "post".
Qed.

Lemma rel_find_empty_r K e (slots : list (term * option term)) Ψ :
  (REL e << fill K (repr (find slot_empty slots) : expr) : Ψ) -∗
  REL e << fill K (find_list is_empty_slot (repr slots)) : Ψ.
Proof.
iIntros "post".
iApply (rel_find_list_r _ _ _ slot_empty is_empty_slot slots with "post");
  first solve_ndisj.
move=> K' [pk o] _. iIntros "post". rewrite /is_empty_slot /=. rel_pures_r.
case: o => [ct|] /=; rel_pures_r; by iApply "post".
Qed.

Lemma rel_pkeys_l K e ks votes Ψ :
  length ks ≤ length votes →
  (REL fill K (repr (pkeys ks) : expr) << e : Ψ) -∗
  REL fill K (map_list (λ: "p", pkey (Fst "p"))%V (repr (zip ks votes))) << e : Ψ.
Proof.
iIntros (Hlen) "post". rewrite -(pkeys_zip Hlen).
iApply (rel_map_list_l _ _ _ (λ p : sign_key * Z, Spec.pkey (p.1 : term)) _ (zip ks votes)
          with "post").
move=> K' [sk v] _. iIntros "post". rewrite /=. rel_pures_l.
rel_apply_l rel_pkey_l. by iApply "post".
Qed.

Lemma rel_pkeys_r K e ks votes Ψ :
  length ks ≤ length votes →
  (REL e << fill K (repr (pkeys ks) : expr) : Ψ) -∗
  REL e << fill K (map_list (λ: "p", pkey (Fst "p"))%V (repr (zip ks votes))) : Ψ.
Proof.
iIntros (Hlen) "post". rewrite -(pkeys_zip Hlen).
iApply (rel_map_list_r _ _ _ (λ p : sign_key * Z, Spec.pkey (p.1 : term)) _ (zip ks votes)
          with "post"); first solve_ndisj.
move=> K' [sk v] _. iIntros "post". rewrite /=. rel_pures_r.
rel_apply_r rel_pkey_r. by iApply "post".
Qed.

(** * Arbitrator *)

Lemma rel_record_ballot skT skT' ks ks' votes votes' st m m' :
  length st = length ks → length votes = length ks → length votes' = length ks' →
  slots_ok skT skT' votes votes' st →
  cryptis_rel_ctx -∗ voter_keys skT skT' ks ks' votes votes' -∗ PUB⟨m, m'⟩ -∗
  REL record_ballot m (repr (slots_l (pkeys ks) st))
   << record_ballot m' (repr (slots_r (pkeys ks') st)) : λ v v',
    (∃ st', ⌜v = repr (slots_l (pkeys ks) st')⌝ ∗ ⌜v' = repr (slots_r (pkeys ks') st')⌝ ∗
            ⌜length st' = length st⌝ ∗ ⌜slots_ok skT skT' votes votes' st'⌝)%I.
Proof.
rewrite /= ![@repr_list]unlock /voter_keys.
elim: ks ks' st votes votes' => [|sk ks IH] ks' st votes votes' Hst Hv Hv' Hok;
  iIntros "#Hctx #Hkeys #Hm".
- iDestruct (big_sepL2_nil_inv_l with "Hkeys") as %->.
  case: st Hst Hok => [|??] //= _ _.
  rel_rec_l. rel_rec_r. rel_pures_l. rel_pures_r. rel_values. iModIntro.
  iExists []. iPureIntro. by do !split => //=.
- iDestruct (big_sepL2_cons_inv_l with "Hkeys") as (sk' ks'' ->) "[#HV #Hkeys']".
  case: st Hst Hok => [|o st] //= [Hst].
  case: votes votes' Hv Hv' => [|v votes] [|v' votes'] //= [Hv] [Hv'] [Ho Hok].
  rel_rec_l. rel_rec_r. rel_pures_l. rel_pures_r.
  iMod (pub_verify_cases with "Hctx HV Hm") as "[[%HnL %HnR]|(%n & %n' & -> & ->)]".
  + rel_apply_l rel_verify'_l. iModIntro. iSplit.
    { iIntros (u _ Hdec). by rewrite HnL in Hdec. }
    iIntros "_". rel_pures_l.
    rel_apply_r rel_verify'_r. iSplit.
    { iIntros (u' _ Hdec). by rewrite HnR in Hdec. }
    iIntros "_". rel_pures_r.
    rel_bind_l (record_ballot _ _). rel_bind_r (record_ballot _ _).
    iApply (refines_bind with "[]").
    { by iApply (IH _ st votes votes' Hst Hv Hv' Hok with "Hctx Hkeys' Hm"). }
    iIntros (? ?) "(%st' & -> & -> & %Hlen' & %Hok')" => /=.
    rel_pures_l. rel_pures_r. rel_values. iModIntro.
    iExists (o :: st'). iPureIntro. do 2 (split; first done).
    split; [by rewrite /= Hlen' | by split].
  + rel_apply_l rel_verify'_l. iModIntro. iSplit; last first.
    { iIntros (Hdec). by rewrite dec_sign in Hdec. }
    iIntros (u e _). case: e => /tag_inj <-.
    rel_apply_r rel_verify'_r. iSplit; last first.
    { iIntros (Hdec). by rewrite dec_sign in Hdec. }
    iIntros (u' e' _). case: e' => /tag_inj <-.
    rel_pures_l. rel_pures_r. rel_values. iModIntro.
    iExists (Some (ballot_ct skT n (TInt v), ballot_ct skT' n' (TInt v')) :: st).
    iPureIntro. do 2 (split; first done). split; first done. split; last done.
    by exists n, n'.
Qed.

Lemma rel_collect c c' skT skT' ks ks' votes votes' st :
  length st = length ks → length votes = length ks → length votes' = length ks' →
  length ks = length ks' →
  slots_ok skT skT' votes votes' st →
  cryptis_rel_ctx -∗ channel_rel c c' -∗ voter_keys skT skT' ks ks' votes votes' -∗
  REL collect c (repr (slots_l (pkeys ks) st))
   << collect c' (repr (slots_r (pkeys ks') st)) : λ v v',
    (∃ st', ⌜v = repr (slots_l (pkeys ks) st')⌝ ∗ ⌜v' = repr (slots_r (pkeys ks') st')⌝ ∗
            ⌜length st' = length st⌝ ∗ ⌜slots_ok skT skT' votes votes' st'⌝ ∗
            ⌜Forall is_Some st'⌝)%I.
Proof.
iIntros (Hst Hv Hv' Hkk Hok) "#Hctx #Hc #Hkeys".
have Hlen_l : length (pkeys ks) = length st by rewrite /pkeys length_map.
have Hlen_r : length (pkeys ks') = length st by rewrite /pkeys length_map; lia.
iLöb as "IH" forall (st Hst Hok Hlen_l Hlen_r).
rel_rec_l. rel_rec_r. rel_pures_l. rel_pures_r.
rel_apply_l rel_find_empty_l. rel_apply_r rel_find_empty_r.
case eL: (find slot_empty (slots_l (pkeys ks) st)) => [p|].
- have [p' eR] : ∃ p', find slot_empty (slots_r (pkeys ks') st) = Some p'.
  { case e: (find _ _) => [p'|]; first by eauto.
    move/(find_slot_empty_None snd Hlen_r): e => Hall.
    by have := proj2 (find_slot_empty_None fst Hlen_l) Hall; rewrite eL. }
  rewrite eR /=. rel_pures_l. rel_pures_r.
  rel_bind_l (recv _). rel_bind_r (recv _).
  iApply refines_bind'. iApply rel_recv => //.
  iIntros (m m') "#Hm" => /=.
  rel_bind_l (record_ballot _ _). rel_bind_r (record_ballot _ _).
  iApply (refines_bind with "[]").
  { by iApply (rel_record_ballot _ _ Hst Hv Hv' Hok with "Hctx Hkeys Hm"). }
  iIntros (? ?) "(%st' & -> & -> & %Hlen' & %Hok')" => /=.
  rel_pures_l. rel_pures_r.
  rewrite -Hlen'. iApply ("IH" $! st' with "[%] [%] [%] [%]"); try lia; try done.
- move/(find_slot_empty_None fst Hlen_l): eL => Hall.
  rewrite (proj2 (find_slot_empty_None snd Hlen_r) Hall) /=.
  rel_pures_l. rel_pures_r. rel_values.
Qed.

Lemma rel_arbitrator c c' skT skT' ks ks' cands votes votes' :
  votes ≡ₚ votes' →
  length votes = length ks → length votes' = length ks' → length ks = length ks' →
  cryptis_rel_ctx -∗ channel_rel c c' -∗ voter_keys skT skT' ks ks' votes votes' -∗
  REL arbitrator c skT (repr cands) (repr (pkeys ks))
   << arbitrator c' skT' (repr cands) (repr (pkeys ks')) : ().
Proof.
iIntros (Hperm Hv Hv' Hkk) "#Hctx #Hc #Hkeys".
rewrite /arbitrator. rel_pures_l. rel_pures_r.
rel_apply_l rel_init_slots_l. rel_apply_r rel_init_slots_r.
rewrite /pkeys !length_map -/(pkeys ks) -/(pkeys ks') -Hkk.
rel_bind_l (collect _ _). rel_bind_r (collect _ _).
iApply (refines_bind with "[]").
{ iApply (rel_collect with "Hctx Hc Hkeys") => //.
  - by rewrite length_replicate.
  - by apply: slots_ok_replicate; lia. }
iIntros (? ?) "(%st & -> & -> & %Hlen & %Hok & %Hall)" => /=.
rewrite length_replicate in Hlen.
rel_pures_l. rel_pures_r.
rel_apply_l rel_seed_l. rel_apply_r rel_seed_r.
rel_apply_l rel_tally_slots_l. rel_apply_r rel_tally_slots_r.
rewrite (tally_slots_l_eq (seed cands) Hlen Hv Hok Hall).
rewrite (tally_slots_r_eq (seed cands) (eq_trans Hlen Hkk) Hv' Hok Hall).
rel_pures_l. rel_pures_r.
rel_apply_l rel_result_l. rel_apply_r rel_result_r.
have [HbL HmL] := to_map_foldr_incr votes (bst_seed cands).
have [HbR HmR] := to_map_foldr_incr votes' (bst_seed cands).
have Heq : AVL.to_list (foldr incr (seed cands) votes) =
           AVL.to_list (foldr incr (seed cands) votes').
{ apply: AVL.to_list_to_map => //. rewrite HmL HmR. exact: foldr_incr_map_perm. }
rewrite /result Heq.
iApply (rel_send with "Hc"). iNext. iApply pub_pair_terms.
Qed.

End Arbitrator.
