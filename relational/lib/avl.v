(** Relational specs of the AVL map operations in [cryptis/lib/avl.v].  Each
    side owns its map and steps independently: nothing relates the two maps. *)

From reloc Require Import reloc.
From cryptis Require Import lib.
From cryptis.lib Require Import avl.
From cryptis.hyper Require Import lib.

Section Proofs.

Context `{!relocG Σ}.

Implicit Types (t : AVL.tree) (m w : val) (p : loc) (Ψ : val → val → iProp Σ).

Definition is_avl_spec : val → AVL.tree → iProp Σ := avl_at (λ p w, p ↦ₛ w)%I.

#[local] Abbreviation is_tree_spec := (avl_tree_at (λ p w, p ↦ₛ w)%I).

Lemma refines_avl_new_l K e Ψ :
  (∀ m, is_avl m AVL.Leaf -∗ REL fill K (m : expr) << e : Ψ) -∗
  REL fill K (avl_new #()) << e : Ψ.
Proof.
iIntros "post". iApply refines_wp_l. iApply twp_wp. by iApply twp_avl_new.
Qed.

Lemma refines_avl_insert_l K e k v m t Ψ :
  is_avl m t -∗
  (is_avl m (AVL.insert k v t) -∗ REL fill K (#() : expr) << e : Ψ) -∗
  REL fill K (avl_insert #k #v m) << e : Ψ.
Proof.
iIntros "Hm post". iApply refines_wp_l. iApply twp_wp.
by iApply (twp_avl_insert with "Hm").
Qed.

Lemma refines_avl_lookup_l K e k m t Ψ :
  is_avl m t -∗
  (is_avl m t -∗ REL fill K (repr (AVL.lookup k t) : expr) << e : Ψ) -∗
  REL fill K (avl_lookup #k m) << e : Ψ.
Proof.
iIntros "Hm post". iApply refines_wp_l. iApply twp_wp.
by iApply (twp_avl_lookup with "Hm").
Qed.

Lemma refines_avl_to_list_l K e m t Ψ :
  is_avl m t -∗
  (is_avl m t -∗ REL fill K (repr (AVL.to_list t) : expr) << e : Ψ) -∗
  REL fill K (avl_to_list m) << e : Ψ.
Proof.
iIntros "Hm post". iApply refines_wp_l. iApply twp_wp.
by iApply (twp_avl_to_list with "Hm").
Qed.

#[local] Lemma refines_avl_height_r E K e t w Ψ :
  ↑specN ⊆ E →
  is_tree_spec t w -∗
  (is_tree_spec t w -∗ REL e << fill K (#(AVL.height t) : expr) @ E : Ψ) -∗
  REL e << fill K (avl_height w) @ E : Ψ.
Proof.
move=> HE. iIntros "Ht post". case: t => [|l k v h r] /=.
- iDestruct "Ht" as %->. rel_rec_r. rel_pures_r. by iApply "post".
- iDestruct "Ht" as (p wl wr ->) "(Hp & Hl & Hr)". rel_rec_r. rel_pures_r.
  rel_load_r. rel_pures_r. iApply "post". iExists p, wl, wr. by iFrame.
Qed.

#[local] Lemma refines_avl_set_node_r E K e p w0 l k v r wl wr Ψ :
  ↑specN ⊆ E →
  p ↦ₛ w0 -∗ is_tree_spec l wl -∗ is_tree_spec r wr -∗
  (∀ w, is_tree_spec (AVL.node l k v r) w -∗
        REL e << fill K (w : expr) @ E : Ψ) -∗
  REL e << fill K (avl_set_node #p wl #k #v wr) @ E : Ψ.
Proof.
move=> HE. iIntros "Hp Hl Hr post". rel_rec_r. rel_pures_r.
rel_apply_r (refines_avl_height_r with "Hl"). iIntros "Hl". rel_pures_r.
rel_apply_r (refines_avl_height_r with "Hr"). iIntros "Hr". rel_pures_r.
case: bool_decide_reflect => ?; rel_pures_r; rel_store_r; rel_pures_r;
  iApply "post"; iExists p, wl, wr.
- rewrite Z.max_r; last lia. by iFrame.
- rewrite Z.max_l; last lia. by iFrame.
Qed.

#[local] Lemma refines_avl_bal_r E K e p w0 l k v r wl wr Ψ :
  ↑specN ⊆ E →
  p ↦ₛ w0 -∗ is_tree_spec l wl -∗ is_tree_spec r wr -∗
  (∀ w, is_tree_spec (AVL.bal l k v r) w -∗
        REL e << fill K (w : expr) @ E : Ψ) -∗
  REL e << fill K (avl_bal #p wl #k #v wr) @ E : Ψ.
Proof.
move=> HE. iIntros "Hp Hl Hr post". rel_rec_r. rel_pures_r.
rel_apply_r (refines_avl_height_r with "Hl"). iIntros "Hl". rel_pures_r.
rel_apply_r (refines_avl_height_r with "Hr"). iIntros "Hr". rel_pures_r.
rewrite /AVL.bal. case: bool_decide_reflect => _; rel_pures_r.
{ case: l => [|ll lk lv lh lr] /=.
  { iDestruct "Hl" as %->. rel_pures_r.
    by rel_apply_r (refines_avl_set_node_r _ _ _ _ _ AVL.Leaf with "Hp [//] Hr"). }
  iDestruct "Hl" as (pl wll wlr ->) "(Hpl & Hll & Hlr)". rel_pures_r.
  rel_load_r. rel_pures_r.
  rel_apply_r (refines_avl_height_r with "Hll"). iIntros "Hll".
  rel_apply_r (refines_avl_height_r with "Hlr"). iIntros "Hlr". rel_pures_r.
  case: bool_decide_reflect => _; rel_pures_r.
  { rel_apply_r (refines_avl_set_node_r with "Hp Hlr Hr"). iIntros (w) "Hw".
    by rel_apply_r (refines_avl_set_node_r _ _ _ _ _ _ _ _ (AVL.node lr k v r)
                      with "Hpl Hll Hw"). }
  case: lr => [|lrl lrk lrv lrh lrr] /=.
  { iDestruct "Hlr" as %->. rel_pures_r.
    rel_apply_r (refines_avl_set_node_r _ _ _ _ _ (AVL.Node ll lk lv lh AVL.Leaf)
                   with "Hp [Hpl Hll] Hr"); last done.
    iExists pl, wll, NONEV. by iFrame. }
  iDestruct "Hlr" as (plr wlrl wlrr ->) "(Hplr & Hlrl & Hlrr)". rel_pures_r.
  rel_load_r. rel_pures_r.
  rel_apply_r (refines_avl_set_node_r with "Hp Hlrr Hr"). iIntros (w1) "H1".
  rel_apply_r (refines_avl_set_node_r with "Hpl Hll Hlrl"). iIntros (w2) "H2".
  by rel_apply_r (refines_avl_set_node_r _ _ _ _ _ (AVL.node ll lk lv lrl) _ _
                    (AVL.node lrr k v r) with "Hplr H2 H1"). }
case: bool_decide_reflect => _; rel_pures_r;
  last by rel_apply_r (refines_avl_set_node_r with "Hp Hl Hr").
case: r => [|rl rk rv rh rr] /=.
{ iDestruct "Hr" as %->. rel_pures_r.
  by rel_apply_r (refines_avl_set_node_r _ _ _ _ _ _ _ _ AVL.Leaf with "Hp Hl [//]"). }
iDestruct "Hr" as (pr wrl wrr ->) "(Hpr & Hrl & Hrr)". rel_pures_r.
rel_load_r. rel_pures_r.
rel_apply_r (refines_avl_height_r with "Hrr"). iIntros "Hrr".
rel_apply_r (refines_avl_height_r with "Hrl"). iIntros "Hrl". rel_pures_r.
case: bool_decide_reflect => _; rel_pures_r.
{ rel_apply_r (refines_avl_set_node_r with "Hp Hl Hrl"). iIntros (w) "Hw".
  by rel_apply_r (refines_avl_set_node_r _ _ _ _ _ (AVL.node l k v rl)
                      with "Hpr Hw Hrr"). }
case: rl => [|rll rlk rlv rlh rlr] /=.
{ iDestruct "Hrl" as %->. rel_pures_r.
  rel_apply_r (refines_avl_set_node_r _ _ _ _ _ _ _ _ (AVL.Node AVL.Leaf rk rv rh rr)
                 with "Hp Hl [Hpr Hrr]"); last done.
  iExists pr, NONEV, wrr. by iFrame. }
iDestruct "Hrl" as (prl wrll wrlr ->) "(Hprl & Hrll & Hrlr)". rel_pures_r.
rel_load_r. rel_pures_r.
rel_apply_r (refines_avl_set_node_r with "Hpr Hrlr Hrr"). iIntros (w1) "H1".
rel_apply_r (refines_avl_set_node_r with "Hp Hl Hrll"). iIntros (w2) "H2".
by rel_apply_r (refines_avl_set_node_r _ _ _ _ _ (AVL.node l k v rll) _ _
                  (AVL.node rlr rk rv rr) with "Hprl H2 H1").
Qed.

#[local] Lemma refines_avl_insert_node_r E K e k v t w Ψ :
  ↑specN ⊆ E →
  is_tree_spec t w -∗
  (∀ w', is_tree_spec (AVL.insert k v t) w' -∗
         REL e << fill K (w' : expr) @ E : Ψ) -∗
  REL e << fill K (avl_insert_node #k #v w) @ E : Ψ.
Proof.
move=> HE.
elim: t K w => [|l IHl k' v' h r IHr] K w /=; iIntros "Ht post".
{ iDestruct "Ht" as %->. rel_rec_r. rel_pures_r. rel_alloc_r p as "Hp".
  rel_pures_r. iApply "post". iExists p, NONEV, NONEV. by iFrame. }
iDestruct "Ht" as (p wl wr ->) "(Hp & Hl & Hr)". rel_rec_r. rel_pures_r.
rel_load_r. rel_pures_r.
case: bool_decide_reflect => _; rel_pures_r.
{ rel_apply_r (IHl with "Hl"). iIntros (wl') "Hl".
  by rel_apply_r (refines_avl_bal_r with "Hp Hl Hr"). }
case: bool_decide_reflect => _; rel_pures_r.
{ rel_apply_r (IHr with "Hr"). iIntros (wr') "Hr".
  by rel_apply_r (refines_avl_bal_r with "Hp Hl Hr"). }
rel_store_r. rel_pures_r. iApply "post". iExists p, wl, wr. by iFrame.
Qed.

#[local] Lemma refines_avl_lookup_node_r E K e k t w Ψ :
  ↑specN ⊆ E →
  is_tree_spec t w -∗
  (is_tree_spec t w -∗
   REL e << fill K (repr (AVL.lookup k t) : expr) @ E : Ψ) -∗
  REL e << fill K (avl_lookup_node #k w) @ E : Ψ.
Proof.
move=> HE.
elim: t K w => [|l IHl k' v' h r IHr] K w /=; iIntros "Ht post".
{ iDestruct "Ht" as %->. rel_rec_r. rel_pures_r. by iApply "post". }
iDestruct "Ht" as (p wl wr ->) "(Hp & Hl & Hr)". rel_rec_r. rel_pures_r.
rel_load_r. rel_pures_r.
case: bool_decide_reflect => _; rel_pures_r.
{ rel_apply_r (IHl with "Hl"). iIntros "Hl".
  iApply "post". iExists p, wl, wr. by iFrame. }
case: bool_decide_reflect => _; rel_pures_r.
{ rel_apply_r (IHr with "Hr"). iIntros "Hr".
  iApply "post". iExists p, wl, wr. by iFrame. }
iApply "post". iExists p, wl, wr. by iFrame.
Qed.

#[local] Lemma refines_avl_to_list_acc_r E K e t w acc Ψ :
  ↑specN ⊆ E →
  is_tree_spec t w -∗
  (is_tree_spec t w -∗
   REL e << fill K (repr (AVL.to_list_acc t acc) : expr) @ E : Ψ) -∗
  REL e << fill K (avl_to_list_acc w (repr acc)) @ E : Ψ.
Proof.
move=> HE.
elim: t K w acc => [|l IHl k v h r IHr] K w acc /=; iIntros "Ht post".
{ iDestruct "Ht" as %->. rel_rec_r. rel_pures_r. by iApply "post". }
iDestruct "Ht" as (p wl wr ->) "(Hp & Hl & Hr)". rel_rec_r. rel_pures_r.
rel_load_r. rel_pures_r.
rel_apply_r (IHr with "Hr"). iIntros "Hr". rel_pures_r.
rewrite -[InjRV (PairV _ _)](repr_listE ((k, v) :: AVL.to_list_acc r acc)).
rel_apply_r (IHl with "Hl"). iIntros "Hl".
iApply "post". iExists p, wl, wr. by iFrame.
Qed.

Lemma refines_avl_new_r E K e Ψ :
  ↑specN ⊆ E →
  (∀ m, is_avl_spec m AVL.Leaf -∗ REL e << fill K (m : expr) @ E : Ψ) -∗
  REL e << fill K (avl_new #()) @ E : Ψ.
Proof.
move=> HE. rewrite /is_avl_spec /avl_at /=. iIntros "post".
rel_rec_r. rel_alloc_r p as "Hp". iApply "post". iExists p, NONEV. by iFrame.
Qed.

Lemma refines_avl_insert_r E K e k v m t Ψ :
  ↑specN ⊆ E →
  is_avl_spec m t -∗
  (is_avl_spec m (AVL.insert k v t) -∗
   REL e << fill K (#() : expr) @ E : Ψ) -∗
  REL e << fill K (avl_insert #k #v m) @ E : Ψ.
Proof.
move=> HE. rewrite /is_avl_spec /avl_at /=.
iIntros "(%p & %w & -> & Hp & Ht) post". rel_rec_r. rel_pures_r. rel_load_r.
rel_apply_r (refines_avl_insert_node_r with "Ht"). iIntros (w') "Ht". rel_store_r.
iApply "post". iExists p, w'. by iFrame.
Qed.

Lemma refines_avl_lookup_r E K e k m t Ψ :
  ↑specN ⊆ E →
  is_avl_spec m t -∗
  (is_avl_spec m t -∗
   REL e << fill K (repr (AVL.lookup k t) : expr) @ E : Ψ) -∗
  REL e << fill K (avl_lookup #k m) @ E : Ψ.
Proof.
move=> HE. rewrite /is_avl_spec /avl_at /=.
iIntros "(%p & %w & -> & Hp & Ht) post". rel_rec_r. rel_pures_r. rel_load_r.
rel_apply_r (refines_avl_lookup_node_r with "Ht"). iIntros "Ht".
iApply "post". iExists p, w. by iFrame.
Qed.

Lemma refines_avl_to_list_r E K e m t Ψ :
  ↑specN ⊆ E →
  is_avl_spec m t -∗
  (is_avl_spec m t -∗
   REL e << fill K (repr (AVL.to_list t) : expr) @ E : Ψ) -∗
  REL e << fill K (avl_to_list m) @ E : Ψ.
Proof.
move=> HE. rewrite /is_avl_spec /avl_at /=.
iIntros "(%p & %w & -> & Hp & Ht) post". rel_rec_r. rel_load_r. rel_pures_r.
rewrite -[InjLV _](repr_listE (@nil (Z * Z))).
rel_apply_r (refines_avl_to_list_acc_r with "Ht"). iIntros "Ht".
iApply "post". iExists p, w. by iFrame.
Qed.

End Proofs.
