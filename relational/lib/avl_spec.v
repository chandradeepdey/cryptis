(** Relational specs of the AVL map operations in [lib/avl.v].  The code is
    heap-free, so each side steps independently through [pure_twp_rel_l] and
    [pure_twp_rel_r]: nothing relates the two trees. *)

From reloc Require Import reloc.
From cryptis Require Import lib.
From cryptis.lib Require Import avl.
From cryptis.hyper Require Import lib_spec.

Section Proofs.

Context `{!relocG Σ}.

Implicit Types (t : AVL.tree) (Ψ : val → val → iProp Σ).

Ltac solve_pure := rewrite /= ?andb_True; repeat split; apply: tree_pure.

Lemma rel_avl_insert_l E K e k v t Ψ :
  (REL fill K (repr (AVL.insert k v t) : expr) << e @ E : Ψ) -∗
  REL fill K (avl_insert #k #v (repr t)) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=; last by move=> ?; iIntros "_"; iApply twp_avl_insert.
solve_pure.
Qed.

Lemma rel_avl_insert_r E K e k v t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (AVL.insert k v t) : expr) @ E : Ψ) -∗
  REL e << fill K (avl_insert #k #v (repr t)) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=; last by move=> ?; iIntros "_"; iApply twp_avl_insert.
solve_pure.
Qed.

Lemma rel_avl_lookup_l E K e k t Ψ :
  (REL fill K (repr (AVL.lookup k t) : expr) << e @ E : Ψ) -∗
  REL fill K (avl_lookup #k (repr t)) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=; last by move=> ?; iIntros "_"; iApply twp_avl_lookup.
solve_pure.
Qed.

Lemma rel_avl_lookup_r E K e k t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (AVL.lookup k t) : expr) @ E : Ψ) -∗
  REL e << fill K (avl_lookup #k (repr t)) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=; last by move=> ?; iIntros "_"; iApply twp_avl_lookup.
solve_pure.
Qed.

Lemma rel_avl_to_list_l E K e t Ψ :
  (REL fill K (repr (AVL.to_list t) : expr) << e @ E : Ψ) -∗
  REL fill K (avl_to_list (repr t)) << e @ E : Ψ.
Proof.
iApply pure_twp_rel_l => //=; last by move=> ?; iIntros "_"; iApply twp_avl_to_list.
solve_pure.
Qed.

Lemma rel_avl_to_list_r E K e t Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (AVL.to_list t) : expr) @ E : Ψ) -∗
  REL e << fill K (avl_to_list (repr t)) @ E : Ψ.
Proof.
move=> ?.
iApply pure_twp_rel_r => //=; last by move=> ?; iIntros "_"; iApply twp_avl_to_list.
solve_pure.
Qed.

End Proofs.
