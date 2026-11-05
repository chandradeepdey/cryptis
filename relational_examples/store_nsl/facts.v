(** Pure facts of the NSL store case study.  [db_of ops] is the database the
    server holds after the stores [ops], in order.  When the stores are to
    distinct keys, their order does not matter, so the final load gives the
    same value in both runs. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From cryptis Require Import lib.
From cryptis.lib Require Import avl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition db_of (ops : list (Z * Z)) : AVL.tree :=
  foldl (λ t p, AVL.insert p.1 p.2 t) AVL.Leaf ops.

Lemma bst_db_of ops : AVL.bst (db_of ops).
Proof. apply: AVL.bst_foldl_insert. exact: AVL.bst_leaf. Qed.

Lemma to_map_db_of ops : AVL.to_map (db_of ops) = list_to_map (reverse ops).
Proof.
rewrite /db_of AVL.to_map_foldl_insert; last exact: AVL.bst_leaf.
by rewrite AVL.to_map_leaf right_id_L.
Qed.

Lemma to_map_db_of_perm ops ops' :
  NoDup ops.*1 → ops ≡ₚ ops' →
  AVL.to_map (db_of ops) = AVL.to_map (db_of ops').
Proof.
move=> nodup perm. rewrite !to_map_db_of.
apply: list_to_map_proper.
- by rewrite fmap_reverse reverse_Permutation.
- by rewrite !reverse_Permutation.
Qed.

Lemma lookup_db_of_perm k ops ops' :
  NoDup ops.*1 → ops ≡ₚ ops' →
  AVL.lookup k (db_of ops) = AVL.lookup k (db_of ops').
Proof.
move=> nodup perm.
rewrite !AVL.lookup_to_map; try exact: bst_db_of.
by rewrite (to_map_db_of_perm nodup perm).
Qed.
