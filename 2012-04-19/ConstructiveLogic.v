Require Import Arith.
Require Import List.

Inductive proposition : Set :=
    Pimp  : proposition -> proposition -> proposition
  | Patom : nat -> proposition.

Notation "A *-> B" := (Pimp A B) (at level 20, right associativity).

Definition assump : Set := list proposition.

Inductive hilbert : assump -> proposition -> Prop :=
    Hmp       : forall {a : assump} {p1 p2 : proposition},
                hilbert a (p1 *-> p2) -> hilbert a p1 -> hilbert a p2
  | Hasp      : forall {a : assump} {p : proposition}, In p a -> hilbert a p
  | Hstarling : forall {a : assump} {p1 p2 p3 : proposition},
                hilbert a ((p1 *-> p2 *-> p3) *-> (p1 *-> p2) *-> p1 *-> p3)
  | Hkestrel  : forall {a : assump} {p1 p2 : proposition}, hilbert a (p1 *-> p2 *-> p1).

Inductive nd : assump -> proposition -> Prop :=
    NDmp   : forall {a : assump} {p1 p2 : proposition}, nd a (p1 *-> p2) -> nd a p1 -> nd a p2
  | NDasp  : forall {a : assump} {p : proposition}, In p a -> nd a p
  | NDimpi : forall {a : assump} {p1 p2 : proposition}, nd (p1 :: a) p2 -> nd a (p1 *-> p2).

Lemma NDstarling : forall {a : assump} {p1 p2 p3 : proposition},
                   nd a ((p1 *-> p2 *-> p3) *-> (p1 *-> p2) *-> p1 *-> p3).
  intros.
  repeat apply NDimpi.
  apply (@NDmp _ p2).
  apply (@NDmp _ p1) ; apply NDasp ; unfold In ; auto.
  apply (@NDmp _ p1) ; apply NDasp ; unfold In ; auto.
Defined.

Lemma NDkestrel : forall {a : assump} {p1 p2 : proposition}, nd a (p1 *-> p2 *-> p1).
  intros.
  repeat apply NDimpi.
  apply NDasp ; unfold In ; auto.
Defined.

Lemma Hidiot : forall {a : assump} {p : proposition}, hilbert a (p *-> p).
  intros.
  exact (Hmp (Hmp (@Hstarling a p (p *-> p) p) Hkestrel) Hkestrel).
Defined.

Theorem hilbert_nd_homomorphism : forall {a : assump} {p : proposition}, hilbert a p -> nd a p.
  intros.
  induction H.
  exact (NDmp IHhilbert1 IHhilbert2).
  exact (NDasp H).
  exact NDstarling.
  exact NDkestrel.
Defined.

Lemma Himpi : forall {a : assump} {p1 p2 : proposition}, hilbert (p1 :: a) p2 -> hilbert a (p1 *-> p2).
  intros.
  refine (hilbert_ind (fun a p1 =>
    match a with nil => True | p2 :: a => hilbert a (p2 *-> p1) end) _ _ _ _ (p1 :: a) p2 H) ;
    intros ; destruct a0 ; auto.
  exact (Hmp (Hmp Hstarling H1) H3).
  case H0 ; intros.
  rewrite H1 ; exact Hidiot.
  exact (Hmp Hkestrel (Hasp H1)).
  exact (Hmp Hkestrel Hstarling).
  exact (Hmp Hkestrel Hkestrel).
Defined.

Theorem nd_hilbert_homomorphism : forall {a : assump} {p : proposition}, nd a p -> hilbert a p.
  intros.
  induction H.
  exact (Hmp IHnd1 IHnd2).
  exact (Hasp H).  
  exact (Himpi IHnd).
Defined.

Theorem nd_hilbert_isomorphism : forall {a : assump} {p : proposition}, nd a p <-> hilbert a p.
  intros.
  exact (conj nd_hilbert_homomorphism hilbert_nd_homomorphism).
Defined.

