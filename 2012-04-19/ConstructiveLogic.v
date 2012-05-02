
Require Import Arith.
Require Import List.

Inductive elem {A : Set} : A -> list A -> Prop :=
    Ezero : forall {x : A} {y : list A}, elem x (x :: y)
  | Esucc : forall {x : A} {y : list A} {x' : A},
            elem x y -> elem x (x' :: y).

Definition contains {A : Set} (l1 l2 : list A) : Set :=
  forall (x : A), elem x l1 -> elem x l2.

Lemma cid : forall {A : Set} {l : list A}, contains l l.
  repeat intro.
  exact H.
Defined.

Lemma ectrans : forall {A : Set} {x : A} {l1 l2 : list A},
                elem x l1 -> contains l1 l2 -> elem x l2.
  intros.
  induction H.
  apply (H0 x Ezero).
  apply IHelem.
  intro ; intro.
  apply (H0 x0 (Esucc H1)).
Defined.

Lemma cstep : forall {A : Set} {x : A} {l1 l2 : list A},
              contains l1 l2 -> contains (x :: l1) (x :: l2).
  repeat intro.
  inversion H0.
  apply Ezero.
  apply Esucc.
  apply (ectrans H3 H).
Defined.

Lemma csucc : forall {A : Set} {x : A} {l1 l2 : list A},
              contains l1 l2 -> contains l1 (x :: l2).
  repeat intro.
  inversion H0 ; apply (Esucc (ectrans H0 H)).
Defined.

Lemma emap : forall {A B : Set} {x : A} {l : list A} (f : A -> B),
             elem x l -> elem (f x) (map f l).
  intros.
  induction H.
  exact Ezero.
  exact (Esucc IHelem).
Defined.

Inductive proposition : Set :=
    Pimp  : proposition -> proposition -> proposition
  | Patom : nat -> proposition.

Notation "A *-> B" := (Pimp A B) (at level 20, right associativity).

Definition assump : Set := list proposition.

Inductive hilbert : assump -> proposition -> Prop :=
    Hmp       : forall {a : assump} {p1 p2 : proposition},
                hilbert a (p1 *-> p2) -> hilbert a p1 -> hilbert a p2
  | Hasp      : forall {a : assump} {p : proposition}, elem p a -> hilbert a p
  | Hstarling : forall {a : assump} {p1 p2 p3 : proposition},
                hilbert a ((p1 *-> p2 *-> p3) *-> (p1 *-> p2) *-> p1 *-> p3)
  | Hkestrel  : forall {a : assump} {p1 p2 : proposition},
                hilbert a (p1 *-> p2 *-> p1).

Inductive nd : assump -> proposition -> Prop :=
    NDmp   : forall {a : assump} {p1 p2 : proposition}, nd a (p1 *-> p2) -> nd a p1 -> nd a p2
  | NDasp  : forall {a : assump} {p : proposition}, elem p a -> nd a p
  | NDimpi : forall {a : assump} {p1 p2 : proposition}, nd (p1 :: a) p2 -> nd a (p1 *-> p2).

Lemma NDstarling : forall {a : assump} {p1 p2 p3 : proposition},
                   nd a ((p1 *-> p2 *-> p3) *-> (p1 *-> p2) *-> p1 *-> p3).
  intros.
  repeat apply NDimpi.
  apply (NDmp
    (NDmp (NDasp (Esucc (Esucc Ezero))) (NDasp Ezero))
    (NDmp (NDasp (Esucc Ezero)) (NDasp Ezero))).
Defined.

Lemma NDkestrel : forall {a : assump} {p1 p2 : proposition}, nd a (p1 *-> p2 *-> p1).
  intros.
  repeat apply NDimpi.
  apply (NDasp (Esucc Ezero)).
Defined.

Lemma Hidentity : forall {a : assump} {p : proposition}, hilbert a (p *-> p).
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
    match a with
    | nil => hilbert nil p1
    | p2 :: a => hilbert a (p2 *-> p1)
    end)
    _ _ _ _ (p1 :: a) p2 H) ; intros ; destruct a0.
  exact (Hmp H0 H2).
  exact (Hmp (Hmp Hstarling H1) H3).
  exact (Hasp H0).
  inversion H0.
  exact Hidentity.
  exact (Hmp Hkestrel (Hasp H3)).
  exact Hstarling.
  exact (Hmp Hkestrel Hstarling).
  exact Hkestrel.
  exact (Hmp Hkestrel Hkestrel).
Defined.

Theorem nd_hilbert_homomorphism : forall {a : assump} {p : proposition}, nd a p -> hilbert a p.
  intros.
  induction H.
  exact (Hmp IHnd1 IHnd2).
  exact (Hasp H).  
  exact (Himpi IHnd).
Defined.
