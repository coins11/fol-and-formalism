Require Import Arith.
Require Import List.

Inductive proposition : Set :=
    Pbot  : proposition
  | Patom : nat -> proposition
  | Pimp  : proposition -> proposition -> proposition
  | Pand  : proposition -> proposition -> proposition
  | Por   : proposition -> proposition -> proposition.

Definition assump : Set := list proposition.

Definition Pneg (p : proposition) : proposition := Pimp p Pbot.

Inductive elem {A : Set} : A -> list A -> Prop :=
    Ezero : forall {x : A} {y : list A}, elem x (x :: y)
  | Esucc : forall {x : A} {y : list A} {x' : A},
            elem x y -> elem x (x' :: y).

Definition contains {A : Set} (l1 l2 : list A) : Set :=
  forall (x : A), elem x l1 -> elem x l2.

Lemma cid : forall {A : Set} {l : list A}, contains l l.
  intros.
  intro.
  intro.
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
  intros.
  intro.
  intros.
  inversion H0.
  apply Ezero.
  apply Esucc.
  apply (ectrans H3 H).
Defined.

Lemma csucc : forall {A : Set} {x : A} {l1 l2 : list A},
              contains l1 l2 -> contains l1 (x :: l2).
  intros.
  intro.
  intros.
  inversion H0 ; apply (Esucc (ectrans H0 H)).
Defined.

Lemma emap : forall {A B : Set} {x : A} {l : list A} (f : A -> B),
             elem x l -> elem (f x) (map f l).
  intros.
  induction H.
  exact Ezero.
  exact (Esucc IHelem).
Defined.

Inductive nkrule : assump -> proposition -> Prop :=
    NKasp   : forall {p : proposition} {a : assump}, elem p a -> nkrule a p
  | NKandi  : forall {p1 p2 : proposition} {a : assump},
              nkrule a p1 -> nkrule a p2 -> nkrule a (Pand p1 p2)
  | NKande1 : forall {p1 p2 : proposition} {a : assump},
              nkrule a (Pand p1 p2) -> nkrule a p1
  | NKande2 : forall {p1 p2 : proposition} {a : assump},
              nkrule a (Pand p1 p2) -> nkrule a p2
  | NKimpi  : forall {p1 p2 : proposition} {a : assump},
              nkrule (p1 :: a) p2 -> nkrule a (Pimp p1 p2)
  | NKimpe  : forall {p1 p2 : proposition} {a : assump},
              nkrule a (Pimp p1 p2) -> nkrule a p1 -> nkrule a p2
  | NKori1  : forall {p1 p2 : proposition} {a : assump},
              nkrule a p1 -> nkrule a (Por p1 p2)
  | NKori2  : forall {p1 p2 : proposition} {a : assump},
              nkrule a p2 -> nkrule a (Por p1 p2)
  | NKore   : forall {p1 p2 p3 : proposition} {a : assump},
              nkrule a (Por p1 p2) -> nkrule (p1 :: a) p3 ->
              nkrule (p2 :: a) p3 -> nkrule a p3
  | NKbote  : forall {p : proposition} {a : assump}, nkrule a Pbot -> nkrule a p
  | NKlem   : forall {p : proposition} {a : assump}, nkrule a (Por p (Pneg p)).

Inductive njrule : assump -> proposition -> Prop :=
    NJasp   : forall {p : proposition} {a : assump}, elem p a -> njrule a p
  | NJandi  : forall {p1 p2 : proposition} {a : assump},
              njrule a p1 -> njrule a p2 -> njrule a (Pand p1 p2)
  | NJande1 : forall {p1 p2 : proposition} {a : assump},
              njrule a (Pand p1 p2) -> njrule a p1
  | NJande2 : forall {p1 p2 : proposition} {a : assump},
              njrule a (Pand p1 p2) -> njrule a p2
  | NJimpi  : forall {p1 p2 : proposition} {a : assump},
              njrule (p1 :: a) p2 -> njrule a (Pimp p1 p2)
  | NJimpe  : forall {p1 p2 : proposition} {a : assump},
              njrule a (Pimp p1 p2) -> njrule a p1 -> njrule a p2
  | NJori1  : forall {p1 p2 : proposition} {a : assump},
              njrule a p1 -> njrule a (Por p1 p2)
  | NJori2  : forall {p1 p2 : proposition} {a : assump},
              njrule a p2 -> njrule a (Por p1 p2)
  | NJore   : forall {p1 p2 p3 : proposition} {a : assump},
              njrule a (Por p1 p2) -> njrule (p1 :: a) p3 ->
              njrule (p2 :: a) p3 -> njrule a p3
  | NJbote  : forall {p : proposition} {a : assump}, njrule a Pbot -> njrule a p.

Theorem NJtoNK : forall (a : assump) (p : proposition), njrule a p -> nkrule a p.
  intros.
  induction H.
  apply (@NKasp p a) ; auto.
  apply NKandi ; auto.
  apply (@NKande1 p1 p2) ; auto.
  apply (@NKande2 p1 p2) ; auto.
  apply NKimpi ; auto.
  apply (@NKimpe p1 p2) ; auto.
  apply NKori1 ; auto.
  apply NKori2 ; auto.
  apply (@NKore p1 p2 p3) ; auto.
  apply NKbote ; auto.
Defined.

Theorem NJK : forall {a1 a2 : assump} {p : proposition},
              contains a1 a2 -> njrule a1 p -> njrule a2 p.
  intros.
  revert a2 H.
  induction H0 ; intros.
  apply (@NJasp p a2) ; auto.
  apply NJandi ; auto.
  apply (@NJande1 p1 p2) ; auto.
  apply (@NJande2 p1 p2) ; auto.
  apply (NJimpi (IHnjrule _ (cstep H))).
  apply (NJimpe (IHnjrule1 _ H) (IHnjrule2 _ H)).
  apply (NJori1 (IHnjrule _ H)).
  apply (NJori2 (IHnjrule _ H)).
  apply (NJore (IHnjrule1 _ H) (IHnjrule2 (p1 :: a2) (cstep H))
    (IHnjrule3 (p2 :: a2) (cstep H))).
  apply (NJbote (IHnjrule a2 H)).
Defined.

Theorem NKtoNJ : forall (a : assump) (p : proposition),
                 nkrule a p -> njrule (map (fun p => Pneg (Pneg p)) a) (Pneg (Pneg p)).
  intros.
  induction H.
  exact (NJasp (emap (fun p => Pneg (Pneg p)) H)).
  exact (NJimpi
    (NJimpe
      (NJK (csucc cid) IHnkrule1)
      (NJimpi
        (NJimpe
          (NJK (csucc (csucc cid)) IHnkrule2)
          (NJimpi
            (NJimpe
              (NJasp (Esucc (Esucc Ezero)))
              (NJandi (NJasp (Esucc Ezero)) (NJasp Ezero)))))))).
  exact (NJimpi
    (NJimpe
      (NJK (csucc cid) IHnkrule)
      (NJimpi (NJimpe (NJasp (Esucc Ezero)) (NJande1 (NJasp Ezero)))))).
  exact (NJimpi
    (NJimpe
      (NJK (csucc cid) IHnkrule)
      (NJimpi (NJimpe (NJasp (Esucc Ezero)) (NJande2 (NJasp Ezero)))))).
  apply NJimpi.

