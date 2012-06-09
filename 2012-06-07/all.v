
Theorem p1 : forall (A B : Prop), B -> A -> B.
  tauto.
Qed.

Theorem p2 : forall (A : Prop), A /\ A -> A.
  tauto.
Qed.

Theorem p3 : forall (A : Prop), A -> A /\ A.
  tauto.
Qed.

Theorem p4 : forall (A B : Prop), A /\ B -> B /\ A.
  tauto.
Qed.

Theorem p5 : forall (A B C : Prop), (A -> B) /\ (B -> C) -> (A -> C).
  tauto.
Qed.

Theorem p6 : forall (A B C : Prop), (A -> B -> C) -> (A /\ B -> C).
  tauto.
Qed.

Theorem p7 : forall (A B C : Prop), (A /\ B -> C) -> (A -> B -> C).
  tauto.
Qed.

Theorem p8 : forall (A B C : Prop), (A /\ B) /\ C -> A /\ (B /\ C).
  tauto.
Qed.

Theorem p9 : forall (A B : Prop), A /\ (A -> B) -> B.
  tauto.
Qed.

Theorem p10 : forall (A B C : Prop), (A /\ B) /\ (A -> (B -> C)) -> C.
  tauto.
Qed.

Theorem p11 : forall (A B C : Prop), (A -> B /\ C) -> (A -> B) /\ (A -> C).
  tauto.
Qed.

Theorem p12 : forall (A B C : Prop), (A -> B) /\ (A -> C) -> (A -> B /\ C).
  tauto.
Qed.

Theorem p13 : forall (A : Prop), A \/ A -> A.
  tauto.
Qed.

Theorem p14 : forall (A : Prop), A -> A \/ A.
  tauto.
Qed.

Theorem p15 : forall (A B : Prop), A \/ B -> B \/ A.
  tauto.
Qed.

Theorem p16 : forall (A B C : Prop), (A \/ B) /\ C -> (A /\ C) \/ (B /\ C).
  tauto.
Qed.

Theorem p17 : forall (A B C : Prop), (A /\ C) \/ (B /\ C) -> (A \/ B) /\ C.
  tauto.
Qed.

Theorem p18 : forall (A B C : Prop), (A /\ B) \/ C -> (A \/ C) /\ (B \/ C).
  tauto.
Qed.

Theorem p19 : forall (A B C : Prop), (A \/ C) /\ (B \/ C) -> (A /\ B) \/ C.
  tauto.
Qed.

Theorem p20 : forall (A : Prop), A -> ~ ~ A.
  tauto.
Qed.

Theorem p22 : forall (A B : Prop), ~ (A \/ B) -> ~ A /\ ~ B.
  tauto.
Qed.

Theorem p23 : forall (A B : Prop), ~ A /\ ~ B -> ~ (A \/ B).
  tauto.
Qed.

Theorem p24 : forall (A B : Prop), (A -> B) -> (~ B -> ~ A).
  tauto.
Qed.

Theorem p27 : forall (A B : Prop), ~ A \/ ~ B -> ~ (A /\ B).
  tauto.
Qed.

Theorem p28 : forall (A B : Prop), ~ A \/ B -> (A -> B).
  tauto.
Qed.

Theorem p30 : forall (T1 T2 : Set) (A : T1 -> T2 -> Prop),
  (forall (x : T1) (y : T2), A x y) -> (forall (y : T2) (x : T1), A x y).
  intros ; exact (H x y).
Qed.

Theorem p31 : forall (T : Set) (A B : T -> Prop),
  (forall (x : T), (A x /\ B x)) -> (forall (x : T), A x) /\ (forall (x : T), B x).
  intros ; split ; intro ; destruct (H x) ; auto.
Qed.

Theorem p32 : forall (T : Set) (A B : T -> Prop),
  (forall (x : T), A x) /\ (forall (x : T), B x) -> (forall (x : T), (A x /\ B x)).
  intros ; split ; destruct H ; auto.
Qed.

Theorem p33 : forall (T1 T2 : Set) (A : T1 -> T2 -> Prop),
  (exists x : T1, exists y : T2, A x y) -> (exists y : T2, exists x : T1, A x y).
  intros ; repeat destruct H ; repeat eexists ; apply H.
Qed.

Theorem p34 : forall (T : Set) (A B : T -> Prop),
  (exists x : T, A x \/ B x) -> (exists x : T, A x) \/ (exists x : T, B x).
  intros ; repeat destruct H ; [left | right] ; eexists ; apply H.
Qed.

Theorem p35 : forall (T : Set) (A B : T -> Prop),
  (exists x : T, A x) \/ (exists x : T, B x) -> (exists x : T, A x \/ B x).
  intros ; repeat destruct H ; eexists ; [left | right] ; apply H.
Qed.

Theorem p36 : forall (T : Set) (A : T -> Prop),
  ~ (exists x : T, A x) -> (forall (x : T), ~ A x).
  repeat intro ; apply H ; eexists ; apply H0.
Qed.

Theorem p37 : forall (T : Set) (A : T -> Prop),
  (forall (x : T), ~ A x) -> ~ (exists x : T, A x).
  repeat intro ; destruct H0 ; apply (H x H0).
Qed.

Theorem p38 : forall (A : Prop), ~ A -> (A -> False).
  tauto.
Qed.

Theorem p39 : forall (A : Prop), (A -> False) -> ~ A.
  tauto.
Qed.

Theorem p40 : forall (T : Set) (A B : T -> Prop),
  (forall (x : T), A x) \/ (forall (x : T), B x) -> (forall (x : T), A x \/ B x).
  intros ; destruct H ; [left | right] ; apply H.
Qed.

Theorem p41 : forall (T : Set) (A B : T -> Prop),
  (exists x : T, A x /\ B x) -> (exists x : T, A x) /\ (exists x : T, B x).
  intros ; repeat destruct H ; split ; eexists ; [apply H | apply H0].
Qed.

Theorem p43 : forall (T : Set) (A : T -> Prop),
  (exists x : T, ~ A x) -> ~ (forall (x : T), A x).
  repeat intro ; destruct H ; apply H ; apply H0.
Qed.

Theorem p44 : forall (T : Set) (A : T -> Prop) (B : Prop),
  (exists x : T, A x /\ B) -> (exists x : T, A x) /\ B.
  intros ; repeat destruct H ; split ; [eexists ; apply H | auto].
Qed.

Theorem p45 : forall (T : Set) (A : T -> Prop) (B : Prop),
  (exists x : T, A x) /\ B -> (exists x : T, A x /\ B).
  intros ; repeat destruct H ; eexists ; split ; [apply H | auto].
Qed.

Theorem p46 : forall (T : Set) (A : T -> Prop) (B : Prop),
  (forall (x : T), A x -> B) -> ((exists x : T, A x) -> B).
  intros ; destruct H0 ; apply (H x H0).
Qed.

Theorem p47 : forall (T : Set) (A : T -> Prop) (B : Prop),
  ((exists x : T, A x) -> B) -> (forall x : T, A x -> B).
  intros ; apply H ; eexists ; apply H0.
Qed.

Theorem p50 : forall (T : Set) (A : T -> Prop) (B : Prop),
  (forall (x : T), A x) \/ B -> (forall (x : T), A x \/ B).
  intros ; destruct H ; [left ; apply H | right ; auto].
Qed.

Section Classical.

Variable lem : forall (P : Prop), P \/ ~ P.

Theorem p21 : forall (A : Prop), ~ ~ A -> A.
  intros ; destruct (lem A) ; tauto.
Qed.

Theorem p25 : forall (A B : Prop), (~ B -> ~ A) -> (A -> B).
  intros ; destruct (lem B) ; tauto.
Qed.

Theorem p26 : forall (A B : Prop), ~ (A /\ B) -> ~ A \/ ~ B.
  intros ; destruct (lem A) ; tauto.
Qed.

Theorem p29 : forall (A B : Prop), (A -> B) -> ~ A \/ B.
  intros ; destruct (lem A) ; tauto.
Qed.

Theorem p42 : forall (T : Set) (A : T -> Prop),
  ~ (forall (x : T), A x) -> (exists x : T, ~ A x).
  intros.
  destruct (lem (exists x : T, ~ A x)) ; auto.
  apply False_ind.
  apply H.
  intro.
  destruct (lem (A x)) ; auto.
  destruct (H0 (ex_intro _ x H1)).
Qed.

Theorem p48 : forall (A B : Prop), (~ A -> B) -> A \/ B.
  intros ; destruct (lem A) ; auto.
Qed.

Theorem p49 : forall (T : Set) (A : T -> Prop),
  ~ (exists x : T, ~ A x) -> (forall (x : T), A x).
  intros ; destruct (lem (A x)) ; auto.
  destruct (H (ex_intro _ x H0)).
Qed.

Theorem p51 : forall (T : Set) (A : T -> Prop) (B : Prop),
  (forall (x : T), A x \/ B) -> (forall (x : T), A x) \/ B.
  intros.
  destruct (lem B) ; auto.
  left ; intro ; destruct (H x) ; [auto | contradiction].
Qed.

End Classical.
