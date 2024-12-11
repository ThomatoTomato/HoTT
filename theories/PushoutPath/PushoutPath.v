Require Import Basics.
Require Import Colimits.Pushout.
Require Import Spaces.Nat.
Require Import Basics.Tactics.
Require Import Diagrams.Sequence.
Require Import WildCat.
Require Import Colimits.Colimit.
Require Import Colimits.Sequential.
Require Import Diagram.
Require Import Graph.
Require Import Types.
Require Import PushoutPath.Interleaving.

(** FIXME: Move this somewhere else. *)
Section InverseEquivCoh.

  (** Given type families [P : A -> Type], [Q : B -> Type], an equivalence [e : A <~> B], and a family of equivalences [f : forall (a : A), P a <~> Q (e a)], we get a family of equivalences [finv : forall (b : B), Q b <~> P (e^-1 b)] and some results about compositions of [f] and [finv]. *)

  Context {A B : Type} {P : A -> Type} {Q : B -> Type} (e : A <~> B) (f : forall (a : A), P a <~> Q (e a)).

  Definition finv : forall (b : B), Q b <~> P (e^-1 b).
  Proof.
    intro b.
    transitivity (Q (e (e^-1 b))).
    - snrapply equiv_transport.
      exact (eisretr e b)^.
    - symmetry.
      exact (f (e^-1 b)).
  Defined.

  Definition finv_f : forall (a : A), (finv (e a)) o (f a) == transport (fun y => P y) (eissect e a)^.
  Proof.
    intros a x.
    simpl.
    lhs nrapply (ap (fun z => (f (e^-1 (e a)))^-1 (transport Q z^ (f a x))) (eisadj e a)).
    nrapply (moveR_equiv_V' (f (e^-1 (e a)))).
    lhs nrapply (ap (fun z => transport Q z (f a x)) (ap_V e _)^).
    by destruct (eissect e a)^.
  Defined.

  Definition f_finv : forall (b : B), (f (e^-1 b)) o (finv b) == transport (fun y => Q y) (eisretr e b)^.
  Proof.
    intros b x.
    by nrapply (moveR_equiv_M' (f (e^-1 b))).
  Defined.
End InverseEquivCoh.

(** * Work towards characterizing the path types in a pushout of a span [R : A -> B -> Type]. The goal here is to work in half-steps, so that each construction only happens once. [C] will be used to denote a type that might be [A] or [B].  We think of a term of [Family C] as being the family [fun c => a0 squiggle_t c]. *)
Definition Family (C : Type) := C -> Type.

(** Here [P a] should be thought of as [a_0 squiggle_t a] and [Q b] as [a_0 squiggle_{t+1} b].  This describes the type of the "dot" operation [- ._t -]. This will also be used with [A] and [B] swapped and [R] flipped. *)
Definition Dot {A B : Type} (R : A -> B -> Type) (P : Family A) (Q : Family B)
  := forall (a : A) (b : B) (r : R a b) (p : P a), Q b.

Section InductiveStep.

  (** Given two families [P] and [Q] and a dot map from [P] to [Q], we define one more family [P'], a stage map from [Q] to [P'] (relative to the flipped relation), and a fiberwise map iota from [P] to [P']. Note that [flip R] has type [B -> A -> Type]. *)

  Context {A B : Type} (R : A -> B -> Type).
  Context {P : Family A} {Q : Family B} (dot : Dot R P Q).

  (** We define the new type family as the pushout. *)
  Definition family_step : Family A.
  Proof.
    intro a.
    snrapply (@Pushout ({b : B & R a b} * P a) (P a) {b : B & (R a b * Q b)}).
    - exact snd.
    - intros [[b r] p].
      exact (b; (r, dot a b r p)).
  Defined.

  (** We define the next "dot" map as [pushr]. *)
  Definition dot_step : Dot (flip R) Q family_step
:= fun b a r q => pushr (b; (r, q)).

  (** We define iota as [pushl]. *)
  Definition iota_step : forall a, P a -> family_step a
    := fun a p => pushl p.

  (** We define the homotopy showing that the composition of the two dot maps is iota. *)
  Definition homotopy_step : forall (a : A) (b : B) (r : R a b), 
    (iota_step a) == (dot_step b a r) o (dot a b r) 
    := fun a b r p => (pglue ((b ; r) , p)).
End InductiveStep.

Section ZigzagIdentity.

  (** Construct the identity zigzag sequence. *)

  Context {A B : Type} (R : A -> B -> Type) (a0 : A).

  (** Use a record type for a full step to avoid the interleaved sequence and [flip R]. *)
  Record Zig : Type := {
    P : Family A;
    Q : Family B;
    concatQP : Dot (flip R) Q P;
  }.

  Definition Qsucc (Z : Zig) : Family B
    := family_step (flip R) (concatQP Z).

  Definition concatPQ (Z : Zig) : Dot R (P Z) (Qsucc Z)
    := dot_step (flip R) (concatQP Z).

  Definition Psucc (Z : Zig) : Family A
    := family_step R (concatPQ Z).

  Definition concatQPsucc (Z : Zig) : Dot (flip R) (Qsucc Z) (Psucc Z)
    := dot_step R (concatPQ Z).

  Definition zigzag_step (Z : Zig) : Zig
    := Build_Zig (Psucc Z) (Qsucc Z) (concatQPsucc Z).

  (** The initial zigzag: over [A] we have the identity type at [a0] and over [B] we have the empty type; these should be thought of as paths of length 0 and -1, respectively. *)
  Definition zigzag_initial : Zig.
  Proof.
    snrapply Build_Zig.
    - exact (fun a => a0 = a). (** Define [P0 := Id a0] *)
    - exact (fun b => Empty). (** Define [Q0 := Empty] *)
  - intros b a r q; destruct q. (** Define [Q0 -> P_0] *)
  Defined.

  Definition zigzag : nat -> Zig
    := fun n => nat_iter n zigzag_step zigzag_initial.

  Definition zigzag_P : A -> Sequence.
  Proof.
    intro a.
    snrapply Build_Sequence.
    - intro n; exact (P (zigzag n) a).
    - intro n. cbn. apply iota_step.
  Defined.

  Definition zigzag_Q : B -> Sequence.
  Proof.
    intro b.
    snrapply Build_Sequence.
    - intro n; exact (Q (zigzag n) b).
    - intro n. cbn. apply iota_step.
  Defined.

  Definition zigzag_gluePQ {a : A} {b : B} (r : R a b) 
    : DiagramMap (zigzag_P a) (succ_seq (zigzag_Q b)).
  Proof.
    snrapply Build_DiagramMap.
    - intro n; exact (concatPQ (zigzag n) a b r).
    - intros n m g x.
      destruct g.
      lhs nrapply homotopy_step.
      apply ap.
      symmetry.
      apply homotopy_step.
  Defined.

  Definition zigzag_glueQP {a : A} {b : B} (r : R a b) 
: DiagramMap (zigzag_Q b) (zigzag_P a).
  Proof.
    snrapply Build_DiagramMap.
    - intro n; exact (concatQP (zigzag n) b a r).
    - intros n m g x.
      destruct g.
      lhs nrapply homotopy_step.
      apply ap.
      symmetry.
      apply homotopy_step.
  Defined.

  Definition zigzag_gluePQP {a : A} {b : B} (r : R a b) (n : nat)
    : (fun (x : zigzag_P a n) => x^+) == zigzag_glueQP r (S n) o zigzag_gluePQ r n
    := (homotopy_step R _ a b r).

  Definition zigzag_glueQPQ {a : A} {b : B} (r : R a b) (n : nat)
    : (fun (x : zigzag_Q b n) => x^+) == zigzag_gluePQ r n o zigzag_glueQP r n
    := (homotopy_step (flip R) _ b a r).

  (** The colimit of paths starting and ending in A. *)
  Definition zigzag_Pinf (a : A) : Type
    := Colimit (zigzag_P a).

  (** Our candidate for reflexivity: the colimit of reflexivity. *)
  Definition zigzag_refl : zigzag_Pinf a0
    := @colim _ (zigzag_P a0) 0%nat idpath.

  (** The colimit of paths starting in A and ending in B. *)
  Definition zigzag_Qinf (b : B) : Type 
    := Colimit (zigzag_Q b).

  Section GluingEquiv.

    Context {a : A} {b : B} (r : R a b).

    (** The gluing equivalence. *)
    Definition equiv_zigzag_glueinf
      : (zigzag_Pinf a) <~> (zigzag_Qinf b)
      := equiv_zigzag_glue (zigzag_glueQP r) (zigzag_gluePQ r) (zigzag_glueQPQ r) (zigzag_gluePQP r).

    Definition zigzag_gluePQinf : zigzag_Pinf a -> zigzag_Qinf b
      := equiv_zigzag_glueinf.

    Definition zigzag_glueQPinf : zigzag_Qinf b -> zigzag_Pinf a
      := equiv_zigzag_glueinf^-1.

    Definition zigzag_comp_eissect (n : nat) (p : zigzag_P a n) : (eissect equiv_zigzag_glueinf (@colim _ (zigzag_P a) n p)) = (ap (@colim _ (zigzag_P a) (S n)) (zigzag_gluePQP r n p)^) @ (@colimp _ (zigzag_P a) n _ _ p)
      := zigzag_comp_eissect (zigzag_glueQP r) (zigzag_gluePQ r) (zigzag_glueQPQ r) (zigzag_gluePQP r) n p.

    Definition zigzag_comp_eisretr (n : nat) (q : zigzag_Q b n) : (eisretr equiv_zigzag_glueinf (@colim _ (zigzag_Q b) n q)) = (ap (@colim _ (zigzag_Q b) (S n)) (zigzag_glueQPQ r n q)^) @ (@colimp _ (zigzag_Q b) n _ _ q)
      := zigzag_comp_eisretr (zigzag_glueQP r) (zigzag_gluePQ r) (zigzag_glueQPQ r) (zigzag_gluePQP r) n q.

  End GluingEquiv.

  (** Prove that the colimit of the identity zigzag is equivalent to the identity type for pushouts. *)

  (** FIXME: This is essentially [SpanPushout]. *)

  Definition relation_total : Type
    := {x : A * B | R (fst x) (snd x)}.

  Definition relation_pushout : Type.
  Proof.
    snrapply Pushout.
    + exact relation_total.
    + exact A.
    + exact B.
    + exact (fst o pr1).
    + exact (snd o pr1).
  Defined.

  Context `{Univalence}.

  (** The candidate for the identity type. *)
  Definition zigzag_family_half
    : relation_pushout -> Type
    := induced_fam_pod (Build_poDescent zigzag_Pinf zigzag_Qinf (fun x => equiv_zigzag_glueinf (pr2 x))).

  (** Contruct the half-induction principle from Kraus-von Raumer. *)
  Context (P : forall (a : A) (p : zigzag_family_half (pushl a)), Type)
    (Q : forall (b : B) (q : zigzag_family_half (pushr b)), Type)
    (refl : P a0 zigzag_refl)
    (e : forall (a : A) (b : B) (r : R a b) (p : zigzag_family_half (pushl a)), P a p <~> Q b (zigzag_gluePQinf r p)).

  (** Coq is very bad at scoping in [colim] and [colimP] when dealing with natural numbers. *)
  Let colimL {a : A} {n : nat} (p : zigzag_P a n) : zigzag_Pinf a
    := @colim _ (zigzag_P a) n p.

  Let colimR {b : B} {n : nat} (q : zigzag_Q b n) : zigzag_Qinf b
    := @colim _ (zigzag_Q b) n q.

  Let colimpL {a : A} {n : nat} (p : zigzag_P a n) 
    := @colimp _ (zigzag_P a) n (S n) idpath p.

  Let colimpR {b : B} {n : nat} (q : zigzag_Q b n) 
    := @colimp _ (zigzag_Q b) n (S n) idpath q.

  Let einv (a : A) (b : B) (r : R a b) (q : zigzag_Qinf b) : Q b q <~> P a (zigzag_glueQPinf r q)
    := finv (equiv_zigzag_glueinf r) (e a b r) q.

  Let iotaP {a : A} (n : nat) := (seq_to_succ_seq (zigzag_P a) n).

  Let iotaQ {b : B} (n : nat) := (seq_to_succ_seq (zigzag_Q b) n).

  (** The two type families, viewed over the sequences [zigzag_P] and [zigzag_Q] instead of their colimits. *)
  Let Pn (n : nat) (a : A) (p : zigzag_P a n)
    := P a (colimL p).

  Let Qn (n : nat) (b : B) (q : zigzag_Q b n)
    := Q b (colimR q).

  (** These are the maps used in the pushout defining [P_{n+1}] in the identity zigzag. *)
  Let pushfP (a : A) (n : nat) : forall (c : ({b : B | R a b} * (zigzag_P a n))), zigzag_P a n
    := snd.

  Let pushgP (a : A) (n : nat)
    : forall (c : ({b : B | R a b} * (zigzag_P a n))), {b : B & (R a b * (zigzag_Q b (S n)))}.
  Proof.
    intros [[b r] p].
    exact (b ; (r , (zigzag_gluePQ r n p))).
  Defined.

  (** These are the maps used in the pushout defining [Q_{n+1}] in the identity zigzag. *)
  Let pushfQ (b : B) (n : nat) : forall (c : ({a : A | R a b} * (zigzag_Q b n))), zigzag_Q b n
    := snd.

  Let pushgQ (b : B) (n : nat)
    : forall (c : ({a : A | R a b} * (zigzag_Q b n))), {a : A & (R a b * (zigzag_P a n))}.
  Proof.
    intros [[a r] q].
    exact (a ; (r , (zigzag_glueQP r n q))).
  Defined.

  (* The type of the maps we wish to construct: *)
  Let indLn (n : nat) := forall (a : A) (p : zigzag_P a n), Pn n a p.
  Let indRn (n : nat) := forall (b : B) (q : zigzag_Q b n), Qn n b q.

  (* The goal of this section is to represent the data needed to produce something of type [indL (S n) a] from something of type [indRn (S n)] and [indLn n]; we are capturing the following situation:

<<
    
                   pushg := (b, r, gluePQ n r p)                                 (b, r, q, indR n+1 b q)

  (b : B)x(r : R a b)x(p : a0 ~>n a) -----> (b : B)x(r : R a b)x(q : a0 ~>n+1 b) ----------------------.
               |                                            |                                           \
               |                                            |                                            \
 pushf := pr3  |                                            | (b, r, q) |-> glueQP n+1 r q                \
               |                                            |                                              \
               v                                            v                                               v
               (p : a0 ~>n A) ---------------------------> (p' : a0 ~>n+1 a)         (b : B)x(r : R a b)x(q : a0 ~>n+1 b)xQn n+1 b q
                \                                                                                           |
                 \                iotaP                                                                     |
                  \                                                                             inv a b r q |
                   \                                                                                        |
                    \                                                                                       v
                     \                                                                          Pn n+1 a (zigzag_glueQP n+1 r q)
                      `--------------> Pn n+1 a p^+

>>

We don't care about the bottom left map (which is [indL n a] followed by [transport colimp]) but to define [indR (S n)] it is extremely helpful to have the top right square, i.e. the composition of the right map in the pushout followed by the induced map, commute judgementally without any additional transports.

  The right case changes the square slightly, replacing [e] with [einv] and some indexing changes due to the asymmetricity of the zigzag construction.
  *)

  Section ind_dataL.
    Context (n : nat) (ind_indRn : indRn (S n)) (a : A).

    Definition ind_pushcP : forall (c : {b : B & (R a b * (zigzag_Q b (S n)))}), Pn (S n) a (zigzag_glueQP (fst (pr2 c)) (S n) (snd (pr2 c)))
      := fun c => (einv a (pr1 c) (fst (pr2 c)) (colimR (snd (pr2 c))) (ind_indRn (pr1 c) (snd (pr2 c)))).

    Record pushout_ind_data_P : Type := {
      ind_pushbP : (forall (p : zigzag_P a n), Pn (S n) a (iotaP n p));
      ind_pushaP : (forall (c : ({b : B | R a b} * (zigzag_P a n))), pglue c # (ind_pushbP ((pushfP a n) c)) = ind_pushcP ((pushgP a n) c))
    }.

    (* Take the pushout *)
    Definition pushout_ind_P_res (ind : pushout_ind_data_P) : (forall (p : zigzag_P a (S n)), Pn (S n) a p).
    Proof.
      snrapply Pushout_ind.
      - exact (ind_pushbP ind).
      - exact ind_pushcP.
      - exact (ind_pushaP ind).
    Defined.

  End ind_dataL.

  (* The goal of this section is to represent the data needed to produce something of type [Rn (S n)] from something of type [Ln n] *)
  Section ind_dataR.
    Context (n : nat) (ind_indLn : indLn n) (b : B).

    Definition ind_pushcQ : forall (c : {a : A & (R a b * (zigzag_P a n))}), Qn (S n) b (zigzag_gluePQ (fst (pr2 c)) n (snd (pr2 c)))
      := fun c => (e (pr1 c) b (fst (pr2 c)) (colimL (snd (pr2 c))) (ind_indLn (pr1 c) (snd (pr2 c)))).

    Record pushout_ind_data_Q : Type := {
      ind_pushbQ : (forall (q : zigzag_Q b n), Qn (S n) b (iotaQ n q));
      ind_pushaQ : (forall (c : ({a : A | R a b} * (zigzag_Q b n))), pglue c # (ind_pushbQ ((pushfQ b n) c)) = ind_pushcQ ((pushgQ b n) c))
    }.

    (* Take the pushout *)
    Definition pushout_ind_Q_res (ind : pushout_ind_data_Q) : (forall (q : zigzag_Q b (S n)), Qn (S n) b q).
    Proof.
      snrapply Pushout_ind.
      - exact (ind_pushbQ ind).
      - exact ind_pushcQ.
      - exact (ind_pushaQ ind).
    Defined.
  End ind_dataR.

  (** Interaction of iterated transport with composition of the type family. *)
  Local Definition transportlemma {X X' Y : Type} (f : X -> X') (g : X -> Y) (g' : X' -> Y) (Z : Y -> Type) {x : X} {y : X'} (p : f x = y) (q : g x = g' (f x)) : (fun z => (transport (Z o g') p (transport Z q z))) == (transport Z (q @ ap g' p)).
  Proof.
    destruct p.
    simpl.
    intro z.
    by rhs apply (ap (fun a => transport Z a z) (concat_p1 q)).
  Defined.

  (* We have the following situation:

<<
    
                                                                 (b, r, a', r', p', indL n a p')

   (b : B)x(r : R a b)x(a' : A)x(r' : R a' b)x(p' : a0 ~>n a') -----------------> (b : B)x(r : R a b)x(a' : A)x(r' : R a' b)x(p' : a0 ~>n a')xPn n a' p'
                 ^                                     \                                                    |
                / (b, r, a, r, p)                       \ (b, r, gluePQ n r' p')                            |
               /                                         v                         (b, r, q, indR n+1 b q)  |
  (b : B)x(r : R a b)x(p : a0 ~>n a) -----> (b : B)x(r : R a b)x(q : a0 ~>n+1 b) ------------.              |
               |                                            |                                 \             | e a' b r' p'
               |            (b, r, gluePQ n r p)            |                                  \            |
 pushf := pr3  |                                            | glueQP n+1 r q                    \           |
               |                                            |                                    \          |
               v                                            v                                     v         v
         (p : a0 ~>n A) ---------------------------> (p' : a0 ~>n+1 a)                      (b : B)x(r : R a b)x(q : a0 ~>n+1 b)xQn n+1 b q
                \                                                                                           |
                 \                iotaP                                                                     |
                  \                                                                            einv a b r q |
                   \                                                                                        |
                    \                                                                                       v
                     \                                                                          Pn n+1 a (zigzag_glueQP n+1 r q)
                      `--------------> Pn n+1 a p^+

>> 

  using the notation [a0 ~>m x] to mean either [zigzag_P] or [zigzag_Q] at index [m] (NOT using [m] as the "path length", i.e.~the real path length is [2*m] for P and [2*m-1] for Q. *)

  Local Definition indL_step (n : nat) (a : A) (indLp : indLn n) 
    (indRp_data : forall (b : B), pushout_ind_data_Q n indLp b)
    : pushout_ind_data_P n (fun b => pushout_ind_Q_res n indLp b (indRp_data b)) a.
  Proof.
    pose (indRp := fun b => pushout_ind_Q_res n indLp b (indRp_data b)).
    snrapply (Build_pushout_ind_data_P n indRp a).
    - intro p.
      (* The left map is exactly what it should be: the previous left induction followed by transport along [colimp]. This makes descent to the colimit immediate later on and MUST NOT BE CHANGED. *)
      apply (transport (fun z => P a z) (colimpL p)^).
      exact (indLp a p).
    - intros [[b r] p].

      (* Go on the top path of the diagram instead; using [pushout_ind_data_Q] ensures that this commutes judgementally. *)
      change (ind_pushcP n indRp a (pushgP a n ((b; r), p))) 
        with (einv a b r (@colimR b (S n) (zigzag_gluePQ r n p)) (e a b r (colimL p) (indLp a p))).

      (* Compute the [einv o e] bit. *)
      rhs apply (finv_f (equiv_zigzag_glueinf r) (e a b r) (colimL p) (indLp a p)).

      (* Use the computation of [eissect equiv_zigzag_glueinf]. *)
      transitivity (transport (fun y : zigzag_family_half (pushl a) => P a y)
         (ap (inj (zigzag_P a) n.+1%nat)
            (zigzag_gluePQP r n p)^ @ 
          colimpL p)^ (indLp a p)).
        + rhs nrapply (ap (fun z => transport (P a) z (indLp a p)) _).
          2: {
            lhs nrapply inv_pV.
            lhs nrapply (1 @@ (inverse2 (ap_V _ (zigzag_gluePQP r n p)))).
            lhs nrapply (1 @@ (inv_V _)); reflexivity.
          }
          refine ((transportlemma _ (@colimL a n) (@colimL a (S n)) (fun y => P a y) (pglue ((b ; r), p)) (@colimpL a n p)^ (indLp a p)) @ _).
          by lhs nrapply (ap (fun z => transport (P a) z (indLp a p)) ((inv_V _) @@ 1)).
        + change (zigzag_family_half (pushl a)) with (zigzag_Pinf a).
          nrapply (ap (fun z => transport (P a) z (indLp a p))).
          nrapply (ap (fun z => z^) (zigzag_comp_eissect r n _))^.
  Defined.


  (** FIXME: Reprove once [indL_step] is cleaned up. *)
  Local Definition indR_step (n : nat) (b : B) (indRp : indRn (S n))
    (indLp_data : forall (a : A), pushout_ind_data_P n indRp a)
    : pushout_ind_data_Q (S n) (fun a => pushout_ind_P_res n indRp a (indLp_data a)) b.
  Proof.
    pose (indLp := fun a => pushout_ind_P_res n indRp a (indLp_data a)).
    snrapply (Build_pushout_ind_data_Q (S n) indLp b).
    - intro q.
      apply (transport (fun z => Q b z) (colimpR q)^).
      exact (indRp b q).
    - intros [[a r] q].

      transparent assert (bigindRp : (forall (c : {b' : B | (R a b') * (zigzag_Q b' (S n))}), {b' : B | (R a b') * {q'' : zigzag_Q b' (S n) & Qn (S n) b' q''}})). {
        intros [b' [r' q']].
        exact (b' ; (r' , (q' ; indRp b' q'))).
      }

      transparent assert (bigeinv : (forall (c : {b' : B | (R a b') * {q'' : zigzag_Q b' (S n) & Qn (S n) b' q''}}), Pn (S n) a (zigzag_glueQP (fst (pr2 c)) (S n) (pr1 (snd (pr2 c)))))). {
        intros [b' [r' [q'' z]]].
        exact (einv a b' r' (colimR q'') z).
      }

      transparent assert (bigindLp : (forall (p : zigzag_P a (S n)), Pn (S n) a p)). {
        intro p.
        exact (indLp a p).
      }

      transparent assert (bigglue : (forall (c : {b' : B | (R a b') * (zigzag_Q b' (S n))}), (zigzag_P a (S n)))). {
        exact pushr.
      }

      transparent assert (incl : ((zigzag_Q b (S n)) -> {b' : B | (R a b') * (zigzag_Q b' (S n))})). {
        intro q'.
        exact (b ; (r , q')).
      }

      change (ind_pushcQ (S n) indLp b (pushgQ b (S n) ((a; r), q))) with (e a b r (@colimL a (S n) (zigzag_glueQP r (S n) q)) (bigeinv (bigindRp (incl q)))).
      simpl pushfP.
      rhs apply (f_finv (equiv_zigzag_glueinf r) (e a b r) (colimR q) (pr2 (snd (pr2 (bigindRp (incl q)))))).

      transitivity (transport (fun y : zigzag_family_half (pushr b) => Q b y)
         (ap (inj (zigzag_Q b) n.+2%nat)
            (zigzag_glueQPQ r (S n) q)^ @ 
          colimpR q)^ (snd (bigindRp (incl q)).2).2).
      + unfold zigzag_gluePQP.
        unfold homotopy_step.
        rewrite inv_pV.
        rewrite ap_V.
        rewrite inv_V.
        change (zigzag_family_half (pushr b)) with (zigzag_Qinf b).
        refine ((transportlemma _ (@colimR b (S n)) (@colimR b n.+2) (fun y => Q b y) (pglue ((a ; r), q)) (@colimpR b (S n) q)^ (indRp b q)) @ _).
        by rewrite inv_V.
      + change (zigzag_family_half (pushr b)) with (zigzag_Qinf b).
        apply (ap (fun z => transport (Q b) z (snd (bigindRp (incl q)).2).2)).
        nrapply (ap (fun z => z^) (zigzag_comp_eisretr r (S n) _))^.
  Defined.

  (** Conduct two inductions steps at once. *)
  Local Definition double_ind_step (n : nat) (indLp : indLn n) (indRp_data : forall (b : B), pushout_ind_data_Q n indLp b) : {indL : indLn (S n) & (forall (b : B), pushout_ind_data_Q (S n) indL b)}.
  Proof.
    pose (indRp := fun b => pushout_ind_Q_res n indLp b (indRp_data b)).
    snrapply (_ ; _).
    - intro b.
      snrapply pushout_ind_P_res.
      + exact indRp.
      + snrapply indL_step.
    - intro a.
      snrapply indR_step.
  Defined.

  (** Do the double induction. *)
  Local Definition double_ind (n : nat) : {indL : indLn n & (forall (b : B), pushout_ind_data_Q n indL b)}.
  Proof.
    induction n.
    - snrapply (_ ; _).
      + intros _ []; exact refl.
      + intro b.
        snrapply Build_pushout_ind_data_Q.
        * intro q.
          destruct q.
        * intros [[a r] q].
          destruct q.
    - destruct IHn as [indLp indRp].
      exact (double_ind_step n indLp indRp).
  Defined.

  (** The sequence of left induction maps. *)
  Definition indL_seq (a : A) (n : nat) (p : zigzag_P a n) : Pn n a p.
  Proof.
    exact (pr1 (double_ind n) a p).
  Defined.

  (** The sequence of right induction maps. *)
  Definition indR_seq (b : B) (n : nat) (q : zigzag_Q b n) : Qn n b q.
  Proof.
    induction n.
    - destruct q.
    - destruct (double_ind n) as [indL indR_data].
      exact (pushout_ind_Q_res n indL b (indR_data b) q).
  Defined.

  (** The left maps descend to the colimit. *)
  Definition indL_colim (a : A) (p : zigzag_Pinf a) : P a p.
  Proof.
    snrapply Colimit_ind.
    - intros n pn.
      exact (indL_seq a n pn).
    - intros n _ [] pn.
      unfold indL_seq; simpl.
      lhs nrapply (transport_pp _ _ _ _)^.
      by lhs nrapply (ap (fun z => transport (P a) z _) (concat_Vp _)).
  Defined.

  (** The right maps descend to the colimit. *)
  Definition indR_colim (b : B) (q : zigzag_Qinf b) : Q b q.
  Proof.
    snrapply Colimit_ind.
    - intros n qn.
      exact (indR_seq b n qn).
    - intros n _ [] qn.
      induction n.
      + destruct qn.
      + unfold indR_seq; simpl.
        lhs nrapply (transport_pp _ _ _ _)^.
        by lhs nrapply (ap (fun z => transport (Q b) z _) (concat_Vp _)).
  Defined.

  (** The left colimit map computes on reflexivity. *)
  Definition indL_comp_refl : (indL_colim a0 zigzag_refl) = refl.
  Proof.
    reflexivity.
  Defined.

  (** The colimit maps compute on gluing. *)
  Definition ind_comp_glue {a : A} {b : B} (r : R a b) (p : zigzag_Pinf a) : indR_colim b (zigzag_gluePQinf r p) = e a b r p (indL_colim a p).
  Proof.
    revert p.
    snrapply Colimit_ind.
    - intros n pn.
      reflexivity.
    - intros n _ [] pn.
      lhs nrapply (transport_paths_FlFr_D (f:=fun z => indR_colim b (_ r z))).
      Open Scope long_path_scope.
      rewrite concat_p1.
      rewrite apD_compose.
      unfold zigzag_gluePQinf.
      unfold equiv_zigzag_glueinf.
      simpl.
      unfold zigzag_glue_map_inv_inf.
      (* Bad: rewrite (functor_Colimit_half_beta_colimp (zigzag_glue_map_inv (zigzag_glueQP r) (zigzag_gluePQ r) (zigzag_glueQPQ r) (zigzag_gluePQP r)) (Colimit_succ _) n (S n) idpath pn). *)
      pose (rew := (functor_Colimit_half_beta_colimp (zigzag_glue_map_inv (zigzag_glueQP r) (zigzag_gluePQ r) (zigzag_glueQPQ r) (zigzag_gluePQP r)) (Colimit_succ _) n (S n) idpath pn)).
      rewrite (apD02 (indR_colim b) rew).
      (* Bad: destruct rew. *)
    Admitted.
End ZigzagIdentity.

Section KvRApplication.
  (** Conclude by applying Kraus-von Raumer to get an equivalence with the identity types. *)

  Context {A B : Type} (R : A -> B -> Type) (a0 : A) `{Univalence}.

  Let R' := relation_total R.
  Let f : R' -> A := fst o pr1.
  Let g : R' -> B := snd o pr1.

  (** Package the data for KvR. *)
  Local Definition zigzag_poDescent : poDescent f g.
  Proof.
    snrapply Build_poDescent.
    + exact (zigzag_Pinf R a0).
    + exact (zigzag_Qinf R a0).
    + intros [[a b] r]; exact (equiv_zigzag_glueinf R a0 r).
  Defined.

  Local Definition zigzag_based_ind : forall (Qe : poDepDescent zigzag_poDescent) (q0 : podd_faml Qe a0 (zigzag_refl R a0)), poDepDescentSection Qe.
  Proof.
    intros Qe q0.
    Check podd_faml Qe.
    pose (indL := indL_colim R a0 (podd_faml Qe) (podd_famr Qe) q0 (fun a b r => podd_e Qe ((a , b) ; r))).
    pose (indR := indR_colim R a0 (podd_faml Qe) (podd_famr Qe) q0 (fun a b r => podd_e Qe ((a , b) ; r))).
    snrapply Build_poDepDescentSection.
    - exact indL.
    - exact indR.
    - intros [[a b] r] pf; symmetry.
      snrapply ind_comp_glue.
  Defined.

  (** Get the equivalence. *)
  Definition zigzag_equiv_identity (x : Pushout f g) : (pushl a0) = x <~> (zigzag_family_half R a0 x).
  Proof.
    snrapply induced_fam_pod_equiv_path.
    2: exact zigzag_based_ind.
    intros Qe q0.
    unfold zigzag_based_ind.
    simpl podds_sectl.
    snrapply indL_comp_refl.
    + exact (podd_famr Qe).
    + exact (fun a b r => podd_e Qe ((a , b) ; r)).
  Defined.
End KvRApplication.
