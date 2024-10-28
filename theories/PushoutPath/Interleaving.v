Require Import Basics.
Require Import Colimits.Pushout.
Require Import Spaces.Nat.
Require Import Basics.Tactics.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.
Require Import Diagrams.Cocone.
Require Import Diagrams.Sequence.
Require Import WildCat.
Require Import Colimits.Colimit.
Require Import Colimits.Sequential.
Require Import Diagram.
Require Import Types.

(** Suppose we have sequences [A_i] and [B_i]. An interleaving from [A_i] to [B_i] consists of two natural transformations d : A_i => B_i (d for down) and u : B_i => A_i+1 (u for up), such that the composites (u o d) and (d o i) correspond to the morphisms in the diagram itself. In other words, the following diagram is commutative: *)
    
(**  
<<
    A_0 -------> A_1 ------> A_2 ------>
        \        ^  \        ^ 
         \      /    \      /  
          \    /      \    /         ...
           v  /        v  /
           B_0 ------> B_1 ------->
>> 
*)

(** Given the setup above, we want to say that the colimit of the upper lower sequences are the same. From a sequence A, we can produce a diagram map from [A] to [succ_seq A]. It's the map that applies the arrow in the sequence to every element. *)

Definition seq_to_succ_seq (A : Sequence) : DiagramMap A (succ_seq A).
Proof.
  snrapply Build_DiagramMap.
  - intros n a. exact a^+. 
  - intros m n [] x. reflexivity.
Defined.

(** Given a map of sequences we can define a map between 
    their succesor sequences. *)

Definition succ_seq_map_seq_map {A B : Sequence} (f : DiagramMap A B) 
  : DiagramMap (succ_seq A) (succ_seq B).
Proof.
  snrapply Build_DiagramMap.
  - exact (f o S).
  - intros m n []. exact (DiagramMap_comm f _).
Defined.

(** A cocone over a sequence defines a cocone over the successor sequence *)

Definition succ_seq_cocone_seq_cocone {A : Sequence} (T : Type) (C : Cocone A T)
  : Cocone (succ_seq A) T.
Proof.
  srapply Build_Cocone.
  - exact (C o S).
  - intros m n []. rapply (legs_comm C).
Defined.

(** [cocone_precompose (seq_to_succ_seq A)] is an equivalence *)

Definition isequiv_cocone_precompose_seq_to_succ_seq
  `{Funext} {A : Sequence} {X : Type} 
  : IsEquiv (cocone_precompose (seq_to_succ_seq A) (X:=X)).
Proof.
  snrapply isequiv_adjointify.
  - exact (succ_seq_cocone_seq_cocone X).
  - intro C.
    snrapply path_cocone.
    + intro n. simpl. exact (legs_comm C n _ idpath).
    + intros m n [] a. simpl.
      exact (concat_1p _ @@ 1).
  - intro C.
    snrapply path_cocone.
    + intro n. simpl. exact (legs_comm C n _ idpath).
    + intros m n [] a. simpl.
      exact (concat_1p _ @@ 1).
Defined.

(** The cocone [colim_A] induces [idmap : A_w -> A_w]. *)

Definition col_legs_induces_idmap `{Funext} {A : Sequence}
  {A_w} (colim_A : IsColimit A A_w) 
  : cocone_postcompose_inv colim_A colim_A = idmap.
Proof.
  snrapply (equiv_inj (cocone_postcompose colim_A)).
  - exact (iscolimit_unicocone colim_A A_w).
  - lhs nrapply (eisretr (cocone_postcompose colim_A)).
    exact (cocone_postcompose_identity colim_A)^.
Defined.

(** We show that the map induced by [succ_seq_to_seq] is an equivalence. *)

Section Is_Equiv_colim_succ_seq_to_seq_map.
  Context `{Funext} {A : Sequence}
    {A_w : Type} (colim_A : IsColimit A A_w).

  (** The legs of [colim_A] induces a cocone from [succ_seq A] over [A_w] *)

  Definition cocone_succ_seq_over_col 
    : Cocone (succ_seq A) A_w
    := succ_seq_cocone_seq_cocone A_w colim_A.

  (** We start by showing that [abstr_colim_seq_to_abstr_colim_succ_seq] is a split-monomorphism. Observe that [cocone_succ_seq_over_col] essentially defines the same cocone as [colim_A]. I.e. the following  diagram is commutative: *)
  
  (**
  <<
                  A          succ_seq A
               ______          ______
              |      | =====>  \     |
              |      |         /     |
               ‾‾‾‾‾‾          ‾‾‾‾‾‾
                   \  \      /  /
            colim_A \  \    /  / cocone_succ_seq_over_col
                      colim A
  >>
  *)

  Definition legs_comm_cocone_succ_seq_over_col_with_col 
    (n : sequence_graph) 
    : cocone_precompose (seq_to_succ_seq A) cocone_succ_seq_over_col n
      == colim_A n := (legs_comm (iscolimit_cocone colim_A) _ _ _).

  Definition cocone_succ_seq_over_col_is_ess_col 
    : cocone_precompose (seq_to_succ_seq A) cocone_succ_seq_over_col
      = iscolimit_cocone colim_A.
  Proof.
    apply (path_cocone 
      legs_comm_cocone_succ_seq_over_col_with_col).
    intros m n [] a. 
    unfold legs_comm_cocone_succ_seq_over_col_with_col.
    simpl. exact (concat_1p _ @@ 1).
  Defined.

  (* The cocone of [succ_seq A] over colim A is universal *)

  Instance iscolimit_succ_seq_A_over_A_w : IsColimit (succ_seq A) A_w.
  Proof.
  snrapply (Build_IsColimit cocone_succ_seq_over_col).
  snrapply Build_UniversalCocone.
  intro Y.
  srapply isequiv_adjointify.
  - intro C.
    exact (cocone_postcompose_inv colim_A (cocone_precompose (seq_to_succ_seq A) C)).
  - intro C.
    snrapply (equiv_inj (cocone_precompose (seq_to_succ_seq A))).
    + exact (isequiv_cocone_precompose_seq_to_succ_seq (X:=Y)).
    + lhs_V nrapply cocone_precompose_postcompose.
      lhs nrapply (ap (fun x => cocone_postcompose x _)
        cocone_succ_seq_over_col_is_ess_col).
      nrapply (eisretr (cocone_postcompose colim_A)).
  - intro f.
    nrapply (equiv_inj (cocone_postcompose colim_A)).
    + exact (iscolimit_unicocone colim_A Y).
    + lhs nrapply (eisretr (cocone_postcompose colim_A)).
      lhs_V nrapply cocone_precompose_postcompose.
      exact (ap (fun x => cocone_postcompose x f) cocone_succ_seq_over_col_is_ess_col).
  Defined.

  (** Alias for the above definition. *)

  Definition colim_succ := iscolimit_succ_seq_A_over_A_w.

  (** We take the colimit of [seq_to_succ_seq] and obtain a map [A_w -> A_w] *)

  Definition abstr_colim_seq_to_abstr_colim_succ_seq
    : A_w -> A_w 
    := functor_colimit (seq_to_succ_seq A) colim_A colim_succ.

  Definition abstr_colim_seq_to_abstr_colim_succ_seq_is_idmap
    : abstr_colim_seq_to_abstr_colim_succ_seq = idmap.
  Proof.
    unfold abstr_colim_seq_to_abstr_colim_succ_seq, functor_colimit.
    lhs nrapply (ap (fun x => cocone_postcompose_inv colim_A x)
      cocone_succ_seq_over_col_is_ess_col).
    nrapply (equiv_inj (cocone_postcompose colim_A)).
    - nrapply (iscolimit_unicocone colim_A).
    - lhs nrapply (eisretr (cocone_postcompose colim_A)).
      exact (cocone_postcompose_identity colim_A)^.
  Defined.

  (** The cocone [cocone_succ_seq_over_col] induces a map [A_w -> A_w] *)

  Definition abstr_colim_succ_seq_to_abstr_colim_seq
    : A_w -> A_w 
    := (cocone_postcompose_inv colim_succ cocone_succ_seq_over_col).

  Definition abstr_colim_succ_seq_to_abstr_colim_seq_is_idmap
    : abstr_colim_succ_seq_to_abstr_colim_seq = idmap.
  Proof.
    unfold abstr_colim_succ_seq_to_abstr_colim_seq.
    nrapply (equiv_inj (cocone_postcompose colim_A)).
    - nrapply (iscolimit_unicocone colim_A).
    - lhs nrapply (eisretr (cocone_postcompose colim_A)).
      lhs nrapply (cocone_succ_seq_over_col_is_ess_col).
      exact (cocone_postcompose_identity colim_A)^.
  Defined.

  (** The maps defined above are equivalences *)

  Definition sec_abstr_colim_seq_to_abstr_succ_seq
    : abstr_colim_succ_seq_to_abstr_colim_seq
    o abstr_colim_seq_to_abstr_colim_succ_seq
      = idmap.
  Proof.
    lhs nrapply (ap _ abstr_colim_seq_to_abstr_colim_succ_seq_is_idmap).
    exact abstr_colim_succ_seq_to_abstr_colim_seq_is_idmap.
  Defined.

  Definition ret_abstr_colim_seq_to_abstr_succ_seq
    : abstr_colim_seq_to_abstr_colim_succ_seq 
    o abstr_colim_succ_seq_to_abstr_colim_seq
      = idmap.
  Proof.
    lhs nrapply (ap _ abstr_colim_seq_to_abstr_colim_succ_seq_is_idmap).
    exact abstr_colim_succ_seq_to_abstr_colim_seq_is_idmap.
  Defined.

  (** [abstr_colim_seq_to_abstr_colim_succ_seq] is an equivalence *)
    
  Definition equiv_abstr_colim_seq_to_abstr_colim_succ_seq
    : IsEquiv abstr_colim_seq_to_abstr_colim_succ_seq.
  Proof.
    snrapply isequiv_adjointify.
    - exact abstr_colim_succ_seq_to_abstr_colim_seq.
    - exact (apD10 ret_abstr_colim_seq_to_abstr_succ_seq).
    - exact (apD10 sec_abstr_colim_seq_to_abstr_succ_seq).
  Defined.

End Is_Equiv_colim_succ_seq_to_seq_map.

(** Intersplitting is a pun of interleaving and splitting. We will at first only assume that every other triangle is commutative. In this case, colim A is a retract of colim B. *)

Section Intersplitting.
  Context `{Funext} {A B : Sequence} 
    {A_w : Type} (colim_A : IsColimit A A_w)
    {B_w : Type} (colim_B : IsColimit B B_w)
    (d : DiagramMap A B) 
    (u : DiagramMap B (succ_seq A))
    (comm_triangle : seq_to_succ_seq A = diagram_comp u d).
    
  (** Given the data above, we show that the associated diagram in the
      colimit is also commutative. *)

  (**
  <<
                  id
        col A_i -----> col A_i+1
            \           ^
             \         /
              \       /
               v     /
              col B_i
  >>
  *)

  (** It follows that d is split-epi, and u is split-mono, as desired. *)

  Definition colimit_comm_triangle : 
    abstr_colim_seq_to_abstr_colim_succ_seq colim_A
      = (functor_colimit u _ (colim_succ colim_A)) o (functor_colimit d _ _).
  Proof.
    rhs nrapply functor_colimit_compose.
    exact (ap (fun x => functor_colimit x colim_A (colim_succ colim_A)) 
      comm_triangle).
  Defined.

  Definition colim_d_split_epi : 
    idmap = (functor_colimit u _ (colim_succ colim_A)) o (functor_colimit d _ _)
    := ((abstr_colim_seq_to_abstr_colim_succ_seq_is_idmap colim_A)^ @ colimit_comm_triangle).

  Definition isequiv_colim_composite
    : IsEquiv ((functor_colimit u colim_B (colim_succ colim_A)) 
      o (functor_colimit d colim_A colim_B)).
  Proof.
    apply (@isequiv_homotopic A_w _
      (abstr_colim_seq_to_abstr_colim_succ_seq colim_A)
      ((functor_colimit u _ _) o (functor_colimit d _ _))
      (equiv_abstr_colim_seq_to_abstr_colim_succ_seq colim_A)).
    apply apD10.
    exact colimit_comm_triangle.
  Defined.

End Intersplitting.

(** Given families of maps `f n : A n -> B n` and `g : B n -> A (n + 1)` with homotopies showing that they form zigzags, construct the actual diagram maps and show that their composition is equal to the successor diagram map. *)

Section Interme.
  Context `{Funext} {A B : Sequence}
    (f : forall (n : nat), A n -> B n)
    (g : forall (n : nat), B n -> A (S n))
    (U : forall (n : nat), (fun (x : A n) => x^+) == (g n) o (f n))
    (L : forall (n : nat), (fun (x : B n) => x^+) == (f (S n)) o (g n)).

  (** The map built from `f`. Note that [zigzag_glue_map_tri] depends heavily on the exact homotopy used here. *)
  Definition zigzag_glue_map : DiagramMap A B.
  Proof.
    snrapply Build_DiagramMap.
    - exact f.
    - intros n m [] x.
      lhs apply (L n).
      apply ap.
      exact (U n x)^.
  Defined.

  (** The map built from `g`. *)
  Definition zigzag_glue_map_inv : DiagramMap B (succ_seq A).
  Proof.
    snrapply Build_DiagramMap.
    - exact g.
    - intros n m [] x.
      lhs apply (U (S n)).
      apply ap.
      exact (L n x)^.
  Defined.

  Local Open Scope path_scope.

  (** Show that the composition of the two maps is the successor map. *)
  Definition zigzag_glue_map_tri : (diagram_comp zigzag_glue_map_inv zigzag_glue_map) = seq_to_succ_seq A.
  Proof.
    snrapply path_DiagramMap.
    - intros n x.
      simpl.
      exact (U n x)^.
    - (* Conduct "a little path algebra" *) 
      intros n m [] x.
      simpl.
      unfold CommutativeSquares.comm_square_comp.
      (* We need to show, stripping brackets:
      1)   U n.+1 (g n (f n x))
      2) @ ap (g n.+1) (L n (f n x))^) 
      3) @ ap (g n.+1) (L n (f n x) @ ap (f n.+1) (U n x)^)
      4) @ (U n.+1 x ^+)^ 
          = 
      5)  ap (fun a : A n.+1%nat => a ^+) (U n x)^ 
      6) @ 1
       *)
      (* Bring the concatenation out of `ap` in 3) *)
      lhs nrapply (1 @@ ap_pp (g n.+1) (L n (f n x)) (ap (f n.+1) (U n x)^) @@ 1).
      (* Bring the inverse out of `ap` in 2) *)
      lhs nrapply (1 @@ ap_V (g n.+1) (L n (f n x)) @@ 1 @@ 1).
      (* Remove reflexivity 6) *)
      rhs apply (concat_p1 (ap (fun a => a ^+) (U n x)^)).
      (* Change associativity of 1 2 3 *)
      lhs nrapply (concat_pp_p (U n.+1 _) ((ap (g n.+1) _)^) _ @@ 1).
      (* Change associativity of 2 3 3.5 *)
      lhs nrapply (1 @@ concat_p_pp ((ap _ _)^) (ap _ _) _ @@ 1).
      (* 2 and 3 are inverse *)
      lhs nrapply (1 @@ (concat_Vp (ap (g n.+1) (L n (f n x))) @@ 1) @@ 1).
      (* Remove the reflexivity *)
      lhs nrapply (1 @@ concat_1p _ @@ 1).
      (* Add (U n.+1 x ^* ) on the right to both sides *)
      apply (cancelR _ _ ((U n.+1 x ^+))).
      (* Change associativity on the left... *)
      lhs nrapply (concat_pp_p _ _ _).
      (* ...and cancel 4 with the newly-added path *)
      lhs nrapply (1 @@ concat_Vp _).
      (* Remove the residual 1 *)
      lhs nrapply (concat_p1 _).
      (* `ap` of `ap` is `ap` of composition of functions *)
      lhs nrapply (1 @@ ap_compose (f n.+1) (g n.+1) _)^.
      (* Finish by naturality of `ap` *)
      exact (concat_Ap _ _)^.
  Defined.
End Interme.

(** Assuming that there are [A, B : Sequence] that fits in an interleaving diagram,
    their colimits are isomorphic. We proceed by using the 2-out-of-6 property.  *)

Section Interleaving.
  Context `{Funext} {A B : Sequence} 
    {A_w : Type} (colim_A : IsColimit A A_w)
    {B_w : Type} (colim_B : IsColimit B B_w)
    (f : forall (n : nat), A n -> B n)
    (g : forall (n : nat), B n -> A (S n))
    (U : forall (n : nat), (fun (x : A n) => x^+) == (g n) o (f n))
    (L : forall (n : nat), (fun (x : B n) => x^+) == (f (S n)) o (g n)).

  Let d := zigzag_glue_map f g U L.

  Let u := zigzag_glue_map_inv f g U L.
  
  (* We need two equalities: [seq_to_succ_seq A = d o u] and 
  [seq_to_succ_seq B = (succ_seq_map_seq_map d) o u. *)

  (* The first equality needed is exactly what we came up with in the previous section. *)
  Let tri1 : seq_to_succ_seq A = diagram_comp u d
   := (zigzag_glue_map_tri f g U L)^.

  (* The second one requires some massaging: applying [zigzag_glue_map_tr] to the shifted 
  functions doesn't exactly give us `(succ_seq_map_seq_map d)`, but we can find an equality
  between them. *)
  (* TODO: This probably shouldn't be necessary. *)
  Let tri2 : seq_to_succ_seq B = diagram_comp (succ_seq_map_seq_map d) u.
  Proof.
    symmetry.
    pose (f':=g);
    pose (g':=(fun n => f (S n)));
    pose (U':=L);
    pose (L':=(fun n => U (S n)));
    (* Coq can't guess `succ_seq A` here *)
    pose (attempt:=(@zigzag_glue_map_tri _ B (succ_seq A) f' g' U' L')).
    assert (eq : (succ_seq_map_seq_map d) = (@zigzag_glue_map_inv B (succ_seq A) f' g' U' L')).
    - snrapply path_DiagramMap.
      + reflexivity.
      + intros n m y x; destruct y. 
        simpl.
        rhs nrapply (concat_1p _).
        nrapply (concat_p1 _).
    - exact (transport (fun x => diagram_comp x u = seq_to_succ_seq B) eq^ attempt).
  Defined.

  Definition isequiv_interleaved_colim_maps
    : IsEquiv (functor_colimit d _ _).
  Proof.
    nrapply two_out_of_sixR.
    - exact (isequiv_colim_composite colim_A colim_B d u tri1).
    - exact (isequiv_colim_composite colim_B (colim_succ colim_A) u 
      (succ_seq_map_seq_map d) tri2).
  Defined.

  Definition equiv_interleaved_colim : A_w <~> B_w.
  Proof.
    snrapply Build_Equiv.
    - exact (functor_colimit d colim_A colim_B).
    - exact isequiv_interleaved_colim_maps.
  Defined.
End Interleaving.
