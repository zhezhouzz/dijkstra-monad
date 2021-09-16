Require Import List.
Require Import Coq.micromega.Lia.
Require Import Arith.
(* Require Import Logic. *)
Import ListNotations.

Definition Pre {State: Type}: Type := State -> Type.

Definition Post {State: Type} (A: Type): Type := (A * State) -> Type.

Definition WpSt {State: Type} (A: Type): Type := @Post State A -> @Pre State.

Definition return_wp_st {State: Type} (A: Type) (x: A): WpSt A :=
  fun (post: Post A) (s0: State) => post (x, s0).

Definition bind_wp_st {State: Type} (A: Type) (B: Type) (wp: WpSt A) (f: A -> WpSt B): WpSt B :=
  fun (post: Post B) (s0: State) =>
    wp (fun tmp =>
          let (x, s1) := tmp in
          f x post s1) s0.

(* Ref Example *)

Definition Addr := nat.

Definition Heap := list (Addr * nat).

Fixpoint update (h: Heap) (l: Addr) (x: nat) :=
  match h with
  | [] => [(l, x)]
  | (l', x') :: t => if beq_nat l l' then (l', x) :: t else (l', x') :: (update t l x)
  end.

Fixpoint select (h: Heap) (l: Addr) :=
  match h with
  | [] => 0
  | (l', x') :: t => if beq_nat l l' then x' else (select t l)
  end.

Fixpoint l_in_h (h: Heap) (l: Addr) :=
   match h with
  | [] => False
  | (l', _) :: t => if beq_nat l l' then True else l_in_h t l
  end.

Definition ref_f: (nat -> @WpSt Heap Addr) :=
  fun x: nat =>
    fun post: (Post Addr) =>
      fun h: Heap => forall l: Addr, (l_in_h h l = False) -> (post (l, update h l x)).

Definition deref_f: (Addr -> @WpSt Heap nat) :=
  fun l: Addr =>
    fun post: (Post nat) =>
      fun h: Heap => post (select h l, h).

Definition refupdate_f: ((Addr * nat) -> @WpSt Heap unit) :=
  fun tmp: (Addr * nat) =>
    let (l, x) := tmp in
    fun post: (Post unit) =>
      fun h: Heap => post (tt, update h l x).

(* Use monadic composition to build program *)

(* let swap x y := *)
(*     let x_value := !x in *)
(*     let y_value := !y in *)
(*     let _ = x := y_value in *)
(*     y := x_value *)

Definition swap_f (x: Addr) (y: Addr) : @WpSt Heap unit :=
  bind_wp_st Addr unit
    (deref_f x)
    (fun x_value: nat =>
       bind_wp_st Addr unit
         (deref_f y)
         (fun y_value: nat =>
            bind_wp_st unit unit
            (refupdate_f (x, y_value))
            (fun _ =>
               refupdate_f (y, x_value)
            )
         )
    ).

Definition post: @Post Heap unit :=
  fun tmp =>
    let (_, h) := tmp in
    (select h 0) = 3 /\ (select h 1) = 5.

Lemma lemma_example: ((swap_f 0 1) post) ([(0, 5); (1, 3)]).
Proof.
  unfold swap_f.
  unfold bind_wp_st at 1.
  unfold deref_f at 1.
  unfold bind_wp_st at 1.
  unfold deref_f at 1.
  unfold bind_wp_st at 1.
  unfold refupdate_f at 1.
  unfold refupdate_f at 1.
  simpl.
  lia.
Qed.

Lemma lemma_total: forall x y: Addr, forall h: Heap, forall post: @Post Heap unit, ((swap_f x y) post) h.
Proof.
  unfold swap_f.
  unfold bind_wp_st at 1.
  unfold deref_f at 1.
  unfold bind_wp_st at 1.
  unfold deref_f at 1.
  unfold bind_wp_st at 1.
  unfold refupdate_f at 1.
  unfold refupdate_f at 1.
Admitted.

Inductive DST {State: Type} (A: Type): (@WpSt State A) -> Type :=
| dst_return: forall a: A, DST A (return_wp_st A a)
| dst_bind: forall B: Type, forall wpb: WpSt B, forall f: B -> WpSt A,
        DST B wpb -> (forall b: B, DST A (f b)) -> DST A (bind_wp_st B A wpb f).

Lemma dst_ref: forall x: nat, DST Addr (ref_f x).
Admitted.
Lemma dst_deref: forall l: Addr, DST nat (deref_f l).
Admitted.
Lemma dst_refupdate: forall l: Addr, forall x: nat, DST unit (refupdate_f (l, x)).
Admitted.

Lemma lemma_swap_f : forall x y: Addr, DST unit (swap_f x y).
Proof.
  intros.
  apply dst_bind. apply dst_deref.
  intro x_value.
  apply dst_bind. apply dst_deref.
  intro y_value.
  apply dst_bind. apply dst_refupdate.
  intros useless. clear useless.
  apply dst_refupdate.
Qed.

