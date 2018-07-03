Require Import Coq.Logic.FunctionalExtensionality.

Class Monad (m: Type -> Type) : Type :=
  {
    return_ {A}: A -> m A;
    bind {A B}:  m A -> (A -> m B) -> m B;
    right_unit {A}: forall (a: m A), a = bind a (@return_ A);
    left_unit: forall A (a: A) B (f: A -> m B),
        f a = bind (return_ a) f;
    associativity: forall A (ma: m A) B f C (g: B -> m C),
        bind ma (fun x => bind (f x) g) = bind (bind ma f) g
  }.

Notation "a >>= f" := (bind a f) (at level 50, left associativity).

Definition wbind {A B: Type} {m: Type -> Type} {monad: Monad m} (ma: m A) (mb: m B) :=  ma >>= fun _ => mb.

Notation "a >> f" := (wbind a f) (at level 50, left associativity).

Notation "'do' a <- e ; c" := (e >>= (fun a => c)) (at level 60, right associativity).

Section StateMonad.

  Definition State (s a : Type) : Type := s -> a * s.

  Instance stateMonad {s: Type}: Monad (State s).
  Proof.
    refine (Build_Monad (State s) (fun A x s => (x, s)) (fun A B c1 c2 s1 => let (x, s2) := c1 s1 in c2 x s2) _ _ _); intros; extensionality x; auto.
    - destruct (a x); auto.
    - destruct (ma x). auto.
  Defined.

  Definition get {s: Type}: State s s := fun x => (x, x).

  Definition put {s: Type}: s -> State s unit := fun x _ => (tt, x).

End StateMonad.

Global Existing Instance stateMonad.

