Require Export Coq.Strings.String.
Require Export Computation.Core ADTRefinement.
Require Export Bedrock.Platform.Facade.DFacade Bedrock.Platform.Cito.StringMap.

(* Don't print (elt:=...) everywhere *)
Unset Printing Implicit Defensive.

(****************)
(** Telescopes **)
(****************)

Class FacadeWrapper (WrappingType WrappedType: Type) :=
  { wrap:        WrappedType -> WrappingType;
    wrap_inj: forall v v', wrap v = wrap v' -> v = v' }.

Inductive NameTag av T :=
| NTNone : NameTag av T
| NTSome (key: string) (H: FacadeWrapper (Value av) T) : NameTag av T.

Arguments NTNone {av T}.
Arguments NTSome {av T} key {H}.

Definition NameTagAsStringOption {av T} (nt: NameTag av T) :=
  match nt with
  | NTNone => None
  | NTSome key H => Some key
  end.

Inductive Telescope av : Type :=
| Nil : Telescope av
| Cons : forall T (key: NameTag av T)
           (val: Comp T)
           (tail: T -> Telescope av),
    Telescope av.

Arguments Nil {av}.
Arguments Cons {av T} key val tail.

(*************************)
(** Telescope notations **)
(*************************)

Notation "[[  k ~~> v 'as' kk  ]]  ::  t" :=
  (Cons k v (fun kk => t)) (at level 21, right associativity, arguments at next level) : telescope_scope.

Global Open Scope telescope_scope.

Notation "[[  ` k ~~> v 'as' kk  ]]  ::  t" :=
  ([[ NTSome k ~~> v as kk]] :: t) (at level 21, right associativity, arguments at next level) : telescope_scope.

Notation "[[  k ->> v 'as' kk  ]]  ::  t" :=
  ([[ k ~~> (ret v) as kk ]] :: t) (at level 21, right associativity, arguments at next level) : telescope_scope.

Notation "[[  ` k ->> v 'as' kk  ]]  ::  t" :=
  ([[ NTSome k ->> v as kk ]] :: t) (at level 21, right associativity, arguments at next level) : telescope_scope.

Notation "[[  v 'as' kk  ]]  ::  t" :=
  ([[ NTNone ~~> v as kk ]] :: t) (at level 21, right associativity, arguments at next level) : telescope_scope.

(**********************************************)
(** SameValues: matching FMaps to Telescopes **)
(**********************************************)

Definition SameADTs {av} m1 m2 :=
  (forall k v, StringMap.MapsTo k (@ADT av v) m1 <-> StringMap.MapsTo k (@ADT av v) m2).

Definition SameSCAs {av} m1 m2 :=
  (forall k v, StringMap.MapsTo k (@SCA av v) m1 -> StringMap.MapsTo k (@SCA av v) m2).

Definition WeakEq {av} m1 m2 :=
  @SameADTs av m1 m2 /\ @SameSCAs av m1 m2.

Fixpoint SameValues {av} ext fmap (tenv: Telescope av) :=
  match tenv with
  | Nil => WeakEq ext fmap
  | Cons T key val tail =>
    match key with
      | NTSome k H => match StringMap.find k fmap with
                  | Some v => exists v', val ↝ v' /\ v = wrap v' /\ SameValues ext (StringMap.remove k fmap) (tail v')
                  | None => False
                  end
      | NTNone => exists v', val ↝ v' /\ SameValues ext fmap (tail v')
    end
  end.

Notation "ENV ≲ TENV ∪ EXT" := (SameValues EXT ENV TENV) (at level 50).

(******************************************)
(** Facade states in terms of telescopes **)
(******************************************)

Definition ProgOk {av} ext env prog (initial_tstate final_tstate: Telescope av) :=
  forall initial_state: State av,
    (initial_state ≲ initial_tstate ∪ ext) ->
    Safe env prog initial_state /\
    forall final_state: State av,
      @RunsTo _ env prog initial_state final_state ->
      (final_state ≲ final_tstate ∪ ext).

Notation "{{ A }} P {{ B }} ∪ {{ ext }} // EV" :=
  (ProgOk ext EV P A B)
    (at level 60, format "'[v' '{{'  A  '}}' '/'    P '/' '{{'  B  '}}'  ∪  '{{'  ext  '}}'  //  EV ']'").
