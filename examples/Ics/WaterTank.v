Require Import Ics.


Inductive action := Nothing | Fill | Empty.
(** What the controller may do in each timestep (lasting 1 s) *)

(** * As a warmup, consider a controller in a very friendly world where physics is entirely predictable.
    * Whenever the controller asks for filling or emptying, it is easy to predict precisely
    * how much will happen in 1 second. *)

Module Type DETERMINISTIC.
  Parameter tankMax : Z.
  (** How high (m) may the water rise safely? *)

  Parameter sensorAccuracy : Z.
  (** Our one sensor must be at least this close to the true water value. *)

  Axiom sensorAccuracy_positive : 0 <= sensorAccuracy.

  Parameter fillRate : Z.
  (** Rate (m/s) at which tank fills on request *)

  Parameter emptyRate : Z.
  (** Rate (m/s) at which tank empties on request *)
End DETERMINISTIC.

Module Deterministic(Import M : DETERMINISTIC).
  Local Hint Extern 1 (0 <= sensorAccuracy) => apply sensorAccuracy_positive.

  (** Type signature of an implementation *)
  Definition sig : ADTSig :=
    ADTsignature {
      Constructor "new" : Z -> rep,
      (** Initialize, with starting water level (trusted to be accurate). *)

      Method "update" : rep x Z -> rep x unit,
      (** Record new sensor reading. *)

      Method "timestep" : rep x Z -> rep x action
      (** Decide what to do over the next second. *)
    }.

  (** Now the spec, which builds in the plant model, namely the true water level. *)
  Definition spec := ADTRep Z {
    Def Constructor "new"(trueLevel : Z) : rep :=
      ret trueLevel,
    Def Method "update"(trueLevel : rep, sensor : Z) : unit :=
      if Zabs (sensor - trueLevel) <? sensorAccuracy then
        ret (trueLevel, tt)
      else
        (* The sensor broke the rules!  Change the state arbitrarily to make anything safe. *)
        trueLevel' <- {_ | True};
        ret (trueLevel', tt),
    Def Method "timestep"(trueLevel : rep, targetLevel : Z) : action :=
      act <- {act | match act with
                    | Nothing => True
                    | Fill => trueLevel + fillRate < tankMax
                    | Empty => trueLevel - emptyRate >= 0
                    end};
      ret (match act with
           | Nothing => trueLevel
           | Fill => trueLevel + fillRate
           | Empty => trueLevel - emptyRate
           end, act)
  }.

  (** A basic fact about approximation: it's always OK to give the exact answer! *)
  Lemma easy_approx : forall (d : Z),
    refine {nr' : Z | Zabs (nr' - d) <= sensorAccuracy} (ret d).
  Proof.
    implement.
  Qed.

  (** Any new sensor value is a proper approximation of the water level. *)
  Lemma newSensorOk : forall sensor trueLevel,
    refine (p <- (if Z.abs (sensor - trueLevel) <? sensorAccuracy
                  then ret (trueLevel, ())
                  else trueLevel' <- {_ | True};
                       ret (trueLevel', ()));
            sensor' <- {nr' : Z | Z.abs (nr' - fst p) <= sensorAccuracy};
            ret (sensor', snd p))
           (ret (sensor, ())).
  Proof.
    implement;
    try match goal with
        | [ H : _ = ?sensor - ?E |- _ ] =>
          unify E sensor; generalize sensorAccuracy_positive
        end; implement.
  Qed.

  (** Justify the obvious choice of actions. *)
  Lemma chooseAction : forall trueLevel sensor targetLevel,
    Z.abs (sensor - trueLevel) <= sensorAccuracy
    -> refine (p <- (act <- {act : action |
                             match act with
                             | Nothing => True
                             | Fill => trueLevel + fillRate < tankMax
                             | Empty => trueLevel - emptyRate >= 0
                             end};
                     ret
                       (match act with
                        | Nothing => trueLevel
                        | Fill => trueLevel + fillRate
                        | Empty => trueLevel - emptyRate
                        end, act));
               sensor' <- {n : Z | Z.abs (n - fst p) <= sensorAccuracy};
               ret (sensor', snd p))
              (if (sensor <? targetLevel) && (sensor + sensorAccuracy + fillRate <? tankMax) then
                 ret (sensor + fillRate, Fill)
               else if (sensor >? targetLevel) && (sensor - sensorAccuracy - emptyRate >=? 0) then
                 ret (sensor - emptyRate, Empty)
               else
                 ret (sensor, Nothing)).
  Proof.
    implement.
  Qed.

  (** Now we derive the overall implementation. *)
  Definition impl : Sharpened spec.
  Proof.
    unfold spec.

    (** The main idea of the implementation is to store the sensor value as an approximation of water level.
      * Here we give an abstraction relation capturing that idea. *)
    hone representation using (fun abs conc => Zabs (conc - abs) <= sensorAccuracy).

    (** Now we fill in method implementations, one at a time. *)

    hone constructor "new". {
      simplify.
      rewrite easy_approx.
      finish honing.
    }

    hone method "update". {
      rewrite newSensorOk.
      finish honing.
    }

    hone method "timestep". {
      rewrite chooseAction with (targetLevel := n) by eauto.
      finish honing.
    }

    (** Inspecting the code, we see that it looks good.  Time to end the derivation. *)
    finished.
  Defined.

  (** As a last check, we extract an executable Coq program from the derivation and print it. *)

  Definition impl' : cADT sig.
  Proof.
    extract impl.
  Defined.

  Print impl'.
End Deterministic.


(** * Now let's move to a more realistic world, where we only have bounds on filling/emptying speeds. *)

Module Type NONDETERMINISTIC.
  Parameter tankMax : Z.
  (** How high (m) may the water rise safely? *)

  Parameter sensorAccuracy : Z.
  (** Our one sensor must be at least this close to the true water value. *)

  Axiom sensorAccuracy_positive : 0 <= sensorAccuracy.

  (** Bounds on how much filling or emptying will happen in 1 second *)
  Parameters minFill maxFill minEmpty maxEmpty : Z.

  Axiom fillBounds : minFill <= maxFill.
  Axiom emptyBounds : minEmpty <= maxEmpty.
End NONDETERMINISTIC.

Module Nondeterministic(Import M : NONDETERMINISTIC).
  Local Hint Extern 1 (0 <= sensorAccuracy) => apply sensorAccuracy_positive.

  (** We use this type as input to the main controller method.
    * Only the [TargetLevel] field would actually be present at runtime;
    * the others are just a specification device, and the final implementation shouldn't inspect them. *)
  Record request := {
    TargetLevel : Z;
    FillRate : Z;
    EmptyRate : Z
  }.

  (** Type signature of an implementation *)
  Definition sig : ADTSig :=
    ADTsignature {
      Constructor "new" : Z -> rep,
      (** Initialize, with starting water level (trusted to be accurate). *)

      Method "update" : rep x Z -> rep x unit,
      (** Record new sensor reading. *)

      Method "timestep" : rep x request -> rep x action
      (** Decide what to do over the next second. *)
    }.

  (** Now the spec, modeling nondeterministic filling/emptying. *)
  Definition spec := ADTRep Z {
    Def Constructor "new"(trueLevel : Z) : rep :=
      ret trueLevel,
    Def Method "update"(trueLevel : rep, sensor : Z) : unit :=
      if Zabs (sensor - trueLevel) <? sensorAccuracy then
        ret (trueLevel, tt)
      else
        (* The sensor broke the rules!  Change the state arbitrarily to make anything safe. *)
        trueLevel' <- {_ | True};
        ret (trueLevel', tt),
    Def Method "timestep"(trueLevel : rep, r : request) : action :=
      act <- {act | match act with
                    | Nothing => True
                    | Fill => trueLevel + maxFill < tankMax
                    | Empty => trueLevel - maxEmpty >= 0
                    end};
      trueLevel' <- {trueLevel' | minFill <= FillRate r <= maxFill
                                  -> minEmpty <= EmptyRate r <= maxEmpty
                                  -> match act with
                                     | Nothing => trueLevel' = trueLevel
                                     | Fill => trueLevel' = trueLevel + FillRate r
                                     | Empty => trueLevel' = trueLevel - EmptyRate r
                                     end};
      ret (trueLevel', act)
  }.

  (** Intervals of possible values, which we'll use to record our knowledge in the implementation *)
  Record interval := Interval {
    Min : Z;
    Max : Z
  }.

  (** A basic fact about interval approximation: it's always OK to give the exact answer! *)
  Lemma easy_approx : forall (d : Z),
    refine {i | Min i <= d <= Max i} (ret (Interval d d)).
  Proof.
    implement.
  Qed.

  (** Any new sensor value is a proper approximation of the water level. *)
  Lemma newSensorOk : forall sensor trueLevel,
    refine (p <- (if Z.abs (sensor - trueLevel) <? sensorAccuracy
                  then ret (trueLevel, ())
                  else trueLevel' <- {_ | True};
                       ret (trueLevel', ()));
            sensor' <- {i | Min i <= fst p <= Max i};
            ret (sensor', snd p))
           (ret (Interval (sensor - sensorAccuracy) (sensor + sensorAccuracy), ())).
  Proof.
    implement; generalize sensorAccuracy_positive; implement.
  Qed.

  (** Justify the obvious choice of actions. *)
  Lemma chooseAction : forall trueLevel sensor r,
    Min sensor <= trueLevel <= Max sensor
    -> refine (p <- (act <- {act : action |
                             match act with
                             | Nothing => True
                             | Fill => trueLevel + maxFill < tankMax
                             | Empty => trueLevel - maxEmpty >= 0
                             end};
                     trueLevel' <- {trueLevel' : Z |
                                    minFill <= FillRate r <= maxFill ->
                                    minEmpty <= EmptyRate r <= maxEmpty ->
                                    match act with
                                    | Nothing => trueLevel' = trueLevel
                                    | Fill => trueLevel' = trueLevel + FillRate r
                                    | Empty => trueLevel' = trueLevel - EmptyRate r
                                    end};
                     ret (trueLevel', act));
               sensor' <- {sensor' : interval | Min sensor' <= fst p <= Max sensor'};
               ret (sensor', snd p))
              (if (Min sensor <? TargetLevel r) && (Max sensor + maxFill <? tankMax) then
                 ret (Interval (Min sensor + minFill) (Max sensor + maxFill), Fill)
               else if (Max sensor >? TargetLevel r) && (Min sensor - maxEmpty >=? 0) then
                 ret (Interval (Min sensor - maxEmpty) (Max sensor - minEmpty), Empty)
               else
                 ret (sensor, Nothing)).
  Proof.
    intros.

    (* Case split on whether the environment is following the rules in choosing water motion rates *)
    assert ((minFill <= FillRate r <= maxFill /\ minEmpty <= EmptyRate r <= maxEmpty)
            \/ ~(minFill <= FillRate r <= maxFill /\ minEmpty <= EmptyRate r <= maxEmpty))
      by (destruct (Z_le_gt_dec minFill (FillRate r)), (Z_le_gt_dec (FillRate r) maxFill),
          (Z_le_gt_dec minEmpty (EmptyRate r)), (Z_le_gt_dec (EmptyRate r) maxEmpty); omega).

    intuition; implement1;
    (simplify with monad laws;
     do 2 intro;
     repeat computes_to_inv; subst; simpl in *;
       solve [ econstructor; split;
               repeat match goal with
                      | [ |- Ensembles.In _ _ _ ] => econstructor; split
                      end; repeat implement; generalize fillBounds, emptyBounds; omega
             | econstructor; split;
               repeat match goal with
                      | [ |- Ensembles.In _ _ _ ] => econstructor; split
                      end;
               try match goal with
                   | [ |- Ensembles.In _ _ {| Min := ?min; Max := _ |} ] => instantiate (1 := min)
                   end;
               repeat implement; generalize fillBounds, emptyBounds; omega ]).
  Qed.

  (** Now we derive the overall implementation. *)
  Definition impl : Sharpened spec.
  Proof.
    unfold spec.

    (** This time around, we represent our sensor estimate with _intervals_. *)
    hone representation using (fun abs conc => Min conc <= abs <= Max conc).

    (** Now we fill in method implementations, one at a time. *)

    hone constructor "new". {
      simplify.
      rewrite easy_approx.
      finish honing.
    }

    hone method "update". {
      rewrite newSensorOk.
      finish honing.
    }

    hone method "timestep". {
      rewrite chooseAction with (r := n) by eauto.
      finish honing.
    }

    (** Inspecting the code, we see that it looks good.  Time to end the derivation. *)
    finished.
  Defined.

  (** As a last check, we extract an executable Coq program from the derivation and print it. *)

  Definition impl' : cADT sig.
  Proof.
    extract impl.
  Defined.

  Print impl'.
End Nondeterministic.
