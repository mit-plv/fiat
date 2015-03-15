Require Import Ics.


Parameter tankMax : Z.
(** How high (m) may the water rise safely? *)

Parameter fillRate : Z.
(** Rate (m/s) at which tank fills on request *)

Parameter emptyRate : Z.
(** Rate (m/s) at which tank empties on request *)

Inductive action := Nothing | Fill | Empty.
(** What the controller may do in each timestep (lasting 1 s) *)


(** * A water tank with a single sensor *)
Module OneSensor.
  Parameter sensorAccuracy : Z.
  (** Our one sensor must be at least this close to the true water value. *)

  Axiom sensorAccuracy_positive : 0 <= sensorAccuracy.
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
        trueLevel' <- {x | True};
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
                  else trueLevel' <- {_ : Z | True};
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
End OneSensor.
