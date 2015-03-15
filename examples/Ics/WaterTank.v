Require Import Ics.


Parameter tankMax : Z.
(** How high (m) may the water rise safely? *)

Parameter fillRate : Z.
(** Rate (m/s) at which tank fills on request *)

Parameter emptyRate : Z.
(** Rate (m/s) at which tank empties on request *)

Inductive action := Nothing | Fill | Empty.
(** What the controller may do in each timestamp (lasting 1 s) *)


(** * A water tank with a single sensor *)
Module OneSensor.
  Parameter sensorAccuracy : Z.
  (** Our one sensor must be at least this close to the true water value. *)

  (** Type signature of an implementation *)
  Definition sig : ADTSig :=
    ADTsignature {
      Constructor "new" : Z -> rep,
      (** Initialize, with starting sensor value. *)

      Method "update" : rep x Z -> rep x unit,
      (** Record new sensor reading. *)

      Method "timestep" : rep x Z -> rep x action
      (** Decide what to do over the next second. *)
    }.

  (** In this spec, the rep state is the current sensor value. *)
  Definition spec := ADTRep Z {
    Def Constructor "new"(reading : Z) : rep :=
      ret reading,
    Def Method "update"(r : rep, sensor : Z) : unit :=
      ret (sensor, tt),
    Def Method "timestep"(sensor : rep, targetLevel : Z) : action :=
      (* Choose an action that is safe for any possible sensor value. *)
      act <- {act | act = Fill ->
                    forall level, Zabs (sensor - level) < sensorAccuracy
                                  -> level + fillRate < tankMax };
      ret (sensor, act)
  }.

  (** Here's one conservative strategy for picking an action. *)
  Lemma conservativeFill : forall (sensor targetLevel : Z),
    refine {act | act = Fill ->
                  forall level, Zabs (sensor - level) < sensorAccuracy
                                -> level + fillRate < tankMax }
           (if targetLevel <? sensor then
              ret Empty
            else if (targetLevel >? sensor) && (sensor + sensorAccuracy + fillRate <? tankMax) then
              ret Fill
            else
              ret Nothing).
  Proof.
    implement.
  Qed.

  (** Now we derive the overall implementation. *)
  Definition impl : Sharpened spec.
  Proof.
    unfold spec.

    hone method "timestep". {
      rewrite conservativeFill with (targetLevel := n).
      simplify.
      finish honing.
    }

    finished.
  Defined.

  Definition impl' : cADT sig.
  Proof.
    extract impl.
  Defined.

  Print impl'.
End OneSensor.


(** * A water tank with multiple sensors, some of which may be spoofed at any moment *)
(* (This part is an a preliminary state, after I switched to working on the simpler example above first.) *)
Module MultiSensor.
  (** * Some helper definitions to use in the spec *)

  (** How many of the [readings] are no more than [epsilon] off from the [trueValue]? *)
  Definition withinEpsilon (epsilon trueValue : Z) (readings : list Z) : nat :=
    length (filter (fun reading => Zabs (trueValue - reading) <? epsilon) readings).

  (** Replace one saved reading with a new value. *)
  Definition replaceReading (readings : list Z) (id : nat) (value : Z) : list Z :=
    firstn id readings ++ value :: skipn (S id) readings.

  (** * Specification *)

  Definition spec := ADTRep (list Z) {
    Def Constructor "new"(readings : list Z) : rep :=
      ret readings,
    Def Method "update"(r : rep, arg : nat * Z) : unit :=
      let r' := replaceReading r (fst arg) (snd arg) in
      ret (r', tt)
    }.
End MultiSensor.
