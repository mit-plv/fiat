Require Import Bedrock.Platform.tests.Ros Bedrock.Platform.XmlProg.

Module M.
  Definition buf_size := 1024%N.
  Definition outbuf_size := 1024%N.
  Definition heapSize := (1024 * 1024)%N.

  Definition dbaddr (n : nat) := ((heapSize + 50 + 2 + N.of_nat n) * 4)%N.

  Definition ts :=
    {| Name := "params";
      Address := dbaddr 0;
      Schema := "key" :: "value" :: nil
    |}

    :: nil.

  Definition pr := SimpleROS (
    (* Set the value of a parameter. *)
    RosCommand "setParam"(!string $"caller_id", !string $"key", !any $$"value")
    Do
      Delete "params" Where ("key" = $"key");;
      Insert "params" ($"key", $"value");;

      Response Success
        Message "Parameter set."
        Body ignore
      end
    end;;

    (* Get the value of a parameter. *)
    RosCommand "getParam"(!string $"caller_id", !string $"key")
    Do
      IfHas "params" Where ("key" = $"key") then
        Response Success
          Message "Parameter value is:"
          Body
            From "params" Where ("key" = $"key") Write
              "params"#"value"
        end
      else
        Response UserError
          Message "Parameter not found."
          Body ignore
        end
      end
    end;;

    (* List all parameters that are set. *)
    RosCommand "getParamNames"(!string $"caller_id")
    Do
      Response Success
        Message "Parameter names are:"
        Body
          ArrayFrom "params" Write
            !string "params"#"key"
      end
    end
  ).

  Theorem Wf : wf ts pr buf_size outbuf_size.
    wf.
  Qed.

  Definition port : W := 11311%N.
  Definition numWorkers : W := 10.
End M.

Module E := Make(M).
