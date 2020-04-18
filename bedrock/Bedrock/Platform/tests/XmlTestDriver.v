Require Import Bedrock.Bedrock Bedrock.Platform.Xml Bedrock.Platform.XmlProg.

Module M.
  Definition buf_size := 1024%N.
  Definition outbuf_size := 2%N.
  Definition heapSize := (1024 * 1024 * 25)%N.

  Definition ts := {| Name := "rpcs";
    Address := ((heapSize + 50 + 2) * 4)%N;
    Schema := "cmd" :: "a" :: "b" :: nil
  |} :: nil.

  Definition pr := Match
    "rpc"/(
      "cmd"/"frob"
      & "mode"/$"mode"
      & "args"/(
        "string"/$"a";;
        "string"/$"b"
        )
    )
  Do
    Write <*> "answer" </>
      <*> "mode" </> $"mode" </>,
      <*> "a" </> $"a" </>,
      <*> "b" </> $"b" </>
    </>;;
    Insert "rpcs" ("frob", $"a", $"b");;
    Write <*> "extra" </>
      <*> "boring" </> "constant" </>,
      <*> "B" </> $"b" </>
    </>
  end%program.

  Theorem Wf : wf ts pr buf_size outbuf_size.
    wf.
  Qed.

  Definition port : W := 8080%N.
  Definition numWorkers : W := 10.
End M.

Module E := Make(M).
