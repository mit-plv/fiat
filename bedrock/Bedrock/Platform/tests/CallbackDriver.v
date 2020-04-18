Require Import Bedrock.Bedrock Bedrock.Platform.Xml Bedrock.Platform.XmlProg.

Module M.
  Definition buf_size := 1024%N.
  Definition outbuf_size := 1024%N.
  Definition heapSize := (1024 * 1024)%N.

  Definition ts : tables := nil.

  Definition pr := Match
    "rpc"/(
      "url"/$"url"
      & "text"/$"text"
    )
  Do
    Send $"url" Value $"text";;
    Write <*> "ok" </>
      "yup"
    </>
  end%program.

  Theorem Wf : wf ts pr buf_size outbuf_size.
    wf.
  Qed.

  Definition port : W := 8080%N.
  Definition numWorkers : W := 10.
End M.

Module E := Make(M).
