Narcissus: Correct-By-Construction Derivation of Decoders and Encoders from Binary Formats
======================================================================

This archive holds the source code of Narcissus, a Coq library for synthesizing
binary encoders and decoders from specifications. A virtual machine is available
for reproducing our results.

## Introduction

This artifact aims to demonstrate that (1) the usability of the Narcissus
framework, and (2) the performance of the generated encoders and decoders for
real world applications is reasonable.

The next section (Getting started) contains instructions on running the virtual
machine, and stepping through the tutorial in our paper, Section 1.1 (A tour of
Narcissus).

Section (Replicating our benchmarks) explains how to reproduce the
benchmarks in our paper, Section 6 (Evaluation).

Section (General instructions) shows how to build and use our library in
general, outside of the virtual machine.

Section (Paper-to-artifact correspondence guide) points the definitions, lemmas,
and rules in the paper to the actual implementation in our code. This helps
users to navigate and understand our codebase.

Section (Build the virtual machine) contains instructions on how to set up our
virtual machine and its environment from scratch.

## Getting started

The provided virtual machine was tested in Oracle Virtual Box (6.0.8). You may
need the login information to run `sudo` command:

- user name: narcissus
- password: ae

After launching a terminal, you can experiment with our tutorial interactively
(also in the paper, Setion 1.1):

```
cd ~/fiat

# use Coq IDE
coqide src/Narcissus/Examples/README.v

# or Emacs + Proof general
emacs src/Narcissus/Examples/README.v
```

Stepping through `README.v` shows the generated encoders and decoders. For
presentation purposes, we may show them in a more succinct and readable form in
the paper. See also section (Paper-to-artifact correspondence guide) for more
details.

You can add `Print Assumptions enc_dec` (or replace `enc_dec` with the
definition in question) to the Coq file and process it, to make sure there is no
unproved hypotheses or undesirable axioms. The only axioms we use is
`functional_extensionality_dep`, a well-known axiom proved to be consistent with
Coq's logic.

## Replicating our benchmarks

One word of caution: performance measurements are well-known to be finicky, and
the reproduced results may not match those in the paper perfectly. The following
factors can affect measurements by introducing noise that blurs the results:

* Power saving (on laptops)
* Dynamic frequency scaling (most commonly on laptops)
* Caching issues

Additionally, results collected inside of a virtual machine tend to be more
noisy.

#### Microbenchmarks

These benchmarks are explained in our paper, Section 6.1 (Benchmarking)

This benchmark outputs a plot similar to the one in Figure 12. The results
should be in the order of a few microseconds per packet.

Running this benchmark could take around 40 minutes to finish.

```
cd ~/fiat/src/Narcissus/Examples/NetworkStack/benchmarks

# could take around 40 minutes
./microbenchmarks.sh

# generate the plot
./plot.py ../microbenchmarks.out

# open the plot file
xdg-open ../microbenchmarks.out.pdf
```

#### Mirage OS integration benchmarks

These benchmarks are explained in our paper, Section 6.2 (Mirage OS
Integration).

To reproduce this experiment, we have to setup a tun/tap interface first.

```
sudo ip link show
# run the follows if tap0 interface is not shown in the ouput

sudo modprobe tun
sudo ip tuntap add mode tap tap0
sudo ip link set tap0 up
sudo ip addr add 10.0.0.1/24 dev tap0
```

Then disconnect the virtual machine from the internet, otherwise remote
resources like external scripts and images will affect load times. In the Ubuntu
system in our virtual machine, you can click the internet icon at the top-right
corner, and turn off the connection there.

To experiment manually:

- Run the mirage-www server with native Mirage's own encoders and decoders
```
cd ~/mirage/mirage-www/src

# use Mirage's own encoders and decoders
echo "" > /tmp/fiat4mirage.config

# This runs the website on http://10.0.0.2:8080/
./main.native
```

Now browse the website at http://10.0.0.2:8080/. Be sure the URL's protocol is
http but not https. (Firefox brower is available in the virtual machine)


- Run the mirage-www server with our encoders and decoders
```
cd ~/mirage/mirage-www/src

# use our encoders and decoders
echo "ipv4-encoding ipv4-decoding arpv4-encoding arpv4-decoding ethif-encoding ethif-decoding udp-encoding udp-decoding tcp-encoding tcp-decoding" > /tmp/fiat4mirage.config

# This runs the website on http://10.0.0.2:8080/
./main.native
```

Now browse the website again at http://10.0.0.2:8080/. Observe that the website
loads correctly, and the browsing speed is reasonable. Compared to the previous
set up (Mirage's own encoders and decoders), the performance difference should
be slim.

To reproduce the plot in our paper, Section 6.2
```
cd ~/mirage/mirage-www/src

./plot_mirage_www.py ../firefox-logs/2018-11-17-02-29-26
```
This plot uses the data we collected from our experiment.

You can also run the full benchmark and generate the plot with the new data.
Running the full benchmarks could take more than an hour. Each configuration is
repeated 200 times by default, but you can reduce this value by changing
`REPEATS_BY_CONFIG` in `benchmark_mirage_www.py`. However, lower values will
lead to lower accuracy.

To run the full benchmarks (A Firefox window will repeatedly flicker on the screen)
```
cd ~/mirage/mirage-www/src

# run the benchmark. It could take more than an hour
./benchmark_mirage_www.py

# generate the plot (replace [date] below by the timestamped folder generated by the benchmarking script)
./plot_mirage_www.py ../firefox-logs/[date]

# open the plot file
xdg-open mirage-www.pdf
```

The overhead shown in the plot should be less than +10% (negative number is
possible).

#### Re-compile Narcissus

The code in the virtual machine is pre-compiled. If you intend to re-compile the
whole project, please be warned that at least 4 Gigabytes of memory is needed to
build it, and it also takes a long time to build. See also Section (Build the
virtual machine).

```
cd ~/fiat

# clean it
make clean

# compile it
make -j4 narcissus
make -j4 src/Narcissus/Examples/NetworkStack/Fiat4Mirage.vo

# update the encoders and decoders
cp Fiat4Mirage.ml ~/mirage/mirage-tcpip/src/fiat4mirage

# recompile tcpip module against the new generated encoders and decoders
opam upgrade --working-dir tcpip

cd ~/mirage/mirage-www/src/

# This requires the tun/tap interface mentioned above
mirage configure -t unix --net=direct --http-port=8080

make

# run the server
./main.native
```

## General instructions

#### Dependencies:
  * To build the library: Coq 8.7.2

#### Building Narcissus:
  * To build the core library: `make narcissus`

#### Examples and case study:
  * A tour of Narcissus can be found in src/Narcissus/Examples/README.v
  * The examples from our mirage case study can be found in src/Narcissus/Examples/NetworkStack
  
## Paper-to-artifact correspondence guide
  * All examples from Section 1.1 (A tour of Narcissus) can be found in src/Narcissus/Examples/README.v
    - We also generate a checking (`AlignedEncode_Nil`) at the end of an encoder
      to make sure the buffer size is big enough, which we omitted in the paper
      for brevity.
    - The `>>>` notation is unfolded and reduced in the generated encoder. We
      still keep `>>>` in the paper to make it more readable.

  * The definitions of format, encoder, and decoder, in Section 2 (Naricssus, Formally):

  | Definition | File                         | Name    |
  |------------|------------------------------|---------|
  | FormatM    | src/Narcissus/Common/Specs.v | FormatM |
  | EncodeM    | src/Narcissus/Common/Specs.v | EncodeM |
  | DecodeM    | src/Narcissus/Common/Specs.v | DecodeM |
  
  * The formats for base types, in Figure 1 (Formats for base types included in Narcissus):

  | Base Type              | File                                 | Name of format               |
  |------------------------|--------------------------------------|------------------------------|
  | Booleans               | src/Narcissus/Formats/Bool.v         | format_bool                  |
  | Peano Numbers          | src/Narcissus/Formats/NatOpt.v       | format_nat                   |
  | Variable-Length List   | src/Narcissus/Formats/FixListOpt.v   | format_list                  |
  | Variable-Length String | src/Narcissus/Formats/StringOpt.v    | format_string_with_term_char |
  | Option Type            | src/Narcissus/Formats/Option.v       | format_option                |
  | Enumerated Types       | src/Narcissus/Formats/EnumOpt.v      | format_enum                  |
  | Fixed-Length Words     | src/Narcissus/Formats/WordOpt.v      | format_word                  |
  | Unspecified BitString  | src/Narcissus/Formats/ByteBuffer.v   | format_bytebuffer            |
  | Fixed-Length List      | src/Narcissus/Formats/Vector.v       | format_Vector                |
  | Fixed-Length String    | src/Narcissus/Formats/FixStringOpt.v | format_string                |
  | Ascii Character        | src/Narcissus/Formats/AsciiOpt.v     | format_ascii                 |
  | Variant Types          | src/Narcissus/Formats/SumTypeOpt.v   | format_SumType               |

  * The format combinators, in Section 2 (Naricssus, Formally):

  | Format combinator | File                                        | Name of format    |
  |-------------------|---------------------------------------------|-------------------|
  | ++                | src/Narcissus/Formats/Base/SequenceFormat.v | sequence_Format   |
  | ⊚                 | src/Narcissus/Formats/Base/FMapFormat.v     | Compose_Format    |
  | ◦                 | src/Narcissus/Formats/Base/FMapFormat.v     | Restrict_Format   |
  | ∩                 | src/Narcissus/Formats/Base/FMapFormat.v     | Projection_Format |
  | ∪                 | src/Narcissus/Formats/Base/UnionFormat.v    | Union_Format      |
  | ε                 | src/Narcissus/Formats/Empty.v               | empty_Format      |

  * The monadic operators (return, bind and the set-comprehension operator), in
    Section 2 (Naricssus, Formally), can be found in src/Computation/Core.v

  * The bitstring abstract data type, in Figure 2 (The ByteString interface),
    can be found in src/Narcissus/Common/Monoid.v, named `QueueMonoidOpt`.

  * The definitions and theorems of encoder/decoder correctness:
    - Our actual definitions have additional minor side conditions that are
      omitted in the paper for presentation purposes, such as the invariant on
      the state. The rules below may also have minor side conditions. See the
      corresponding definitions/theorems in the artifact for the complete
      formalism.

  | Definition                           | File                         | Name                 |
  |--------------------------------------|------------------------------|----------------------|
  | Definition 2.1 (Encoder Correctness) | src/Narcissus/Common/Specs.v | CorrectEncoder       |
  | Definition 2.2 (Decoder Correctness) | src/Narcissus/Common/Specs.v | CorrectDecoder_id    |
  | Theorem 2.3 (Decode Inverts Encode)  | src/Narcissus/Common/Specs.v | CorrectDecodeEncode' |
  | Theorem 2.4 (Encode Inverts Decode)  | src/Narcissus/Common/Specs.v | CorrectEncodeDecode' |

  * The encoder rules, in Figure 3 (Correctness rules for encoder combinators):
  
  | Rule     | File                                        | Name                             |
  |----------|---------------------------------------------|----------------------------------|
  | EncSeq   | src/Narcissus/Formats/Base/SequenceFormat.v | CorrectEncoder_sequence          |
  | EncComp  | src/Narcissus/Formats/Base/FMapFormat.v     | CorrectEncoder_Projection_Format |
  | EncEmpty | src/Narcissus/Formats/Empty.v               | CorrectEncoderEmpty              |
  | EncRest  | src/Narcissus/Formats/Base/FMapFormat.v     | CorrectEncoder_Restrict_Format   |
  | EncUnion | src/Narcissus/Formats/Base/UnionFormat.v    | CorrectEncoder_Union             |

  * The definition of `DecodeCM`, in Section 3.1 (Decoders), is simply `DecodeM
    (V * T) T`. Definition 3.1 (Decoder Combinator Soundness) and definition 3.2
    (Decoder Combinator Consistency) are defined in
    src/Narcissus/Common/Specs.v, named `CorrectDecoder`, as conjunction of
    these two definitons.

  * The decoder rules, in Figure 5 (Selected correctness rules for decoder
    combinators):
    - We use `CorrectDecoder` (the dotted roundtrip relation) directly in the
      actual definition for `CorrectDecoder_id` (the solid roundtrip relation),
      by choosing the equality relation as the view and the original format as
      the conformance format. This is explained in Section 3.1 (Decoders). It is
      also justified by the lemma `CorrectDecoder_equiv_CorrectDecoder_id` in
      src/Narcissus/Common/Specs.v

  | Rule       | File                               | Name                    |
  |------------|------------------------------------|-------------------------|
  | DecList    | src/Narcissus/Formats/FixListOpt.v | FixList_decode_correct  |
  | DecDone    | src/Narcissus/Formats/Empty.v      | CorrectDecoderEmpty     |
  | DecSeqProj | src/Narcissus/Formats/Sequence.v   | format_sequence_correct |

  * The decoder rules, in Figure 7 (Additional decoder combinator correctness rules):

  | Rule        | File                                        | Name                      |
  |-------------|---------------------------------------------|---------------------------|
  | DecCompose  | src/Narcissus/Formats/Base/FMapFormat.v     | Compose_decode_correct    |
  | DecViewDone | src/Narcissus/Formats/Empty.v               | ExtractViewFrom           |
  | DecInject   | src/Narcissus/Formats/Base/FMapFormat.v     | injection_decode_correct  |
  | DecSeq      | src/Narcissus/Formats/Base/SequenceFormat.v | Sequence_decode_correct   |
  | DecUnion    | src/Narcissus/Common/ComposeIf.v            | composeIf_format_correct' |

  * The definitions of byte-aligned encoders/decoders and their correctness, in
    Section 3.2 (Improving Performance of Encoders and Decoders):

  | Definition                                            | File                                      | Name                       |
  |-------------------------------------------------------|-------------------------------------------|----------------------------|
  | AlignEncodeM                                          | src/Narcissus/BinLib/AlignedEncodeMonad.v | AlignedEncodeM             |
  | AlignDecodeM                                          | src/Narcissus/BinLib/AlignedDecodeMonad.v | AlignedDecodeM             |
  | Definition 3.3 (Correctness of Byte-Aligned Encoders) | src/Narcissus/BinLib/AlignedEncodeMonad.v | EncodeMEquivAlignedEncodeM |
  | Definition 3.4 (Correctness of Byte-Aligned Decoders) | src/Narcissus/BinLib/AlignedDecodeMonad.v | DecodeMEquivAlignedDecodeM |
  
  * The byte-aligned decoder rules, in Figure 8 (A Selection of byte-alignment
    rules for decoders):

  | Rule           | File                                      | Name                              |
  |----------------|-------------------------------------------|-----------------------------------|
  | AlignDecSeq    | src/Narcissus/BinLib/AlignedDecodeMonad.v | Bind_DecodeMEquivAlignedDecodeM   |
  | AlignDecThrow  | src/Narcissus/BinLib/AlignedDecodeMonad.v | AlignedDecode_Throw               |
  | AlignDecByte   | src/Narcissus/BinLib/AlignWord.v          | AlignedDecodeCharM                |
  | AlignDecReturn | src/Narcissus/BinLib/AlignedDecodeMonad.v | Return_DecodeMEquivAlignedDecodeM |
  
  * The implementation of the automation algorithm, in Section 4 (Automation
    Derivations), can be found in src/Narcissus/Automation. Specifically, the
    entry point of `DeriveDecoder`, shown in Algorithm 1, is
    `synthesize_aligned_decoder` in src/Narcissus/Automation/AlignedAutomation.v
  
  * The combinators for IP Checksums, in Figure 10 (Format, encoder, and decoder
    combinator for IP Checksums):

  | Definition         | File                               | Name                               |
  |--------------------|------------------------------------|------------------------------------|
  | IP_Checksum_format | src/Narcissus/Formats/IPChecksum.v | format_IP_Checksum                 |
  | IP_Checksum_decode | src/Narcissus/Formats/IPChecksum.v | format_IP_Checksum                 |
  | DecChkSum          | src/Narcissus/Formats/IPChecksum.v | compose_IPChecksum_format_correct' |

  * The example of IPv4 header format, in Figure 11 (Format for IP version 4
    headers, using the IP Checksum format), can be found in
    src/Narcissus/Examples/NetworkStack/IPv4Header.v

## Building the virtual machine

#### Common setup

- Download Ubuntu 18.04.2 LTS from https://www.ubuntu.com/download/desktop and install it in a VM

- Set up OPAM and Coq (At least 4GB of memory is required to compile the dependencies and the artifact)

```
sudo apt install curl git build-essential m4 python2.7 python python3-pip libgmp-dev autoconf aspcud
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
opam init -y --compiler=4.04.2
# also put eval $(opam env) in .profile to avoid running this command everytime (reboot needed)
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq=8.7.2
```

#### Microbenchmarks

- Clone Fiat
```
cd ~
git clone --recursive https://github.com/jonathye/fiat.git --depth 1 -b icfp2019 ~/fiat
opam install core_bench=v0.9.0
```

- Build it

```
cd ~/fiat
make -j4 narcissus
make -j4 src/Narcissus/Examples/NetworkStack/Fiat4Mirage.vo
```
- Run the benchmark
```
cd src/Narcissus/Examples/NetworkStack/benchmarks
pip3 install --user scapy==2.4.2 sexpdata==0.0.3
sudo apt install python3-matplotlib
opam install cstruct=3.2.1
./microbenchmarks.sh
./plot.py ../microbenchmarks.out
```

#### Mirage OS integration

- Setup mirage and its dependencies
```
opam repo add mirage-dev https://github.com/mirage/mirage-dev.git
opam install mirage=3.2.0 mirage-clock-unix=1.4.1 mirage-flow=1.5.0
opam install mirage-vnetif=0.4.0 mirage-types=3.2.0 mirage-types-lwt=3.2.0 io-page-unix=2.0.1 randomconv=0.1.0
```

- Get our copy of mirage-tcpip
```
mkdir ~/mirage; cd ~/mirage
git clone https://github.com/cpitclaudel/mirage-tcpip.git --depth 1 -b mirage-tcpip-icfp19 ~/mirage/mirage-tcpip
make -C ~/mirage/mirage-tcpip
```

- Tell OPAM about the local clone

```
opam pin --dev-repo add tcpip.dev~mirage.1 ~/mirage/mirage-tcpip/
```

- Set up mirage-www

  - Dependencies
  ```
  opam install crunch=2.1.0 cow=2.3.0 cowabloga=0.4.0 duration=0.1.1 functoria-runtime=2.2.1 io-page=2.0.1 lwt=4.1.0 xapi-rrd=1.0.2 mirage-conduit=3.0.1 mirage-http=3.2.0 mirage-logs=0.3.0 mirage-net-unix=2.4.1 mirage-random=1.1.0 mirage-runtime=3.2.0 mirage-unix=3.0.8 nocrypto=0.5.4-1 ptime=0.8.4 cohttp-mirage=1.1.0 alcotest=0.8.4 pcap-format=0.5.1
  ln -s ~/.opam/4.04.2/bin/jbuilder ~/.opam/4.04.2/bin/dune # c3 isn't correctly configured
  opam install c3=0.4.0
  ```

  - Sources
  ```
  git clone https://github.com/cpitclaudel/mirage-www.git -b mirage-www-icfp2019 ~/mirage/mirage-www
  ```

  - Set up a tun/tap interface
  ```
  sudo ip link show
  sudo modprobe tun
  sudo ip tuntap add mode tap tap0
  sudo ip link set tap0 up
  sudo ip addr add 10.0.0.1/24 dev tap0
  ```

  - Build the website
  ```
  cd ~/mirage/mirage-www/src
  # This requires the tun/tap interface above
  mirage configure -t unix --net=direct --http-port=8080
  make
  ```

  - Run it
  ```
  echo "ipv4-encoding ipv4-decoding arpv4-encoding arpv4-decoding ethif-encoding ethif-decoding udp-encoding udp-decoding tcp-encoding tcp-decoding" > /tmp/fiat4mirage.config
  # This runs the website on http://10.0.0.2:8080/
  ./main.native
  ```

- Run the benchmarks and reproduce the plots

  - Dependencies
  ```
  pip3 install --user selenium
  cd /usr/local/bin
  curl -sL https://github.com/mozilla/geckodriver/releases/download/v0.23.0/geckodriver-v0.23.0-linux64.tar.gz | sudo tar xz
  sudo chmod +x ./geckodriver
  ```

  - Run the benchmarks (disconnect the VM from the internet before running this step, otherwise remote resources like external scripts and images will affect load times)
  ```
  cd ~/mirage/mirage-www/src
  ./benchmark_mirage_www.py
  ```

  - Reproduce the plots (replace ``[date]`` below by the name of the timestamped folder generated by the benchmarking script)
  ```
  sudo apt install python3-matplotlib python3-scipy
  ./plot_mirage_www.py ../firefox-logs/[date]
  ```
