#!/usr/bin/env python3
"""Generate a .v file with tests for various supported protocols."""

from binascii import unhexlify
from scapy.all import Ether, IP, TCP, UDP, ARP, raw

def read_payload(path):
    with open(path, mode="rb") as payload:
        return payload.read()

CAP_ARP_REQUEST = unhexlify(
    b"4851b70e985950c7bf3edacd0806000108000604000150c7bf3edacdc0a8010100000000"
    b"0000c0a8016d")

CAP_ARP_RESPONSE = unhexlify(
    b"50c7bf3edacd4851b70e9859080600010800060400024851b70e9859c0a8016d50c7bf3e"
    b"dacdc0a80101")

CAP_DNS_REQUEST = unhexlify(
    b"50c7bf3edacd4851b70e9859080045000039c72140004011efd3c0a8016dc0a80101863e"
    b"00350025fa922b7101000001000000000000076578616d706c6503636f6d0000010001")

CAP_DNS_RESPONSE = unhexlify(
    b"4851b70e985950c7bf3edacd080045000049cea740004011e83dc0a80101c0a8016d0035"
    b"863e0035ab6c2b7181800001000100000000076578616d706c6503636f6d0000010001c0"
    b"0c0001000100008ee000045db8d822")

CAP_NTP_REQUEST = unhexlify(
    b"50c7bf3edacd4851b70e985908004500004c2a5b40004011688cc0a8016d84a36101007b"
    b"007b0038d55de30003fa0001000000010000000000000000000000000000000000000000"
    b"00000000000000000000def16724e92b6b31")

CAP_NTP_RESPONSE = unhexlify(
    b"4851b70e985950c7bf3edacd08004520004c82ec0000361159db84a36101c0a8016d007b"
    b"007b0038f7da1c010de300000010000000204e495354def166cb00000000def16724e92b"
    b"6b31def16724f15e9d2adef16724f15ea6fb")

CAP_HTTP_REQUEST = unhexlify(
    b"50c7bf3edacd4851b70e985908004500007f1bf1400040064369c0a8016d976581a4902a"
    b"0050137d78f1f36f442f801800e51dd800000101080ae46e028950ce296e474554202f20"
    b"485454502f312e310d0a486f73743a206e7974696d65732e636f6d0d0a557365722d4167"
    b"656e743a206375726c2f372e34372e300d0a4163636570743a202a2f2a0d0a0d0a")

CAP_HTTP_RESPONSE = unhexlify(
    b"4851b70e985950c7bf3edacd0800452001666d5f40003b06f5f3976581a4c0a8016d0050"
    b"902af36f442f137d793c80180037210100000101080a50ce2973e46e0289485454502f31"
    b"2e3120333031204d6f766564205065726d616e656e746c790d0a5365727665723a205661"
    b"726e6973680d0a52657472792d41667465723a20300d0a436f6e74656e742d4c656e6774"
    b"683a20300d0a4c6f636174696f6e3a2068747470733a2f2f7777772e6e7974696d65732e"
    b"636f6d2f0d0a4163636570742d52616e6765733a2062797465730d0a446174653a205468"
    b"752c203132204a756c20323031382030313a34363a313920474d540d0a582d5365727665"
    b"642d42793a2063616368652d626f73383233302d424f530d0a582d43616368653a204849"
    b"540d0a582d43616368652d486974733a20300d0a582d4672616d652d4f7074696f6e733a"
    b"2044454e590d0a436f6e6e656374696f6e3a20636c6f73650d0a582d4150492d56657273"
    b"696f6e3a20462d300d0a0d0a")

BENCHMARKS = [
    ("ARP",
     [("Request", Ether(CAP_ARP_REQUEST), ["Ether", "ARP"]),
      ("Response", Ether(CAP_ARP_RESPONSE), ["Ether", "ARP"])]),
    ("HTTP",
     [("Request", Ether(CAP_HTTP_REQUEST), ["Ether", "IP", "TCP"]),
      ("Response", Ether(CAP_HTTP_RESPONSE), ["Ether", "IP", "TCP"])]),
    ("NTP",
     [("Request", Ether(CAP_NTP_REQUEST), ["Ether", "IP", "UDP"]),
      ("Response", Ether(CAP_NTP_RESPONSE), ["Ether", "IP", "UDP"])])
]

LAYERS = {"Ether": Ether, "ARP": ARP, "IP": IP, "TCP": TCP, "UDP": UDP}

def fmtarray(nums):
    return "Vector.map (@natToWord 8) [{}]".format(";".join(map(str, nums)))

def fmtip(ip):
    return fmtarray(ip.split("."))

def mktestname(protocol, direction, layer, kind, length):
    return "{}_{}_{}_{}_{}".format(protocol, direction, layer, kind, length).lower()

def ocaml_hexdump(bs):
    return "".join(r"\x{:02x}".format(b) for b in bs)

def mkenc(inputname, length, packet, layer):
    out = "(FreshBuffer {} buf)".format(length)
    if layer is Ether:
        return "fiat_ethernet_encode {} {}".format(inputname, out)
    elif layer is ARP:
        return "fiat_arp_encode {} {}".format(inputname, out)
    elif layer is IP:
        return "fiat_ipv4_encode {} {}".format(inputname, out)
    elif layer is TCP:
        return "fiat_tcp_encode {} ({}) ({}) (natToWord 16 {}) {}".format(
            inputname,
            fmtip(packet[IP].src), fmtip(packet[IP].dst), len(packet[TCP]), out)
    elif layer is UDP:
        return "fiat_udp_encode {} ({}) ({}) (natToWord 16 {}) {}".format(
            inputname,
            fmtip(packet[IP].src), fmtip(packet[IP].dst), len(packet[UDP]), out)
    else:
        raise ValueError("Unexpected layer {}".format(layer))

def mkdec(inputname, length, packet, layer):
    if layer is Ether:
        return "fiat_ethernet_decode {} {}".format(inputname, length)
    elif layer is ARP:
        return "fiat_arp_decode {}".format(inputname)
    elif layer is IP:
        return "fiat_ipv4_decode {}".format(inputname)
    elif layer is TCP:
        return "fiat_tcp_decode {} ({}) ({}) (natToWord 16 {})".format(
            inputname,
            fmtip(packet[IP].src), fmtip(packet[IP].dst), length)
    elif layer is UDP:
        return "fiat_udp_decode {} ({}) ({}) (natToWord 16 {})".format(
            inputname,
            fmtip(packet[IP].src), fmtip(packet[IP].dst), length)
    else:
        raise ValueError("Unexpected layer {}".format(layer))

LETDEF_BYTESTRING_TEMPLATE = '''Definition {} :=
  Eval compute in {}.'''
def mkletdef_bytestring(letname, subpacket):
    return LETDEF_BYTESTRING_TEMPLATE.format(letname, fmtarray(raw(subpacket)))

LETDEF_PACKET_TEMPLATE = '''Definition {} :=
  Eval compute in (must ({}) I).'''
def mkletdef_packet(letname, bytestring_name, packet, layer):
    decexpr = mkdec(bytestring_name, len(packet[layer]), packet, layer)
    return LETDEF_PACKET_TEMPLATE.format(letname, decexpr)

BENCHMARK_TEMPLATE = '''\
(* {} *)
Compute (must ({}) I).\
'''
def mkbench(testname, inputname, kind, length, packet, layer):
    benchexpr = (mkenc if kind == "encode" else mkdec)(inputname, length, packet, layer)
    return BENCHMARK_TEMPLATE.format(testname, benchexpr)

MAIN_TEMPLATE = '''\
Require Import Fiat.Narcissus.Examples.NetworkStack.TestInfrastructure.

Definition buf := MakeBuffer 4096.

{}

{}
'''
def main():
    definitions, benchmarks = [], []
    for protocol, packets in BENCHMARKS:
        for direction, packet, layernames in packets:
            for layername in layernames:
                layer = LAYERS[layername]
                length = len(raw(packet[layer]))
                enc_name = mktestname(protocol, direction, layername, "encode", length)
                dec_name = mktestname(protocol, direction, layername, "decode", length)
                enc_inputname, dec_inputname = enc_name + "_input", dec_name + "_input"
                definitions.append(mkletdef_bytestring(dec_inputname, packet[layer]))
                definitions.append(mkletdef_packet(enc_inputname, dec_inputname, packet, layer))
                benchmarks.append(mkbench(enc_name, enc_inputname, "encode", length, packet, layer))
                benchmarks.append(mkbench(dec_name, dec_inputname, "decode", length, packet, layer))
    with open("../Microbenchmarks.v", mode="w") as f:
        f.write(MAIN_TEMPLATE.format("\n\n".join(definitions), "\n\n".join(benchmarks)))

if __name__ == '__main__':
    main()
