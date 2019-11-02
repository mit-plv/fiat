from scapy.all import * # pylint: disable=unused-wildcard-import
import random
import string
from pprint import pprint
from binascii import hexlify
from scapy.utils import PcapWriter
from scapy.config import conf
import os

inside = "18.0.0.0/28"
outside = "1.1.1.0/28"

random.seed(0)

PKT_TEMPLATE = """
Definition {} : ByteBuffer.t _ :=
  Eval compute in Vector.map (@NToWord 8) [{}]%N."""

def bytes2fiat(name, bs):
    nums = "; ".join(str(int(b)) for b in bs)
    return PKT_TEMPLATE.format(name, nums)

def pkt2fiat(name, pkt):
    del pkt.chksum
    pkt.show2(dump=True)
    return bytes2fiat(name, bytes(pkt))

def sstr(obj):
    return "".join("\\x{}".format(hex(ord(c))[2:].rjust(2, "0")) for c in str(obj))

def random_payload(length):
    return "".join(random.choice(string.ascii_lowercase) for _ in range(length))

def random_ip(network):
    return str(RandIP(network))

def make_outgoing():
    return IP(src=random_ip(inside), dst=random_ip(outside))/UDP(sport=23, dport=23)/b"outgoing:accept"

def find_previous(history, src, dst):
    count = sum(pkt[IP].dst == dst for pkt in history) # pkt[IP].src == src and
    return ("accept ({})".format(count) if count > 0 else "reject").encode("ascii")

def make_incoming(history):
    src, dst = random_ip(outside), random_ip(inside)
    decision = find_previous(history, src=dst, dst=src)
    payload = b"incoming:" + decision
    return IP(src=src, dst=dst)/UDP(sport=23, dport=23)/payload

def main():
    history = []
    for idx in range(50):
        outgoing = random.uniform(0, 1) > 0.7
        pkt = make_outgoing() if outgoing else make_incoming(history)
        history.append(pkt)
        fiat = pkt2fiat("pkt{}".format(idx), pkt)
        pkt_bytes = hexlify(bytes(pkt)).decode("ascii")
        # print(fiat)
        print("{}\t{}\t{}".format(idx, pkt_bytes, "pass" if b"accept" in bytes(pkt[UDP].payload) else "fail"))
    print(os.getcwd())
    wrpcap("stateful_guard.pcap", history)
    return history

if __name__ == '__main__':
    main()
