from scapy.all import * # pylint: disable=unused-wildcard-import
import random, string
from pprint import pprint

inside = "18.0.0.0/30"
outside = "19.0.0.0/30"

random.seed(0)

def random_payload(length):
    return "".join(random.choice(string.ascii_lowercase) for _ in range(length))

def random_ip(network):
    return str(RandIP(network))

def make_outgoing():
    return Ether()/IP(src=random_ip(inside), dst=random_ip(outside))/UDP(sport=23, dport=23)/b"outgoing:accept"

def find_previous(history, src, dst):
    for pkt in history:
        if pkt[IP].src == src and pkt[IP].dst == dst:
            print("Found", repr(pkt))
            return True
    return False

def make_incoming(history):
    src, dst = random_ip(outside), random_ip(inside)
    decision = b"accept" if find_previous(history, src=dst, dst=src) else b"reject"
    payload = b"incoming:" + decision
    return Ether()/IP(src=src, dst=dst)/UDP(sport=23, dport=23)/payload

def main():
    history = []
    for _ in range(50):
        outgoing = random.uniform(0, 1) > 0.7
        pkt = make_outgoing() if outgoing else make_incoming(history)
        history.append(pkt)
        print(repr(pkt))
    wrpcap("stateful_guard.pcap", history)

if __name__ == '__main__':
    main()
