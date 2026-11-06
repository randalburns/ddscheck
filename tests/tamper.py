#!/usr/bin/env python3
"""Mutate a certificate and confirm ddscheck never proves anything it should not."""
import random, subprocess, sys, tempfile, os

cert, checker = sys.argv[1], ".lake/build/bin/ddscheck"
data = open(cert, "rb").read()

def run(blob):
    with tempfile.NamedTemporaryFile(suffix=".cert", delete=False) as f:
        f.write(blob)
    r = subprocess.run([checker, f.name], capture_output=True, text=True)
    os.unlink(f.name)
    return r.returncode, r.stdout

rc, out = run(data)
assert rc == 0 and "1 proved, 0 rejected" in out, out
truth = data[2]
print(f"baseline: proved, North-South take {truth}")

# Every false claim about the trick count must be rejected.
for k in range(14):
    if k == truth:
        continue
    rc, out = run(data[:2] + bytes([k]) + data[3:])
    assert rc != 0 and "REJECTED" in out, f"false claim {k} accepted:\n{out}"
print("false trick counts: all 13 rejected")

# A different trump suit or opening leader must not borrow this proof.
for strain in range(5):
    if strain == data[0]:
        continue
    rc, out = run(bytes([strain]) + data[1:])
    assert "PROVED" not in out, f"strain {strain} accepted:\n{out}"
for leader in range(4):
    if leader == data[1]:
        continue
    rc, out = run(data[:1] + bytes([leader]) + data[2:])
    assert "PROVED" not in out, f"leader {leader} accepted:\n{out}"
print("other strains and leaders: all rejected")

# Random corruption may still pass only if it changed nothing that matters, so any
# PROVED line must still state the true result for the same deal, strain and leader.
random.seed(1)
trials, proved, refused = int(sys.argv[2]), 0, 0
for _ in range(trials):
    i = random.randrange(3 + 56, len(data))  # past the claim itself
    blob = bytearray(data)
    blob[i] ^= 1 << random.randrange(8)
    rc, out = run(bytes(blob))
    if "PROVED" in out:
        proved += 1
        assert f"North-South take {truth}," in out, out
    else:
        refused += 1
print(f"random bit flips: {refused} refused, {proved} harmless, 0 false proofs")
