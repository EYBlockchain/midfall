#!/usr/bin/env python3
"""Check the tracked Sepolia Moonlight deployment source/runtime pair.

This does not claim that the current Lean generator reproduces the deployed
Moonlight source: the deployment was rendered by a superseded generator.  It
checks the narrower, falsifiable fact that the checked-in source is the source
of the checked-in fetched runtime bytecode:

  1. the Halo2VerifyingKey constructor's payload mstores rebuild the runtime
     bytecode exactly (`0xfe || payload`), and
  2. compiling the Halo2Verifier source with the pinned solc/settings reproduces
     the fetched runtime after filling the one immutable address and removing
     solc's CBOR trailer.

Exit 0 only when both checks pass.  Run from the repository root or from
`proofs/solidity-verifier`.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
D = ROOT / "proofs/solidity-verifier/deployments/sepolia/moonlight-wrap"
SOLC = Path(os.environ.get("SOLC", ROOT / "proofs/solidity-verifier/.solc/solc"))


def read_hex(path: Path) -> bytes:
    return bytes.fromhex(path.read_text().strip().removeprefix("0x"))


def check_vk() -> bool:
    src = (D / "Halo2VerifyingKey.sol").read_text()
    runtime = read_hex(D / "Halo2VerifyingKey.runtime.bytecode.hex")
    words: dict[int, bytes] = {}
    for off, val in re.findall(
        r"mstore\(add\(payload,\s*(0x[0-9a-fA-F]+)\),\s*(0x[0-9a-fA-F]+)\)", src
    ):
        words[int(off, 16)] = int(val, 16).to_bytes(32, "big")
    payload = bytearray(0x4280)
    for off, word in words.items():
        if off + 32 > len(payload):
            print(f"[VK] mstore offset out of range: {off:#x}")
            return False
        payload[off : off + 32] = word
    built = b"\xfe" + bytes(payload)
    ok = built == runtime
    print(f"[VK] mstore words={len(words)} built={len(built)} fetched={len(runtime)} exact={ok}")
    if not ok:
        for i, (a, b) in enumerate(zip(built, runtime)):
            if a != b:
                print(f"[VK] first difference at {i:#x}: {a:#x} != {b:#x}")
                break
    return ok


def check_verifier() -> bool:
    src = D / "Halo2Verifier.sol"
    deployed = read_hex(D / "Halo2Verifier.runtime.bytecode.hex")
    if not SOLC.exists() and not (shutil_which := os.popen(f"command -v {SOLC}").read().strip()):
        print(f"[verifier] solc not found: {SOLC}")
        return False
    cmd = [
        str(SOLC),
        "--via-ir",
        "--optimize",
        "--optimize-runs",
        "200",
        "--evm-version",
        "cancun",
        "--metadata-hash",
        "none",
        "--bin-runtime",
        str(src),
    ]
    try:
        out = subprocess.run(cmd, check=True, capture_output=True, text=True, cwd=ROOT).stdout
    except subprocess.CalledProcessError as exc:
        print(f"[verifier] solc failed: {exc.stderr.strip()[-500:]}")
        return False
    match = re.search(r"Binary of the runtime part:\s*\n([0-9a-fA-F]+)", out)
    if not match:
        print("[verifier] solc produced no runtime")
        return False
    compiled = bytearray.fromhex(match.group(1))

    # Fill the AUTHORIZED_VK immutable at the offsets the deployed runtime uses.
    # The source has one constructor argument, so these are the only placeholders.
    vk_addr = bytes.fromhex("80b32f68a333df55da60bec44c498477a8311ede")
    offsets = [i for i in range(len(deployed)) if deployed.startswith(vk_addr, i)]
    if len(offsets) != 2:
        print(f"[verifier] expected two AUTHORIZED_VK immutable slots, found {offsets}")
        return False
    for off in offsets:
        compiled[off : off + 20] = vk_addr

    # The deployed runtime was built with metadata stripped; solc CLI still adds
    # the 12-byte CBOR trailer.  The tracked deployment is the prefix.
    prefix = bytes(compiled[: len(deployed)])
    trailer = bytes(compiled[len(deployed) :])
    ok = prefix == deployed
    print(
        f"[verifier] compiled={len(compiled)} fetched={len(deployed)} "
        f"trailer={trailer.hex()} prefix-exact={ok}"
    )
    if not ok:
        for i, (a, b) in enumerate(zip(prefix, deployed)):
            if a != b:
                print(f"[verifier] first difference at {i:#x}: {a:#x} != {b:#x}")
                break
    return ok


def main() -> int:
    vk = check_vk()
    verifier = check_verifier()
    print(f"[moonlight-artifacts] vk={vk} verifier={verifier}")
    return 0 if vk and verifier else 1


if __name__ == "__main__":
    sys.exit(main())
