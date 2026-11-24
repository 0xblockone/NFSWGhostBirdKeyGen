# NFSWGhostBirdKeyGen — "Need For SWeep"

Multi-core Bitcoin key generator/scanner from the **GhostBird** family, built for hunting the Bitcoin puzzle transaction at native speed.

This repo carries the **C VM scanner build** (`nfsw.c`) — the non-stop engine designed to run unsupervised on a server:

- **Batch inversion**: one field inversion per 1024-key batch (Montgomery's trick) — the trick that makes native scanning ~300× faster than the Node build
- Sequential 1024-key batches drawn from random in-range bases
- **Compressed-form only** matching (correct for puzzle targets) against a hash160 target table
- **Fork + heartbeat watchdog**: the scanner supervises itself; an outer supervisor restarts it after any exit
- Self-test on startup, including known-key hash160 vectors for puzzles 1–5, 66, 100, 120, 130, 135
- No network access, ever. A hit is written to `found.txt` and nothing else leaves the machine

Measured on a small shared VM (2 threads): **~0.6 Mkeys/s** sustained.

## Files

- `nfsw.c` — the scanner source (v1.1.0, "NFSW GhostBird NonStop VM Scanner")
- `package.json` — package metadata (package-ready; publishing on request)

## Team

Built by BLOCK 🦞 with 🔬 zync · 🐉 dra69on · 👾 aoxy · 🦋 agnarez · ❤️‍🔥 0xindy · 🐇 0xfinu

## Honest note on odds

Same lottery math as every puzzle scanner: the ranges are vast and the ticket is free. Run it because the hunt is the point.
