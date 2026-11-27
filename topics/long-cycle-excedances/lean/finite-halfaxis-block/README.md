# Cutoff-eight finite certificate scaling pilot

This package exercises the two largest old sizes in the [compact window
archive](../../finite-prefix/dyadic-windows/README.md) from #331. It reuses the
[exact first-pair proof and quantified block
consumer](../finite-halfaxis/README.md) from #332.

The pilot checks the stored insertion transitions 249 to 250 and 250 to 251.
It checks all compiled windows, adjacent ordering and the odd center at old
size 249. These are numerical leaves and their transfer to the block
consumer's hypotheses. Applying the block consumer to the original rows
throughout the prefix requires all intervening insertion transitions and all
219 windows families. That full run and final quantified theorem are pending.

On local Lean 4.19, the directed Horner arithmetic for all 496 signs at old
size 250 passed in four processes, each with 31 windows. Each used about
34 user CPU seconds and at most 3.04 GB RSS. The full 250-slot shortened
insertion check used 18.34 user seconds and 2.32 GB RSS. The single-process
check of the old-size-249 windows, including the odd center, used 101.15 user
seconds and 2.88 GB RSS. These local arithmetic measurements used a
compatibility environment. The hosted pilot tests the production pin with a
six-GiB process address-space limit and a three-minute wall-clock limit per
compile or replay.

Run from the repository root with Lean 4.33.1 and GNU `time` on Linux.

```sh
python3 -Bu topics/long-cycle-excedances/lean/finite-halfaxis-block/check.py \
  /tmp/halfaxis-block-pin /path/to/quotient-import-objects.tar.zst
```

The second argument is optional. The generator also emits the sources for the
full quantified certificate when invoked without `--pilot`. Its full output
is about 13 MiB before compilation. Production benchmarking precedes any
all-size replay.
