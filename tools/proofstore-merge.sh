#!/bin/sh
# Git merge driver for *.proof-store files (see Readme.md, "Proof store files").
# A proof store is a binary append-only log; two valid logs concatenated are
# still a valid log (readers re-synchronize on the frame MAGIC, later frames
# win, `compact` deduplicates).  So merging is plain concatenation.
#
# Invoked by git as:  proofstore-merge.sh %A %O %B %L %P
#   $1 = ours (also the file git takes as the merge result)
#   $2 = ancestor (unused)
#   $3 = theirs
set -e
cat "$3" >> "$1"
exit 0
