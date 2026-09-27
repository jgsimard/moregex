"""Central performance thresholds validated by the benchmark suite."""

# Literal search strategies become worthwhile only after startup cost is
# amortized over a moderately large subject.
comptime LARGE_LITERAL_HAYSTACK_BYTES = 4096

# Reverse scanning is reserved for sufficiently selective literal anchors.
comptime REVERSE_LITERAL_MIN_BYTES = 8

# The dedicated short-literal verifier uses one or two 16-byte loads.
comptime SHORT_LITERAL_MIN_BYTES = 16
comptime SHORT_LITERAL_MAX_BYTES = 32

# This path avoids repeated giveback over very large homogeneous runs.
comptime GREEDY_RUN_SUFFIX_HAYSTACK_BYTES = 65536

# Small bounded delimiter runs use the ordinary generic executor.
comptime DELIMITED_REPEAT_PLAN_MINIMUM = 8

# Counted repetitions above this size are not expanded into Thompson states.
comptime MAX_NFA_REPEAT_EXPANSION = 256
