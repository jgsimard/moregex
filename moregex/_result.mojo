"""Shared match-span and capture payload representations."""

from std.utils import StaticTuple


@fieldwise_init
struct _MatchSpan(TrivialRegisterPassable):
    """A half-open byte span shared by all executors."""

    var start: Int
    var end: Int

    @always_inline
    def consumed(self) -> Int:
        return self.end - self.start

    @always_inline
    def is_empty(self) -> Bool:
        return self.start == self.end


@fieldwise_init
struct _CaptureOffsets[capture_count: Int](ImplicitlyCopyable):
    """The complete match and numbered-capture half-open offsets."""

    var starts: StaticTuple[Int, Self.capture_count + 1]
    var ends: StaticTuple[Int, Self.capture_count + 1]

    @always_inline
    def match_span(self) -> _MatchSpan:
        return _MatchSpan(self.starts[0], self.ends[0])


@fieldwise_init
struct _CaptureParticipation(TrivialRegisterPassable):
    """A match span plus one bit for each participating capture group."""

    var span: _MatchSpan
    var groups: UInt64
