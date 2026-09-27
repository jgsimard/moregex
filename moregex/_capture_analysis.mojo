"""Capture participation analysis."""

from ._ast import CaptureNode, OrNode, RegexNode, RepeatNode, SequenceNode
from ._syntax import Regex


def _sequence_mandatory_capture_mask[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int
]() -> Int:
    comptime if item == sequence.count:
        return 0
    return _mandatory_capture_mask[nodes, sequence.items[item]]() | (
        _sequence_mandatory_capture_mask[nodes, sequence, item + 1]()
    )


def _alternation_mandatory_capture_mask[
    nodes: List[RegexNode], alternation: OrNode
]() -> Int:
    comptime if alternation.count == 0:
        return 0
    var required = _mandatory_capture_mask[nodes, alternation.options[0]]()
    comptime for option in range(1, alternation.count):
        required &= _mandatory_capture_mask[
            nodes, alternation.options[option]
        ]()
    return required


def _mandatory_capture_mask[nodes: List[RegexNode], node_index: Int]() -> Int:
    """Return capture groups participating in every match of an AST node."""
    comptime node = nodes[node_index]
    comptime if node.isa[CaptureNode]():
        comptime capture = node[CaptureNode]
        return (Int(1) << (capture.index - 1)) | _mandatory_capture_mask[
            nodes, capture.child
        ]()
    elif node.isa[SequenceNode]():
        return _sequence_mandatory_capture_mask[nodes, node[SequenceNode], 0]()
    elif node.isa[OrNode]():
        return _alternation_mandatory_capture_mask[nodes, node[OrNode]]()
    elif node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        comptime if repeat.minimum > 0:
            return _mandatory_capture_mask[nodes, repeat.child]()
        return 0
    return 0


def _all_captures_mandatory[regex: Regex]() -> Bool:
    """Return whether every numbered group participates in every match."""
    comptime if regex.capture_count == 0:
        return True
    comptime expected = (Int(1) << regex.capture_count) - 1
    return (
        _mandatory_capture_mask[regex.nodes, regex.capture_root]() == expected
    )


def _constant_capture_participation_sequence[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int
]() -> Int:
    """Return the participating capture count, or -1 when it can vary."""
    comptime if item == sequence.count:
        return 0
    else:
        comptime head = _constant_capture_participation[
            nodes, sequence.items[item]
        ]()
        comptime tail = _constant_capture_participation_sequence[
            nodes, sequence, item + 1
        ]()
        comptime if head < 0 or tail < 0:
            return -1
        return head + tail


def _constant_capture_participation_alternation[
    nodes: List[RegexNode], alternation: OrNode
]() -> Int:
    """Return a common alternative capture count, or -1 when it varies."""
    comptime if alternation.count == 0:
        return 0
    else:
        comptime expected = _constant_capture_participation[
            nodes, alternation.options[0]
        ]()
        comptime if expected < 0:
            return -1
        comptime for option in range(1, alternation.count):
            comptime actual = _constant_capture_participation[
                nodes, alternation.options[option]
            ]()
            comptime if actual != expected:
                return -1
        return expected


def _constant_capture_participation[
    nodes: List[RegexNode], node_index: Int
]() -> Int:
    """Return captures participating in every match, independent of identity.

    A negative result means that the count can vary. A repeated branch with
    captures is conservative: different iterations may populate different
    groups even when each iteration has the same capture count.
    """
    comptime node = nodes[node_index]
    comptime if node.isa[CaptureNode]():
        comptime child = _constant_capture_participation[
            nodes, node[CaptureNode].child
        ]()
        comptime if child < 0:
            return -1
        return child + 1
    elif node.isa[SequenceNode]():
        return _constant_capture_participation_sequence[
            nodes, node[SequenceNode], 0
        ]()
    elif node.isa[OrNode]():
        return _constant_capture_participation_alternation[
            nodes, node[OrNode]
        ]()
    elif node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        comptime child = _constant_capture_participation[nodes, repeat.child]()
        comptime if repeat.maximum == 0 or child == 0:
            return 0
        comptime if repeat.minimum == 0 or repeat.maximum != 1 or child < 0:
            return -1
        return child
    return 0


def _constant_capture_count[regex: Regex]() -> Int:
    """Return the fixed participating-group count including group zero."""
    comptime captures = _constant_capture_participation[
        regex.nodes, regex.capture_root
    ]()
    comptime if captures < 0:
        return -1
    return captures + 1
