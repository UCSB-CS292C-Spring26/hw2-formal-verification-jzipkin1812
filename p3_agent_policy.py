"""
CS292C Homework 2 — Problem 3: Agent Permission Policy Verification (25 points)
=================================================================================
Encode a realistic agent permission policy as SMT formulas and use Z3 to
analyze it for safety properties and privilege escalation vulnerabilities.
"""

from z3 import *

# ============================================================================
# Constants
# ============================================================================

FILE_READ = 0
FILE_WRITE = 1
SHELL_EXEC = 2
NETWORK_FETCH = 3

ADMIN = 0
DEVELOPER = 1
VIEWER = 2

# ============================================================================
# Sorts and Functions
#
# You will use these to build your policy encoding.
# Do NOT modify these declarations.
# ============================================================================

User = DeclareSort('User')
Resource = DeclareSort('Resource')

role         = Function('role', User, IntSort())          # 0=admin, 1=dev, 2=viewer
is_sensitive = Function('is_sensitive', Resource, BoolSort())
in_sandbox   = Function('in_sandbox', Resource, BoolSort())
owner        = Function('owner', Resource, User)

# The core predicate: is this (user, tool, resource) triple allowed?
allowed = Function('allowed', User, IntSort(), Resource, BoolSort())


# ============================================================================
# Part (a): Encode the Policy — 10 pts
#
# Encode rules R1–R5 from the README as Z3 constraints.
#
# You must design the encoding yourself. Consider:
# - Use ForAll to make rules apply to all users/resources.
# - Encode both what IS allowed and what is NOT allowed.
# - Rule R4 overrides R3 — handle this carefully.
#
# Return a list of Z3 constraints.
# ============================================================================

def make_policy():
    u = Const('u', User)
    r = Const('r', Resource)
    t = Int('t')

    constraints = []

    constraints.append( ForAll([u, t, r], allowed(u, t, r) == Or(
        # Viewer may only read
        And(
            role(u) == VIEWER,
            t == FILE_READ,
            Not(is_sensitive(r))
        ),

        # Developer may read anything, write owned or sandbox, and network sandbox
        And(
            role(u) == DEVELOPER,
            Or(
                t == FILE_READ,
                And(t == FILE_WRITE, Or(owner(r) == u, in_sandbox(r))),
                And(t == NETWORK_FETCH, in_sandbox(r))
            )
        ),

        # Admin can do anything except network non sandbox and r4 later
        And(
            role(u) == ADMIN,
            Or(
                And(t == NETWORK_FETCH, in_sandbox(r)),
                And(t != NETWORK_FETCH)
            )
        ))
    ))

    # R4
    constraints.append(
        ForAll([u, r],
            Not(allowed(u, SHELL_EXEC, r)) == is_sensitive(r)
        )
    )

    return constraints


def make_policy_r6():
    u = Const('u', User)
    r = Const('r', Resource)
    t = Int('t')

    constraints = []

    constraints.append( ForAll([u, t, r], allowed(u, t, r) == Or(
        # Viewer may only read
        And(
            role(u) == VIEWER,
            t == FILE_READ,
            Not(is_sensitive(r))
        ),

        # Developer may read anything, write owned or sandbox, and network sandbox
        # R6: Developer may shell exec non sensitive sandbox resources
        And(
            role(u) == DEVELOPER,
            Or(
                t == FILE_READ,
                And(t == FILE_WRITE, Or(owner(r) == u, in_sandbox(r))),
                And(t == NETWORK_FETCH, in_sandbox(r)),
                And(t == SHELL_EXEC, in_sandbox(r), Not(is_sensitive(r)))
            )
        ),

        # Admin can do anything except network non sandbox and r4 later
        And(
            role(u) == ADMIN,
            Or(
                And(t == NETWORK_FETCH, in_sandbox(r)),
                And(t != NETWORK_FETCH)
            )
        ))
    ))

    # R4
    constraints.append(
        ForAll([u, r],
            Not(allowed(u, SHELL_EXEC, r)) == is_sensitive(r)
        )
    )

    return constraints


# ============================================================================
# Part (b): Policy Queries — 8 pts
# ============================================================================

def query(description, policy, extra):
    """Helper: check if extra constraints are SAT under the policy."""
    s = Solver()
    s.add(policy)
    s.add(extra)
    result = s.check()
    print(f"  {description}")
    print(f"  → {result}")
    if result == sat:
        m = s.model()
        print(f"    Model: {m}")
    print()
    return result


def part_b():
    """
    Answer the four queries from the README.
    For query 4, also demonstrate what becomes possible without R4.
    """
    policy = make_policy()
    print("=== Part (b): Policy Queries ===\n")

    u = Const('u', User)
    r = Const('r', Resource)

    # Q1: Can a developer write to a sensitive file they don't own, in the sandbox?
    query("Q1", policy, [
        role(u) == DEVELOPER,
        is_sensitive(r),
        in_sandbox(r),
        allowed(u, FILE_WRITE, r)
    ])

    # Q2: Can an admin network_fetch a resource outside the sandbox?
    query("Q2", policy, [
        role(u) == ADMIN,
        Not(in_sandbox(r)),
        allowed(u, NETWORK_FETCH, r)
    ])

    # Q3: Is there ANY role that can shell_exec on a sensitive resource?
    query("Q3", policy, [
        is_sensitive(r),
        allowed(u, SHELL_EXEC, r)
    ])

    # Q4: [EXPLAIN] in a comment Remove R4 — what dangerous action becomes possible?
    # If you remove R4, admins can shell_exec on a sensitive resource,
    # which is dangerous by definition.
    # We can create this policy by removing the R4 constraint from the list
    policyWithoutR4 = make_policy()[0:-1]
    query("Q4", policyWithoutR4, [
        is_sensitive(r),
        allowed(u, SHELL_EXEC, r)
    ])


# ============================================================================
# Part (c): Privilege Escalation — 7 pts
#
# New rule R6: Developers may shell_exec on non-sensitive sandbox resources.
#
# Attack scenario: A developer uses shell_exec on a non-sensitive sandbox
# resource to change ANOTHER resource's sensitivity flag (e.g., modifying
# a config file that controls access). This makes a previously sensitive
# resource become non-sensitive, bypassing R4 on the next step.
#
# Model this as a 2-step trace where a resource's sensitivity changes
# between steps.
# ============================================================================

def part_c():
    print("=== Part (c): Privilege Escalation ===\n")

    # The code for modelling the escalation attack was written by a Chat GPT coding agent.
    base_policy = make_policy()

    # Fresh symbols
    dev = Const("dev", User)
    r1  = Const("r1", Resource)
    r2  = Const("r2", Resource)

    # Time-indexed sensitivity
    sens0 = Function("sens0", Resource, BoolSort())   # before step1
    sens1 = Function("sens1", Resource, BoolSort())   # after step1

    u = Const("u_r6", User)
    r = Const("r_r6", Resource)

    policy_r6 = make_policy_r6()

    # ------------------------------------------------------------
    # STEP 1:
    # developer can shell_exec r1 initially
    # ------------------------------------------------------------
    query(
        "Developer can shell exec on non-sensitive sandbox:",
        policy_r6,
        [
            role(dev) == DEVELOPER,
            in_sandbox(r1) == True,
            is_sensitive(r1) == False,
            allowed(dev, SHELL_EXEC, r1)
        ]
    )

    query(
        "r2 was blocked before but not after, so the escalation attack works",
        policy_r6,
        [
            role(dev) == DEVELOPER,

            # r1 launchpad
            in_sandbox(r1) == True,
            is_sensitive(r1) == False,
            allowed(dev, SHELL_EXEC, r1),

            # r2 sandbox target
            in_sandbox(r2) == True,
            r1 != r2,

            # before step1
            sens0(r2) == True,

            # after step1 side effect
            sens1(r2) == False,

            # blocked before
            Not(And(
                role(dev) == DEVELOPER,
                in_sandbox(r2),
                Not(sens0(r2))
            )),

            # allowed after
            And(
                role(dev) == DEVELOPER,
                in_sandbox(r2),
                Not(sens1(r2))
            )
        ]
    )

    # FIX: We could add a new rule:
    # No resource's sensitivity may ever change.
    x = Const("x_fix", Resource)
    # We can model this by enforcing sensitivity being identical from 0 to 1 timestamps.
    fix = ForAll([x], sens1(x) == sens0(x))

    fixed = query(
        "Apply fix: labels immutable, attack should fail",
        policy_r6,
        [
            fix,

            role(dev) == DEVELOPER,
            in_sandbox(r1) == True,
            is_sensitive(r1) == False,

            in_sandbox(r2) == True,
            sens0(r2) == True,

            # try to make target executable after step1
            And(
                role(dev) == DEVELOPER,
                in_sandbox(r2),
                Not(sens1(r2))
            )
        ]
    )
    if fixed == unsat:
        print("ESCALATION BLOCKED")

    # Explanation:
    # By ensuring that no resource may have its sensitivity changed,
    # we prevent the escalation attack, which relies on using shell_exec
    # to make a previously sensitive resource non-sensitive.
    # This ensures that r6 can allow shell_exec on non-sensitive resources
    # without causing problems for other resources.

# ============================================================================
if __name__ == "__main__":
    part_b()
    part_c()
