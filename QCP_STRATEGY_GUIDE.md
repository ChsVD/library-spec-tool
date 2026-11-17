# Using QCP Strategies Instead of Excessive `which implies` Annotations

## 1. Goal

In this verification project, many C annotations currently use `which implies` to manually unfold predicates or expose intermediate assertions needed by QCP symbolic execution.

For example, the C code may conceptually contain annotations such as:

```text
store_foo(p, x)

which implies

store(field_1, v1) *
store(field_2, v2) *
...
```

This approach is valid, but it becomes repetitive when the same predicate decomposition is required in many functions.

Use QCP strategies aggressively as the default mechanism for reusable representation-level symbolic-execution reasoning. Demonstrated duplication is not required: a natural, reusable relationship between an abstract predicate and its resources is sufficient reason to prefer a strategy.

The main principle is:

> Use C annotations to describe program logic, use QCP strategies by default for reusable representation-level predicate transformations, and use Rocq proofs for substantial mathematical and abstract logical reasoning.

Do **not** try to eliminate every `which implies`. Instead, move reusable structural reasoning into strategies while keeping function-specific reasoning explicit.

Do not pursue strategy count as a goal. Soundness, canonical-state quality, and maintainability take priority over automation quantity.

---

# 2. Mental Model: `which implies` vs. Strategy

A `which implies` annotation can be understood as:

> At this exact program point, manually transform the current assertion into another assertion.

A strategy can be understood as:

> Register a reusable, proved assertion-transformation rule so that QCP can apply the transformation automatically whenever the same symbolic-execution situation occurs.

Therefore:

```text
which implies
```

is usually **local and explicit**, while a strategy is **global/reusable automation**.

A strategy is appropriate whenever a transformation expresses a reusable predicate/resource relationship, even if only one current function needs it. Repetition strengthens the case but is not a prerequisite.

---

# 3. Typical Problem: An Abstract Predicate Hides a Memory Cell

Suppose we have a Rocq predicate:

```coq
Definition store_int_pair (p : addr) (x y : Z) : Assertion :=
  &(p # "int_pair" ->ₛ "a") # Int |-> x **
  &(p # "int_pair" ->ₛ "b") # Int |-> y.
```

The C-level Spec may intentionally remain abstract:

```c
Require store_int_pair(p, x, y)
```

Now consider:

```c
int temp = p->a;
```

To symbolically execute this read, QCP needs something equivalent to:

```text
store(&(p->a), ?v)
```

However, the symbolic state only contains:

```text
store_int_pair(p, x, y)
```

QCP does not simply unfold every Rocq definition automatically.

Without a strategy, one might manually write an intermediate annotation equivalent to:

```text
store_int_pair(p, x, y)

which implies

store(&(p->a), x) *
store(&(p->b), y)
```

This works, but repeating it in many C functions is undesirable.

A strategy should automate this kind of reusable transformation.

---

# 4. Strategies Operate on Entailment Problems

When QCP wants to execute:

```c
temp = p->a;
```

conceptually, it needs to solve an entailment of the form:

```text
LEFT
    Current symbolic assertion

|--

RIGHT
    store(&(p->a), ?v) * ?Frame
```

For example:

```text
LEFT:
    store_int_pair(p, x, y)

RIGHT:
    store(&(p->a), v)
```

The strategy tells QCP how the assertion on the left can satisfy the resource requirement on the right.

This explains why QCP strategy rules contain sections such as:

```text
left :
right :
action :
```

---

# 5. Basic Read Strategy

A simplified strategy may look like:

```text
id : 0
priority : core(1)

left :
    store_int_pair(?p, ?x, ?y) at 0

right :
    store(field_addr(?p, int_pair, a), I32, ?v) at 1

action :
    left_erase(0);
    right_erase(1);
    left_add(store(field_addr(p, int_pair, b), I32, y));
    right_add(v == x);
```

This should be understood as follows.

---

## 5.1 `id`

```text
id : 0
```

The strategy has a unique identifier.

Use unique IDs within the relevant strategy set so that generated proof obligations and debugging output can identify individual rules.

---

## 5.2 `priority : core(1)`

A `core` strategy is generally used **before a symbolic memory operation**, when QCP needs additional resources to execute that operation.

For example:

```c
x = task->field;
```

requires QCP to find a suitable `store(...)`.

Similarly:

```c
task->field = value;
```

requires QCP to establish writable permission for the target memory cell.

A useful mental model is:

> `core` strategies open abstract predicates on demand so that the next C operation can execute.

The priority number controls ordering among applicable strategies. Smaller priority values have higher priority.

Do not assign priorities arbitrarily. Prefer a consistent hierarchy across the project.

---

# 6. Pattern Variables: `?p` vs. `p`

Consider:

```text
left :
    store_int_pair(?p, ?x, ?y)
```

The variables:

```text
?p
?x
?y
```

are pattern/meta variables introduced during matching.

If the current symbolic state contains:

```text
store_int_pair(task1, 3, 7)
```

the strategy may match:

```text
p = task1
x = 3
y = 7
```

After matching, actions use the matched variables without `?`:

```text
p
x
y
```

A useful rule is:

```text
?p    introduces or matches a metavariable
p     refers to the already matched metavariable
```

Be careful not to confuse the two forms.

---

# 7. Understanding `at N`

For example:

```text
left :
    store_int_pair(?p, ?x, ?y) at 0
```

and:

```text
right :
    store(field_addr(?p, int_pair, a), I32, ?v) at 1
```

The `at` indices give names to the matched assertion atoms.

They can then be referenced by actions:

```text
left_erase(0);
right_erase(1);
```

Conceptually:

```text
at 0
```

marks the matched left-side assertion as item `0`, while:

```text
at 1
```

marks the right-side requirement as item `1`.

---

# 8. Understanding the Main Actions

Suppose the current problem is:

```text
LEFT:
    store_int_pair(p, x, y)

RIGHT:
    store(&(p->a), v)
```

The strategy performs the following transformation.

### Step 1: consume the abstract predicate

```text
left_erase(0);
```

This removes:

```text
store_int_pair(p, x, y)
```

from the left side because the strategy is decomposing it.

### Step 2: satisfy the requested memory resource

```text
right_erase(1);
```

The right-side memory requirement is handled by this rule.

### Step 3: preserve the unused part of the predicate

```text
left_add(
    store(field_addr(p, int_pair, b), I32, y)
);
```

The original predicate represents:

```text
store(&(p->a), x) *
store(&(p->b), y)
```

The `a` field is consumed to satisfy the current read operation.

The `b` field remains part of the symbolic state.

### Step 4: connect the symbolic read value with the abstract value

```text
right_add(v == x);
```

This tells QCP that the value being read from field `a` is exactly `x`.

Conceptually, the strategy performs:

```text
store_int_pair(p, x, y)

=>

store(&(p->a), x) *
store(&(p->b), y)
```

while using the first resource to satisfy the read and keeping the second as the frame.

---

# 9. Read and Write Strategies Are Different

Do not assume that a strategy for reading a field is automatically sufficient for writing that field.

For a read:

```c
x = p->a;
```

QCP needs to know both:

1. that the memory cell exists, and
2. its current value.

Therefore, the right side typically contains something like:

```text
store(addr, ?v)
```

For a write:

```c
p->a = x;
```

the old value may not matter. QCP mainly needs writable permission.

A write-oriented strategy may therefore match:

```text
has_permission(addr)
```

rather than:

```text
store(addr, ?v)
```

For example:

```text
id : 2
priority : core(1)

left :
    store_int_pair(?p, ?x, ?y) at 0

right :
    has_permission(
        field_addr(?p, int_pair, a),
        I32
    ) at 1

action :
    left_erase(0);
    right_erase(1);
    left_add(
        store(
            field_addr(p, int_pair, b),
            I32,
            y
        )
    );
```

A useful rule is:

```text
READ:
    usually match store(addr, ?v)

WRITE:
    usually match has_permission(addr)
```

When implementing strategies for project predicates, always distinguish these two cases.

---

# 10. Folding Predicates Back with `post` Strategies

If every field access permanently unfolds an abstract predicate, the symbolic state will quickly become large and difficult to manage.

For example, after executing a memory operation, the state may contain:

```text
store(&(p->a), x) *
store(&(p->b), y)
```

instead of the preferred abstraction:

```text
store_int_pair(p, x, y)
```

A `post` strategy can restore the abstract form:

```text
id : 4
priority : post(1)

left :
    store(field_addr(?p, int_pair, a), I32, ?x) at 0
    store(field_addr(p, int_pair, b), I32, ?y) at 1

action :
    left_erase(0);
    left_erase(1);
    left_add(store_int_pair(p, x, y));
```

This produces a desirable lifecycle:

```text
Abstract predicate
        |
        | core strategy
        v
Field-level resources
        |
        | symbolic execution of C statement
        v
Updated field-level resources
        |
        | post strategy
        v
Abstract predicate
```

This pattern should be preferred whenever possible.

---

# 11. Recommended Project Style: Keep Abstract Predicates as the Normal Form

For a large verification project, define a preferred symbolic-state representation.

For example, normal symbolic states may contain abstractions such as:

```text
task_inv(...)
*
assign_ready_pending(...)
*
occupy_dll_node(...)
```

rather than dozens of raw:

```text
store(...)
```

assertions.

Strategies should preserve this abstraction boundary.

A good general design is:

```text
large abstraction
       |
       | demand-driven core strategy
       v
medium-level abstraction
       |
       | demand-driven core strategy
       v
small predicate
       |
       | demand-driven core strategy
       v
individual memory cell
```

After the C operation, `post` strategies should move in the opposite direction.

---

# 12. Example for RTOS Task Predicates

Suppose the project defines:

```text
store_task_dync_sched(dyn, d)
```

which internally represents fields such as:

```text
stat
advance_cnt
cur_prio
origin_timeslice
rest_timeslice
sched_link
bitmap_column
delay
```

Suppose the C code performs:

```c
task->dync_sched_member.stat = KTASK_READY;
```

A manual annotation style may repeatedly unfold the whole predicate:

```text
store_task_dync_sched(...)

which implies

store(stat, ...)
*
store(advance_cnt, ...)
*
store(cur_prio, ...)
*
...
*
store(delay, ...)
```

This unnecessarily exposes implementation details in the C annotation.

Instead, prefer the following architecture:

```text
C-level symbolic state:

    store_task_dync_sched(task, d)
```

When the C statement needs `stat`:

```text
store_task_dync_sched(task, d)
        |
        | core strategy
        v
resource for stat
+
remaining representation
        |
        | execute C assignment
        v
updated stat resource
+
remaining representation
        |
        | post strategy
        v
store_task_dync_sched(task, set_status(d, KTASK_READY))
```

The C verification should ideally expose:

```text
before:
    store_task_dync_sched(task, d)

C:
    task->stat = KTASK_READY;

after:
    store_task_dync_sched(
        task,
        set_status(d, KTASK_READY)
    )
```

without manually exposing every other field.

---

# 13. Do Not Unfold Large Invariants Aggressively

Avoid strategies such as:

```text
task_inv(...)
    =>
all task fields
*
stack resources
*
scheduler resources
*
ID resources
*
global map resources
*
...
```

merely because one field is being accessed.

Likewise, do not automatically unfold an entire:

```text
os_inv(...)
```

for a small field operation.

This causes:

- symbolic-state explosion,
- slower strategy matching,
- fragile proof automation,
- unnecessary dependencies between unrelated predicates,
- more difficult strategy-loop debugging.

Instead, structure predicates hierarchically.

For example:

```text
task_inv
   ↓
store_task_descriptor
   ↓
store_task_dync_sched
   ↓
store of one field
```

Each strategy should expose only the resources needed for the current symbolic operation.

This is **demand-driven unfolding**.

---

# 14. Canonical Form Is a Central Design Principle

Before writing many strategies, decide:

> What should a normal symbolic assertion look like when no low-level memory access is currently being executed?

This representation is the project's **canonical form**.

For example:

```text
task_inv(...)
*
assign_ready_pending(...)
*
occupy_dll_node(...)
```

may be canonical, while this may not be:

```text
store(field1, ...)
*
store(field2, ...)
*
store(field3, ...)
*
...
```

Then define strategies according to the following policy:

```text
core:
    canonical form
        ->
    expose exactly the resource needed by the next operation

post:
    low-level resources
        ->
    restore canonical form
```

Strategies therefore serve not only to remove annotations but also to maintain a stable symbolic-state normal form.

---

# 15. What Should Become a Strategy?

Whenever encountering a `which implies`, ask:

> Is this implication determined primarily by the representation of a reusable data structure, rather than by the algorithm of the current function?

If the answer is **yes**, first attempt to express it as a clean, sound, and appropriately scoped strategy. Apply this rule to both new and existing annotations; do not wait for the transformation to appear multiple times.

Typical examples:

```text
store_task(...)
    ->
store(task->field, ...)
```

```text
store_idnode(...)
    ->
store(idnode->id, ...)
```

```text
dll_node(...)
    ->
store(node->next, ...)
```

```text
store_delay(...)
    ->
store(delay->ticks, ...)
```

These are representation-level transformations for which strategy is the default. The same preference applies to exposing embedded objects or list nodes, obtaining ownership or write permission, decomposing reusable object predicates, reconstructing abstractions, and normalizing assertions.

If the implication is algorithm-specific, keep it explicit.

For example:

```text
ticks <= current_ticks
    ->
the insertion point belongs between prefix and suffix
```

or:

```text
task status is READY
    ->
a particular abstract scheduler transition is valid
```

These are usually algorithmic facts rather than data-representation plumbing.

They are generally better expressed using explicit intermediate assertions, `which implies`, or Rocq lemmas.

Use `which implies` as the explicit fallback when reasoning depends strongly on the current control-flow point, cannot be matched safely, risks loops or excessive triggering, or is substantially clearer locally. Before retaining a nontrivial representation-level implication, briefly consider whether an appropriate strategy should exist instead.

---

# 16. A Practical Classification Rule

Use the following classification.

| Reason for assertion transformation | Preferred mechanism |
|---|---|
| Field access through a reusable abstract predicate | `core` strategy |
| Ownership or write-permission extraction | `core` strategy |
| Embedded object/node exposure or reusable object decomposition | Scoped, demand-driven strategy |
| Reconstructing an abstract predicate after memory access | `post` strategy |
| Canonicalizing symbolic state | `post` strategy |
| One-off function-specific implication | `which implies` |
| Complex list/order reasoning | Rocq lemma / explicit assertion |
| Abstract state transition specific to an algorithm | Explicit Spec/assertion reasoning |
| Large invariant opening only for one field | Avoid; introduce intermediate predicates/strategies |

Do not mechanically replace every `which implies` with a strategy.

The default division is: strategy for reusable representation reasoning, `which implies` for explicit local fallback, and Rocq lemmas for mathematical or abstract logical reasoning.

---

# 17. Strategy Loops Must Be Avoided

Be careful when introducing rules in opposite directions.

For example, if the same strategy phase contains:

```text
A -> B
```

and:

```text
B -> A
```

then automation may repeatedly produce:

```text
A
-> B
-> A
-> B
-> ...
```

This causes strategy divergence.

One reason the following architecture works well is that unfolding and folding occur in different phases:

```text
core:
    abstract -> concrete

post:
    concrete -> abstract
```

When adding strategies, always check for:

- direct loops,
- indirect loops through multiple predicates,
- rules that continually enlarge the assertion,
- overlapping strategies with incompatible normal forms.

Do not solve genuine divergence merely by increasing the strategy-application limit. Fix the rule design whenever possible.

---

# 18. Strategies Must Remain Sound

A QCP strategy is **not** an unchecked rewrite rule.

Conceptually, if a strategy performs:

```text
A -> B
```

there must ultimately be a proof that the corresponding entailment is valid.

For example:

```coq
store_int_pair p x y
|--
&(p->a) |-> x **
&(p->b) |-> y
```

The normal workflow uses `StrategyCheck` to generate strategy-related proof obligations.

A typical generated structure includes files conceptually similar to:

```text
*_strategy_goal.v
*_strategy_proof.v
*_strategy_goal_check.v
```

The generated strategy goals must be proved in Rocq.

Therefore:

```text
strategy
    != axiom

strategy
    != unchecked rewrite

strategy
    = proved entailment + automatic application
```

When adding a new strategy, do not consider the task complete merely because symbolic execution succeeds. Ensure the generated strategy proof obligations are also discharged.

---

# 19. Suggested File Organization

A typical organization is:

```text
predicate/header declarations
    |
    +-- xxx.h

strategy rules
    |
    +-- xxx.strategies

strategy proofs
    |
    +-- generated/proof Rocq files
```

For example, a header may expose the predicate:

```c
/*@ Extern Coq
      (store_int_pair : Z -> Z -> Z -> Assertion)
*/
```

and include its strategies:

```c
/*@ include strategies "xxx.strategies" */
```

The strategy file may include the relevant declarations:

```text
#include "xxx.h"
```

and then define:

```text
id : ...
priority : ...
left : ...
right : ...
action : ...
```

Organize strategies by the abstract predicates they manipulate. In CRTOS, place rules under `annotated_C/strategy/`; do not place C headers there. Reuse existing headers when possible, and place strategy-specific QCP declaration headers under `annotated_C/src/headers/`.

Avoid putting all project strategies into one huge file unless there is a strong architectural reason.

---

# 20. Recommended Migration Process for This Project

Do **not** begin by rewriting `os_inv`, `task_inv`, or another very large invariant.

Instead, choose a small predicate that:

1. has a clear representation,
2. has a natural reusable relationship with its fields, embedded objects, or permissions,
3. allows safely scoped matching while preserving untouched resources.

Repeated annotations and use by several functions help prioritize candidates, but neither is required.

Good candidates may include predicates around:

```text
store_task_dync_sched
store_idnode
store_delay
store_sched_link
```

depending on the current project definitions.

For one selected predicate, proceed incrementally.

## Step 1: Identify one representative field read

For example:

```c
x = obj->field;
```

Inspect any existing `which implies` annotations used to expose this field and search for related uses. Design the strategy from the predicate/resource relationship even if this is the only current use.

## Step 2: Add one `core` read strategy

Make the field readable directly from the abstract predicate without an intermediate C annotation.

Verify that the symbolic execution result remains correct.

## Step 3: Add one `core` write strategy

Handle:

```c
obj->field = value;
```

using the appropriate permission-oriented matching
